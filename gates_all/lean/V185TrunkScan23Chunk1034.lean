import V185TrunkScan23Chunk1033

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6121628 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 1, 9]
def baseStart_6121628 : Nat := 118140960795 + 6121628 * 2 ^ 59
def prefixEnd_6121628 : Nat := 4983230072969 + 3 ^ 40 * 6121628 * 2
def baseEnd_6121628 : Nat := 1047779184007226778665717

theorem tailTrace_6121628 : CollatzResearch.WordTrace tailWord_6121628 prefixEnd_6121628 1047779184007226778665717 := by
  unfold tailWord_6121628
  simp only [CollatzResearch.WordTrace]
  refine ⟨111637057933197360835866769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148849410577596481114489025 111637057933197360835866769)
  ·
    refine ⟨83727793449898020626900077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111637057933197360835866769 83727793449898020626900077)
    ·
      refine ⟨31397922543711757735087529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83727793449898020626900077 31397922543711757735087529)
      ·
        refine ⟨23548441907783818301315647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31397922543711757735087529 23548441907783818301315647)
        ·
          refine ⟨35322662861675727451973471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23548441907783818301315647 35322662861675727451973471)
          ·
            refine ⟨52983994292513591177960207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35322662861675727451973471 52983994292513591177960207)
            ·
              refine ⟨79475991438770386766940311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52983994292513591177960207 79475991438770386766940311)
              ·
                refine ⟨119213987158155580150410467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79475991438770386766940311 119213987158155580150410467)
                ·
                  refine ⟨178820980737233370225615701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119213987158155580150410467 178820980737233370225615701)
                  ·
                    refine ⟨1047779184007226778665717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 178820980737233370225615701 1047779184007226778665717)
                    ·
                      rfl

theorem cell23_6121628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_6121628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121628 prefixEnd_6121628 := by exact prefixLift 6121628
  have htrace : WordTrace (prefixWord ++ tailWord_6121628) baseStart_6121628 baseEnd_6121628 := by
    simpa [prefixWord, tailWord_6121628, baseEnd_6121628] using wordTrace_append hprefix tailTrace_6121628
  have hstable : (prefixWord ++ tailWord_6121628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121628).length < 2 ^ (prefixWord ++ tailWord_6121628).sum := by decide
  have hdescent : baseEnd_6121628 < baseStart_6121628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121669 : List Nat := [1, 3, 1, 1, 1, 1, 8, 1, 1, 3, 2]
def baseStart_6121669 : Nat := 118140960795 + 6121669 * 2 ^ 59
def prefixEnd_6121669 : Nat := 4983230072969 + 3 ^ 40 * 6121669 * 2
def baseEnd_6121669 : Nat := 3143358604728514675584463

theorem tailTrace_6121669 : CollatzResearch.WordTrace tailWord_6121669 prefixEnd_6121669 3143358604728514675584463 := by
  unfold tailWord_6121669
  simp only [CollatzResearch.WordTrace]
  refine ⟨223275611259246185673976061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148850407506164123782650707 223275611259246185673976061)
  ·
    refine ⟨83728354222217319627741023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223275611259246185673976061 83728354222217319627741023)
    ·
      refine ⟨125592531333325979441611535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83728354222217319627741023 125592531333325979441611535)
      ·
        refine ⟨188388796999988969162417303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125592531333325979441611535 188388796999988969162417303)
        ·
          refine ⟨282583195499983453743625955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188388796999988969162417303 282583195499983453743625955)
          ·
            refine ⟨423874793249975180615438933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282583195499983453743625955 423874793249975180615438933)
            ·
              refine ⟨4967282733398146647837175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 423874793249975180615438933 4967282733398146647837175)
              ·
                refine ⟨7450924100097219971755763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4967282733398146647837175 7450924100097219971755763)
                ·
                  refine ⟨11176386150145829957633645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7450924100097219971755763 11176386150145829957633645)
                  ·
                    refine ⟨4191144806304686234112617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11176386150145829957633645 4191144806304686234112617)
                    ·
                      refine ⟨3143358604728514675584463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4191144806304686234112617 3143358604728514675584463)
                      ·
                        rfl

theorem cell23_6121669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 1, 3, 2].length) (baseStart_6121669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121669 prefixEnd_6121669 := by exact prefixLift 6121669
  have htrace : WordTrace (prefixWord ++ tailWord_6121669) baseStart_6121669 baseEnd_6121669 := by
    simpa [prefixWord, tailWord_6121669, baseEnd_6121669] using wordTrace_append hprefix tailTrace_6121669
  have hstable : (prefixWord ++ tailWord_6121669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121669).length < 2 ^ (prefixWord ++ tailWord_6121669).sum := by decide
  have hdescent : baseEnd_6121669 < baseStart_6121669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121722 : List Nat := [3, 1, 1, 1, 1, 5, 3, 3, 5]
def baseStart_6121722 : Nat := 118140960795 + 6121722 * 2 ^ 59
def prefixEnd_6121722 : Nat := 4983230072969 + 3 ^ 40 * 6121722 * 2
def baseEnd_6121722 : Nat := 349265091022578107580191

theorem tailTrace_6121722 : CollatzResearch.WordTrace tailWord_6121722 prefixEnd_6121722 349265091022578107580191 := by
  unfold tailWord_6121722
  simp only [CollatzResearch.WordTrace]
  refine ⟨55819386082013543931413855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148851696218702783817103613 55819386082013543931413855)
  ·
    refine ⟨83729079123020315897120783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55819386082013543931413855 83729079123020315897120783)
    ·
      refine ⟨125593618684530473845681175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83729079123020315897120783 125593618684530473845681175)
      ·
        refine ⟨188390428026795710768521763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125593618684530473845681175 188390428026795710768521763)
        ·
          refine ⟨282585642040193566152782645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188390428026795710768521763 282585642040193566152782645)
          ·
            refine ⟨26492403941268146826823373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 282585642040193566152782645 26492403941268146826823373)
            ·
              refine ⟨9934651477975555060058765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26492403941268146826823373 9934651477975555060058765)
              ·
                refine ⟨3725494304240833147522037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9934651477975555060058765 3725494304240833147522037)
                ·
                  refine ⟨349265091022578107580191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3725494304240833147522037 349265091022578107580191)
                  ·
                    rfl

theorem cell23_6121722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3, 5].length) (baseStart_6121722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121722 prefixEnd_6121722 := by exact prefixLift 6121722
  have htrace : WordTrace (prefixWord ++ tailWord_6121722) baseStart_6121722 baseEnd_6121722 := by
    simpa [prefixWord, tailWord_6121722, baseEnd_6121722] using wordTrace_append hprefix tailTrace_6121722
  have hstable : (prefixWord ++ tailWord_6121722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121722).length < 2 ^ (prefixWord ++ tailWord_6121722).sum := by decide
  have hdescent : baseEnd_6121722 < baseStart_6121722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121742 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2]
def baseStart_6121742 : Nat := 118140960795 + 6121742 * 2 ^ 59
def prefixEnd_6121742 : Nat := 4983230072969 + 3 ^ 40 * 6121742 * 2
def baseEnd_6121742 : Nat := 3143396088816292889971627

theorem tailTrace_6121742 : CollatzResearch.WordTrace tailWord_6121742 prefixEnd_6121742 3143396088816292889971627 := by
  unfold tailWord_6121742
  simp only [CollatzResearch.WordTrace]
  refine ⟨27909784223497714892672935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148852182525321146094255653 27909784223497714892672935)
  ·
    refine ⟨41864676335246572339009403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27909784223497714892672935 41864676335246572339009403)
    ·
      refine ⟨62797014502869858508514105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41864676335246572339009403 62797014502869858508514105)
      ·
        refine ⟨47097760877152393881385579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62797014502869858508514105 47097760877152393881385579)
        ·
          refine ⟨70646641315728590822078369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47097760877152393881385579 70646641315728590822078369)
          ·
            refine ⟨52984980986796443116558777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70646641315728590822078369 52984980986796443116558777)
            ·
              refine ⟨39738735740097332337419083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52984980986796443116558777 39738735740097332337419083)
              ·
                refine ⟨59608103610145998506128625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39738735740097332337419083 59608103610145998506128625)
                ·
                  refine ⟨44706077707609498879596469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59608103610145998506128625 44706077707609498879596469)
                  ·
                    refine ⟨4191194785088390519962169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44706077707609498879596469 4191194785088390519962169)
                    ·
                      refine ⟨3143396088816292889971627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4191194785088390519962169 3143396088816292889971627)
                      ·
                        rfl

theorem cell23_6121742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_6121742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121742 prefixEnd_6121742 := by exact prefixLift 6121742
  have htrace : WordTrace (prefixWord ++ tailWord_6121742) baseStart_6121742 baseEnd_6121742 := by
    simpa [prefixWord, tailWord_6121742, baseEnd_6121742] using wordTrace_append hprefix tailTrace_6121742
  have hstable : (prefixWord ++ tailWord_6121742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121742).length < 2 ^ (prefixWord ++ tailWord_6121742).sum := by decide
  have hdescent : baseEnd_6121742 < baseStart_6121742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121745 : List Nat := [1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 5]
def baseStart_6121745 : Nat := 118140960795 + 6121745 * 2 ^ 59
def prefixEnd_6121745 : Nat := 4983230072969 + 3 ^ 40 * 6121745 * 2
def baseEnd_6121745 : Nat := 3143397629258256378234113

theorem tailTrace_6121745 : CollatzResearch.WordTrace tailWord_6121745 prefixEnd_6121745 3143397629258256378234113 := by
  unfold tailWord_6121745
  simp only [CollatzResearch.WordTrace]
  refine ⟨223278383206970850653742689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148852255471313900435828459 223278383206970850653742689)
  ·
    refine ⟨167458787405228137990307017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223278383206970850653742689 167458787405228137990307017)
    ·
      refine ⟨125594090553921103492730263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167458787405228137990307017 125594090553921103492730263)
      ·
        refine ⟨188391135830881655239095395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125594090553921103492730263 188391135830881655239095395)
        ·
          refine ⟨282586703746322482858643093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188391135830881655239095395 282586703746322482858643093)
          ·
            refine ⟨13246251738108866383998895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 282586703746322482858643093 13246251738108866383998895)
            ·
              refine ⟨19869377607163299575998343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13246251738108866383998895 19869377607163299575998343)
              ·
                refine ⟨29804066410744949363997515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19869377607163299575998343 29804066410744949363997515)
                ·
                  refine ⟨44706099616117424045996273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29804066410744949363997515 44706099616117424045996273)
                  ·
                    refine ⟨33529574712088068034497205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44706099616117424045996273 33529574712088068034497205)
                    ·
                      refine ⟨3143397629258256378234113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33529574712088068034497205 3143397629258256378234113)
                      ·
                        rfl

theorem cell23_6121745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_6121745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121745 prefixEnd_6121745 := by exact prefixLift 6121745
  have htrace : WordTrace (prefixWord ++ tailWord_6121745) baseStart_6121745 baseEnd_6121745 := by
    simpa [prefixWord, tailWord_6121745, baseEnd_6121745] using wordTrace_append hprefix tailTrace_6121745
  have hstable : (prefixWord ++ tailWord_6121745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121745).length < 2 ^ (prefixWord ++ tailWord_6121745).sum := by decide
  have hdescent : baseEnd_6121745 < baseStart_6121745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121775 : List Nat := [1, 1, 2, 1, 2, 1, 4, 3, 1, 4, 3]
def baseStart_6121775 : Nat := 118140960795 + 6121775 * 2 ^ 59
def prefixEnd_6121775 : Nat := 4983230072969 + 3 ^ 40 * 6121775 * 2
def baseEnd_6121775 : Nat := 3143413033677891260858975

theorem tailTrace_6121775 : CollatzResearch.WordTrace tailWord_6121775 prefixEnd_6121775 3143413033677891260858975 := by
  unfold tailWord_6121775
  simp only [CollatzResearch.WordTrace]
  refine ⟨223279477396862165777334779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148852984931241443851556519 223279477396862165777334779)
  ·
    refine ⟨334919216095293248666002169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223279477396862165777334779 334919216095293248666002169)
    ·
      refine ⟨251189412071469936499501627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334919216095293248666002169 251189412071469936499501627)
      ·
        refine ⟨376784118107204904749252441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251189412071469936499501627 376784118107204904749252441)
        ·
          refine ⟨282588088580403678561939331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376784118107204904749252441 282588088580403678561939331)
          ·
            refine ⟨423882132870605517842908997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282588088580403678561939331 423882132870605517842908997)
            ·
              refine ⟨79477899913238534595545437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 423882132870605517842908997 79477899913238534595545437)
              ·
                refine ⟨29804212467464450473329539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79477899913238534595545437 29804212467464450473329539)
                ·
                  refine ⟨44706318701196675709994309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29804212467464450473329539 44706318701196675709994309)
                  ·
                    refine ⟨8382434756474376695623933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44706318701196675709994309 8382434756474376695623933)
                    ·
                      refine ⟨3143413033677891260858975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8382434756474376695623933 3143413033677891260858975)
                      ·
                        rfl

theorem cell23_6121775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4, 3].length) (baseStart_6121775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121775 prefixEnd_6121775 := by exact prefixLift 6121775
  have htrace : WordTrace (prefixWord ++ tailWord_6121775) baseStart_6121775 baseEnd_6121775 := by
    simpa [prefixWord, tailWord_6121775, baseEnd_6121775] using wordTrace_append hprefix tailTrace_6121775
  have hstable : (prefixWord ++ tailWord_6121775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121775).length < 2 ^ (prefixWord ++ tailWord_6121775).sum := by decide
  have hdescent : baseEnd_6121775 < baseStart_6121775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121795 : List Nat := [1, 1, 1, 3, 1, 3, 3, 4, 6]
def baseStart_6121795 : Nat := 118140960795 + 6121795 * 2 ^ 59
def prefixEnd_6121795 : Nat := 4983230072969 + 3 ^ 40 * 6121795 * 2
def baseEnd_6121795 : Nat := 349269255921220131400987

theorem tailTrace_6121795 : CollatzResearch.WordTrace tailWord_6121795 prefixEnd_6121795 349269255921220131400987 := by
  unfold tailWord_6121795
  simp only [CollatzResearch.WordTrace]
  refine ⟨223280206856789709193062839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148853471237859806128708559 223280206856789709193062839)
  ·
    refine ⟨334920310285184563789594259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223280206856789709193062839 334920310285184563789594259)
    ·
      refine ⟨502380465427776845684391389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334920310285184563789594259 502380465427776845684391389)
      ·
        refine ⟨188392674535416317131646771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 502380465427776845684391389 188392674535416317131646771)
        ·
          refine ⟨282589011803124475697470157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188392674535416317131646771 282589011803124475697470157)
          ·
            refine ⟨105970879426171678386551309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 282589011803124475697470157 105970879426171678386551309)
            ·
              refine ⟨39739079784814379394956741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105970879426171678386551309 39739079784814379394956741)
              ·
                refine ⟨7451077459652696136554389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39739079784814379394956741 7451077459652696136554389)
                ·
                  refine ⟨349269255921220131400987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7451077459652696136554389 349269255921220131400987)
                  ·
                    rfl

theorem cell23_6121795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 6].length) (baseStart_6121795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121795 prefixEnd_6121795 := by exact prefixLift 6121795
  have htrace : WordTrace (prefixWord ++ tailWord_6121795) baseStart_6121795 baseEnd_6121795 := by
    simpa [prefixWord, tailWord_6121795, baseEnd_6121795] using wordTrace_append hprefix tailTrace_6121795
  have hstable : (prefixWord ++ tailWord_6121795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121795).length < 2 ^ (prefixWord ++ tailWord_6121795).sum := by decide
  have hdescent : baseEnd_6121795 < baseStart_6121795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121799 : List Nat := [1, 1, 4, 1, 2, 2, 3, 4, 1, 4]
def baseStart_6121799 : Nat := 118140960795 + 6121799 * 2 ^ 59
def prefixEnd_6121799 : Nat := 4983230072969 + 3 ^ 40 * 6121799 * 2
def baseEnd_6121799 : Nat := 1047808452404533055652955

theorem tailTrace_6121799 : CollatzResearch.WordTrace tailWord_6121799 prefixEnd_6121799 1047808452404533055652955 := by
  unfold tailWord_6121799
  simp only [CollatzResearch.WordTrace]
  refine ⟨223280352748775217876208451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148853568499183478584138967 223280352748775217876208451)
  ·
    refine ⟨334920529123162826814312677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223280352748775217876208451 334920529123162826814312677)
    ·
      refine ⟨62797599210593030027683627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 334920529123162826814312677 62797599210593030027683627)
      ·
        refine ⟨94196398815889545041525441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62797599210593030027683627 94196398815889545041525441)
        ·
          refine ⟨70647299111917158781144081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94196398815889545041525441 70647299111917158781144081)
          ·
            refine ⟨52985474333937869085858061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70647299111917158781144081 52985474333937869085858061)
            ·
              refine ⟨19869552875226700907196773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52985474333937869085858061 19869552875226700907196773)
              ·
                refine ⟨3725541164105006420099395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19869552875226700907196773 3725541164105006420099395)
                ·
                  refine ⟨5588311746157509630149093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3725541164105006420099395 5588311746157509630149093)
                  ·
                    refine ⟨1047808452404533055652955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5588311746157509630149093 1047808452404533055652955)
                    ·
                      rfl

theorem cell23_6121799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_6121799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121799 prefixEnd_6121799 := by exact prefixLift 6121799
  have htrace : WordTrace (prefixWord ++ tailWord_6121799) baseStart_6121799 baseEnd_6121799 := by
    simpa [prefixWord, tailWord_6121799, baseEnd_6121799] using wordTrace_append hprefix tailTrace_6121799
  have hstable : (prefixWord ++ tailWord_6121799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121799).length < 2 ^ (prefixWord ++ tailWord_6121799).sum := by decide
  have hdescent : baseEnd_6121799 < baseStart_6121799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121812 : List Nat := [2, 4, 1, 1, 2, 2, 2, 3, 6]
def baseStart_6121812 : Nat := 118140960795 + 6121812 * 2 ^ 59
def prefixEnd_6121812 : Nat := 4983230072969 + 3 ^ 40 * 6121812 * 2
def baseEnd_6121812 : Nat := 349270225829123068455145

theorem tailTrace_6121812 : CollatzResearch.WordTrace tailWord_6121812 prefixEnd_6121812 349270225829123068455145 := by
  unfold tailWord_6121812
  simp only [CollatzResearch.WordTrace]
  refine ⟨111640413448864060548215845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148853884598485414064287793 111640413448864060548215845)
  ·
    refine ⟨20932577521662011352790471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111640413448864060548215845 20932577521662011352790471)
    ·
      refine ⟨31398866282493017029185707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20932577521662011352790471 31398866282493017029185707)
      ·
        refine ⟨47098299423739525543778561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31398866282493017029185707 47098299423739525543778561)
        ·
          refine ⟨35323724567804644157833921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47098299423739525543778561 35323724567804644157833921)
          ·
            refine ⟨26492793425853483118375441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35323724567804644157833921 26492793425853483118375441)
            ·
              refine ⟨19869595069390112338781581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26492793425853483118375441 19869595069390112338781581)
              ·
                refine ⟨7451098151021292127043093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19869595069390112338781581 7451098151021292127043093)
                ·
                  refine ⟨349270225829123068455145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7451098151021292127043093 349270225829123068455145)
                  ·
                    rfl

theorem cell23_6121812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_6121812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121812 prefixEnd_6121812 := by exact prefixLift 6121812
  have htrace : WordTrace (prefixWord ++ tailWord_6121812) baseStart_6121812 baseEnd_6121812 := by
    simpa [prefixWord, tailWord_6121812, baseEnd_6121812] using wordTrace_append hprefix tailTrace_6121812
  have hstable : (prefixWord ++ tailWord_6121812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121812).length < 2 ^ (prefixWord ++ tailWord_6121812).sum := by decide
  have hdescent : baseEnd_6121812 < baseStart_6121812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121826 : List Nat := [3, 3, 2, 1, 1, 4, 1, 1, 2, 2, 3]
def baseStart_6121826 : Nat := 118140960795 + 6121826 * 2 ^ 59
def prefixEnd_6121826 : Nat := 4983230072969 + 3 ^ 40 * 6121826 * 2
def baseEnd_6121826 : Nat := 3143439221191270561321241

theorem tailTrace_6121826 : CollatzResearch.WordTrace tailWord_6121826 prefixEnd_6121826 3143439221191270561321241 := by
  unfold tailWord_6121826
  simp only [CollatzResearch.WordTrace]
  refine ⟨55820334379919350371860333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148854225013118267658294221 55820334379919350371860333)
  ·
    refine ⟨20932625392469756389447625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55820334379919350371860333 20932625392469756389447625)
    ·
      refine ⟨15699469044352317292085719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20932625392469756389447625 15699469044352317292085719)
      ·
        refine ⟨23549203566528475938128579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15699469044352317292085719 23549203566528475938128579)
        ·
          refine ⟨35323805349792713907192869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23549203566528475938128579 35323805349792713907192869)
          ·
            refine ⟨6623213503086133857598663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35323805349792713907192869 6623213503086133857598663)
            ·
              refine ⟨9934820254629200786397995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6623213503086133857598663 9934820254629200786397995)
              ·
                refine ⟨14902230381943801179596993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9934820254629200786397995 14902230381943801179596993)
                ·
                  refine ⟨11176672786457850884697745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14902230381943801179596993 11176672786457850884697745)
                  ·
                    refine ⟨8382504589843388163523309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11176672786457850884697745 8382504589843388163523309)
                    ·
                      refine ⟨3143439221191270561321241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8382504589843388163523309 3143439221191270561321241)
                      ·
                        rfl

theorem cell23_6121826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_6121826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121826 prefixEnd_6121826 := by exact prefixLift 6121826
  have htrace : WordTrace (prefixWord ++ tailWord_6121826) baseStart_6121826 baseEnd_6121826 := by
    simpa [prefixWord, tailWord_6121826, baseEnd_6121826] using wordTrace_append hprefix tailTrace_6121826
  have hstable : (prefixWord ++ tailWord_6121826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121826).length < 2 ^ (prefixWord ++ tailWord_6121826).sum := by decide
  have hdescent : baseEnd_6121826 < baseStart_6121826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121876 : List Nat := [2, 4, 2, 1, 3, 1, 2, 2, 1, 5]
def baseStart_6121876 : Nat := 118140960795 + 6121876 * 2 ^ 59
def prefixEnd_6121876 : Nat := 4983230072969 + 3 ^ 40 * 6121876 * 2
def baseEnd_6121876 : Nat := 1047821631741331788565337

theorem tailTrace_6121876 : CollatzResearch.WordTrace tailWord_6121876 prefixEnd_6121876 1047821631741331788565337 := by
  unfold tailWord_6121876
  simp only [CollatzResearch.WordTrace]
  refine ⟨111641580584748130013380741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148855440779664173351174321 111641580584748130013380741)
  ·
    refine ⟨20932796359640274377508889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111641580584748130013380741 20932796359640274377508889)
    ·
      refine ⟨15699597269730205783131667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20932796359640274377508889 15699597269730205783131667)
      ·
        refine ⟨23549395904595308674697501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15699597269730205783131667 23549395904595308674697501)
        ·
          refine ⟨8831023464223240753011563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23549395904595308674697501 8831023464223240753011563)
          ·
            refine ⟨13246535196334861129517345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8831023464223240753011563 13246535196334861129517345)
            ·
              refine ⟨9934901397251145847138009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13246535196334861129517345 9934901397251145847138009)
              ·
                refine ⟨7451176047938359385353507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9934901397251145847138009 7451176047938359385353507)
                ·
                  refine ⟨11176764071907539078030261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7451176047938359385353507 11176764071907539078030261)
                  ·
                    refine ⟨1047821631741331788565337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11176764071907539078030261 1047821631741331788565337)
                    ·
                      rfl

theorem cell23_6121876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_6121876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121876 prefixEnd_6121876 := by exact prefixLift 6121876
  have htrace : WordTrace (prefixWord ++ tailWord_6121876) baseStart_6121876 baseEnd_6121876 := by
    simpa [prefixWord, tailWord_6121876, baseEnd_6121876] using wordTrace_append hprefix tailTrace_6121876
  have hstable : (prefixWord ++ tailWord_6121876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121876).length < 2 ^ (prefixWord ++ tailWord_6121876).sum := by decide
  have hdescent : baseEnd_6121876 < baseStart_6121876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121892 : List Nat := [2, 3, 1, 2, 1, 1, 2, 4, 1, 2, 4]
def baseStart_6121892 : Nat := 118140960795 + 6121892 * 2 ^ 59
def prefixEnd_6121892 : Nat := 4983230072969 + 3 ^ 40 * 6121892 * 2
def baseEnd_6121892 : Nat := 3143473110914467303095937

theorem tailTrace_6121892 : CollatzResearch.WordTrace tailWord_6121892 prefixEnd_6121892 3143473110914467303095937 := by
  unfold tailWord_6121892
  simp only [CollatzResearch.WordTrace]
  refine ⟨111641872368719147379671965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148855829824958863172895953 111641872368719147379671965)
  ·
    refine ⟨41865702138269680267376987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111641872368719147379671965 41865702138269680267376987)
    ·
      refine ⟨62798553207404520401065481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41865702138269680267376987 62798553207404520401065481)
      ·
        refine ⟨47098914905553390300799111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62798553207404520401065481 47098914905553390300799111)
        ·
          refine ⟨70648372358330085451198667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47098914905553390300799111 70648372358330085451198667)
          ·
            refine ⟨105972558537495128176798001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70648372358330085451198667 105972558537495128176798001)
            ·
              refine ⟨79479418903121346132598501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105972558537495128176798001 79479418903121346132598501)
              ·
                refine ⟨14902391044335252399862219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79479418903121346132598501 14902391044335252399862219)
                ·
                  refine ⟨22353586566502878599793329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14902391044335252399862219 22353586566502878599793329)
                  ·
                    refine ⟨16765189924877158949844997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22353586566502878599793329 16765189924877158949844997)
                    ·
                      refine ⟨3143473110914467303095937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16765189924877158949844997 3143473110914467303095937)
                      ·
                        rfl

theorem cell23_6121892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_6121892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121892 prefixEnd_6121892 := by exact prefixLift 6121892
  have htrace : WordTrace (prefixWord ++ tailWord_6121892) baseStart_6121892 baseEnd_6121892 := by
    simpa [prefixWord, tailWord_6121892, baseEnd_6121892] using wordTrace_append hprefix tailTrace_6121892
  have hstable : (prefixWord ++ tailWord_6121892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121892).length < 2 ^ (prefixWord ++ tailWord_6121892).sum := by decide
  have hdescent : baseEnd_6121892 < baseStart_6121892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121896 : List Nat := [2, 1, 6, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_6121896 : Nat := 118140960795 + 6121896 * 2 ^ 59
def prefixEnd_6121896 : Nat := 4983230072969 + 3 ^ 40 * 6121896 * 2
def baseEnd_6121896 : Nat := 3143475164837085287445919

theorem tailTrace_6121896 : CollatzResearch.WordTrace tailWord_6121896 prefixEnd_6121896 3143475164837085287445919 := by
  unfold tailWord_6121896
  simp only [CollatzResearch.WordTrace]
  refine ⟨111641945314711901721244771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148855927086282535628326361 111641945314711901721244771)
  ·
    refine ⟨167462917972067852581867157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111641945314711901721244771 167462917972067852581867157)
    ·
      refine ⟨7849824279940680589775023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 167462917972067852581867157 7849824279940680589775023)
      ·
        refine ⟨11774736419911020884662535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7849824279940680589775023 11774736419911020884662535)
        ·
          refine ⟨17662104629866531326993803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11774736419911020884662535 17662104629866531326993803)
          ·
            refine ⟨26493156944799796990490705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17662104629866531326993803 26493156944799796990490705)
            ·
              refine ⟨19869867708599847742868029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26493156944799796990490705 19869867708599847742868029)
              ·
                refine ⟨7451200390724942903575511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19869867708599847742868029 7451200390724942903575511)
                ·
                  refine ⟨11176800586087414355363267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7451200390724942903575511 11176800586087414355363267)
                  ·
                    refine ⟨16765200879131121533044901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11176800586087414355363267 16765200879131121533044901)
                    ·
                      refine ⟨3143475164837085287445919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16765200879131121533044901 3143475164837085287445919)
                      ·
                        rfl

theorem cell23_6121896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_6121896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121896 prefixEnd_6121896 := by exact prefixLift 6121896
  have htrace : WordTrace (prefixWord ++ tailWord_6121896) baseStart_6121896 baseEnd_6121896 := by
    simpa [prefixWord, tailWord_6121896, baseEnd_6121896] using wordTrace_append hprefix tailTrace_6121896
  have hstable : (prefixWord ++ tailWord_6121896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121896).length < 2 ^ (prefixWord ++ tailWord_6121896).sum := by decide
  have hdescent : baseEnd_6121896 < baseStart_6121896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121913 : List Nat := [1, 2, 1, 4, 3, 3, 1, 1, 3, 2, 2]
def baseStart_6121913 : Nat := 118140960795 + 6121913 * 2 ^ 59
def prefixEnd_6121913 : Nat := 4983230072969 + 3 ^ 40 * 6121913 * 2
def baseEnd_6121913 : Nat := 3143483894008211720933341

theorem tailTrace_6121913 : CollatzResearch.WordTrace tailWord_6121913 prefixEnd_6121913 3143483894008211720933341 := by
  unfold tailWord_6121913
  simp only [CollatzResearch.WordTrace]
  refine ⟨223284510670362215345858393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148856340446908143563905595 223284510670362215345858393)
  ·
    refine ⟨167463383002771661509393795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223284510670362215345858393 167463383002771661509393795)
    ·
      refine ⟨251195074504157492264090693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167463383002771661509393795 251195074504157492264090693)
      ·
        refine ⟨47099076469529529799517005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 251195074504157492264090693 47099076469529529799517005)
        ·
          refine ⟨17662153676073573674818877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47099076469529529799517005 17662153676073573674818877)
          ·
            refine ⟨6623307628527590128057079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17662153676073573674818877 6623307628527590128057079)
            ·
              refine ⟨9934961442791385192085619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6623307628527590128057079 9934961442791385192085619)
              ·
                refine ⟨14902442164187077788128429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9934961442791385192085619 14902442164187077788128429)
                ·
                  refine ⟨5588415811570154170548161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14902442164187077788128429 5588415811570154170548161)
                  ·
                    refine ⟨4191311858677615627911121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5588415811570154170548161 4191311858677615627911121)
                    ·
                      refine ⟨3143483894008211720933341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4191311858677615627911121 3143483894008211720933341)
                      ·
                        rfl

theorem cell23_6121913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_6121913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121913 prefixEnd_6121913 := by exact prefixLift 6121913
  have htrace : WordTrace (prefixWord ++ tailWord_6121913) baseStart_6121913 baseEnd_6121913 := by
    simpa [prefixWord, tailWord_6121913, baseEnd_6121913] using wordTrace_append hprefix tailTrace_6121913
  have hstable : (prefixWord ++ tailWord_6121913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121913).length < 2 ^ (prefixWord ++ tailWord_6121913).sum := by decide
  have hdescent : baseEnd_6121913 < baseStart_6121913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121935 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 8]
def baseStart_6121935 : Nat := 118140960795 + 6121935 * 2 ^ 59
def prefixEnd_6121935 : Nat := 4983230072969 + 3 ^ 40 * 6121935 * 2
def baseEnd_6121935 : Nat := 3143495190582610634858239

theorem tailTrace_6121935 : CollatzResearch.WordTrace tailWord_6121935 prefixEnd_6121935 3143495190582610634858239 := by
  unfold tailWord_6121935
  simp only [CollatzResearch.WordTrace]
  refine ⟨223285313076282513103159259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148856875384188342068772839 223285313076282513103159259)
  ·
    refine ⟨334927969614423769654738889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223285313076282513103159259 334927969614423769654738889)
    ·
      refine ⟨251195977210817827241054167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334927969614423769654738889 251195977210817827241054167)
      ·
        refine ⟨376793965816226740861581251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251195977210817827241054167 376793965816226740861581251)
        ·
          refine ⟨565190948724340111292371877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376793965816226740861581251 565190948724340111292371877)
          ·
            refine ⟨105973302885813770867319727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 565190948724340111292371877 105973302885813770867319727)
            ·
              refine ⟨158959954328720656300979591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105973302885813770867319727 158959954328720656300979591)
              ·
                refine ⟨238439931493080984451469387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158959954328720656300979591 238439931493080984451469387)
                ·
                  refine ⟨357659897239621476677204081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 238439931493080984451469387 357659897239621476677204081)
                  ·
                    refine ⟨268244922929716107507903061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 357659897239621476677204081 268244922929716107507903061)
                    ·
                      refine ⟨3143495190582610634858239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 268244922929716107507903061 3143495190582610634858239)
                      ·
                        rfl

theorem cell23_6121935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 8].length) (baseStart_6121935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121935 prefixEnd_6121935 := by exact prefixLift 6121935
  have htrace : WordTrace (prefixWord ++ tailWord_6121935) baseStart_6121935 baseEnd_6121935 := by
    simpa [prefixWord, tailWord_6121935, baseEnd_6121935] using wordTrace_append hprefix tailTrace_6121935
  have hstable : (prefixWord ++ tailWord_6121935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121935).length < 2 ^ (prefixWord ++ tailWord_6121935).sum := by decide
  have hdescent : baseEnd_6121935 < baseStart_6121935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6121969 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 3, 4, 2]
def baseStart_6121969 : Nat := 118140960795 + 6121969 * 2 ^ 59
def prefixEnd_6121969 : Nat := 4983230072969 + 3 ^ 40 * 6121969 * 2
def baseEnd_6121969 : Nat := 3143512648924863501833083

theorem tailTrace_6121969 : CollatzResearch.WordTrace tailWord_6121969 prefixEnd_6121969 3143512648924863501833083 := by
  unfold tailWord_6121969
  simp only [CollatzResearch.WordTrace]
  refine ⟨223286553158159336909896961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148857702105439557939931307 223286553158159336909896961)
  ·
    refine ⟨167464914868619502682422721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223286553158159336909896961 167464914868619502682422721)
    ·
      refine ⟨125598686151464627011817041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167464914868619502682422721 125598686151464627011817041)
      ·
        refine ⟨94199014613598470258862781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125598686151464627011817041 94199014613598470258862781)
        ·
          refine ⟨35324630480099426347073543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94199014613598470258862781 35324630480099426347073543)
          ·
            refine ⟨52986945720149139520610315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35324630480099426347073543 52986945720149139520610315)
            ·
              refine ⟨79480418580223709280915473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52986945720149139520610315 79480418580223709280915473)
              ·
                refine ⟨59610313935167781960686605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79480418580223709280915473 59610313935167781960686605)
                ·
                  refine ⟨22353867725687918235257477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59610313935167781960686605 22353867725687918235257477)
                  ·
                    refine ⟨4191350198566484669110777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22353867725687918235257477 4191350198566484669110777)
                    ·
                      refine ⟨3143512648924863501833083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4191350198566484669110777 3143512648924863501833083)
                      ·
                        rfl

theorem cell23_6121969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 4, 2].length) (baseStart_6121969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6121969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6121969 prefixEnd_6121969 := by exact prefixLift 6121969
  have htrace : WordTrace (prefixWord ++ tailWord_6121969) baseStart_6121969 baseEnd_6121969 := by
    simpa [prefixWord, tailWord_6121969, baseEnd_6121969] using wordTrace_append hprefix tailTrace_6121969
  have hstable : (prefixWord ++ tailWord_6121969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6121969).length < 2 ^ (prefixWord ++ tailWord_6121969).sum := by decide
  have hdescent : baseEnd_6121969 < baseStart_6121969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6121969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122007 : List Nat := [1, 1, 3, 6, 1, 2, 2, 1, 1, 3, 2]
def baseStart_6122007 : Nat := 118140960795 + 6122007 * 2 ^ 59
def prefixEnd_6122007 : Nat := 4983230072969 + 3 ^ 40 * 6122007 * 2
def baseEnd_6122007 : Nat := 3143532161189734353157909

theorem tailTrace_6122007 : CollatzResearch.WordTrace tailWord_6122007 prefixEnd_6122007 3143532161189734353157909 := by
  unfold tailWord_6122007
  simp only [CollatzResearch.WordTrace]
  refine ⟨223287939132021669399780275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148858626088014446266520183 223287939132021669399780275)
  ·
    refine ⟨334931908698032504099670413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223287939132021669399780275 334931908698032504099670413)
    ·
      refine ⟨125599465761762189037376405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 334931908698032504099670413 125599465761762189037376405)
      ·
        refine ⟨5887474957582602611127019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 125599465761762189037376405 5887474957582602611127019)
        ·
          refine ⟨8831212436373903916690529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5887474957582602611127019 8831212436373903916690529)
          ·
            refine ⟨6623409327280427937517897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8831212436373903916690529 6623409327280427937517897)
            ·
              refine ⟨4967556995460320953138423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6623409327280427937517897 4967556995460320953138423)
              ·
                refine ⟨7451335493190481429707635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4967556995460320953138423 7451335493190481429707635)
                ·
                  refine ⟨11177003239785722144561453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7451335493190481429707635 11177003239785722144561453)
                  ·
                    refine ⟨4191376214919645804210545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11177003239785722144561453 4191376214919645804210545)
                    ·
                      refine ⟨3143532161189734353157909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4191376214919645804210545 3143532161189734353157909)
                      ·
                        rfl

theorem cell23_6122007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_6122007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122007 prefixEnd_6122007 := by exact prefixLift 6122007
  have htrace : WordTrace (prefixWord ++ tailWord_6122007) baseStart_6122007 baseEnd_6122007 := by
    simpa [prefixWord, tailWord_6122007, baseEnd_6122007] using wordTrace_append hprefix tailTrace_6122007
  have hstable : (prefixWord ++ tailWord_6122007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122007).length < 2 ^ (prefixWord ++ tailWord_6122007).sum := by decide
  have hdescent : baseEnd_6122007 < baseStart_6122007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122019 : List Nat := [1, 1, 1, 4, 4, 1, 1, 2, 2, 3, 3]
def baseStart_6122019 : Nat := 118140960795 + 6122019 * 2 ^ 59
def prefixEnd_6122019 : Nat := 4983230072969 + 3 ^ 40 * 6122019 * 2
def baseEnd_6122019 : Nat := 3143538322957588306207853

theorem tailTrace_6122019 : CollatzResearch.WordTrace tailWord_6122019 prefixEnd_6122019 3143538322957588306207853 := by
  unfold tailWord_6122019
  simp only [CollatzResearch.WordTrace]
  refine ⟨223288376807978195449217111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148858917871985463632811407 223288376807978195449217111)
  ·
    refine ⟨334932565211967293173825667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223288376807978195449217111 334932565211967293173825667)
    ·
      refine ⟨502398847817950939760738501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334932565211967293173825667 502398847817950939760738501)
      ·
        refine ⟨94199783965865801205138469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 502398847817950939760738501 94199783965865801205138469)
        ·
          refine ⟨17662459493599837725963463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94199783965865801205138469 17662459493599837725963463)
          ·
            refine ⟨26493689240399756588945195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17662459493599837725963463 26493689240399756588945195)
            ·
              refine ⟨39740533860599634883417793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26493689240399756588945195 39740533860599634883417793)
              ·
                refine ⟨29805400395449726162563345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39740533860599634883417793 29805400395449726162563345)
                ·
                  refine ⟨22354050296587294621922509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29805400395449726162563345 22354050296587294621922509)
                  ·
                    refine ⟨8382768861220235483220941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22354050296587294621922509 8382768861220235483220941)
                    ·
                      refine ⟨3143538322957588306207853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8382768861220235483220941 3143538322957588306207853)
                      ·
                        rfl

theorem cell23_6122019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_6122019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122019 prefixEnd_6122019 := by exact prefixLift 6122019
  have htrace : WordTrace (prefixWord ++ tailWord_6122019) baseStart_6122019 baseEnd_6122019 := by
    simpa [prefixWord, tailWord_6122019, baseEnd_6122019] using wordTrace_append hprefix tailTrace_6122019
  have hstable : (prefixWord ++ tailWord_6122019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122019).length < 2 ^ (prefixWord ++ tailWord_6122019).sum := by decide
  have hdescent : baseEnd_6122019 < baseStart_6122019 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122020 : List Nat := [2, 3, 1, 5, 1, 1, 1, 1, 4, 2, 2]
def baseStart_6122020 : Nat := 118140960795 + 6122020 * 2 ^ 59
def prefixEnd_6122020 : Nat := 4983230072969 + 3 ^ 40 * 6122020 * 2
def baseEnd_6122020 : Nat := 3143538836438242802295349

theorem tailTrace_6122020 : CollatzResearch.WordTrace tailWord_6122020 prefixEnd_6122020 3143538836438242802295349 := by
  unfold tailWord_6122020
  simp only [CollatzResearch.WordTrace]
  refine ⟨111644206640487286310001757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148858942187316381746669009 111644206640487286310001757)
  ·
    refine ⟨41866577490182732366250659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111644206640487286310001757 41866577490182732366250659)
    ·
      refine ⟨62799866235274098549375989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41866577490182732366250659 62799866235274098549375989)
      ·
        refine ⟨5887487459556946739003999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62799866235274098549375989 5887487459556946739003999)
        ·
          refine ⟨8831231189335420108505999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5887487459556946739003999 8831231189335420108505999)
          ·
            refine ⟨13246846784003130162758999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8831231189335420108505999 13246846784003130162758999)
            ·
              refine ⟨19870270176004695244138499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13246846784003130162758999 19870270176004695244138499)
              ·
                refine ⟨29805405264007042866207749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19870270176004695244138499 29805405264007042866207749)
                ·
                  refine ⟨5588513487001320537413953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29805405264007042866207749 5588513487001320537413953)
                  ·
                    refine ⟨4191385115250990403060465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5588513487001320537413953 4191385115250990403060465)
                    ·
                      refine ⟨3143538836438242802295349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4191385115250990403060465 3143538836438242802295349)
                      ·
                        rfl

theorem cell23_6122020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_6122020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122020 prefixEnd_6122020 := by exact prefixLift 6122020
  have htrace : WordTrace (prefixWord ++ tailWord_6122020) baseStart_6122020 baseEnd_6122020 := by
    simpa [prefixWord, tailWord_6122020, baseEnd_6122020] using wordTrace_append hprefix tailTrace_6122020
  have hstable : (prefixWord ++ tailWord_6122020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122020).length < 2 ^ (prefixWord ++ tailWord_6122020).sum := by decide
  have hdescent : baseEnd_6122020 < baseStart_6122020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122026 : List Nat := [3, 1, 4, 1, 1, 2, 2, 4, 5]
def baseStart_6122026 : Nat := 118140960795 + 6122026 * 2 ^ 59
def prefixEnd_6122026 : Nat := 4983230072969 + 3 ^ 40 * 6122026 * 2
def baseEnd_6122026 : Nat := 349282435258018864313369

theorem tailTrace_6122026 : CollatzResearch.WordTrace tailWord_6122026 prefixEnd_6122026 349282435258018864313369 := by
  unfold tailWord_6122026
  simp only [CollatzResearch.WordTrace]
  refine ⟨55822158029738208911180483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148859088079301890429814621 55822158029738208911180483)
  ·
    refine ⟨83733237044607313366770725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55822158029738208911180483 83733237044607313366770725)
    ·
      refine ⟨15699981945863871256269511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83733237044607313366770725 15699981945863871256269511)
      ·
        refine ⟨23549972918795806884404267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15699981945863871256269511 23549972918795806884404267)
        ·
          refine ⟨35324959378193710326606401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23549972918795806884404267 35324959378193710326606401)
          ·
            refine ⟨26493719533645282744954801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35324959378193710326606401 26493719533645282744954801)
            ·
              refine ⟨19870289650233962058716101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26493719533645282744954801 19870289650233962058716101)
              ·
                refine ⟨3725679309418867886009269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19870289650233962058716101 3725679309418867886009269)
                ·
                  refine ⟨349282435258018864313369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3725679309418867886009269 349282435258018864313369)
                  ·
                    rfl

theorem cell23_6122026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4, 5].length) (baseStart_6122026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122026 prefixEnd_6122026 := by exact prefixLift 6122026
  have htrace : WordTrace (prefixWord ++ tailWord_6122026) baseStart_6122026 baseEnd_6122026 := by
    simpa [prefixWord, tailWord_6122026, baseEnd_6122026] using wordTrace_append hprefix tailTrace_6122026
  have hstable : (prefixWord ++ tailWord_6122026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122026).length < 2 ^ (prefixWord ++ tailWord_6122026).sum := by decide
  have hdescent : baseEnd_6122026 < baseStart_6122026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122032 : List Nat := [2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 5]
def baseStart_6122032 : Nat := 118140960795 + 6122032 * 2 ^ 59
def prefixEnd_6122032 : Nat := 4983230072969 + 3 ^ 40 * 6122032 * 2
def baseEnd_6122032 : Nat := 3143544998206096755345293

theorem tailTrace_6122032 : CollatzResearch.WordTrace tailWord_6122032 prefixEnd_6122032 3143544998206096755345293 := by
  unfold tailWord_6122032
  simp only [CollatzResearch.WordTrace]
  refine ⟨111644425478465549334720175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148859233971287399112960233 111644425478465549334720175)
  ·
    refine ⟨167466638217698324002080263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111644425478465549334720175 167466638217698324002080263)
    ·
      refine ⟨251199957326547486003120395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167466638217698324002080263 251199957326547486003120395)
      ·
        refine ⟨376799935989821229004680593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251199957326547486003120395 376799935989821229004680593)
        ·
          refine ⟨282599951992365921753510445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376799935989821229004680593 282599951992365921753510445)
          ·
            refine ⟨105974981997137220657566417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 282599951992365921753510445 105974981997137220657566417)
            ·
              refine ⟨79481236497852915493174813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105974981997137220657566417 79481236497852915493174813)
              ·
                refine ⟨29805463686694843309940555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79481236497852915493174813 29805463686694843309940555)
                ·
                  refine ⟨44708195530042264964910833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29805463686694843309940555 44708195530042264964910833)
                  ·
                    refine ⟨33531146647531698723683125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44708195530042264964910833 33531146647531698723683125)
                    ·
                      refine ⟨3143544998206096755345293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33531146647531698723683125 3143544998206096755345293)
                      ·
                        rfl

theorem cell23_6122032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 5].length) (baseStart_6122032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122032 prefixEnd_6122032 := by exact prefixLift 6122032
  have htrace : WordTrace (prefixWord ++ tailWord_6122032) baseStart_6122032 baseEnd_6122032 := by
    simpa [prefixWord, tailWord_6122032, baseEnd_6122032] using wordTrace_append hprefix tailTrace_6122032
  have hstable : (prefixWord ++ tailWord_6122032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122032).length < 2 ^ (prefixWord ++ tailWord_6122032).sum := by decide
  have hdescent : baseEnd_6122032 < baseStart_6122032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122059 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 1, 6, 2]
def baseStart_6122059 : Nat := 118140960795 + 6122059 * 2 ^ 59
def prefixEnd_6122059 : Nat := 4983230072969 + 3 ^ 40 * 6122059 * 2
def baseEnd_6122059 : Nat := 3143558862183768149707669

theorem tailTrace_6122059 : CollatzResearch.WordTrace tailWord_6122059 prefixEnd_6122059 3143558862183768149707669 := by
  unfold tailWord_6122059
  simp only [CollatzResearch.WordTrace]
  refine ⟨223289835727833282280673231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148859890485222188187115487 223289835727833282280673231)
  ·
    refine ⟨334934753591749923421009847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223289835727833282280673231 334934753591749923421009847)
    ·
      refine ⟨502402130387624885131514771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334934753591749923421009847 502402130387624885131514771)
      ·
        refine ⟨753603195581437327697272157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502402130387624885131514771 753603195581437327697272157)
        ·
          refine ⟨282601198343038997886477059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 753603195581437327697272157 282601198343038997886477059)
          ·
            refine ⟨423901797514558496829715589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282601198343038997886477059 423901797514558496829715589)
            ·
              refine ⟨79481587033979718155571673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 423901797514558496829715589 79481587033979718155571673)
              ·
                refine ⟨59611190275484788616678755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79481587033979718155571673 59611190275484788616678755)
                ·
                  refine ⟨89416785413227182925018133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59611190275484788616678755 89416785413227182925018133)
                  ·
                    refine ⟨4191411816245024199610225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89416785413227182925018133 4191411816245024199610225)
                    ·
                      refine ⟨3143558862183768149707669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4191411816245024199610225 3143558862183768149707669)
                      ·
                        rfl

theorem cell23_6122059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 6, 2].length) (baseStart_6122059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122059 prefixEnd_6122059 := by exact prefixLift 6122059
  have htrace : WordTrace (prefixWord ++ tailWord_6122059) baseStart_6122059 baseEnd_6122059 := by
    simpa [prefixWord, tailWord_6122059, baseEnd_6122059] using wordTrace_append hprefix tailTrace_6122059
  have hstable : (prefixWord ++ tailWord_6122059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122059).length < 2 ^ (prefixWord ++ tailWord_6122059).sum := by decide
  have hdescent : baseEnd_6122059 < baseStart_6122059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122069 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 5, 4]
def baseStart_6122069 : Nat := 118140960795 + 6122069 * 2 ^ 59
def prefixEnd_6122069 : Nat := 4983230072969 + 3 ^ 40 * 6122069 * 2
def baseEnd_6122069 : Nat := 1047854665663437703527541

theorem tailTrace_6122069 : CollatzResearch.WordTrace tailWord_6122069 prefixEnd_6122069 1047854665663437703527541 := by
  unfold tailWord_6122069
  simp only [CollatzResearch.WordTrace]
  refine ⟨223290200457797053988537261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148860133638531369325691507 223290200457797053988537261)
  ·
    refine ⟨83733825171673895245701473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223290200457797053988537261 83733825171673895245701473)
    ·
      refine ⟨62800368878755421434276105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83733825171673895245701473 62800368878755421434276105)
      ·
        refine ⟨47100276659066566075707079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62800368878755421434276105 47100276659066566075707079)
        ·
          refine ⟨70650414988599849113560619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47100276659066566075707079 70650414988599849113560619)
          ·
            refine ⟨105975622482899773670340929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70650414988599849113560619 105975622482899773670340929)
            ·
              refine ⟨79481716862174830252755697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105975622482899773670340929 79481716862174830252755697)
              ·
                refine ⟨59611287646631122689566773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79481716862174830252755697 59611287646631122689566773)
                ·
                  refine ⟨5588558216871667752146885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59611287646631122689566773 5588558216871667752146885)
                  ·
                    refine ⟨1047854665663437703527541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5588558216871667752146885 1047854665663437703527541)
                    ·
                      rfl

theorem cell23_6122069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_6122069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122069 prefixEnd_6122069 := by exact prefixLift 6122069
  have htrace : WordTrace (prefixWord ++ tailWord_6122069) baseStart_6122069 baseEnd_6122069 := by
    simpa [prefixWord, tailWord_6122069, baseEnd_6122069] using wordTrace_append hprefix tailTrace_6122069
  have hstable : (prefixWord ++ tailWord_6122069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122069).length < 2 ^ (prefixWord ++ tailWord_6122069).sum := by decide
  have hdescent : baseEnd_6122069 < baseStart_6122069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122072 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 1, 3, 6]
def baseStart_6122072 : Nat := 118140960795 + 6122072 * 2 ^ 59
def prefixEnd_6122072 : Nat := 4983230072969 + 3 ^ 40 * 6122072 * 2
def baseEnd_6122072 : Nat := 3143565537432276598845109

theorem tailTrace_6122072 : CollatzResearch.WordTrace tailWord_6122072 prefixEnd_6122072 3143565537432276598845109 := by
  unfold tailWord_6122072
  simp only [CollatzResearch.WordTrace]
  refine ⟨111645154938393092750448235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148860206584524123667264313 111645154938393092750448235)
  ·
    refine ⟨167467732407589639125672353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111645154938393092750448235 167467732407589639125672353)
    ·
      refine ⟨125600799305692229344254265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167467732407589639125672353 125600799305692229344254265)
      ·
        refine ⟨94200599479269172008190699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125600799305692229344254265 94200599479269172008190699)
        ·
          refine ⟨141300899218903758012286049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94200599479269172008190699 141300899218903758012286049)
          ·
            refine ⟨105975674414177818509214537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141300899218903758012286049 105975674414177818509214537)
            ·
              refine ⟨79481755810633363881910903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105975674414177818509214537 79481755810633363881910903)
              ·
                refine ⟨119222633715950045822866355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79481755810633363881910903 119222633715950045822866355)
                ·
                  refine ⟨178833950573925068734299533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119222633715950045822866355 178833950573925068734299533)
                  ·
                    refine ⟨67062731465221900775362325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 178833950573925068734299533 67062731465221900775362325)
                    ·
                      refine ⟨3143565537432276598845109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67062731465221900775362325 3143565537432276598845109)
                      ·
                        rfl

theorem cell23_6122072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_6122072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122072 prefixEnd_6122072 := by exact prefixLift 6122072
  have htrace : WordTrace (prefixWord ++ tailWord_6122072) baseStart_6122072 baseEnd_6122072 := by
    simpa [prefixWord, tailWord_6122072, baseEnd_6122072] using wordTrace_append hprefix tailTrace_6122072
  have hstable : (prefixWord ++ tailWord_6122072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122072).length < 2 ^ (prefixWord ++ tailWord_6122072).sum := by decide
  have hdescent : baseEnd_6122072 < baseStart_6122072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122159 : List Nat := [1, 1, 2, 1, 2, 5, 1, 3, 1, 6]
def baseStart_6122159 : Nat := 118140960795 + 6122159 * 2 ^ 59
def prefixEnd_6122159 : Nat := 4983230072969 + 3 ^ 40 * 6122159 * 2
def baseEnd_6122159 : Nat := 1047870070083072586152403

theorem tailTrace_6122159 : CollatzResearch.WordTrace tailWord_6122159 prefixEnd_6122159 1047870070083072586152403 := by
  unfold tailWord_6122159
  simp only [CollatzResearch.WordTrace]
  refine ⟨223293483027470999359313531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148862322018313999572875687 223293483027470999359313531)
  ·
    refine ⟨334940224541206499038970297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223293483027470999359313531 334940224541206499038970297)
    ·
      refine ⟨251205168405904874279227723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334940224541206499038970297 251205168405904874279227723)
      ·
        refine ⟨376807752608857311418841585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251205168405904874279227723 376807752608857311418841585)
        ·
          refine ⟨282605814456642983564131189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376807752608857311418841585 282605814456642983564131189)
          ·
            refine ⟨26494295105310279709137299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 282605814456642983564131189 26494295105310279709137299)
            ·
              refine ⟨39741442657965419563705949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26494295105310279709137299 39741442657965419563705949)
              ·
                refine ⟨14903040996737032336389731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39741442657965419563705949 14903040996737032336389731)
                ·
                  refine ⟨22354561495105548504584597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14903040996737032336389731 22354561495105548504584597)
                  ·
                    refine ⟨1047870070083072586152403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22354561495105548504584597 1047870070083072586152403)
                    ·
                      rfl

theorem cell23_6122159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 6].length) (baseStart_6122159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122159 prefixEnd_6122159 := by exact prefixLift 6122159
  have htrace : WordTrace (prefixWord ++ tailWord_6122159) baseStart_6122159 baseEnd_6122159 := by
    simpa [prefixWord, tailWord_6122159, baseEnd_6122159] using wordTrace_append hprefix tailTrace_6122159
  have hstable : (prefixWord ++ tailWord_6122159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122159).length < 2 ^ (prefixWord ++ tailWord_6122159).sum := by decide
  have hdescent : baseEnd_6122159 < baseStart_6122159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122180 : List Nat := [2, 3, 3, 1, 1, 4, 2, 1, 1, 5]
def baseStart_6122180 : Nat := 118140960795 + 6122180 * 2 ^ 59
def prefixEnd_6122180 : Nat := 4983230072969 + 3 ^ 40 * 6122180 * 2
def baseEnd_6122180 : Nat := 1047873664447654058764871

theorem tailTrace_6122180 : CollatzResearch.WordTrace tailWord_6122180 prefixEnd_6122180 1047873664447654058764871 := by
  unfold tailWord_6122180
  simp only [CollatzResearch.WordTrace]
  refine ⟨111647124480197459972913997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148862832640263279963885329 111647124480197459972913997)
  ·
    refine ⟨41867671680074047489842749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111647124480197459972913997 41867671680074047489842749)
    ·
      refine ⟨15700376880027767808691031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41867671680074047489842749 15700376880027767808691031)
      ·
        refine ⟨23550565320041651713036547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15700376880027767808691031 23550565320041651713036547)
        ·
          refine ⟨35325847980062477569554821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23550565320041651713036547 35325847980062477569554821)
          ·
            refine ⟨6623596496261714544291529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35325847980062477569554821 6623596496261714544291529)
            ·
              refine ⟨4967697372196285908218647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6623596496261714544291529 4967697372196285908218647)
              ·
                refine ⟨7451546058294428862327971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4967697372196285908218647 7451546058294428862327971)
                ·
                  refine ⟨11177319087441643293491957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7451546058294428862327971 11177319087441643293491957)
                  ·
                    refine ⟨1047873664447654058764871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11177319087441643293491957 1047873664447654058764871)
                    ·
                      rfl

theorem cell23_6122180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_6122180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122180 prefixEnd_6122180 := by exact prefixLift 6122180
  have htrace : WordTrace (prefixWord ++ tailWord_6122180) baseStart_6122180 baseEnd_6122180 := by
    simpa [prefixWord, tailWord_6122180, baseEnd_6122180] using wordTrace_append hprefix tailTrace_6122180
  have hstable : (prefixWord ++ tailWord_6122180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122180).length < 2 ^ (prefixWord ++ tailWord_6122180).sum := by decide
  have hdescent : baseEnd_6122180 < baseStart_6122180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122200 : List Nat := [2, 1, 2, 2, 3, 3, 2, 1, 3, 2, 2]
def baseStart_6122200 : Nat := 118140960795 + 6122200 * 2 ^ 59
def prefixEnd_6122200 : Nat := 4983230072969 + 3 ^ 40 * 6122200 * 2
def baseEnd_6122200 : Nat := 3143631262956052098044521

theorem tailTrace_6122200 : CollatzResearch.WordTrace tailWord_6122200 prefixEnd_6122200 3143631262956052098044521 := by
  unfold tailWord_6122200
  simp only [CollatzResearch.WordTrace]
  refine ⟨111647489210161231680778027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148863318946881642241037369 111647489210161231680778027)
  ·
    refine ⟨167471233815241847521167041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111647489210161231680778027 167471233815241847521167041)
    ·
      refine ⟨125603425361431385640875281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167471233815241847521167041 125603425361431385640875281)
      ·
        refine ⟨94202569021073539230656461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125603425361431385640875281 94202569021073539230656461)
        ·
          refine ⟨35325963382902577211496173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94202569021073539230656461 35325963382902577211496173)
          ·
            refine ⟨13247236268588466454311065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35325963382902577211496173 13247236268588466454311065)
            ·
              refine ⟨9935427201441349840733299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13247236268588466454311065 9935427201441349840733299)
              ·
                refine ⟨14903140802162024761099949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9935427201441349840733299 14903140802162024761099949)
                ·
                  refine ⟨5588677800810759285412481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14903140802162024761099949 5588677800810759285412481)
                  ·
                    refine ⟨4191508350608069464059361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5588677800810759285412481 4191508350608069464059361)
                    ·
                      refine ⟨3143631262956052098044521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4191508350608069464059361 3143631262956052098044521)
                      ·
                        rfl

theorem cell23_6122200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 3, 2, 2].length) (baseStart_6122200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122200 prefixEnd_6122200 := by exact prefixLift 6122200
  have htrace : WordTrace (prefixWord ++ tailWord_6122200) baseStart_6122200 baseEnd_6122200 := by
    simpa [prefixWord, tailWord_6122200, baseEnd_6122200] using wordTrace_append hprefix tailTrace_6122200
  have hstable : (prefixWord ++ tailWord_6122200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122200).length < 2 ^ (prefixWord ++ tailWord_6122200).sum := by decide
  have hdescent : baseEnd_6122200 < baseStart_6122200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122213 : List Nat := [1, 3, 1, 4, 1, 4, 1, 1, 1, 2, 4]
def baseStart_6122213 : Nat := 118140960795 + 6122213 * 2 ^ 59
def prefixEnd_6122213 : Nat := 4983230072969 + 3 ^ 40 * 6122213 * 2
def baseEnd_6122213 : Nat := 3143637938204560547181961

theorem tailTrace_6122213 : CollatzResearch.WordTrace tailWord_6122213 prefixEnd_6122213 3143637938204560547181961 := by
  unfold tailWord_6122213
  simp only [CollatzResearch.WordTrace]
  refine ⟨223295452569275366581779293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148863635046183577721186195 223295452569275366581779293)
  ·
    refine ⟨83735794713478262468167235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223295452569275366581779293 83735794713478262468167235)
    ·
      refine ⟨125603692070217393702250853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83735794713478262468167235 125603692070217393702250853)
      ·
        refine ⟨23550692263165761319172035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125603692070217393702250853 23550692263165761319172035)
        ·
          refine ⟨35326038394748641978758053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23550692263165761319172035 35326038394748641978758053)
          ·
            refine ⟨6623632199015370371017135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35326038394748641978758053 6623632199015370371017135)
            ·
              refine ⟨9935448298523055556525703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6623632199015370371017135 9935448298523055556525703)
              ·
                refine ⟨14903172447784583334788555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9935448298523055556525703 14903172447784583334788555)
                ·
                  refine ⟨22354758671676875002182833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14903172447784583334788555 22354758671676875002182833)
                  ·
                    refine ⟨16766069003757656251637125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22354758671676875002182833 16766069003757656251637125)
                    ·
                      refine ⟨3143637938204560547181961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16766069003757656251637125 3143637938204560547181961)
                      ·
                        rfl

theorem cell23_6122213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_6122213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122213 prefixEnd_6122213 := by exact prefixLift 6122213
  have htrace : WordTrace (prefixWord ++ tailWord_6122213) baseStart_6122213 baseEnd_6122213 := by
    simpa [prefixWord, tailWord_6122213, baseEnd_6122213] using wordTrace_append hprefix tailTrace_6122213
  have hstable : (prefixWord ++ tailWord_6122213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122213).length < 2 ^ (prefixWord ++ tailWord_6122213).sum := by decide
  have hdescent : baseEnd_6122213 < baseStart_6122213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122228 : List Nat := [2, 6, 1, 1, 3, 1, 1, 3, 1, 1, 3]
def baseStart_6122228 : Nat := 118140960795 + 6122228 * 2 ^ 59
def prefixEnd_6122228 : Nat := 4983230072969 + 3 ^ 40 * 6122228 * 2
def baseEnd_6122228 : Nat := 3143645640414377988494393

theorem tailTrace_6122228 : CollatzResearch.WordTrace tailWord_6122228 prefixEnd_6122228 3143645640414377988494393 := by
  unfold tailWord_6122228
  simp only [CollatzResearch.WordTrace]
  refine ⟨111647999832110512071787669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148863999776147349429050225 111647999832110512071787669)
  ·
    refine ⟨5233499992130180253365047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 111647999832110512071787669 5233499992130180253365047)
    ·
      refine ⟨7850249988195270380047571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5233499992130180253365047 7850249988195270380047571)
      ·
        refine ⟨11775374982292905570071357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7850249988195270380047571 11775374982292905570071357)
        ·
          refine ⟨4415765618359839588776759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11775374982292905570071357 4415765618359839588776759)
          ·
            refine ⟨6623648427539759383165139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4415765618359839588776759 6623648427539759383165139)
            ·
              refine ⟨9935472641309639074747709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6623648427539759383165139 9935472641309639074747709)
              ·
                refine ⟨3725802240491114653030391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9935472641309639074747709 3725802240491114653030391)
                ·
                  refine ⟨5588703360736671979545587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3725802240491114653030391 5588703360736671979545587)
                  ·
                    refine ⟨8383055041105007969318381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5588703360736671979545587 8383055041105007969318381)
                    ·
                      refine ⟨3143645640414377988494393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8383055041105007969318381 3143645640414377988494393)
                      ·
                        rfl

theorem cell23_6122228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_6122228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122228 prefixEnd_6122228 := by exact prefixLift 6122228
  have htrace : WordTrace (prefixWord ++ tailWord_6122228) baseStart_6122228 baseEnd_6122228 := by
    simpa [prefixWord, tailWord_6122228, baseEnd_6122228] using wordTrace_append hprefix tailTrace_6122228
  have hstable : (prefixWord ++ tailWord_6122228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122228).length < 2 ^ (prefixWord ++ tailWord_6122228).sum := by decide
  have hdescent : baseEnd_6122228 < baseStart_6122228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122239 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 4]
def baseStart_6122239 : Nat := 118140960795 + 6122239 * 2 ^ 59
def prefixEnd_6122239 : Nat := 4983230072969 + 3 ^ 40 * 6122239 * 2
def baseEnd_6122239 : Nat := 3143651288701577445456841

theorem tailTrace_6122239 : CollatzResearch.WordTrace tailWord_6122239 prefixEnd_6122239 3143651288701577445456841 := by
  unfold tailWord_6122239
  simp only [CollatzResearch.WordTrace]
  refine ⟨223296400867181173022225771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148864267244787448681483847 223296400867181173022225771)
  ·
    refine ⟨334944601300771759533338657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223296400867181173022225771 334944601300771759533338657)
    ·
      refine ⟨251208450975578819650003993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334944601300771759533338657 251208450975578819650003993)
      ·
        refine ⟨188406338231684114737502995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251208450975578819650003993 188406338231684114737502995)
        ·
          refine ⟨282609507347526172106254493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188406338231684114737502995 282609507347526172106254493)
          ·
            refine ⟨105978565255322314539845435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 282609507347526172106254493 105978565255322314539845435)
            ·
              refine ⟨158967847882983471809768153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105978565255322314539845435 158967847882983471809768153)
              ·
                refine ⟨119225885912237603857326115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158967847882983471809768153 119225885912237603857326115)
                ·
                  refine ⟨178838828868356405785989173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119225885912237603857326115 178838828868356405785989173)
                  ·
                    refine ⟨16766140206408413042436485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 178838828868356405785989173 16766140206408413042436485)
                    ·
                      refine ⟨3143651288701577445456841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16766140206408413042436485 3143651288701577445456841)
                      ·
                        rfl

theorem cell23_6122239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_6122239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122239 prefixEnd_6122239 := by exact prefixLift 6122239
  have htrace : WordTrace (prefixWord ++ tailWord_6122239) baseStart_6122239 baseEnd_6122239 := by
    simpa [prefixWord, tailWord_6122239, baseEnd_6122239] using wordTrace_append hprefix tailTrace_6122239
  have hstable : (prefixWord ++ tailWord_6122239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122239).length < 2 ^ (prefixWord ++ tailWord_6122239).sum := by decide
  have hdescent : baseEnd_6122239 < baseStart_6122239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122249 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 4, 6]
def baseStart_6122249 : Nat := 118140960795 + 6122249 * 2 ^ 59
def prefixEnd_6122249 : Nat := 4983230072969 + 3 ^ 40 * 6122249 * 2
def baseEnd_6122249 : Nat := 1047885474502707468777265

theorem tailTrace_6122249 : CollatzResearch.WordTrace tailWord_6122249 prefixEnd_6122249 1047885474502707468777265 := by
  unfold tailWord_6122249
  simp only [CollatzResearch.WordTrace]
  refine ⟨223296765597144944730089801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148864510398096629820059867 223296765597144944730089801)
  ·
    refine ⟨167472574197858708547567351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223296765597144944730089801 167472574197858708547567351)
    ·
      refine ⟨251208861296788062821351027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167472574197858708547567351 251208861296788062821351027)
      ·
        refine ⟨376813291945182094232026541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251208861296788062821351027 376813291945182094232026541)
        ·
          refine ⟨141304984479443285337009953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 376813291945182094232026541 141304984479443285337009953)
          ·
            refine ⟨105978738359582464002757465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141304984479443285337009953 105978738359582464002757465)
            ·
              refine ⟨79484053769686848002068099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105978738359582464002757465 79484053769686848002068099)
              ·
                refine ⟨119226080654530272003102149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79484053769686848002068099 119226080654530272003102149)
                ·
                  refine ⟨22354890122724426000581653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119226080654530272003102149 22354890122724426000581653)
                  ·
                    refine ⟨1047885474502707468777265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22354890122724426000581653 1047885474502707468777265)
                    ·
                      rfl

theorem cell23_6122249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 6].length) (baseStart_6122249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122249 prefixEnd_6122249 := by exact prefixLift 6122249
  have htrace : WordTrace (prefixWord ++ tailWord_6122249) baseStart_6122249 baseEnd_6122249 := by
    simpa [prefixWord, tailWord_6122249, baseEnd_6122249] using wordTrace_append hprefix tailTrace_6122249
  have hstable : (prefixWord ++ tailWord_6122249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122249).length < 2 ^ (prefixWord ++ tailWord_6122249).sum := by decide
  have hdescent : baseEnd_6122249 < baseStart_6122249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122259 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 5]
def baseStart_6122259 : Nat := 118140960795 + 6122259 * 2 ^ 59
def prefixEnd_6122259 : Nat := 4983230072969 + 3 ^ 40 * 6122259 * 2
def baseEnd_6122259 : Nat := 3143661558314667367206749

theorem tailTrace_6122259 : CollatzResearch.WordTrace tailWord_6122259 prefixEnd_6122259 3143661558314667367206749 := by
  unfold tailWord_6122259
  simp only [CollatzResearch.WordTrace]
  refine ⟨223297130327108716437953831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148864753551405810958635887 223297130327108716437953831)
  ·
    refine ⟨334945695490663074656930747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223297130327108716437953831 334945695490663074656930747)
    ·
      refine ⟨502418543235994611985396121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334945695490663074656930747 502418543235994611985396121)
      ·
        refine ⟨376813907426995958989047091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 502418543235994611985396121 376813907426995958989047091)
        ·
          refine ⟨565220861140493938483570637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376813907426995958989047091 565220861140493938483570637)
          ·
            refine ⟨211957822927685226931338989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 565220861140493938483570637 211957822927685226931338989)
            ·
              refine ⟨79484183597881960099252121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211957822927685226931338989 79484183597881960099252121)
              ·
                refine ⟨59613137698411470074439091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79484183597881960099252121 59613137698411470074439091)
                ·
                  refine ⟨89419706547617205111658637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59613137698411470074439091 89419706547617205111658637)
                  ·
                    refine ⟨33532389955356451916871989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89419706547617205111658637 33532389955356451916871989)
                    ·
                      refine ⟨3143661558314667367206749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33532389955356451916871989 3143661558314667367206749)
                      ·
                        rfl

theorem cell23_6122259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 5].length) (baseStart_6122259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122259 prefixEnd_6122259 := by exact prefixLift 6122259
  have htrace : WordTrace (prefixWord ++ tailWord_6122259) baseStart_6122259 baseEnd_6122259 := by
    simpa [prefixWord, tailWord_6122259, baseEnd_6122259] using wordTrace_append hprefix tailTrace_6122259
  have hstable : (prefixWord ++ tailWord_6122259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122259).length < 2 ^ (prefixWord ++ tailWord_6122259).sum := by decide
  have hdescent : baseEnd_6122259 < baseStart_6122259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122273 : List Nat := [1, 2, 3, 2, 1, 2, 2, 3, 1, 4, 2]
def baseStart_6122273 : Nat := 118140960795 + 6122273 * 2 ^ 59
def prefixEnd_6122273 : Nat := 4983230072969 + 3 ^ 40 * 6122273 * 2
def baseEnd_6122273 : Nat := 3143668747043830312431685

theorem tailTrace_6122273 : CollatzResearch.WordTrace tailWord_6122273 prefixEnd_6122273 3143668747043830312431685 := by
  unfold tailWord_6122273
  simp only [CollatzResearch.WordTrace]
  refine ⟨223297640949057996828963473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148865093966038664552642315 223297640949057996828963473)
  ·
    refine ⟨167473230711793497621722605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223297640949057996828963473 167473230711793497621722605)
    ·
      refine ⟨62802461516922561608145977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167473230711793497621722605 62802461516922561608145977)
      ·
        refine ⟨47101846137691921206109483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62802461516922561608145977 47101846137691921206109483)
        ·
          refine ⟨70652769206537881809164225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47101846137691921206109483 70652769206537881809164225)
          ·
            refine ⟨52989576904903411356873169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70652769206537881809164225 52989576904903411356873169)
            ·
              refine ⟨39742182678677558517654877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52989576904903411356873169 39742182678677558517654877)
              ·
                refine ⟨14903318504504084444120579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39742182678677558517654877 14903318504504084444120579)
                ·
                  refine ⟨22354977756756126666180869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14903318504504084444120579 22354977756756126666180869)
                  ·
                    refine ⟨4191558329391773749908913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22354977756756126666180869 4191558329391773749908913)
                    ·
                      refine ⟨3143668747043830312431685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4191558329391773749908913 3143668747043830312431685)
                      ·
                        rfl

theorem cell23_6122273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_6122273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122273 prefixEnd_6122273 := by exact prefixLift 6122273
  have htrace : WordTrace (prefixWord ++ tailWord_6122273) baseStart_6122273 baseEnd_6122273 := by
    simpa [prefixWord, tailWord_6122273, baseEnd_6122273] using wordTrace_append hprefix tailTrace_6122273
  have hstable : (prefixWord ++ tailWord_6122273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122273).length < 2 ^ (prefixWord ++ tailWord_6122273).sum := by decide
  have hdescent : baseEnd_6122273 < baseStart_6122273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122313 : List Nat := [1, 2, 1, 1, 2, 6, 1, 4, 5]
def baseStart_6122313 : Nat := 118140960795 + 6122313 * 2 ^ 59
def prefixEnd_6122313 : Nat := 4983230072969 + 3 ^ 40 * 6122313 * 2
def baseEnd_6122313 : Nat := 349298809585556683992389

theorem tailTrace_6122313 : CollatzResearch.WordTrace tailWord_6122313 prefixEnd_6122313 349298809585556683992389 := by
  unfold tailWord_6122313
  simp only [CollatzResearch.WordTrace]
  refine ⟨223299099868913083660419593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148866066579275389106946395 223299099868913083660419593)
  ·
    refine ⟨167474324901684812745314695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223299099868913083660419593 167474324901684812745314695)
    ·
      refine ⟨251211487352527219117972043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167474324901684812745314695 251211487352527219117972043)
      ·
        refine ⟨376817231028790828676958065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251211487352527219117972043 376817231028790828676958065)
        ·
          refine ⟨282612923271593121507718549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376817231028790828676958065 282612923271593121507718549)
          ·
            refine ⟨13247480778355927570674307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 282612923271593121507718549 13247480778355927570674307)
            ·
              refine ⟨19871221167533891356011461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13247480778355927570674307 19871221167533891356011461)
              ·
                refine ⟨3725853968912604629252149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19871221167533891356011461 3725853968912604629252149)
                ·
                  refine ⟨349298809585556683992389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3725853968912604629252149 349298809585556683992389)
                  ·
                    rfl

theorem cell23_6122313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4, 5].length) (baseStart_6122313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122313 prefixEnd_6122313 := by exact prefixLift 6122313
  have htrace : WordTrace (prefixWord ++ tailWord_6122313) baseStart_6122313 baseEnd_6122313 := by
    simpa [prefixWord, tailWord_6122313, baseEnd_6122313] using wordTrace_append hprefix tailTrace_6122313
  have hstable : (prefixWord ++ tailWord_6122313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122313).length < 2 ^ (prefixWord ++ tailWord_6122313).sum := by decide
  have hdescent : baseEnd_6122313 < baseStart_6122313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122343 : List Nat := [1, 1, 5, 1, 2, 2, 3, 1, 2, 5]
def baseStart_6122343 : Nat := 118140960795 + 6122343 * 2 ^ 59
def prefixEnd_6122343 : Nat := 4983230072969 + 3 ^ 40 * 6122343 * 2
def baseEnd_6122343 : Nat := 1047901563563215012852121

theorem tailTrace_6122343 : CollatzResearch.WordTrace tailWord_6122343 prefixEnd_6122343 1047901563563215012852121 := by
  unfold tailWord_6122343
  simp only [CollatzResearch.WordTrace]
  refine ⟨223300194058804398784011683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148866796039202932522674455 223300194058804398784011683)
  ·
    refine ⟨334950291088206598176017525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223300194058804398784011683 334950291088206598176017525)
    ·
      refine ⟨31401589789519368579001643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 334950291088206598176017525 31401589789519368579001643)
      ·
        refine ⟨47102384684279052868502465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31401589789519368579001643 47102384684279052868502465)
        ·
          refine ⟨35326788513209289651376849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47102384684279052868502465 35326788513209289651376849)
          ·
            refine ⟨26495091384906967238532637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35326788513209289651376849 26495091384906967238532637)
            ·
              refine ⟨9935659269340112714449739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26495091384906967238532637 9935659269340112714449739)
              ·
                refine ⟨14903488904010169071674609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9935659269340112714449739 14903488904010169071674609)
                ·
                  refine ⟨11177616678007626803755957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14903488904010169071674609 11177616678007626803755957)
                  ·
                    refine ⟨1047901563563215012852121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11177616678007626803755957 1047901563563215012852121)
                    ·
                      rfl

theorem cell23_6122343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_6122343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122343 prefixEnd_6122343 := by exact prefixLift 6122343
  have htrace : WordTrace (prefixWord ++ tailWord_6122343) baseStart_6122343 baseEnd_6122343 := by
    simpa [prefixWord, tailWord_6122343, baseEnd_6122343] using wordTrace_append hprefix tailTrace_6122343
  have hstable : (prefixWord ++ tailWord_6122343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122343).length < 2 ^ (prefixWord ++ tailWord_6122343).sum := by decide
  have hdescent : baseEnd_6122343 < baseStart_6122343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122363 : List Nat := [1, 1, 1, 1, 1, 5, 3, 2, 2, 4, 2]
def baseStart_6122363 : Nat := 118140960795 + 6122363 * 2 ^ 59
def prefixEnd_6122363 : Nat := 4983230072969 + 3 ^ 40 * 6122363 * 2
def baseEnd_6122363 : Nat := 3143714960302734960306271

theorem tailTrace_6122363 : CollatzResearch.WordTrace tailWord_6122363 prefixEnd_6122363 3143714960302734960306271 := by
  unfold tailWord_6122363
  simp only [CollatzResearch.WordTrace]
  refine ⟨223300923518731942199739743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148867282345821294799826495 223300923518731942199739743)
  ·
    refine ⟨334951385278097913299609615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223300923518731942199739743 334951385278097913299609615)
    ·
      refine ⟨502427077917146869949414423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334951385278097913299609615 502427077917146869949414423)
      ·
        refine ⟨753640616875720304924121635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502427077917146869949414423 753640616875720304924121635)
        ·
          refine ⟨1130460925313580457386182453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 753640616875720304924121635 1130460925313580457386182453)
          ·
            refine ⟨105980711748148167879954605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1130460925313580457386182453 105980711748148167879954605)
            ·
              refine ⟨39742766905555562954982977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105980711748148167879954605 39742766905555562954982977)
              ·
                refine ⟨29807075179166672216237233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39742766905555562954982977 29807075179166672216237233)
                ·
                  refine ⟨22355306384375004162177925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29807075179166672216237233 22355306384375004162177925)
                  ·
                    refine ⟨4191619947070313280408361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22355306384375004162177925 4191619947070313280408361)
                    ·
                      refine ⟨3143714960302734960306271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4191619947070313280408361 3143714960302734960306271)
                      ·
                        rfl

theorem cell23_6122363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 4, 2].length) (baseStart_6122363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122363 prefixEnd_6122363 := by exact prefixLift 6122363
  have htrace : WordTrace (prefixWord ++ tailWord_6122363) baseStart_6122363 baseEnd_6122363 := by
    simpa [prefixWord, tailWord_6122363, baseEnd_6122363] using wordTrace_append hprefix tailTrace_6122363
  have hstable : (prefixWord ++ tailWord_6122363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122363).length < 2 ^ (prefixWord ++ tailWord_6122363).sum := by decide
  have hdescent : baseEnd_6122363 < baseStart_6122363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122373 : List Nat := [1, 3, 1, 1, 3, 3, 1, 3, 3, 4]
def baseStart_6122373 : Nat := 118140960795 + 6122373 * 2 ^ 59
def prefixEnd_6122373 : Nat := 4983230072969 + 3 ^ 40 * 6122373 * 2
def baseEnd_6122373 : Nat := 1047906698369759973727075

theorem tailTrace_6122373 : CollatzResearch.WordTrace tailWord_6122373 prefixEnd_6122373 1047906698369759973727075 := by
  unfold tailWord_6122373
  simp only [CollatzResearch.WordTrace]
  refine ⟨223301288248695713907603773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148867525499130475938402515 223301288248695713907603773)
  ·
    refine ⟨83737983093260892715351415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223301288248695713907603773 83737983093260892715351415)
    ·
      refine ⟨125606974639891339073027123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83737983093260892715351415 125606974639891339073027123)
      ·
        refine ⟨188410461959837008609540685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125606974639891339073027123 188410461959837008609540685)
        ·
          refine ⟨70653923234938878228577757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188410461959837008609540685 70653923234938878228577757)
          ·
            refine ⟨26495221213102079335716659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70653923234938878228577757 26495221213102079335716659)
            ·
              refine ⟨39742831819653119003574989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26495221213102079335716659 39742831819653119003574989)
              ·
                refine ⟨14903561932369919626340621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39742831819653119003574989 14903561932369919626340621)
                ·
                  refine ⟨5588835724638719859877733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14903561932369919626340621 5588835724638719859877733)
                  ·
                    refine ⟨1047906698369759973727075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5588835724638719859877733 1047906698369759973727075)
                    ·
                      rfl

theorem cell23_6122373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3, 4].length) (baseStart_6122373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122373 prefixEnd_6122373 := by exact prefixLift 6122373
  have htrace : WordTrace (prefixWord ++ tailWord_6122373) baseStart_6122373 baseEnd_6122373 := by
    simpa [prefixWord, tailWord_6122373, baseEnd_6122373] using wordTrace_append hprefix tailTrace_6122373
  have hstable : (prefixWord ++ tailWord_6122373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122373).length < 2 ^ (prefixWord ++ tailWord_6122373).sum := by decide
  have hdescent : baseEnd_6122373 < baseStart_6122373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122420 : List Nat := [2, 5, 2, 1, 1, 1, 2, 1, 8]
def baseStart_6122420 : Nat := 118140960795 + 6122420 * 2 ^ 59
def prefixEnd_6122420 : Nat := 4983230072969 + 3 ^ 40 * 6122420 * 2
def baseEnd_6122420 : Nat := 349304914300004581921501

theorem tailTrace_6122420 : CollatzResearch.WordTrace tailWord_6122420 prefixEnd_6122420 349304914300004581921501 := by
  unfold tailWord_6122420
  simp only [CollatzResearch.WordTrace]
  refine ⟨111651501239762720467282357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148868668319683627289709809 111651501239762720467282357)
  ·
    refine ⟨10467328241227755043807721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111651501239762720467282357 10467328241227755043807721)
    ·
      refine ⟨7850496180920816282855791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10467328241227755043807721 7850496180920816282855791)
      ·
        refine ⟨11775744271381224424283687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7850496180920816282855791 11775744271381224424283687)
        ·
          refine ⟨17663616407071836636425531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11775744271381224424283687 17663616407071836636425531)
          ·
            refine ⟨26495424610607754954638297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17663616407071836636425531 26495424610607754954638297)
            ·
              refine ⟨19871568457955816215978723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26495424610607754954638297 19871568457955816215978723)
              ·
                refine ⟨29807352686933724323968085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19871568457955816215978723 29807352686933724323968085)
                ·
                  refine ⟨349304914300004581921501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29807352686933724323968085 349304914300004581921501)
                  ·
                    rfl

theorem cell23_6122420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_6122420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122420 prefixEnd_6122420 := by exact prefixLift 6122420
  have htrace : WordTrace (prefixWord ++ tailWord_6122420) baseStart_6122420 baseEnd_6122420 := by
    simpa [prefixWord, tailWord_6122420, baseEnd_6122420] using wordTrace_append hprefix tailTrace_6122420
  have hstable : (prefixWord ++ tailWord_6122420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122420).length < 2 ^ (prefixWord ++ tailWord_6122420).sum := by decide
  have hdescent : baseEnd_6122420 < baseStart_6122420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122450 : List Nat := [3, 2, 2, 3, 1, 2, 1, 1, 3, 5]
def baseStart_6122450 : Nat := 118140960795 + 6122450 * 2 ^ 59
def prefixEnd_6122450 : Nat := 4983230072969 + 3 ^ 40 * 6122450 * 2
def baseEnd_6122450 : Nat := 1047919877706558706639457

theorem tailTrace_6122450 : CollatzResearch.WordTrace tailWord_6122450 prefixEnd_6122450 1047919877706558706639457 := by
  unfold tailWord_6122450
  simp only [CollatzResearch.WordTrace]
  refine ⟨55826024167354189014539201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148869397779611170705437869 55826024167354189014539201)
  ·
    refine ⟨41869518125515641760904401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55826024167354189014539201 41869518125515641760904401)
    ·
      refine ⟨31402138594136731320678301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41869518125515641760904401 31402138594136731320678301)
      ·
        refine ⟨11775801972801274245254363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31402138594136731320678301 11775801972801274245254363)
        ·
          refine ⟨17663702959201911367881545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11775801972801274245254363 17663702959201911367881545)
          ·
            refine ⟨13247777219401433525911159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17663702959201911367881545 13247777219401433525911159)
            ·
              refine ⟨19871665829102150288866739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13247777219401433525911159 19871665829102150288866739)
              ·
                refine ⟨29807498743653225433300109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19871665829102150288866739 29807498743653225433300109)
                ·
                  refine ⟨11177812028869959537487541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29807498743653225433300109 11177812028869959537487541)
                  ·
                    refine ⟨1047919877706558706639457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11177812028869959537487541 1047919877706558706639457)
                    ·
                      rfl

theorem cell23_6122450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_6122450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122450 prefixEnd_6122450 := by exact prefixLift 6122450
  have htrace : WordTrace (prefixWord ++ tailWord_6122450) baseStart_6122450 baseEnd_6122450 := by
    simpa [prefixWord, tailWord_6122450, baseEnd_6122450] using wordTrace_append hprefix tailTrace_6122450
  have hstable : (prefixWord ++ tailWord_6122450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122450).length < 2 ^ (prefixWord ++ tailWord_6122450).sum := by decide
  have hdescent : baseEnd_6122450 < baseStart_6122450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122457 : List Nat := [1, 2, 1, 2, 5, 2, 2, 1, 2, 3, 2]
def baseStart_6122457 : Nat := 118140960795 + 6122457 * 2 ^ 59
def prefixEnd_6122457 : Nat := 4983230072969 + 3 ^ 40 * 6122457 * 2
def baseEnd_6122457 : Nat := 3143763227484257592530839

theorem tailTrace_6122457 : CollatzResearch.WordTrace tailWord_6122457 prefixEnd_6122457 3143763227484257592530839 := by
  unfold tailWord_6122457
  simp only [CollatzResearch.WordTrace]
  refine ⟨223304351980391396253661625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148869567986927597502441083 223304351980391396253661625)
  ·
    refine ⟨167478263985293547190246219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223304351980391396253661625 167478263985293547190246219)
    ·
      refine ⟨251217395977940320785369329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167478263985293547190246219 251217395977940320785369329)
      ·
        refine ⟨188413046983455240589026997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251217395977940320785369329 188413046983455240589026997)
        ·
          refine ⟨17663723154698928805221281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 188413046983455240589026997 17663723154698928805221281)
          ·
            refine ⟨13247792366024196603915961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17663723154698928805221281 13247792366024196603915961)
            ·
              refine ⟨9935844274518147452936971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13247792366024196603915961 9935844274518147452936971)
              ·
                refine ⟨14903766411777221179405457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9935844274518147452936971 14903766411777221179405457)
                ·
                  refine ⟨11177824808832915884554093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14903766411777221179405457 11177824808832915884554093)
                  ·
                    refine ⟨4191684303312343456707785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11177824808832915884554093 4191684303312343456707785)
                    ·
                      refine ⟨3143763227484257592530839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4191684303312343456707785 3143763227484257592530839)
                      ·
                        rfl

theorem cell23_6122457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 3, 2].length) (baseStart_6122457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122457 prefixEnd_6122457 := by exact prefixLift 6122457
  have htrace : WordTrace (prefixWord ++ tailWord_6122457) baseStart_6122457 baseEnd_6122457 := by
    simpa [prefixWord, tailWord_6122457, baseEnd_6122457] using wordTrace_append hprefix tailTrace_6122457
  have hstable : (prefixWord ++ tailWord_6122457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122457).length < 2 ^ (prefixWord ++ tailWord_6122457).sum := by decide
  have hdescent : baseEnd_6122457 < baseStart_6122457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122481 : List Nat := [1, 2, 2, 2, 4, 3, 2, 2, 1, 1, 3]
def baseStart_6122481 : Nat := 118140960795 + 6122481 * 2 ^ 59
def prefixEnd_6122481 : Nat := 4983230072969 + 3 ^ 40 * 6122481 * 2
def baseEnd_6122481 : Nat := 3143775551019965498630729

theorem tailTrace_6122481 : CollatzResearch.WordTrace tailWord_6122481 prefixEnd_6122481 3143775551019965498630729 := by
  unfold tailWord_6122481
  simp only [CollatzResearch.WordTrace]
  refine ⟨223305227332304448352535297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148870151554869632235023531 223305227332304448352535297)
  ·
    refine ⟨167478920499228336264401473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223305227332304448352535297 167478920499228336264401473)
    ·
      refine ⟨125609190374421252198301105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167478920499228336264401473 125609190374421252198301105)
      ·
        refine ⟨94206892780815939148725829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125609190374421252198301105 94206892780815939148725829)
        ·
          refine ⟨17663792396402988590386093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94206892780815939148725829 17663792396402988590386093)
          ·
            refine ⟨6623922148651120721394785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17663792396402988590386093 6623922148651120721394785)
            ·
              refine ⟨4967941611488340541046089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6623922148651120721394785 4967941611488340541046089)
              ·
                refine ⟨3725956208616255405784567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4967941611488340541046089 3725956208616255405784567)
                ·
                  refine ⟨5588934312924383108676851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3725956208616255405784567 5588934312924383108676851)
                  ·
                    refine ⟨8383401469386574663015277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5588934312924383108676851 8383401469386574663015277)
                    ·
                      refine ⟨3143775551019965498630729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8383401469386574663015277 3143775551019965498630729)
                      ·
                        rfl

theorem cell23_6122481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2, 1, 1, 3].length) (baseStart_6122481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122481 prefixEnd_6122481 := by exact prefixLift 6122481
  have htrace : WordTrace (prefixWord ++ tailWord_6122481) baseStart_6122481 baseEnd_6122481 := by
    simpa [prefixWord, tailWord_6122481, baseEnd_6122481] using wordTrace_append hprefix tailTrace_6122481
  have hstable : (prefixWord ++ tailWord_6122481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122481).length < 2 ^ (prefixWord ++ tailWord_6122481).sum := by decide
  have hdescent : baseEnd_6122481 < baseStart_6122481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122510 : List Nat := [4, 1, 1, 2, 2, 3, 3, 7]
def baseStart_6122510 : Nat := 118140960795 + 6122510 * 2 ^ 59
def prefixEnd_6122510 : Nat := 4983230072969 + 3 ^ 40 * 6122510 * 2
def baseEnd_6122510 : Nat := 116436683035516514265485

theorem tailTrace_6122510 : CollatzResearch.WordTrace tailWord_6122510 prefixEnd_6122510 116436683035516514265485 := by
  unfold tailWord_6122510
  simp only [CollatzResearch.WordTrace]
  refine ⟨27913285631149923288167623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148870856699466257536893989 27913285631149923288167623)
  ·
    refine ⟨41869928446724884932251435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27913285631149923288167623 41869928446724884932251435)
    ·
      refine ⟨62804892670087327398377153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41869928446724884932251435 62804892670087327398377153)
      ·
        refine ⟨47103669502565495548782865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62804892670087327398377153 47103669502565495548782865)
        ·
          refine ⟨35327752126924121661587149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47103669502565495548782865 35327752126924121661587149)
          ·
            refine ⟨13247907047596545623095181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35327752126924121661587149 13247907047596545623095181)
            ·
              refine ⟨4967965142848704608660693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13247907047596545623095181 4967965142848704608660693)
              ·
                refine ⟨116436683035516514265485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4967965142848704608660693 116436683035516514265485)
                ·
                  rfl

theorem cell23_6122510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 7].length) (baseStart_6122510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122510 prefixEnd_6122510 := by exact prefixLift 6122510
  have htrace : WordTrace (prefixWord ++ tailWord_6122510) baseStart_6122510 baseEnd_6122510 := by
    simpa [prefixWord, tailWord_6122510, baseEnd_6122510] using wordTrace_append hprefix tailTrace_6122510
  have hstable : (prefixWord ++ tailWord_6122510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122510).length < 2 ^ (prefixWord ++ tailWord_6122510).sum := by decide
  have hdescent : baseEnd_6122510 < baseStart_6122510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122520 : List Nat := [2, 1, 2, 3, 2, 2, 2, 2, 1, 3, 3]
def baseStart_6122520 : Nat := 118140960795 + 6122520 * 2 ^ 59
def prefixEnd_6122520 : Nat := 4983230072969 + 3 ^ 40 * 6122520 * 2
def baseEnd_6122520 : Nat := 3143795576765490846043049

theorem tailTrace_6122520 : CollatzResearch.WordTrace tailWord_6122520 prefixEnd_6122520 3143795576765490846043049 := by
  unfold tailWord_6122520
  simp only [CollatzResearch.WordTrace]
  refine ⟨111653324889581579006602507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148871099852775438675470009 111653324889581579006602507)
  ·
    refine ⟨167479987334372368509903761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111653324889581579006602507 167479987334372368509903761)
    ·
      refine ⟨125609990500779276382427821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167479987334372368509903761 125609990500779276382427821)
      ·
        refine ⟨47103746437792228643410433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125609990500779276382427821 47103746437792228643410433)
        ·
          refine ⟨35327809828344171482557825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47103746437792228643410433 35327809828344171482557825)
          ·
            refine ⟨26495857371258128611918369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35327809828344171482557825 26495857371258128611918369)
            ·
              refine ⟨19871893028443596458938777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26495857371258128611918369 19871893028443596458938777)
              ·
                refine ⟨14903919771332697344204083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19871893028443596458938777 14903919771332697344204083)
                ·
                  refine ⟨22355879656999046016306125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14903919771332697344204083 22355879656999046016306125)
                  ·
                    refine ⟨8383454871374642256114797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22355879656999046016306125 8383454871374642256114797)
                    ·
                      refine ⟨3143795576765490846043049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8383454871374642256114797 3143795576765490846043049)
                      ·
                        rfl

theorem cell23_6122520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_6122520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122520 prefixEnd_6122520 := by exact prefixLift 6122520
  have htrace : WordTrace (prefixWord ++ tailWord_6122520) baseStart_6122520 baseEnd_6122520 := by
    simpa [prefixWord, tailWord_6122520, baseEnd_6122520] using wordTrace_append hprefix tailTrace_6122520
  have hstable : (prefixWord ++ tailWord_6122520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122520).length < 2 ^ (prefixWord ++ tailWord_6122520).sum := by decide
  have hdescent : baseEnd_6122520 < baseStart_6122520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122563 : List Nat := [1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 5]
def baseStart_6122563 : Nat := 118140960795 + 6122563 * 2 ^ 59
def prefixEnd_6122563 : Nat := 4983230072969 + 3 ^ 40 * 6122563 * 2
def baseEnd_6122563 : Nat := 3143817656433634177805351

theorem tailTrace_6122563 : CollatzResearch.WordTrace tailWord_6122563 prefixEnd_6122563 3143817656433634177805351 := by
  unfold tailWord_6122563
  simp only [CollatzResearch.WordTrace]
  refine ⟨223308218118007376357020343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148872145412004917571346895 223308218118007376357020343)
  ·
    refine ⟨334962327177011064535530515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223308218118007376357020343 334962327177011064535530515)
    ·
      refine ⟨502443490765516596803295773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334962327177011064535530515 502443490765516596803295773)
      ·
        refine ⟨188416309037068723801235915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 502443490765516596803295773 188416309037068723801235915)
        ·
          refine ⟨282624463555603085701853873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188416309037068723801235915 282624463555603085701853873)
          ·
            refine ⟨211968347666702314276390405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282624463555603085701853873 211968347666702314276390405)
            ·
              refine ⟨39744065187506683926823201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 211968347666702314276390405 39744065187506683926823201)
              ·
                refine ⟨29808048890630012945117401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39744065187506683926823201 29808048890630012945117401)
                ·
                  refine ⟨22356036667972509708838051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29808048890630012945117401 22356036667972509708838051)
                  ·
                    refine ⟨33534055001958764563257077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22356036667972509708838051 33534055001958764563257077)
                    ·
                      refine ⟨3143817656433634177805351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33534055001958764563257077 3143817656433634177805351)
                      ·
                        rfl

theorem cell23_6122563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_6122563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122563 prefixEnd_6122563 := by exact prefixLift 6122563
  have htrace : WordTrace (prefixWord ++ tailWord_6122563) baseStart_6122563 baseEnd_6122563 := by
    simpa [prefixWord, tailWord_6122563, baseEnd_6122563] using wordTrace_append hprefix tailTrace_6122563
  have hstable : (prefixWord ++ tailWord_6122563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122563).length < 2 ^ (prefixWord ++ tailWord_6122563).sum := by decide
  have hdescent : baseEnd_6122563 < baseStart_6122563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122577 : List Nat := [1, 2, 2, 1, 3, 1, 3, 2, 4, 2, 2]
def baseStart_6122577 : Nat := 118140960795 + 6122577 * 2 ^ 59
def prefixEnd_6122577 : Nat := 4983230072969 + 3 ^ 40 * 6122577 * 2
def baseEnd_6122577 : Nat := 3143824845162797123030287

theorem tailTrace_6122577 : CollatzResearch.WordTrace tailWord_6122577 prefixEnd_6122577 3143824845162797123030287 := by
  unfold tailWord_6122577
  simp only [CollatzResearch.WordTrace]
  refine ⟨223308728739956656748029985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148872485826637771165353323 223308728739956656748029985)
  ·
    refine ⟨167481546554967492561022489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223308728739956656748029985 167481546554967492561022489)
    ·
      refine ⟨125611159916225619420766867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167481546554967492561022489 125611159916225619420766867)
      ·
        refine ⟨188416739874338429131150301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125611159916225619420766867 188416739874338429131150301)
        ·
          refine ⟨70656277452876910924181363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188416739874338429131150301 70656277452876910924181363)
          ·
            refine ⟨105984416179315366386272045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70656277452876910924181363 105984416179315366386272045)
            ·
              refine ⟨39744156067243262394852017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105984416179315366386272045 39744156067243262394852017)
              ·
                refine ⟨29808117050432446796139013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39744156067243262394852017 29808117050432446796139013)
                ·
                  refine ⟨5589021946956083774276065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29808117050432446796139013 5589021946956083774276065)
                  ·
                    refine ⟨4191766460217062830707049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5589021946956083774276065 4191766460217062830707049)
                    ·
                      refine ⟨3143824845162797123030287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4191766460217062830707049 3143824845162797123030287)
                      ·
                        rfl

theorem cell23_6122577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4, 2, 2].length) (baseStart_6122577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122577 prefixEnd_6122577 := by exact prefixLift 6122577
  have htrace : WordTrace (prefixWord ++ tailWord_6122577) baseStart_6122577 baseEnd_6122577 := by
    simpa [prefixWord, tailWord_6122577, baseEnd_6122577] using wordTrace_append hprefix tailTrace_6122577
  have hstable : (prefixWord ++ tailWord_6122577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122577).length < 2 ^ (prefixWord ++ tailWord_6122577).sum := by decide
  have hdescent : baseEnd_6122577 < baseStart_6122577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122610 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 1, 5, 3]
def baseStart_6122610 : Nat := 118140960795 + 6122610 * 2 ^ 59
def prefixEnd_6122610 : Nat := 4983230072969 + 3 ^ 40 * 6122610 * 2
def baseEnd_6122610 : Nat := 3143841790024395493917635

theorem tailTrace_6122610 : CollatzResearch.WordTrace tailWord_6122610 prefixEnd_6122610 3143841790024395493917635 := by
  unfold tailWord_6122610
  simp only [CollatzResearch.WordTrace]
  refine ⟨55827483087209275845995321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148873288232558068922654189 55827483087209275845995321)
  ·
    refine ⟨41870612315406956884496491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55827483087209275845995321 41870612315406956884496491)
    ·
      refine ⟨62805918473110435326744737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41870612315406956884496491 62805918473110435326744737)
      ·
        refine ⟨47104438854832826495058553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62805918473110435326744737 47104438854832826495058553)
        ·
          refine ⟨35328329141124619871293915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47104438854832826495058553 35328329141124619871293915)
          ·
            refine ⟨52992493711686929806940873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35328329141124619871293915 52992493711686929806940873)
            ·
              refine ⟨39744370283765197355205655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52992493711686929806940873 39744370283765197355205655)
              ·
                refine ⟨59616555425647796032808483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39744370283765197355205655 59616555425647796032808483)
                ·
                  refine ⟨89424833138471694049212725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59616555425647796032808483 89424833138471694049212725)
                  ·
                    refine ⟨8383578106731721317113693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 89424833138471694049212725 8383578106731721317113693)
                    ·
                      refine ⟨3143841790024395493917635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8383578106731721317113693 3143841790024395493917635)
                      ·
                        rfl

theorem cell23_6122610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_6122610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122610 prefixEnd_6122610 := by exact prefixLift 6122610
  have htrace : WordTrace (prefixWord ++ tailWord_6122610) baseStart_6122610 baseEnd_6122610 := by
    simpa [prefixWord, tailWord_6122610, baseEnd_6122610] using wordTrace_append hprefix tailTrace_6122610
  have hstable : (prefixWord ++ tailWord_6122610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122610).length < 2 ^ (prefixWord ++ tailWord_6122610).sum := by decide
  have hdescent : baseEnd_6122610 < baseStart_6122610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122654 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 2, 5, 2]
def baseStart_6122654 : Nat := 118140960795 + 6122654 * 2 ^ 59
def prefixEnd_6122654 : Nat := 4983230072969 + 3 ^ 40 * 6122654 * 2
def baseEnd_6122654 : Nat := 3143864383173193321767433

theorem tailTrace_6122654 : CollatzResearch.WordTrace tailWord_6122654 prefixEnd_6122654 3143864383173193321767433 := by
  unfold tailWord_6122654
  simp only [CollatzResearch.WordTrace]
  refine ⟨27913942145084712362322877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148874358107118465932388677 27913942145084712362322877)
  ·
    refine ⟨10467728304406767135871079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27913942145084712362322877 10467728304406767135871079)
    ·
      refine ⟨15701592456610150703806619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10467728304406767135871079 15701592456610150703806619)
      ·
        refine ⟨23552388684915226055709929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15701592456610150703806619 23552388684915226055709929)
        ·
          refine ⟨17664291513686419541782447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23552388684915226055709929 17664291513686419541782447)
          ·
            refine ⟨26496437270529629312673671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17664291513686419541782447 26496437270529629312673671)
            ·
              refine ⟨39744655905794443969010507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26496437270529629312673671 39744655905794443969010507)
              ·
                refine ⟨59616983858691665953515761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39744655905794443969010507 59616983858691665953515761)
                ·
                  refine ⟨44712737894018749465136821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59616983858691665953515761 44712737894018749465136821)
                  ·
                    refine ⟨4191819177564257762356577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44712737894018749465136821 4191819177564257762356577)
                    ·
                      refine ⟨3143864383173193321767433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4191819177564257762356577 3143864383173193321767433)
                      ·
                        rfl

theorem cell23_6122654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_6122654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122654 prefixEnd_6122654 := by exact prefixLift 6122654
  have htrace : WordTrace (prefixWord ++ tailWord_6122654) baseStart_6122654 baseEnd_6122654 := by
    simpa [prefixWord, tailWord_6122654, baseEnd_6122654] using wordTrace_append hprefix tailTrace_6122654
  have hstable : (prefixWord ++ tailWord_6122654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122654).length < 2 ^ (prefixWord ++ tailWord_6122654).sum := by decide
  have hdescent : baseEnd_6122654 < baseStart_6122654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122684 : List Nat := [2, 2, 2, 3, 2, 3, 1, 1, 2, 1, 4]
def baseStart_6122684 : Nat := 118140960795 + 6122684 * 2 ^ 59
def prefixEnd_6122684 : Nat := 4983230072969 + 3 ^ 40 * 6122684 * 2
def baseEnd_6122684 : Nat := 3143879787592828204392295

theorem tailTrace_6122684 : CollatzResearch.WordTrace tailWord_6122684 prefixEnd_6122684 3143879787592828204392295 := by
  unfold tailWord_6122684
  simp only [CollatzResearch.WordTrace]
  refine ⟨111656315675284507011087553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148875087567046009348116737 111656315675284507011087553)
  ·
    refine ⟨83742236756463380258315665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111656315675284507011087553 83742236756463380258315665)
    ·
      refine ⟨62806677567347535193736749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83742236756463380258315665 62806677567347535193736749)
      ·
        refine ⟨23552504087755325697651281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62806677567347535193736749 23552504087755325697651281)
        ·
          refine ⟨17664378065816494273238461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23552504087755325697651281 17664378065816494273238461)
          ·
            refine ⟨6624141774681185352464423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17664378065816494273238461 6624141774681185352464423)
            ·
              refine ⟨9936212662021778028696635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6624141774681185352464423 9936212662021778028696635)
              ·
                refine ⟨14904318993032667043044953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9936212662021778028696635 14904318993032667043044953)
                ·
                  refine ⟨11178239244774500282283715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14904318993032667043044953 11178239244774500282283715)
                  ·
                    refine ⟨16767358867161750423425573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11178239244774500282283715 16767358867161750423425573)
                    ·
                      refine ⟨3143879787592828204392295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16767358867161750423425573 3143879787592828204392295)
                      ·
                        rfl

theorem cell23_6122684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_6122684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122684 prefixEnd_6122684 := by exact prefixLift 6122684
  have htrace : WordTrace (prefixWord ++ tailWord_6122684) baseStart_6122684 baseEnd_6122684 := by
    simpa [prefixWord, tailWord_6122684, baseEnd_6122684] using wordTrace_append hprefix tailTrace_6122684
  have hstable : (prefixWord ++ tailWord_6122684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122684).length < 2 ^ (prefixWord ++ tailWord_6122684).sum := by decide
  have hdescent : baseEnd_6122684 < baseStart_6122684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122687 : List Nat := [1, 1, 2, 2, 2, 2, 5, 1, 2, 2, 3]
def baseStart_6122687 : Nat := 118140960795 + 6122687 * 2 ^ 59
def prefixEnd_6122687 : Nat := 4983230072969 + 3 ^ 40 * 6122687 * 2
def baseEnd_6122687 : Nat := 3143881328034791692654781

theorem tailTrace_6122687 : CollatzResearch.WordTrace tailWord_6122687 prefixEnd_6122687 3143881328034791692654781 := by
  unfold tailWord_6122687
  simp only [CollatzResearch.WordTrace]
  refine ⟨223312740769558145534534315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148875160513038763689689543 223312740769558145534534315)
  ·
    refine ⟨334969111154337218301801473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223312740769558145534534315 334969111154337218301801473)
    ·
      refine ⟨251226833365752913726351105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334969111154337218301801473 251226833365752913726351105)
      ·
        refine ⟨188420125024314685294763329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251226833365752913726351105 188420125024314685294763329)
        ·
          refine ⟨141315093768236013971072497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188420125024314685294763329 141315093768236013971072497)
          ·
            refine ⟨105986320326177010478304373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141315093768236013971072497 105986320326177010478304373)
            ·
              refine ⟨9936217530579094732341035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105986320326177010478304373 9936217530579094732341035)
              ·
                refine ⟨14904326295868642098511553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9936217530579094732341035 14904326295868642098511553)
                ·
                  refine ⟨11178244721901481573883665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14904326295868642098511553 11178244721901481573883665)
                  ·
                    refine ⟨8383683541426111180412749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11178244721901481573883665 8383683541426111180412749)
                    ·
                      refine ⟨3143881328034791692654781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8383683541426111180412749 3143881328034791692654781)
                      ·
                        rfl

theorem cell23_6122687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2, 3].length) (baseStart_6122687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122687 prefixEnd_6122687 := by exact prefixLift 6122687
  have htrace : WordTrace (prefixWord ++ tailWord_6122687) baseStart_6122687 baseEnd_6122687 := by
    simpa [prefixWord, tailWord_6122687, baseEnd_6122687] using wordTrace_append hprefix tailTrace_6122687
  have hstable : (prefixWord ++ tailWord_6122687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122687).length < 2 ^ (prefixWord ++ tailWord_6122687).sum := by decide
  have hdescent : baseEnd_6122687 < baseStart_6122687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122734 : List Nat := [4, 1, 2, 1, 1, 1, 4, 2, 3, 1, 3]
def baseStart_6122734 : Nat := 118140960795 + 6122734 * 2 ^ 59
def prefixEnd_6122734 : Nat := 4983230072969 + 3 ^ 40 * 6122734 * 2
def baseEnd_6122734 : Nat := 3143905461625553008767065

theorem tailTrace_6122734 : CollatzResearch.WordTrace tailWord_6122734 prefixEnd_6122734 3143905461625553008767065 := by
  unfold tailWord_6122734
  simp only [CollatzResearch.WordTrace]
  refine ⟨27914306875048484070186907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148876303333591915040996837 27914306875048484070186907)
  ·
    refine ⟨41871460312572726105280361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27914306875048484070186907 41871460312572726105280361)
    ·
      refine ⟨31403595234429544578960271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41871460312572726105280361 31403595234429544578960271)
      ·
        refine ⟨47105392851644316868440407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31403595234429544578960271 47105392851644316868440407)
        ·
          refine ⟨70658089277466475302660611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47105392851644316868440407 70658089277466475302660611)
          ·
            refine ⟨105987133916199712953990917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70658089277466475302660611 105987133916199712953990917)
            ·
              refine ⟨19872587609287446178873297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105987133916199712953990917 19872587609287446178873297)
              ·
                refine ⟨14904440706965584634154973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19872587609287446178873297 14904440706965584634154973)
                ·
                  refine ⟨5589165265112094237808115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14904440706965584634154973 5589165265112094237808115)
                  ·
                    refine ⟨8383747897668141356712173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5589165265112094237808115 8383747897668141356712173)
                    ·
                      refine ⟨3143905461625553008767065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8383747897668141356712173 3143905461625553008767065)
                      ·
                        rfl

theorem cell23_6122734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_6122734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122734 prefixEnd_6122734 := by exact prefixLift 6122734
  have htrace : WordTrace (prefixWord ++ tailWord_6122734) baseStart_6122734 baseEnd_6122734 := by
    simpa [prefixWord, tailWord_6122734, baseEnd_6122734] using wordTrace_append hprefix tailTrace_6122734
  have hstable : (prefixWord ++ tailWord_6122734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122734).length < 2 ^ (prefixWord ++ tailWord_6122734).sum := by decide
  have hdescent : baseEnd_6122734 < baseStart_6122734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122751 : List Nat := [1, 1, 2, 2, 1, 5, 3, 3, 1, 1, 3]
def baseStart_6122751 : Nat := 118140960795 + 6122751 * 2 ^ 59
def prefixEnd_6122751 : Nat := 4983230072969 + 3 ^ 40 * 6122751 * 2
def baseEnd_6122751 : Nat := 3143914190796679442254487

theorem tailTrace_6122751 : CollatzResearch.WordTrace tailWord_6122751 prefixEnd_6122751 3143914190796679442254487 := by
  unfold tailWord_6122751
  simp only [CollatzResearch.WordTrace]
  refine ⟨223315075041326284464864107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148876716694217522976576071 223315075041326284464864107)
  ·
    refine ⟨334972612561989426697296161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223315075041326284464864107 334972612561989426697296161)
    ·
      refine ⟨251229459421492070022972121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334972612561989426697296161 251229459421492070022972121)
      ·
        refine ⟨188422094566119052517229091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251229459421492070022972121 188422094566119052517229091)
        ·
          refine ⟨282633141849178578775843637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188422094566119052517229091 282633141849178578775843637)
          ·
            refine ⟨26496857048360491760235341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 282633141849178578775843637 26496857048360491760235341)
            ·
              refine ⟨9936321393135184410088253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26496857048360491760235341 9936321393135184410088253)
              ·
                refine ⟨3726120522425694153783095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9936321393135184410088253 3726120522425694153783095)
                ·
                  refine ⟨5589180783638541230674643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3726120522425694153783095 5589180783638541230674643)
                  ·
                    refine ⟨8383771175457811846011965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5589180783638541230674643 8383771175457811846011965)
                    ·
                      refine ⟨3143914190796679442254487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8383771175457811846011965 3143914190796679442254487)
                      ·
                        rfl

theorem cell23_6122751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3, 1, 1, 3].length) (baseStart_6122751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122751 prefixEnd_6122751 := by exact prefixLift 6122751
  have htrace : WordTrace (prefixWord ++ tailWord_6122751) baseStart_6122751 baseEnd_6122751 := by
    simpa [prefixWord, tailWord_6122751, baseEnd_6122751] using wordTrace_append hprefix tailTrace_6122751
  have hstable : (prefixWord ++ tailWord_6122751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122751).length < 2 ^ (prefixWord ++ tailWord_6122751).sum := by decide
  have hdescent : baseEnd_6122751 < baseStart_6122751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122757 : List Nat := [1, 3, 1, 1, 2, 1, 3, 5, 1, 1, 4]
def baseStart_6122757 : Nat := 118140960795 + 6122757 * 2 ^ 59
def prefixEnd_6122757 : Nat := 4983230072969 + 3 ^ 40 * 6122757 * 2
def baseEnd_6122757 : Nat := 3143917271680606418779459

theorem tailTrace_6122757 : CollatzResearch.WordTrace tailWord_6122757 prefixEnd_6122757 3143917271680606418779459 := by
  unfold tailWord_6122757
  simp only [CollatzResearch.WordTrace]
  refine ⟨223315293879304547489582525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148876862586203031659721683 223315293879304547489582525)
  ·
    refine ⟨83743235204739205308593447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223315293879304547489582525 83743235204739205308593447)
    ·
      refine ⟨125614852807108807962890171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83743235204739205308593447 125614852807108807962890171)
      ·
        refine ⟨188422279210663211944335257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125614852807108807962890171 188422279210663211944335257)
        ·
          refine ⟨141316709407997408958251443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188422279210663211944335257 141316709407997408958251443)
          ·
            refine ⟨211975064111996113437377165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141316709407997408958251443 211975064111996113437377165)
            ·
              refine ⟨79490649041998542539016437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211975064111996113437377165 79490649041998542539016437)
              ·
                refine ⟨7452248347687363363032791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79490649041998542539016437 7452248347687363363032791)
                ·
                  refine ⟨11178372521531045044549187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7452248347687363363032791 11178372521531045044549187)
                  ·
                    refine ⟨16767558782296567566823781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11178372521531045044549187 16767558782296567566823781)
                    ·
                      refine ⟨3143917271680606418779459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16767558782296567566823781 3143917271680606418779459)
                      ·
                        rfl

theorem cell23_6122757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 1, 4].length) (baseStart_6122757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122757 prefixEnd_6122757 := by exact prefixLift 6122757
  have htrace : WordTrace (prefixWord ++ tailWord_6122757) baseStart_6122757 baseEnd_6122757 := by
    simpa [prefixWord, tailWord_6122757, baseEnd_6122757] using wordTrace_append hprefix tailTrace_6122757
  have hstable : (prefixWord ++ tailWord_6122757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122757).length < 2 ^ (prefixWord ++ tailWord_6122757).sum := by decide
  have hdescent : baseEnd_6122757 < baseStart_6122757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122780 : List Nat := [2, 2, 3, 1, 1, 1, 3, 10]
def baseStart_6122780 : Nat := 118140960795 + 6122780 * 2 ^ 59
def prefixEnd_6122780 : Nat := 4983230072969 + 3 ^ 40 * 6122780 * 2
def baseEnd_6122780 : Nat := 116441817842061475140439

theorem tailTrace_6122780 : CollatzResearch.WordTrace tailWord_6122780 prefixEnd_6122780 116441817842061475140439 := by
  unfold tailWord_6122780
  simp only [CollatzResearch.WordTrace]
  refine ⟨111658066379110611208834897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148877421838814148278446529 111658066379110611208834897)
  ·
    refine ⟨83743549784332958406626173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111658066379110611208834897 83743549784332958406626173)
    ·
      refine ⟨31403831169124859402484815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83743549784332958406626173 31403831169124859402484815)
      ·
        refine ⟨47105746753687289103727223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31403831169124859402484815 47105746753687289103727223)
        ·
          refine ⟨70658620130530933655590835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47105746753687289103727223 70658620130530933655590835)
          ·
            refine ⟨105987930195796400483386253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70658620130530933655590835 105987930195796400483386253)
            ·
              refine ⟨39745473823423650181269845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105987930195796400483386253 39745473823423650181269845)
              ·
                refine ⟨116441817842061475140439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39745473823423650181269845 116441817842061475140439)
                ·
                  rfl

theorem cell23_6122780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 10].length) (baseStart_6122780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122780 prefixEnd_6122780 := by exact prefixLift 6122780
  have htrace : WordTrace (prefixWord ++ tailWord_6122780) baseStart_6122780 baseEnd_6122780 := by
    simpa [prefixWord, tailWord_6122780, baseEnd_6122780] using wordTrace_append hprefix tailTrace_6122780
  have hstable : (prefixWord ++ tailWord_6122780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122780).length < 2 ^ (prefixWord ++ tailWord_6122780).sum := by decide
  have hdescent : baseEnd_6122780 < baseStart_6122780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122804 : List Nat := [2, 5, 1, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_6122804 : Nat := 118140960795 + 6122804 * 2 ^ 59
def prefixEnd_6122804 : Nat := 4983230072969 + 3 ^ 40 * 6122804 * 2
def baseEnd_6122804 : Nat := 3143941405271367734891743

theorem tailTrace_6122804 : CollatzResearch.WordTrace tailWord_6122804 prefixEnd_6122804 3143941405271367734891743 := by
  unfold tailWord_6122804
  simp only [CollatzResearch.WordTrace]
  refine ⟨111658504055067137258271733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148878005406756183011028977 111658504055067137258271733)
  ·
    refine ⟨10467984755162544117962975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111658504055067137258271733 10467984755162544117962975)
    ·
      refine ⟨15701977132743816176944463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10467984755162544117962975 15701977132743816176944463)
      ·
        refine ⟨23552965699115724265416695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15701977132743816176944463 23552965699115724265416695)
        ·
          refine ⟨35329448548673586398125043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23552965699115724265416695 35329448548673586398125043)
          ·
            refine ⟨52994172823010379597187565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35329448548673586398125043 52994172823010379597187565)
            ·
              refine ⟨19872814808628892348945337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52994172823010379597187565 19872814808628892348945337)
              ·
                refine ⟨14904611106471669261709003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19872814808628892348945337 14904611106471669261709003)
                ·
                  refine ⟨22356916659707503892563505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14904611106471669261709003 22356916659707503892563505)
                  ·
                    refine ⟨16767687494780627919422629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22356916659707503892563505 16767687494780627919422629)
                    ·
                      refine ⟨3143941405271367734891743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16767687494780627919422629 3143941405271367734891743)
                      ·
                        rfl

theorem cell23_6122804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_6122804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122804 prefixEnd_6122804 := by exact prefixLift 6122804
  have htrace : WordTrace (prefixWord ++ tailWord_6122804) baseStart_6122804 baseEnd_6122804 := by
    simpa [prefixWord, tailWord_6122804, baseEnd_6122804] using wordTrace_append hprefix tailTrace_6122804
  have hstable : (prefixWord ++ tailWord_6122804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122804).length < 2 ^ (prefixWord ++ tailWord_6122804).sum := by decide
  have hdescent : baseEnd_6122804 < baseStart_6122804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122862 : List Nat := [4, 1, 2, 4, 2, 1, 2, 1, 1, 2, 3]
def baseStart_6122862 : Nat := 118140960795 + 6122862 * 2 ^ 59
def prefixEnd_6122862 : Nat := 4983230072969 + 3 ^ 40 * 6122862 * 2
def baseEnd_6122862 : Nat := 3143971187149328507966477

theorem tailTrace_6122862 : CollatzResearch.WordTrace tailWord_6122862 prefixEnd_6122862 3143971187149328507966477 := by
  unfold tailWord_6122862
  simp only [CollatzResearch.WordTrace]
  refine ⟨27914890442990518802769355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148879415695949433614769893 27914890442990518802769355)
  ·
    refine ⟨41872335664485778204154033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27914890442990518802769355 41872335664485778204154033)
    ·
      refine ⟨31404251748364333653115525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41872335664485778204154033 31404251748364333653115525)
      ·
        refine ⟨5888297202818312559959161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31404251748364333653115525 5888297202818312559959161)
        ·
          refine ⟨4416222902113734419969371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5888297202818312559959161 4416222902113734419969371)
          ·
            refine ⟨6624334353170601629954057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4416222902113734419969371 6624334353170601629954057)
            ·
              refine ⟨4968250764877951222465543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6624334353170601629954057 4968250764877951222465543)
              ·
                refine ⟨7452376147316926833698315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4968250764877951222465543 7452376147316926833698315)
                ·
                  refine ⟨11178564220975390250547473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7452376147316926833698315 11178564220975390250547473)
                  ·
                    refine ⟨8383923165731542687910605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11178564220975390250547473 8383923165731542687910605)
                    ·
                      refine ⟨3143971187149328507966477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8383923165731542687910605 3143971187149328507966477)
                      ·
                        rfl

theorem cell23_6122862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_6122862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122862 prefixEnd_6122862 := by exact prefixLift 6122862
  have htrace : WordTrace (prefixWord ++ tailWord_6122862) baseStart_6122862 baseEnd_6122862 := by
    simpa [prefixWord, tailWord_6122862, baseEnd_6122862] using wordTrace_append hprefix tailTrace_6122862
  have hstable : (prefixWord ++ tailWord_6122862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122862).length < 2 ^ (prefixWord ++ tailWord_6122862).sum := by decide
  have hdescent : baseEnd_6122862 < baseStart_6122862 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122864 : List Nat := [2, 1, 1, 1, 4, 2, 1, 4, 1, 4, 2]
def baseStart_6122864 : Nat := 118140960795 + 6122864 * 2 ^ 59
def prefixEnd_6122864 : Nat := 4983230072969 + 3 ^ 40 * 6122864 * 2
def baseEnd_6122864 : Nat := 3143972214110637500141467

theorem tailTrace_6122864 : CollatzResearch.WordTrace tailWord_6122864 prefixEnd_6122864 3143972214110637500141467 := by
  unfold tailWord_6122864
  simp only [CollatzResearch.WordTrace]
  refine ⟨111659598244958452381863823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148879464326611269842485097 111659598244958452381863823)
  ·
    refine ⟨167489397367437678572795735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111659598244958452381863823 167489397367437678572795735)
    ·
      refine ⟨251234096051156517859193603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167489397367437678572795735 251234096051156517859193603)
      ·
        refine ⟨376851144076734776788790405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251234096051156517859193603 376851144076734776788790405)
        ·
          refine ⟨70659589514387770647898201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 376851144076734776788790405 70659589514387770647898201)
          ·
            refine ⟨52994692135790827985923651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70659589514387770647898201 52994692135790827985923651)
            ·
              refine ⟨79492038203686241978885477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52994692135790827985923651 79492038203686241978885477)
              ·
                refine ⟨14904757163191170371041027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79492038203686241978885477 14904757163191170371041027)
                ·
                  refine ⟨22357135744786755556561541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14904757163191170371041027 22357135744786755556561541)
                  ·
                    refine ⟨4191962952147516666855289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22357135744786755556561541 4191962952147516666855289)
                    ·
                      refine ⟨3143972214110637500141467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4191962952147516666855289 3143972214110637500141467)
                      ·
                        rfl

theorem cell23_6122864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 1, 4, 2].length) (baseStart_6122864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122864 prefixEnd_6122864 := by exact prefixLift 6122864
  have htrace : WordTrace (prefixWord ++ tailWord_6122864) baseStart_6122864 baseEnd_6122864 := by
    simpa [prefixWord, tailWord_6122864, baseEnd_6122864] using wordTrace_append hprefix tailTrace_6122864
  have hstable : (prefixWord ++ tailWord_6122864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122864).length < 2 ^ (prefixWord ++ tailWord_6122864).sum := by decide
  have hdescent : baseEnd_6122864 < baseStart_6122864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122877 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 4, 2, 4]
def baseStart_6122877 : Nat := 118140960795 + 6122877 * 2 ^ 59
def prefixEnd_6122877 : Nat := 4983230072969 + 3 ^ 40 * 6122877 * 2
def baseEnd_6122877 : Nat := 3143978889359145949278907

theorem tailTrace_6122877 : CollatzResearch.WordTrace tailWord_6122877 prefixEnd_6122877 3143978889359145949278907 := by
  unfold tailWord_6122877
  simp only [CollatzResearch.WordTrace]
  refine ⟨223319670638869807983950885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148879780425913205322633923 223319670638869807983950885)
  ·
    refine ⟨41872438244788088996990791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223319670638869807983950885 41872438244788088996990791)
    ·
      refine ⟨62808657367182133495486187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41872438244788088996990791 62808657367182133495486187)
      ·
        refine ⟨94212986050773200243229281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62808657367182133495486187 94212986050773200243229281)
        ·
          refine ⟨70659739538079900182421961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94212986050773200243229281 70659739538079900182421961)
          ·
            refine ⟨52994804653559925136816471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70659739538079900182421961 52994804653559925136816471)
            ·
              refine ⟨79492206980339887705224707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52994804653559925136816471 79492206980339887705224707)
              ·
                refine ⟨119238310470509831557837061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79492206980339887705224707 119238310470509831557837061)
                ·
                  refine ⟨22357183213220593417094449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119238310470509831557837061 22357183213220593417094449)
                  ·
                    refine ⟨16767887409915445062820837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22357183213220593417094449 16767887409915445062820837)
                    ·
                      refine ⟨3143978889359145949278907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16767887409915445062820837 3143978889359145949278907)
                      ·
                        rfl

theorem cell23_6122877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_6122877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122877 prefixEnd_6122877 := by exact prefixLift 6122877
  have htrace : WordTrace (prefixWord ++ tailWord_6122877) baseStart_6122877 baseEnd_6122877 := by
    simpa [prefixWord, tailWord_6122877, baseEnd_6122877] using wordTrace_append hprefix tailTrace_6122877
  have hstable : (prefixWord ++ tailWord_6122877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122877).length < 2 ^ (prefixWord ++ tailWord_6122877).sum := by decide
  have hdescent : baseEnd_6122877 < baseStart_6122877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122887 : List Nat := [1, 1, 4, 2, 2, 2, 1, 3, 7]
def baseStart_6122887 : Nat := 118140960795 + 6122887 * 2 ^ 59
def prefixEnd_6122887 : Nat := 4983230072969 + 3 ^ 40 * 6122887 * 2
def baseEnd_6122887 : Nat := 349331558240632323350429

theorem tailTrace_6122887 : CollatzResearch.WordTrace tailWord_6122887 prefixEnd_6122887 349331558240632323350429 := by
  unfold tailWord_6122887
  simp only [CollatzResearch.WordTrace]
  refine ⟨223320035368833579691814915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148880023579222386461209943 223320035368833579691814915)
  ·
    refine ⟨334980053053250369537722373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223320035368833579691814915 334980053053250369537722373)
    ·
      refine ⟨62808759947484444288322945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 334980053053250369537722373 62808759947484444288322945)
      ·
        refine ⟨47106569960613333216242209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62808759947484444288322945 47106569960613333216242209)
        ·
          refine ⟨35329927470459999912181657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47106569960613333216242209 35329927470459999912181657)
          ·
            refine ⟨26497445602844999934136243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35329927470459999912181657 26497445602844999934136243)
            ·
              refine ⟨39746168404267499901204365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26497445602844999934136243 39746168404267499901204365)
              ·
                refine ⟨14904813151600312462951637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39746168404267499901204365 14904813151600312462951637)
                ·
                  refine ⟨349331558240632323350429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14904813151600312462951637 349331558240632323350429)
                  ·
                    rfl

theorem cell23_6122887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 7].length) (baseStart_6122887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122887 prefixEnd_6122887 := by exact prefixLift 6122887
  have htrace : WordTrace (prefixWord ++ tailWord_6122887) baseStart_6122887 baseEnd_6122887 := by
    simpa [prefixWord, tailWord_6122887, baseEnd_6122887] using wordTrace_append hprefix tailTrace_6122887
  have hstable : (prefixWord ++ tailWord_6122887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122887).length < 2 ^ (prefixWord ++ tailWord_6122887).sum := by decide
  have hdescent : baseEnd_6122887 < baseStart_6122887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6122967 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 4]
def baseStart_6122967 : Nat := 118140960795 + 6122967 * 2 ^ 59
def prefixEnd_6122967 : Nat := 4983230072969 + 3 ^ 40 * 6122967 * 2
def baseEnd_6122967 : Nat := 3144025102618050597153493

theorem tailTrace_6122967 : CollatzResearch.WordTrace tailWord_6122967 prefixEnd_6122967 3144025102618050597153493 := by
  unfold tailWord_6122967
  simp only [CollatzResearch.WordTrace]
  refine ⟨223322953208543753354727155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148881968805695835569818103 223322953208543753354727155)
  ·
    refine ⟨334984429812815630032090733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223322953208543753354727155 334984429812815630032090733)
    ·
      refine ⟨125619161179805861262034025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 334984429812815630032090733 125619161179805861262034025)
      ·
        refine ⟨94214370884854395946525519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125619161179805861262034025 94214370884854395946525519)
        ·
          refine ⟨141321556327281593919788279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94214370884854395946525519 141321556327281593919788279)
          ·
            refine ⟨211982334490922390879682419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141321556327281593919788279 211982334490922390879682419)
            ·
              refine ⟨317973501736383586319523629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211982334490922390879682419 317973501736383586319523629)
              ·
                refine ⟨119240063151143844869821361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 317973501736383586319523629 119240063151143844869821361)
                ·
                  refine ⟨89430047363357883652366021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119240063151143844869821361 89430047363357883652366021)
                  ·
                    refine ⟨16768133880629603184818629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89430047363357883652366021 16768133880629603184818629)
                    ·
                      refine ⟨3144025102618050597153493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16768133880629603184818629 3144025102618050597153493)
                      ·
                        rfl

theorem cell23_6122967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_6122967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6122967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6122967 prefixEnd_6122967 := by exact prefixLift 6122967
  have htrace : WordTrace (prefixWord ++ tailWord_6122967) baseStart_6122967 baseEnd_6122967 := by
    simpa [prefixWord, tailWord_6122967, baseEnd_6122967] using wordTrace_append hprefix tailTrace_6122967
  have hstable : (prefixWord ++ tailWord_6122967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6122967).length < 2 ^ (prefixWord ++ tailWord_6122967).sum := by decide
  have hdescent : baseEnd_6122967 < baseStart_6122967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6122967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123017 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 2, 1, 7]
def baseStart_6123017 : Nat := 118140960795 + 6123017 * 2 ^ 59
def prefixEnd_6123017 : Nat := 4983230072969 + 3 ^ 40 * 6123017 * 2
def baseEnd_6123017 : Nat := 3144050776650775401528263

theorem tailTrace_6123017 : CollatzResearch.WordTrace tailWord_6123017 prefixEnd_6123017 3144050776650775401528263 := by
  unfold tailWord_6123017
  simp only [CollatzResearch.WordTrace]
  refine ⟨223324776858362611894047305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148883184572241741262698203 223324776858362611894047305)
  ·
    refine ⟨167493582643771958920535479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223324776858362611894047305 167493582643771958920535479)
    ·
      refine ⟨251240373965657938380803219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167493582643771958920535479 251240373965657938380803219)
      ·
        refine ⟨376860560948486907571204829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251240373965657938380803219 376860560948486907571204829)
        ·
          refine ⟨141322710355682590339201811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 376860560948486907571204829 141322710355682590339201811)
          ·
            refine ⟨211984065533523885508802717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141322710355682590339201811 211984065533523885508802717)
            ·
              refine ⟨79494024575071457065801019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211984065533523885508802717 79494024575071457065801019)
              ·
                refine ⟨119241036862607185598701529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79494024575071457065801019 119241036862607185598701529)
                ·
                  refine ⟨89430777646955389199026147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119241036862607185598701529 89430777646955389199026147)
                  ·
                    refine ⟨134146166470433083798539221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89430777646955389199026147 134146166470433083798539221)
                    ·
                      refine ⟨3144050776650775401528263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 134146166470433083798539221 3144050776650775401528263)
                      ·
                        rfl

theorem cell23_6123017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 1, 7].length) (baseStart_6123017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123017 prefixEnd_6123017 := by exact prefixLift 6123017
  have htrace : WordTrace (prefixWord ++ tailWord_6123017) baseStart_6123017 baseEnd_6123017 := by
    simpa [prefixWord, tailWord_6123017, baseEnd_6123017] using wordTrace_append hprefix tailTrace_6123017
  have hstable : (prefixWord ++ tailWord_6123017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123017).length < 2 ^ (prefixWord ++ tailWord_6123017).sum := by decide
  have hdescent : baseEnd_6123017 < baseStart_6123017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123041 : List Nat := [1, 2, 3, 2, 2, 3, 1, 3, 1, 5]
def baseStart_6123041 : Nat := 118140960795 + 6123041 * 2 ^ 59
def prefixEnd_6123041 : Nat := 4983230072969 + 3 ^ 40 * 6123041 * 2
def baseEnd_6123041 : Nat := 1048021033395494435876051

theorem tailTrace_6123041 : CollatzResearch.WordTrace tailWord_6123041 prefixEnd_6123041 1048021033395494435876051 := by
  unfold tailWord_6123041
  simp only [CollatzResearch.WordTrace]
  refine ⟨223325652210275663992920977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148883768140183775995280651 223325652210275663992920977)
  ·
    refine ⟨167494239157706747994690733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223325652210275663992920977 167494239157706747994690733)
    ·
      refine ⟨62810339684140030498009025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167494239157706747994690733 62810339684140030498009025)
      ·
        refine ⟨47107754763105022873506769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62810339684140030498009025 47107754763105022873506769)
        ·
          refine ⟨35330816072328767155130077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47107754763105022873506769 35330816072328767155130077)
          ·
            refine ⟨13249056027123287683173779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35330816072328767155130077 13249056027123287683173779)
            ·
              refine ⟨19873584040684931524760669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13249056027123287683173779 19873584040684931524760669)
              ·
                refine ⟨7452594015256849321785251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19873584040684931524760669 7452594015256849321785251)
                ·
                  refine ⟨11178891022885273982677877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7452594015256849321785251 11178891022885273982677877)
                  ·
                    refine ⟨1048021033395494435876051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11178891022885273982677877 1048021033395494435876051)
                    ·
                      rfl

theorem cell23_6123041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_6123041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123041 prefixEnd_6123041 := by exact prefixLift 6123041
  have htrace : WordTrace (prefixWord ++ tailWord_6123041) baseStart_6123041 baseEnd_6123041 := by
    simpa [prefixWord, tailWord_6123041, baseEnd_6123041] using wordTrace_append hprefix tailTrace_6123041
  have hstable : (prefixWord ++ tailWord_6123041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123041).length < 2 ^ (prefixWord ++ tailWord_6123041).sum := by decide
  have hdescent : baseEnd_6123041 < baseStart_6123041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123064 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 3, 1, 5]
def baseStart_6123064 : Nat := 118140960795 + 6123064 * 2 ^ 59
def prefixEnd_6123064 : Nat := 4983230072969 + 3 ^ 40 * 6123064 * 2
def baseEnd_6123064 : Nat := 3144074910241536717640547

theorem tailTrace_6123064 : CollatzResearch.WordTrace tailWord_6123064 prefixEnd_6123064 3144074910241536717640547 := by
  unfold tailWord_6123064
  simp only [CollatzResearch.WordTrace]
  refine ⟨111663245544596169460504123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148884327392794892614005497 111663245544596169460504123)
  ·
    refine ⟨167494868316894254190756185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111663245544596169460504123 167494868316894254190756185)
    ·
      refine ⟨125621151237670690643067139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167494868316894254190756185 125621151237670690643067139)
      ·
        refine ⟨188431726856506035964600709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125621151237670690643067139 188431726856506035964600709)
        ·
          refine ⟨35330948785594881743362633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188431726856506035964600709 35330948785594881743362633)
          ·
            refine ⟨26498211589196161307521975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35330948785594881743362633 26498211589196161307521975)
            ·
              refine ⟨39747317383794241961282963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26498211589196161307521975 39747317383794241961282963)
              ·
                refine ⟨59620976075691362941924445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39747317383794241961282963 59620976075691362941924445)
                ·
                  refine ⟨22357866028384261103221667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59620976075691362941924445 22357866028384261103221667)
                  ·
                    refine ⟨33536799042576391654832501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22357866028384261103221667 33536799042576391654832501)
                    ·
                      refine ⟨3144074910241536717640547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33536799042576391654832501 3144074910241536717640547)
                      ·
                        rfl

theorem cell23_6123064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_6123064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123064 prefixEnd_6123064 := by exact prefixLift 6123064
  have htrace : WordTrace (prefixWord ++ tailWord_6123064) baseStart_6123064 baseEnd_6123064 := by
    simpa [prefixWord, tailWord_6123064, baseEnd_6123064] using wordTrace_append hprefix tailTrace_6123064
  have hstable : (prefixWord ++ tailWord_6123064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123064).length < 2 ^ (prefixWord ++ tailWord_6123064).sum := by decide
  have hdescent : baseEnd_6123064 < baseStart_6123064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123071 : List Nat := [1, 1, 2, 2, 3, 5, 1, 1, 1, 6]
def baseStart_6123071 : Nat := 118140960795 + 6123071 * 2 ^ 59
def prefixEnd_6123071 : Nat := 4983230072969 + 3 ^ 40 * 6123071 * 2
def baseEnd_6123071 : Nat := 1048026168202039396751005

theorem tailTrace_6123071 : CollatzResearch.WordTrace tailWord_6123071 prefixEnd_6123071 1048026168202039396751005 := by
  unfold tailWord_6123071
  simp only [CollatzResearch.WordTrace]
  refine ⟨223326746400166979116513067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148884497600111319411008711 223326746400166979116513067)
  ·
    refine ⟨334990119600250468674769601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223326746400166979116513067 334990119600250468674769601)
    ·
      refine ⟨251242589700187851506077201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334990119600250468674769601 251242589700187851506077201)
      ·
        refine ⟨188431942275140888629557901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251242589700187851506077201 188431942275140888629557901)
        ·
          refine ⟨70661978353177833236084213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188431942275140888629557901 70661978353177833236084213)
          ·
            refine ⟨6624560470610421865882895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70661978353177833236084213 6624560470610421865882895)
            ·
              refine ⟨9936840705915632798824343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6624560470610421865882895 9936840705915632798824343)
              ·
                refine ⟨14905261058873449198236515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9936840705915632798824343 14905261058873449198236515)
                ·
                  refine ⟨22357891588310173797354773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14905261058873449198236515 22357891588310173797354773)
                  ·
                    refine ⟨1048026168202039396751005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22357891588310173797354773 1048026168202039396751005)
                    ·
                      rfl

theorem cell23_6123071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 6].length) (baseStart_6123071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123071 prefixEnd_6123071 := by exact prefixLift 6123071
  have htrace : WordTrace (prefixWord ++ tailWord_6123071) baseStart_6123071 baseEnd_6123071 := by
    simpa [prefixWord, tailWord_6123071, baseEnd_6123071] using wordTrace_append hprefix tailTrace_6123071
  have hstable : (prefixWord ++ tailWord_6123071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123071).length < 2 ^ (prefixWord ++ tailWord_6123071).sum := by decide
  have hdescent : baseEnd_6123071 < baseStart_6123071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123084 : List Nat := [2, 2, 1, 3, 1, 4, 1, 9]
def baseStart_6123084 : Nat := 118140960795 + 6123084 * 2 ^ 59
def prefixEnd_6123084 : Nat := 4983230072969 + 3 ^ 40 * 6123084 * 2
def baseEnd_6123084 : Nat := 116447599253875060718165

theorem tailTrace_6123084 : CollatzResearch.WordTrace tailWord_6123084 prefixEnd_6123084 116447599253875060718165 := by
  unfold tailWord_6123084
  simp only [CollatzResearch.WordTrace]
  refine ⟨111663610274559941168368153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148884813699413254891157537 111663610274559941168368153)
  ·
    refine ⟨83747707705919955876276115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111663610274559941168368153 83747707705919955876276115)
    ·
      refine ⟨125621561558879933814414173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83747707705919955876276115 125621561558879933814414173)
      ·
        refine ⟨47108085584579975180405315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125621561558879933814414173 47108085584579975180405315)
        ·
          refine ⟨70662128376869962770607973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47108085584579975180405315 70662128376869962770607973)
          ·
            refine ⟨13249149070663118019488995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70662128376869962770607973 13249149070663118019488995)
            ·
              refine ⟨19873723605994677029233493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13249149070663118019488995 19873723605994677029233493)
              ·
                refine ⟨116447599253875060718165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19873723605994677029233493 116447599253875060718165)
                ·
                  rfl

theorem cell23_6123084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 9].length) (baseStart_6123084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123084 prefixEnd_6123084 := by exact prefixLift 6123084
  have htrace : WordTrace (prefixWord ++ tailWord_6123084) baseStart_6123084 baseEnd_6123084 := by
    simpa [prefixWord, tailWord_6123084, baseEnd_6123084] using wordTrace_append hprefix tailTrace_6123084
  have hstable : (prefixWord ++ tailWord_6123084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123084).length < 2 ^ (prefixWord ++ tailWord_6123084).sum := by decide
  have hdescent : baseEnd_6123084 < baseStart_6123084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123112 : List Nat := [2, 1, 4, 3, 1, 3, 1, 1, 3, 2, 2]
def baseStart_6123112 : Nat := 118140960795 + 6123112 * 2 ^ 59
def prefixEnd_6123112 : Nat := 4983230072969 + 3 ^ 40 * 6123112 * 2
def baseEnd_6123112 : Nat := 3144099557312952529840327

theorem tailTrace_6123112 : CollatzResearch.WordTrace tailWord_6123112 prefixEnd_6123112 3144099557312952529840327 := by
  unfold tailWord_6123112
  simp only [CollatzResearch.WordTrace]
  refine ⟨111664120896509221559377795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148885494528678962079170393 111664120896509221559377795)
  ·
    refine ⟨167496181344763832339066693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111664120896509221559377795 167496181344763832339066693)
    ·
      refine ⟨31405534002143218563575005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167496181344763832339066693 31405534002143218563575005)
      ·
        refine ⟨11777075250803706961340627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31405534002143218563575005 11777075250803706961340627)
        ·
          refine ⟨17665612876205560442010941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11777075250803706961340627 17665612876205560442010941)
          ·
            refine ⟨6624604828577085165754103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17665612876205560442010941 6624604828577085165754103)
            ·
              refine ⟨9936907242865627748631155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6624604828577085165754103 9936907242865627748631155)
              ·
                refine ⟨14905360864298441622946733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9936907242865627748631155 14905360864298441622946733)
                ·
                  refine ⟨5589510324111915608605025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14905360864298441622946733 5589510324111915608605025)
                  ·
                    refine ⟨4192132743083936706453769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5589510324111915608605025 4192132743083936706453769)
                    ·
                      refine ⟨3144099557312952529840327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4192132743083936706453769 3144099557312952529840327)
                      ·
                        rfl

theorem cell23_6123112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_6123112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123112 prefixEnd_6123112 := by exact prefixLift 6123112
  have htrace : WordTrace (prefixWord ++ tailWord_6123112) baseStart_6123112 baseEnd_6123112 := by
    simpa [prefixWord, tailWord_6123112, baseEnd_6123112] using wordTrace_append hprefix tailTrace_6123112
  have hstable : (prefixWord ++ tailWord_6123112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123112).length < 2 ^ (prefixWord ++ tailWord_6123112).sum := by decide
  have hdescent : baseEnd_6123112 < baseStart_6123112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123191 : List Nat := [1, 1, 3, 1, 5, 2, 1, 2, 7]
def baseStart_6123191 : Nat := 118140960795 + 6123191 * 2 ^ 59
def prefixEnd_6123191 : Nat := 4983230072969 + 3 ^ 40 * 6123191 * 2
def baseEnd_6123191 : Nat := 349348902476073080083607

theorem tailTrace_6123191 : CollatzResearch.WordTrace tailWord_6123191 prefixEnd_6123191 349348902476073080083607 := by
  unfold tailWord_6123191
  simp only [CollatzResearch.WordTrace]
  refine ⟨223331123159732239610881427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148887415439821493073920951 223331123159732239610881427)
  ·
    refine ⟨334996684739598359416322141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223331123159732239610881427 334996684739598359416322141)
    ·
      refine ⟨125623756777349384781120803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 334996684739598359416322141 125623756777349384781120803)
      ·
        refine ⟨188435635166024077171681205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125623756777349384781120803 188435635166024077171681205)
        ·
          refine ⟨17665840796814757234845113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 188435635166024077171681205 17665840796814757234845113)
          ·
            refine ⟨13249380597611067926133835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17665840796814757234845113 13249380597611067926133835)
            ·
              refine ⟨19874070896416601889200753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13249380597611067926133835 19874070896416601889200753)
              ·
                refine ⟨14905553172312451416900565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19874070896416601889200753 14905553172312451416900565)
                ·
                  refine ⟨349348902476073080083607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14905553172312451416900565 349348902476073080083607)
                  ·
                    rfl

theorem cell23_6123191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 7].length) (baseStart_6123191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123191 prefixEnd_6123191 := by exact prefixLift 6123191
  have htrace : WordTrace (prefixWord ++ tailWord_6123191) baseStart_6123191 baseEnd_6123191 := by
    simpa [prefixWord, tailWord_6123191, baseEnd_6123191] using wordTrace_append hprefix tailTrace_6123191
  have hstable : (prefixWord ++ tailWord_6123191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123191).length < 2 ^ (prefixWord ++ tailWord_6123191).sum := by decide
  have hdescent : baseEnd_6123191 < baseStart_6123191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123206 : List Nat := [6, 1, 2, 1, 1, 1, 4, 1, 1, 3, 2]
def baseStart_6123206 : Nat := 118140960795 + 6123206 * 2 ^ 59
def prefixEnd_6123206 : Nat := 4983230072969 + 3 ^ 40 * 6123206 * 2
def baseEnd_6123206 : Nat := 3144147824494475162064895

theorem tailTrace_6123206 : CollatzResearch.WordTrace tailWord_6123206 prefixEnd_6123206 3144147824494475162064895 := by
  unfold tailWord_6123206
  simp only [CollatzResearch.WordTrace]
  refine ⟨6979114695458684286646171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 148887780169785264781784981 6979114695458684286646171)
  ·
    refine ⟨10468672043188026429969257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6979114695458684286646171 10468672043188026429969257)
    ·
      refine ⟨7851504032391019822476943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10468672043188026429969257 7851504032391019822476943)
      ·
        refine ⟨11777256048586529733715415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7851504032391019822476943 11777256048586529733715415)
        ·
          refine ⟨17665884072879794600573123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11777256048586529733715415 17665884072879794600573123)
          ·
            refine ⟨26498826109319691900859685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17665884072879794600573123 26498826109319691900859685)
            ·
              refine ⟨4968529895497442231411191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26498826109319691900859685 4968529895497442231411191)
              ·
                refine ⟨7452794843246163347116787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4968529895497442231411191 7452794843246163347116787)
                ·
                  refine ⟨11179192264869245020675181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7452794843246163347116787 11179192264869245020675181)
                  ·
                    refine ⟨4192197099325966882753193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11179192264869245020675181 4192197099325966882753193)
                    ·
                      refine ⟨3144147824494475162064895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4192197099325966882753193 3144147824494475162064895)
                      ·
                        rfl

theorem cell23_6123206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_6123206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123206 prefixEnd_6123206 := by exact prefixLift 6123206
  have htrace : WordTrace (prefixWord ++ tailWord_6123206) baseStart_6123206 baseEnd_6123206 := by
    simpa [prefixWord, tailWord_6123206, baseEnd_6123206] using wordTrace_append hprefix tailTrace_6123206
  have hstable : (prefixWord ++ tailWord_6123206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123206).length < 2 ^ (prefixWord ++ tailWord_6123206).sum := by decide
  have hdescent : baseEnd_6123206 < baseStart_6123206 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123208 : List Nat := [2, 1, 3, 1, 2, 2, 4, 3, 5]
def baseStart_6123208 : Nat := 118140960795 + 6123208 * 2 ^ 59
def prefixEnd_6123208 : Nat := 4983230072969 + 3 ^ 40 * 6123208 * 2
def baseEnd_6123208 : Nat := 349349872383976017137765

theorem tailTrace_6123208 : CollatzResearch.WordTrace tailWord_6123208 prefixEnd_6123208 349349872383976017137765 := by
  unfold tailWord_6123208
  simp only [CollatzResearch.WordTrace]
  refine ⟨111665871600335325757125139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148887828800447101009500185 111665871600335325757125139)
  ·
    refine ⟨167498807400502988635687709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111665871600335325757125139 167498807400502988635687709)
    ·
      refine ⟨62812052775188620738382891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167498807400502988635687709 62812052775188620738382891)
      ·
        refine ⟨94218079162782931107574337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62812052775188620738382891 94218079162782931107574337)
        ·
          refine ⟨70663559372087198330680753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94218079162782931107574337 70663559372087198330680753)
          ·
            refine ⟨52997669529065398748010565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70663559372087198330680753 52997669529065398748010565)
            ·
              refine ⟨9937063036699762265251981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52997669529065398748010565 9937063036699762265251981)
              ·
                refine ⟨3726398638762410849469493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9937063036699762265251981 3726398638762410849469493)
                ·
                  refine ⟨349349872383976017137765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3726398638762410849469493 349349872383976017137765)
                  ·
                    rfl

theorem cell23_6123208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3, 5].length) (baseStart_6123208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123208 prefixEnd_6123208 := by exact prefixLift 6123208
  have htrace : WordTrace (prefixWord ++ tailWord_6123208) baseStart_6123208 baseEnd_6123208 := by
    simpa [prefixWord, tailWord_6123208, baseEnd_6123208] using wordTrace_append hprefix tailTrace_6123208
  have hstable : (prefixWord ++ tailWord_6123208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123208).length < 2 ^ (prefixWord ++ tailWord_6123208).sum := by decide
  have hdescent : baseEnd_6123208 < baseStart_6123208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123218 : List Nat := [3, 2, 2, 2, 2, 1, 1, 2, 2, 3, 3]
def baseStart_6123218 : Nat := 118140960795 + 6123218 * 2 ^ 59
def prefixEnd_6123218 : Nat := 4983230072969 + 3 ^ 40 * 6123218 * 2
def baseEnd_6123218 : Nat := 3144153986262329115114839

theorem tailTrace_6123218 : CollatzResearch.WordTrace tailWord_6123218 prefixEnd_6123218 3144153986262329115114839 := by
  unfold tailWord_6123218
  simp only [CollatzResearch.WordTrace]
  refine ⟨55833026982658605805528577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148888071953756282148076205 55833026982658605805528577)
  ·
    refine ⟨41874770236993954354146433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55833026982658605805528577 41874770236993954354146433)
    ·
      refine ⟨31406077677745465765609825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41874770236993954354146433 31406077677745465765609825)
      ·
        refine ⟨23554558258309099324207369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31406077677745465765609825 23554558258309099324207369)
        ·
          refine ⟨17665918693731824493155527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23554558258309099324207369 17665918693731824493155527)
          ·
            refine ⟨26498878040597736739733291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17665918693731824493155527 26498878040597736739733291)
            ·
              refine ⟨39748317060896605109599937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26498878040597736739733291 39748317060896605109599937)
              ·
                refine ⟨29811237795672453832199953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39748317060896605109599937 29811237795672453832199953)
                ·
                  refine ⟨22358428346754340374149965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29811237795672453832199953 22358428346754340374149965)
                  ·
                    refine ⟨8384410630032877640306237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22358428346754340374149965 8384410630032877640306237)
                    ·
                      refine ⟨3144153986262329115114839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8384410630032877640306237 3144153986262329115114839)
                      ·
                        rfl

theorem cell23_6123218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_6123218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123218 prefixEnd_6123218 := by exact prefixLift 6123218
  have htrace : WordTrace (prefixWord ++ tailWord_6123218) baseStart_6123218 baseEnd_6123218 := by
    simpa [prefixWord, tailWord_6123218, baseEnd_6123218] using wordTrace_append hprefix tailTrace_6123218
  have hstable : (prefixWord ++ tailWord_6123218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123218).length < 2 ^ (prefixWord ++ tailWord_6123218).sum := by decide
  have hdescent : baseEnd_6123218 < baseStart_6123218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123278 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3]
def baseStart_6123278 : Nat := 118140960795 + 6123278 * 2 ^ 59
def prefixEnd_6123278 : Nat := 4983230072969 + 3 ^ 40 * 6123278 * 2
def baseEnd_6123278 : Nat := 3144184795101598880364563

theorem tailTrace_6123278 : CollatzResearch.WordTrace tailWord_6123278 prefixEnd_6123278 3144184795101598880364563 := by
  unfold tailWord_6123278
  simp only [CollatzResearch.WordTrace]
  refine ⟨27916787038802131683662311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148889530873611368979532325 27916787038802131683662311)
  ·
    refine ⟨41875180558203197525493467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27916787038802131683662311 41875180558203197525493467)
    ·
      refine ⟨62812770837304796288240201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41875180558203197525493467 62812770837304796288240201)
      ·
        refine ⟨47109578127978597216180151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62812770837304796288240201 47109578127978597216180151)
        ·
          refine ⟨70664367191967895824270227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47109578127978597216180151 70664367191967895824270227)
          ·
            refine ⟨105996550787951843736405341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70664367191967895824270227 105996550787951843736405341)
            ·
              refine ⟨39748706545481941401152003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105996550787951843736405341 39748706545481941401152003)
              ·
                refine ⟨59623059818222912101728005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39748706545481941401152003 59623059818222912101728005)
                ·
                  refine ⟨11179323715916796019074001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59623059818222912101728005 11179323715916796019074001)
                  ·
                    refine ⟨8384492786937597014305501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11179323715916796019074001 8384492786937597014305501)
                    ·
                      refine ⟨3144184795101598880364563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8384492786937597014305501 3144184795101598880364563)
                      ·
                        rfl

theorem cell23_6123278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_6123278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123278 prefixEnd_6123278 := by exact prefixLift 6123278
  have htrace : WordTrace (prefixWord ++ tailWord_6123278) baseStart_6123278 baseEnd_6123278 := by
    simpa [prefixWord, tailWord_6123278, baseEnd_6123278] using wordTrace_append hprefix tailTrace_6123278
  have hstable : (prefixWord ++ tailWord_6123278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123278).length < 2 ^ (prefixWord ++ tailWord_6123278).sum := by decide
  have hdescent : baseEnd_6123278 < baseStart_6123278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123281 : List Nat := [1, 2, 2, 1, 1, 3, 1, 6, 6]
def baseStart_6123281 : Nat := 118140960795 + 6123281 * 2 ^ 59
def prefixEnd_6123281 : Nat := 4983230072969 + 3 ^ 40 * 6123281 * 2
def baseEnd_6123281 : Nat := 349354037282618040958561

theorem tailTrace_6123281 : CollatzResearch.WordTrace tailWord_6123281 prefixEnd_6123281 349354037282618040958561 := by
  unfold tailWord_6123281
  simp only [CollatzResearch.WordTrace]
  refine ⟨223334405729406184981657697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148889603819604123321105131 223334405729406184981657697)
  ·
    refine ⟨167500804297054638736243273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223334405729406184981657697 167500804297054638736243273)
    ·
      refine ⟨125625603222790979052182455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167500804297054638736243273 125625603222790979052182455)
      ·
        refine ⟨188438404834186468578273683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125625603222790979052182455 188438404834186468578273683)
        ·
          refine ⟨282657607251279702867410525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188438404834186468578273683 282657607251279702867410525)
          ·
            refine ⟨105996602719229888575278947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 282657607251279702867410525 105996602719229888575278947)
            ·
              refine ⟨158994904078844832862918421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105996602719229888575278947 158994904078844832862918421)
              ·
                refine ⟨7452886128695851540449301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 158994904078844832862918421 7452886128695851540449301)
                ·
                  refine ⟨349354037282618040958561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7452886128695851540449301 349354037282618040958561)
                  ·
                    rfl

theorem cell23_6123281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 6].length) (baseStart_6123281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123281 prefixEnd_6123281 := by exact prefixLift 6123281
  have htrace : WordTrace (prefixWord ++ tailWord_6123281) baseStart_6123281 baseEnd_6123281 := by
    simpa [prefixWord, tailWord_6123281, baseEnd_6123281] using wordTrace_append hprefix tailTrace_6123281
  have hstable : (prefixWord ++ tailWord_6123281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123281).length < 2 ^ (prefixWord ++ tailWord_6123281).sum := by decide
  have hdescent : baseEnd_6123281 < baseStart_6123281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123285 : List Nat := [1, 3, 2, 1, 2, 5, 1, 1, 3, 4]
def baseStart_6123285 : Nat := 118140960795 + 6123285 * 2 ^ 59
def prefixEnd_6123285 : Nat := 4983230072969 + 3 ^ 40 * 6123285 * 2
def baseEnd_6123285 : Nat := 1048062796488726784325677

theorem tailTrace_6123285 : CollatzResearch.WordTrace tailWord_6123285 prefixEnd_6123285 1048062796488726784325677 := by
  unfold tailWord_6123285
  simp only [CollatzResearch.WordTrace]
  refine ⟨223334551621391693664803309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148889701080927795776535539 223334551621391693664803309)
  ·
    refine ⟨83750456858021885124301241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223334551621391693664803309 83750456858021885124301241)
    ·
      refine ⟨62812842643516413843225931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83750456858021885124301241 62812842643516413843225931)
      ·
        refine ⟨94219263965274620764838897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62812842643516413843225931 94219263965274620764838897)
        ·
          refine ⟨70664447973955965573629173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94219263965274620764838897 70664447973955965573629173)
          ·
            refine ⟨6624791997558371772527735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70664447973955965573629173 6624791997558371772527735)
            ·
              refine ⟨9937187996337557658791603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6624791997558371772527735 9937187996337557658791603)
              ·
                refine ⟨14905781994506336488187405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9937187996337557658791603 14905781994506336488187405)
                ·
                  refine ⟨5589668247939876183070277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14905781994506336488187405 5589668247939876183070277)
                  ·
                    refine ⟨1048062796488726784325677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5589668247939876183070277 1048062796488726784325677)
                    ·
                      rfl

theorem cell23_6123285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_6123285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123285 prefixEnd_6123285 := by exact prefixLift 6123285
  have htrace : WordTrace (prefixWord ++ tailWord_6123285) baseStart_6123285 baseEnd_6123285 := by
    simpa [prefixWord, tailWord_6123285, baseEnd_6123285] using wordTrace_append hprefix tailTrace_6123285
  have hstable : (prefixWord ++ tailWord_6123285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123285).length < 2 ^ (prefixWord ++ tailWord_6123285).sum := by decide
  have hdescent : baseEnd_6123285 < baseStart_6123285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123298 : List Nat := [3, 3, 1, 1, 2, 1, 3, 3, 6]
def baseStart_6123298 : Nat := 118140960795 + 6123298 * 2 ^ 59
def prefixEnd_6123298 : Nat := 4983230072969 + 3 ^ 40 * 6123298 * 2
def baseEnd_6123298 : Nat := 349355007190520978012719

theorem tailTrace_6123298 : CollatzResearch.WordTrace tailWord_6123298 prefixEnd_6123298 349355007190520978012719 := by
  unfold tailWord_6123298
  simp only [CollatzResearch.WordTrace]
  refine ⟨55833756442586149221256637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148890017180229731256684365 55833756442586149221256637)
  ·
    refine ⟨20937658665969805957971239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55833756442586149221256637 20937658665969805957971239)
    ·
      refine ⟨31406487998954708936956859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20937658665969805957971239 31406487998954708936956859)
      ·
        refine ⟨47109731998432063405435289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31406487998954708936956859 47109731998432063405435289)
        ·
          refine ⟨35332298998824047554076467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47109731998432063405435289 35332298998824047554076467)
          ·
            refine ⟨52998448498236071331114701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35332298998824047554076467 52998448498236071331114701)
            ·
              refine ⟨19874418186838526749168013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52998448498236071331114701 19874418186838526749168013)
              ·
                refine ⟨7452906820064447530938005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19874418186838526749168013 7452906820064447530938005)
                ·
                  refine ⟨349355007190520978012719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7452906820064447530938005 349355007190520978012719)
                  ·
                    rfl

theorem cell23_6123298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_6123298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123298 prefixEnd_6123298 := by exact prefixLift 6123298
  have htrace : WordTrace (prefixWord ++ tailWord_6123298) baseStart_6123298 baseEnd_6123298 := by
    simpa [prefixWord, tailWord_6123298, baseEnd_6123298] using wordTrace_append hprefix tailTrace_6123298
  have hstable : (prefixWord ++ tailWord_6123298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123298).length < 2 ^ (prefixWord ++ tailWord_6123298).sum := by decide
  have hdescent : baseEnd_6123298 < baseStart_6123298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123311 : List Nat := [1, 1, 2, 1, 2, 1, 2, 5, 3, 5]
def baseStart_6123311 : Nat := 118140960795 + 6123311 * 2 ^ 59
def prefixEnd_6123311 : Nat := 4983230072969 + 3 ^ 40 * 6123311 * 2
def baseEnd_6123311 : Nat := 1048067246654399083750637

theorem tailTrace_6123311 : CollatzResearch.WordTrace tailWord_6123311 prefixEnd_6123311 1048067246654399083750637 := by
  unfold tailWord_6123311
  simp only [CollatzResearch.WordTrace]
  refine ⟨223335499919297500105249787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148890333279531666736833191 223335499919297500105249787)
  ·
    refine ⟨335003249878946250157874681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223335499919297500105249787 335003249878946250157874681)
    ·
      refine ⟨251252437409209687618406011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335003249878946250157874681 251252437409209687618406011)
      ·
        refine ⟨376878656113814531427609017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251252437409209687618406011 376878656113814531427609017)
        ·
          refine ⟨282658992085360898570706763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376878656113814531427609017 282658992085360898570706763)
          ·
            refine ⟨423988488128041347856060145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282658992085360898570706763 423988488128041347856060145)
            ·
              refine ⟨317991366096031010892045109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 423988488128041347856060145 317991366096031010892045109)
              ·
                refine ⟨29811690571502907271129229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 317991366096031010892045109 29811690571502907271129229)
                ·
                  refine ⟨11179383964313590226673461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29811690571502907271129229 11179383964313590226673461)
                  ·
                    refine ⟨1048067246654399083750637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11179383964313590226673461 1048067246654399083750637)
                    ·
                      rfl

theorem cell23_6123311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 5].length) (baseStart_6123311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123311 prefixEnd_6123311 := by exact prefixLift 6123311
  have htrace : WordTrace (prefixWord ++ tailWord_6123311) baseStart_6123311 baseEnd_6123311 := by
    simpa [prefixWord, tailWord_6123311, baseEnd_6123311] using wordTrace_append hprefix tailTrace_6123311
  have hstable : (prefixWord ++ tailWord_6123311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123311).length < 2 ^ (prefixWord ++ tailWord_6123311).sum := by decide
  have hdescent : baseEnd_6123311 < baseStart_6123311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123335 : List Nat := [1, 1, 4, 1, 2, 1, 4, 2, 2, 3, 2]
def baseStart_6123335 : Nat := 118140960795 + 6123335 * 2 ^ 59
def prefixEnd_6123335 : Nat := 4983230072969 + 3 ^ 40 * 6123335 * 2
def baseEnd_6123335 : Nat := 3144214063498905157351801

theorem tailTrace_6123335 : CollatzResearch.WordTrace tailWord_6123335 prefixEnd_6123335 3144214063498905157351801 := by
  unfold tailWord_6123335
  simp only [CollatzResearch.WordTrace]
  refine ⟨223336375271210552204123459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148890916847473701469415639 223336375271210552204123459)
  ·
    refine ⟨335004562906815828306185189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223336375271210552204123459 335004562906815828306185189)
    ·
      refine ⟨62813355545027967807409723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 335004562906815828306185189 62813355545027967807409723)
      ·
        refine ⟨94220033317541951711114585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62813355545027967807409723 94220033317541951711114585)
        ·
          refine ⟨70665024988156463783335939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94220033317541951711114585 70665024988156463783335939)
          ·
            refine ⟨105997537482234695675003909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70665024988156463783335939 105997537482234695675003909)
            ·
              refine ⟨19874538277919005439063233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105997537482234695675003909 19874538277919005439063233)
              ·
                refine ⟨14905903708439254079297425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19874538277919005439063233 14905903708439254079297425)
                ·
                  refine ⟨11179427781329440559473069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14905903708439254079297425 11179427781329440559473069)
                  ·
                    refine ⟨4192285417998540209802401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11179427781329440559473069 4192285417998540209802401)
                    ·
                      refine ⟨3144214063498905157351801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4192285417998540209802401 3144214063498905157351801)
                      ·
                        rfl

theorem cell23_6123335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 3, 2].length) (baseStart_6123335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123335 prefixEnd_6123335 := by exact prefixLift 6123335
  have htrace : WordTrace (prefixWord ++ tailWord_6123335) baseStart_6123335 baseEnd_6123335 := by
    simpa [prefixWord, tailWord_6123335, baseEnd_6123335] using wordTrace_append hprefix tailTrace_6123335
  have hstable : (prefixWord ++ tailWord_6123335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123335).length < 2 ^ (prefixWord ++ tailWord_6123335).sum := by decide
  have hdescent : baseEnd_6123335 < baseStart_6123335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123385 : List Nat := [1, 2, 1, 3, 2, 2, 3, 3, 1, 2, 3]
def baseStart_6123385 : Nat := 118140960795 + 6123385 * 2 ^ 59
def prefixEnd_6123385 : Nat := 4983230072969 + 3 ^ 40 * 6123385 * 2
def baseEnd_6123385 : Nat := 3144239737531629961726571

theorem tailTrace_6123385 : CollatzResearch.WordTrace tailWord_6123385 prefixEnd_6123385 3144239737531629961726571 := by
  unfold tailWord_6123385
  simp only [CollatzResearch.WordTrace]
  refine ⟨223338198921029410743443609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148892132614019607162295739 223338198921029410743443609)
  ·
    refine ⟨167503649190772058057582707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223338198921029410743443609 167503649190772058057582707)
    ·
      refine ⟨251255473786158087086374061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167503649190772058057582707 251255473786158087086374061)
      ·
        refine ⟨94220802669809282657390273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251255473786158087086374061 94220802669809282657390273)
        ·
          refine ⟨70665602002356961993042705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94220802669809282657390273 70665602002356961993042705)
          ·
            refine ⟨52999201501767721494782029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70665602002356961993042705 52999201501767721494782029)
            ·
              refine ⟨19874700563162895560543261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52999201501767721494782029 19874700563162895560543261)
              ·
                refine ⟨7453012711186085835203723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19874700563162895560543261 7453012711186085835203723)
                ·
                  refine ⟨11179519066779128752805585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7453012711186085835203723 11179519066779128752805585)
                  ·
                    refine ⟨8384639300084346564604189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11179519066779128752805585 8384639300084346564604189)
                    ·
                      refine ⟨3144239737531629961726571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8384639300084346564604189 3144239737531629961726571)
                      ·
                        rfl

theorem cell23_6123385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_6123385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123385 prefixEnd_6123385 := by exact prefixLift 6123385
  have htrace : WordTrace (prefixWord ++ tailWord_6123385) baseStart_6123385 baseEnd_6123385 := by
    simpa [prefixWord, tailWord_6123385, baseEnd_6123385] using wordTrace_append hprefix tailTrace_6123385
  have hstable : (prefixWord ++ tailWord_6123385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123385).length < 2 ^ (prefixWord ++ tailWord_6123385).sum := by decide
  have hdescent : baseEnd_6123385 < baseStart_6123385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123391 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 6]
def baseStart_6123391 : Nat := 118140960795 + 6123391 * 2 ^ 59
def prefixEnd_6123391 : Nat := 4983230072969 + 3 ^ 40 * 6123391 * 2
def baseEnd_6123391 : Nat := 3144242818415556938251543

theorem tailTrace_6123391 : CollatzResearch.WordTrace tailWord_6123391 prefixEnd_6123391 3144242818415556938251543 := by
  unfold tailWord_6123391
  simp only [CollatzResearch.WordTrace]
  refine ⟨223338417759007673768162027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148892278506005115845441351 223338417759007673768162027)
  ·
    refine ⟨335007626638511510652243041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223338417759007673768162027 335007626638511510652243041)
    ·
      refine ⟨251255719978883632989182281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335007626638511510652243041 251255719978883632989182281)
      ·
        refine ⟨188441789984162724741886711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251255719978883632989182281 188441789984162724741886711)
        ·
          refine ⟨282662684976244087112830067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188441789984162724741886711 282662684976244087112830067)
          ·
            refine ⟨423994027464366130669245101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282662684976244087112830067 423994027464366130669245101)
            ·
              refine ⟨158997760299137299000966913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 423994027464366130669245101 158997760299137299000966913)
              ·
                refine ⟨119248320224352974250725185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158997760299137299000966913 119248320224352974250725185)
                ·
                  refine ⟨89436240168264730688043889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119248320224352974250725185 89436240168264730688043889)
                  ·
                    refine ⟨67077180126198548016032917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89436240168264730688043889 67077180126198548016032917)
                    ·
                      refine ⟨3144242818415556938251543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67077180126198548016032917 3144242818415556938251543)
                      ·
                        rfl

theorem cell23_6123391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_6123391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123391 prefixEnd_6123391 := by exact prefixLift 6123391
  have htrace : WordTrace (prefixWord ++ tailWord_6123391) baseStart_6123391 baseEnd_6123391 := by
    simpa [prefixWord, tailWord_6123391, baseEnd_6123391] using wordTrace_append hprefix tailTrace_6123391
  have hstable : (prefixWord ++ tailWord_6123391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123391).length < 2 ^ (prefixWord ++ tailWord_6123391).sum := by decide
  have hdescent : baseEnd_6123391 < baseStart_6123391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123399 : List Nat := [1, 1, 4, 2, 4, 1, 2, 1, 3, 2, 2]
def baseStart_6123399 : Nat := 118140960795 + 6123399 * 2 ^ 59
def prefixEnd_6123399 : Nat := 4983230072969 + 3 ^ 40 * 6123399 * 2
def baseEnd_6123399 : Nat := 3144246926260792906951507

theorem tailTrace_6123399 : CollatzResearch.WordTrace tailWord_6123399 prefixEnd_6123399 3144246926260792906951507 := by
  unfold tailWord_6123399
  simp only [CollatzResearch.WordTrace]
  refine ⟨223338709542978691134453251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148892473028652460756302167 223338709542978691134453251)
  ·
    refine ⟨335008064314468036701679877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223338709542978691134453251 335008064314468036701679877)
    ·
      refine ⟨62814012058962756881564977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 335008064314468036701679877 62814012058962756881564977)
      ·
        refine ⟨47110509044222067661173733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62814012058962756881564977 47110509044222067661173733)
        ·
          refine ⟨8833220445791637686470075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47110509044222067661173733 8833220445791637686470075)
          ·
            refine ⟨13249830668687456529705113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8833220445791637686470075 13249830668687456529705113)
            ·
              refine ⟨9937373001515592397278835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13249830668687456529705113 9937373001515592397278835)
              ·
                refine ⟨14906059502273388595918253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9937373001515592397278835 14906059502273388595918253)
                ·
                  refine ⟨5589772313352520723469345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14906059502273388595918253 5589772313352520723469345)
                  ·
                    refine ⟨4192329235014390542602009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5589772313352520723469345 4192329235014390542602009)
                    ·
                      refine ⟨3144246926260792906951507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4192329235014390542602009 3144246926260792906951507)
                      ·
                        rfl

theorem cell23_6123399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_6123399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123399 prefixEnd_6123399 := by exact prefixLift 6123399
  have htrace : WordTrace (prefixWord ++ tailWord_6123399) baseStart_6123399 baseEnd_6123399 := by
    simpa [prefixWord, tailWord_6123399, baseEnd_6123399] using wordTrace_append hprefix tailTrace_6123399
  have hstable : (prefixWord ++ tailWord_6123399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123399).length < 2 ^ (prefixWord ++ tailWord_6123399).sum := by decide
  have hdescent : baseEnd_6123399 < baseStart_6123399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123412 : List Nat := [2, 4, 2, 1, 1, 4, 1, 1, 1, 2, 4]
def baseStart_6123412 : Nat := 118140960795 + 6123412 * 2 ^ 59
def prefixEnd_6123412 : Nat := 4983230072969 + 3 ^ 40 * 6123412 * 2
def baseEnd_6123412 : Nat := 3144253601509301356088947

theorem tailTrace_6123412 : CollatzResearch.WordTrace tailWord_6123412 prefixEnd_6123412 3144253601509301356088947 := by
  unfold tailWord_6123412
  simp only [CollatzResearch.WordTrace]
  refine ⟨111669591845965797177338245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148892789127954396236450993 111669591845965797177338245)
  ·
    refine ⟨20938048471118586970750921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111669591845965797177338245 20938048471118586970750921)
    ·
      refine ⟨15703536353338940228063191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20938048471118586970750921 15703536353338940228063191)
      ·
        refine ⟨23555304530008410342094787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15703536353338940228063191 23555304530008410342094787)
        ·
          refine ⟨35332956795012615513142181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23555304530008410342094787 35332956795012615513142181)
          ·
            refine ⟨6624929399064865408714159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35332956795012615513142181 6624929399064865408714159)
            ·
              refine ⟨9937394098597298113071239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6624929399064865408714159 9937394098597298113071239)
              ·
                refine ⟨14906091147895947169606859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9937394098597298113071239 14906091147895947169606859)
                ·
                  refine ⟨22359136721843920754410289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14906091147895947169606859 22359136721843920754410289)
                  ·
                    refine ⟨16769352541382940565807717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22359136721843920754410289 16769352541382940565807717)
                    ·
                      refine ⟨3144253601509301356088947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16769352541382940565807717 3144253601509301356088947)
                      ·
                        rfl

theorem cell23_6123412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_6123412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123412 prefixEnd_6123412 := by exact prefixLift 6123412
  have htrace : WordTrace (prefixWord ++ tailWord_6123412) baseStart_6123412 baseEnd_6123412 := by
    simpa [prefixWord, tailWord_6123412, baseEnd_6123412] using wordTrace_append hprefix tailTrace_6123412
  have hstable : (prefixWord ++ tailWord_6123412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123412).length < 2 ^ (prefixWord ++ tailWord_6123412).sum := by decide
  have hdescent : baseEnd_6123412 < baseStart_6123412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123415 : List Nat := [1, 1, 3, 3, 1, 3, 3, 1, 1, 3, 3]
def baseStart_6123415 : Nat := 118140960795 + 6123415 * 2 ^ 59
def prefixEnd_6123415 : Nat := 4983230072969 + 3 ^ 40 * 6123415 * 2
def baseEnd_6123415 : Nat := 3144255141951264844351433

theorem tailTrace_6123415 : CollatzResearch.WordTrace tailWord_6123415 prefixEnd_6123415 3144255141951264844351433 := by
  unfold tailWord_6123415
  simp only [CollatzResearch.WordTrace]
  refine ⟨223339293110920725867035699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148892862073947150578023799 223339293110920725867035699)
  ·
    refine ⟨335008939666381088800553549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223339293110920725867035699 335008939666381088800553549)
    ·
      refine ⟨125628352374892908300207581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335008939666381088800553549 125628352374892908300207581)
      ·
        refine ⟨47110632140584840612577843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125628352374892908300207581 47110632140584840612577843)
        ·
          refine ⟨70665948210877260918866765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47110632140584840612577843 70665948210877260918866765)
          ·
            refine ⟨26499730579078972844575037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70665948210877260918866765 26499730579078972844575037)
            ·
              refine ⟨9937398967154614816715639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26499730579078972844575037 9937398967154614816715639)
              ·
                refine ⟨14906098450731922225073459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9937398967154614816715639 14906098450731922225073459)
                ·
                  refine ⟨22359147676097883337610189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14906098450731922225073459 22359147676097883337610189)
                  ·
                    refine ⟨8384680378536706251603821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22359147676097883337610189 8384680378536706251603821)
                    ·
                      refine ⟨3144255141951264844351433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8384680378536706251603821 3144255141951264844351433)
                      ·
                        rfl

theorem cell23_6123415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_6123415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123415 prefixEnd_6123415 := by exact prefixLift 6123415
  have htrace : WordTrace (prefixWord ++ tailWord_6123415) baseStart_6123415 baseEnd_6123415 := by
    simpa [prefixWord, tailWord_6123415, baseEnd_6123415] using wordTrace_append hprefix tailTrace_6123415
  have hstable : (prefixWord ++ tailWord_6123415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123415).length < 2 ^ (prefixWord ++ tailWord_6123415).sum := by decide
  have hdescent : baseEnd_6123415 < baseStart_6123415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123422 : List Nat := [4, 3, 1, 3, 1, 1, 1, 9]
def baseStart_6123422 : Nat := 118140960795 + 6123422 * 2 ^ 59
def prefixEnd_6123422 : Nat := 4983230072969 + 3 ^ 40 * 6123422 * 2
def baseEnd_6123422 : Nat := 116454027270957270998663

theorem tailTrace_6123422 : CollatzResearch.WordTrace tailWord_6123422 prefixEnd_6123422 116454027270957270998663 := by
  unfold tailWord_6123422
  simp only [CollatzResearch.WordTrace]
  refine ⟨27917443552736920757817565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148893032281263577375027013 27917443552736920757817565)
  ·
    refine ⟨10469041332276345284181587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27917443552736920757817565 10469041332276345284181587)
    ·
      refine ⟨15703561998414517926272381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10469041332276345284181587 15703561998414517926272381)
      ·
        refine ⟨5888835749405444222352143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15703561998414517926272381 5888835749405444222352143)
        ·
          refine ⟨8833253624108166333528215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5888835749405444222352143 8833253624108166333528215)
          ·
            refine ⟨13249880436162249500292323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8833253624108166333528215 13249880436162249500292323)
            ·
              refine ⟨19874820654243374250438485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13249880436162249500292323 19874820654243374250438485)
              ·
                refine ⟨116454027270957270998663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19874820654243374250438485 116454027270957270998663)
                ·
                  rfl

theorem cell23_6123422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 9].length) (baseStart_6123422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123422 prefixEnd_6123422 := by exact prefixLift 6123422
  have htrace : WordTrace (prefixWord ++ tailWord_6123422) baseStart_6123422 baseEnd_6123422 := by
    simpa [prefixWord, tailWord_6123422, baseEnd_6123422] using wordTrace_append hprefix tailTrace_6123422
  have hstable : (prefixWord ++ tailWord_6123422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123422).length < 2 ^ (prefixWord ++ tailWord_6123422).sum := by decide
  have hdescent : baseEnd_6123422 < baseStart_6123422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123428 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 2, 2, 5]
def baseStart_6123428 : Nat := 118140960795 + 6123428 * 2 ^ 59
def prefixEnd_6123428 : Nat := 4983230072969 + 3 ^ 40 * 6123428 * 2
def baseEnd_6123428 : Nat := 3144261817199773293488873

theorem tailTrace_6123428 : CollatzResearch.WordTrace tailWord_6123428 prefixEnd_6123428 3144261817199773293488873 := by
  unfold tailWord_6123428
  simp only [CollatzResearch.WordTrace]
  refine ⟨111669883629936814543629469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148893178173249086058172625 111669883629936814543629469)
  ·
    refine ⟨41876206361226305453861051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111669883629936814543629469 41876206361226305453861051)
    ·
      refine ⟨62814309541839458180791577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41876206361226305453861051 62814309541839458180791577)
      ·
        refine ⟨47110732156379593635593683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62814309541839458180791577 47110732156379593635593683)
        ·
          refine ⟨70666098234569390453390525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47110732156379593635593683 70666098234569390453390525)
          ·
            refine ⟨26499786837963521420021447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70666098234569390453390525 26499786837963521420021447)
            ·
              refine ⟨39749680256945282130032171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26499786837963521420021447 39749680256945282130032171)
              ·
                refine ⟨59624520385417923195048257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39749680256945282130032171 59624520385417923195048257)
                ·
                  refine ⟨44718390289063442396286193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59624520385417923195048257 44718390289063442396286193)
                  ·
                    refine ⟨33538792716797581797214645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44718390289063442396286193 33538792716797581797214645)
                    ·
                      refine ⟨3144261817199773293488873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33538792716797581797214645 3144261817199773293488873)
                      ·
                        rfl

theorem cell23_6123428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_6123428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123428 prefixEnd_6123428 := by exact prefixLift 6123428
  have htrace : WordTrace (prefixWord ++ tailWord_6123428) baseStart_6123428 baseEnd_6123428 := by
    simpa [prefixWord, tailWord_6123428, baseEnd_6123428] using wordTrace_append hprefix tailTrace_6123428
  have hstable : (prefixWord ++ tailWord_6123428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123428).length < 2 ^ (prefixWord ++ tailWord_6123428).sum := by decide
  have hdescent : baseEnd_6123428 < baseStart_6123428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123512 : List Nat := [2, 1, 2, 1, 1, 3, 6, 2, 5]
def baseStart_6123512 : Nat := 118140960795 + 6123512 * 2 ^ 59
def prefixEnd_6123512 : Nat := 4983230072969 + 3 ^ 40 * 6123512 * 2
def baseEnd_6123512 : Nat := 349367216619416773870943

theorem tailTrace_6123512 : CollatzResearch.WordTrace tailWord_6123512 prefixEnd_6123512 349367216619416773870943 := by
  unfold tailWord_6123512
  simp only [CollatzResearch.WordTrace]
  refine ⟨111671415495784655716658395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148895220661046207622211193 111671415495784655716658395)
  ·
    refine ⟨167507123243676983574987593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111671415495784655716658395 167507123243676983574987593)
    ·
      refine ⟨125630342432757737681240695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167507123243676983574987593 125630342432757737681240695)
      ·
        refine ⟨188445513649136606521861043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125630342432757737681240695 188445513649136606521861043)
        ·
          refine ⟨282668270473704909782791565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188445513649136606521861043 282668270473704909782791565)
          ·
            refine ⟨106000601427639341168546837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 282668270473704909782791565 106000601427639341168546837)
            ·
              refine ⟨4968778191920594117275633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106000601427639341168546837 4968778191920594117275633)
              ·
                refine ⟨3726583643940445587956725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4968778191920594117275633 3726583643940445587956725)
                ·
                  refine ⟨349367216619416773870943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3726583643940445587956725 349367216619416773870943)
                  ·
                    rfl

theorem cell23_6123512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2, 5].length) (baseStart_6123512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123512 prefixEnd_6123512 := by exact prefixLift 6123512
  have htrace : WordTrace (prefixWord ++ tailWord_6123512) baseStart_6123512 baseEnd_6123512 := by
    simpa [prefixWord, tailWord_6123512, baseEnd_6123512] using wordTrace_append hprefix tailTrace_6123512
  have hstable : (prefixWord ++ tailWord_6123512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123512).length < 2 ^ (prefixWord ++ tailWord_6123512).sum := by decide
  have hdescent : baseEnd_6123512 < baseStart_6123512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123515 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 2, 5, 2]
def baseStart_6123515 : Nat := 118140960795 + 6123515 * 2 ^ 59
def prefixEnd_6123515 : Nat := 4983230072969 + 3 ^ 40 * 6123515 * 2
def baseEnd_6123515 : Nat := 3144306490016714453100973

theorem tailTrace_6123515 : CollatzResearch.WordTrace tailWord_6123515 prefixEnd_6123515 3144306490016714453100973 := by
  unfold tailWord_6123515
  simp only [CollatzResearch.WordTrace]
  refine ⟨223342940410558442945675999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148895293607038961963783999 223342940410558442945675999)
  ·
    refine ⟨335014410615837664418513999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223342940410558442945675999 335014410615837664418513999)
    ·
      refine ⟨502521615923756496627770999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335014410615837664418513999 502521615923756496627770999)
      ·
        refine ⟨753782423885634744941656499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502521615923756496627770999 753782423885634744941656499)
        ·
          refine ⟨1130673635828452117412484749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 753782423885634744941656499 1130673635828452117412484749)
          ·
            refine ⟨424002613435669544029681781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1130673635828452117412484749 424002613435669544029681781)
            ·
              refine ⟨39750245009594019752782667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 424002613435669544029681781 39750245009594019752782667)
              ·
                refine ⟨59625367514391029629174001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39750245009594019752782667 59625367514391029629174001)
                ·
                  refine ⟨44719025635793272221880501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59625367514391029629174001 44719025635793272221880501)
                  ·
                    refine ⟨4192408653355619270801297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44719025635793272221880501 4192408653355619270801297)
                    ·
                      refine ⟨3144306490016714453100973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4192408653355619270801297 3144306490016714453100973)
                      ·
                        rfl

theorem cell23_6123515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 5, 2].length) (baseStart_6123515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123515 prefixEnd_6123515 := by exact prefixLift 6123515
  have htrace : WordTrace (prefixWord ++ tailWord_6123515) baseStart_6123515 baseEnd_6123515 := by
    simpa [prefixWord, tailWord_6123515, baseEnd_6123515] using wordTrace_append hprefix tailTrace_6123515
  have hstable : (prefixWord ++ tailWord_6123515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123515).length < 2 ^ (prefixWord ++ tailWord_6123515).sum := by decide
  have hdescent : baseEnd_6123515 < baseStart_6123515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123545 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 3, 6, 2]
def baseStart_6123545 : Nat := 118140960795 + 6123545 * 2 ^ 59
def prefixEnd_6123545 : Nat := 4983230072969 + 3 ^ 40 * 6123545 * 2
def baseEnd_6123545 : Nat := 3144321894436349335725835

theorem tailTrace_6123545 : CollatzResearch.WordTrace tailWord_6123545 prefixEnd_6123545 3144321894436349335725835 := by
  unfold tailWord_6123545
  simp only [CollatzResearch.WordTrace]
  refine ⟨223344034600449758069268089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148896023066966505379512059 223344034600449758069268089)
  ·
    refine ⟨167508025950337318551951067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223344034600449758069268089 167508025950337318551951067)
    ·
      refine ⟨251262038925505977827926601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167508025950337318551951067 251262038925505977827926601)
      ·
        refine ⟨188446529194129483370944951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251262038925505977827926601 188446529194129483370944951)
        ·
          refine ⟨282669793791194225056417427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188446529194129483370944951 282669793791194225056417427)
          ·
            refine ⟨424004690686791337584626141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282669793791194225056417427 424004690686791337584626141)
            ·
              refine ⟨159001759007546751594234803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 424004690686791337584626141 159001759007546751594234803)
              ·
                refine ⟨238502638511320127391352205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159001759007546751594234803 238502638511320127391352205)
                ·
                  refine ⟨89438489441745047771757077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 238502638511320127391352205 89438489441745047771757077)
                  ·
                    refine ⟨4192429192581799114301113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89438489441745047771757077 4192429192581799114301113)
                    ·
                      refine ⟨3144321894436349335725835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4192429192581799114301113 3144321894436349335725835)
                      ·
                        rfl

theorem cell23_6123545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 6, 2].length) (baseStart_6123545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123545 prefixEnd_6123545 := by exact prefixLift 6123545
  have htrace : WordTrace (prefixWord ++ tailWord_6123545) baseStart_6123545 baseEnd_6123545 := by
    simpa [prefixWord, tailWord_6123545, baseEnd_6123545] using wordTrace_append hprefix tailTrace_6123545
  have hstable : (prefixWord ++ tailWord_6123545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123545).length < 2 ^ (prefixWord ++ tailWord_6123545).sum := by decide
  have hdescent : baseEnd_6123545 < baseStart_6123545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123555 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 5, 4]
def baseStart_6123555 : Nat := 118140960795 + 6123555 * 2 ^ 59
def prefixEnd_6123555 : Nat := 4983230072969 + 3 ^ 40 * 6123555 * 2
def baseEnd_6123555 : Nat := 1048109009747631432200263

theorem tailTrace_6123555 : CollatzResearch.WordTrace tailWord_6123555 prefixEnd_6123555 1048109009747631432200263 := by
  unfold tailWord_6123555
  simp only [CollatzResearch.WordTrace]
  refine ⟨223344399330413529777132119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148896266220275686518088079 223344399330413529777132119)
  ·
    refine ⟨335016598995620294665698179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223344399330413529777132119 335016598995620294665698179)
    ·
      refine ⟨502524898493430441998547269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335016598995620294665698179 502524898493430441998547269)
      ·
        refine ⟨94223418467518207874727613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 502524898493430441998547269 94223418467518207874727613)
        ·
          refine ⟨35333781925319327953022855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94223418467518207874727613 35333781925319327953022855)
          ·
            refine ⟨53000672887978991929534283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35333781925319327953022855 53000672887978991929534283)
            ·
              refine ⟨79501009331968487894301425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53000672887978991929534283 79501009331968487894301425)
              ·
                refine ⟨59625756998976365920726069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79501009331968487894301425 59625756998976365920726069)
                ·
                  refine ⟨5589914718654034305068069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59625756998976365920726069 5589914718654034305068069)
                  ·
                    refine ⟨1048109009747631432200263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5589914718654034305068069 1048109009747631432200263)
                    ·
                      rfl

theorem cell23_6123555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5, 4].length) (baseStart_6123555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123555 prefixEnd_6123555 := by exact prefixLift 6123555
  have htrace : WordTrace (prefixWord ++ tailWord_6123555) baseStart_6123555 baseEnd_6123555 := by
    simpa [prefixWord, tailWord_6123555, baseEnd_6123555] using wordTrace_append hprefix tailTrace_6123555
  have hstable : (prefixWord ++ tailWord_6123555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123555).length < 2 ^ (prefixWord ++ tailWord_6123555).sum := by decide
  have hdescent : baseEnd_6123555 < baseStart_6123555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123652 : List Nat := [2, 3, 2, 1, 2, 1, 3, 1, 3, 1, 4]
def baseStart_6123652 : Nat := 118140960795 + 6123652 * 2 ^ 59
def prefixEnd_6123652 : Nat := 4983230072969 + 3 ^ 40 * 6123652 * 2
def baseEnd_6123652 : Nat := 3144376836866380417087843

theorem tailTrace_6123652 : CollatzResearch.WordTrace tailWord_6123652 prefixEnd_6123652 3144376836866380417087843 := by
  unfold tailWord_6123652
  simp only [CollatzResearch.WordTrace]
  refine ⟨111673968605531057671706605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148898624807374743562275473 111673968605531057671706605)
  ·
    refine ⟨41877738227074146626889977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111673968605531057671706605 41877738227074146626889977)
    ·
      refine ⟨31408303670305609970167483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41877738227074146626889977 31408303670305609970167483)
      ·
        refine ⟨47112455505458414955251225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31408303670305609970167483 47112455505458414955251225)
        ·
          refine ⟨35334341629093811216438419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47112455505458414955251225 35334341629093811216438419)
          ·
            refine ⟨53001512443640716824657629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35334341629093811216438419 53001512443640716824657629)
            ·
              refine ⟨19875567166365268809246611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53001512443640716824657629 19875567166365268809246611)
              ·
                refine ⟨29813350749547903213869917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19875567166365268809246611 29813350749547903213869917)
                ·
                  refine ⟨11180006531080463705201219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29813350749547903213869917 11180006531080463705201219)
                  ·
                    refine ⟨16770009796620695557801829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11180006531080463705201219 16770009796620695557801829)
                    ·
                      refine ⟨3144376836866380417087843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16770009796620695557801829 3144376836866380417087843)
                      ·
                        rfl

theorem cell23_6123652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_6123652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123652 prefixEnd_6123652 := by exact prefixLift 6123652
  have htrace : WordTrace (prefixWord ++ tailWord_6123652) baseStart_6123652 baseEnd_6123652 := by
    simpa [prefixWord, tailWord_6123652, baseEnd_6123652] using wordTrace_append hprefix tailTrace_6123652
  have hstable : (prefixWord ++ tailWord_6123652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123652).length < 2 ^ (prefixWord ++ tailWord_6123652).sum := by decide
  have hdescent : baseEnd_6123652 < baseStart_6123652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123655 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 5]
def baseStart_6123655 : Nat := 118140960795 + 6123655 * 2 ^ 59
def prefixEnd_6123655 : Nat := 4983230072969 + 3 ^ 40 * 6123655 * 2
def baseEnd_6123655 : Nat := 3144378377308343905350329

theorem tailTrace_6123655 : CollatzResearch.WordTrace tailWord_6123655 prefixEnd_6123655 3144378377308343905350329 := by
  unfold tailWord_6123655
  simp only [CollatzResearch.WordTrace]
  refine ⟨223348046630051246855772419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148898697753367497903848279 223348046630051246855772419)
  ·
    refine ⟨335022069945076870283658629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223348046630051246855772419 335022069945076870283658629)
    ·
      refine ⟨62816638114701913178185993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 335022069945076870283658629 62816638114701913178185993)
      ·
        refine ⟨47112478586026434883639495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62816638114701913178185993 47112478586026434883639495)
        ·
          refine ⟨70668717879039652325459243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47112478586026434883639495 70668717879039652325459243)
          ·
            refine ⟨106003076818559478488188865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70668717879039652325459243 106003076818559478488188865)
            ·
              refine ⟨79502307613919608866141649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106003076818559478488188865 79502307613919608866141649)
              ·
                refine ⟨59626730710439706649606237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79502307613919608866141649 59626730710439706649606237)
                ·
                  refine ⟨22360024016414889993602339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59626730710439706649606237 22360024016414889993602339)
                  ·
                    refine ⟨33540036024622334990403509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22360024016414889993602339 33540036024622334990403509)
                    ·
                      refine ⟨3144378377308343905350329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33540036024622334990403509 3144378377308343905350329)
                      ·
                        rfl

theorem cell23_6123655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_6123655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123655 prefixEnd_6123655 := by exact prefixLift 6123655
  have htrace : WordTrace (prefixWord ++ tailWord_6123655) baseStart_6123655 baseEnd_6123655 := by
    simpa [prefixWord, tailWord_6123655, baseEnd_6123655] using wordTrace_append hprefix tailTrace_6123655
  have hstable : (prefixWord ++ tailWord_6123655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123655).length < 2 ^ (prefixWord ++ tailWord_6123655).sum := by decide
  have hdescent : baseEnd_6123655 < baseStart_6123655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123656 : List Nat := [2, 1, 3, 4, 1, 2, 2, 1, 2, 3, 2]
def baseStart_6123656 : Nat := 118140960795 + 6123656 * 2 ^ 59
def prefixEnd_6123656 : Nat := 4983230072969 + 3 ^ 40 * 6123656 * 2
def baseEnd_6123656 : Nat := 3144378890788998401437825

theorem tailTrace_6123656 : CollatzResearch.WordTrace tailWord_6123656 prefixEnd_6123656 3144378890788998401437825 := by
  unfold tailWord_6123656
  simp only [CollatzResearch.WordTrace]
  refine ⟨111674041551523812013279411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148898722068698416017705881 111674041551523812013279411)
  ·
    refine ⟨167511062327285718019919117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111674041551523812013279411 167511062327285718019919117)
    ·
      refine ⟨62816648372732144257469669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167511062327285718019919117 62816648372732144257469669)
      ·
        refine ⟨11778121569887277048275563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62816648372732144257469669 11778121569887277048275563)
        ·
          refine ⟨17667182354830915572413345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11778121569887277048275563 17667182354830915572413345)
          ·
            refine ⟨13250386766123186679310009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17667182354830915572413345 13250386766123186679310009)
            ·
              refine ⟨9937790074592390009482507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13250386766123186679310009 9937790074592390009482507)
              ·
                refine ⟨14906685111888585014223761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9937790074592390009482507 14906685111888585014223761)
                ·
                  refine ⟨11180013833916438760667821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14906685111888585014223761 11180013833916438760667821)
                  ·
                    refine ⟨4192505187718664535250433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11180013833916438760667821 4192505187718664535250433)
                    ·
                      refine ⟨3144378890788998401437825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4192505187718664535250433 3144378890788998401437825)
                      ·
                        rfl

theorem cell23_6123656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_6123656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123656 prefixEnd_6123656 := by exact prefixLift 6123656
  have htrace : WordTrace (prefixWord ++ tailWord_6123656) baseStart_6123656 baseEnd_6123656 := by
    simpa [prefixWord, tailWord_6123656, baseEnd_6123656] using wordTrace_append hprefix tailTrace_6123656
  have hstable : (prefixWord ++ tailWord_6123656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123656).length < 2 ^ (prefixWord ++ tailWord_6123656).sum := by decide
  have hdescent : baseEnd_6123656 < baseStart_6123656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123669 : List Nat := [1, 3, 2, 1, 1, 1, 7, 1, 1, 1, 4]
def baseStart_6123669 : Nat := 118140960795 + 6123669 * 2 ^ 59
def prefixEnd_6123669 : Nat := 4983230072969 + 3 ^ 40 * 6123669 * 2
def baseEnd_6123669 : Nat := 3144385566037506850575265

theorem tailTrace_6123669 : CollatzResearch.WordTrace tailWord_6123669 prefixEnd_6123669 3144385566037506850575265 := by
  unfold tailWord_6123669
  simp only [CollatzResearch.WordTrace]
  refine ⟨223348557252000527246782061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148899038168000351497854707 223348557252000527246782061)
  ·
    refine ⟨83755708969500197717543273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223348557252000527246782061 83755708969500197717543273)
    ·
      refine ⟨62816781727125148288157455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83755708969500197717543273 62816781727125148288157455)
      ·
        refine ⟨94225172590687722432236183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62816781727125148288157455 94225172590687722432236183)
        ·
          refine ⟨141337758886031583648354275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94225172590687722432236183 141337758886031583648354275)
          ·
            refine ⟨212006638329047375472531413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141337758886031583648354275 212006638329047375472531413)
            ·
              refine ⟨4968905585837047862637455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 212006638329047375472531413 4968905585837047862637455)
              ·
                refine ⟨7453358378755571793956183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4968905585837047862637455 7453358378755571793956183)
                ·
                  refine ⟨11180037568133357690934275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7453358378755571793956183 11180037568133357690934275)
                  ·
                    refine ⟨16770056352200036536401413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11180037568133357690934275 16770056352200036536401413)
                    ·
                      refine ⟨3144385566037506850575265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16770056352200036536401413 3144385566037506850575265)
                      ·
                        rfl

theorem cell23_6123669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 1, 1, 4].length) (baseStart_6123669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123669 prefixEnd_6123669 := by exact prefixLift 6123669
  have htrace : WordTrace (prefixWord ++ tailWord_6123669) baseStart_6123669 baseEnd_6123669 := by
    simpa [prefixWord, tailWord_6123669, baseEnd_6123669] using wordTrace_append hprefix tailTrace_6123669
  have hstable : (prefixWord ++ tailWord_6123669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123669).length < 2 ^ (prefixWord ++ tailWord_6123669).sum := by decide
  have hdescent : baseEnd_6123669 < baseStart_6123669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123670 : List Nat := [5, 3, 2, 1, 1, 1, 2, 2, 6]
def baseStart_6123670 : Nat := 118140960795 + 6123670 * 2 ^ 59
def prefixEnd_6123670 : Nat := 4983230072969 + 3 ^ 40 * 6123670 * 2
def baseEnd_6123670 : Nat := 349376231057573482962529

theorem tailTrace_6123670 : CollatzResearch.WordTrace tailWord_6123670 prefixEnd_6123670 349376231057573482962529 := by
  unfold tailWord_6123670
  simp only [CollatzResearch.WordTrace]
  refine ⟨13959287107812306526098029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148899062483331269611712309 13959287107812306526098029)
  ·
    refine ⟨5234732665429614947286761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13959287107812306526098029 5234732665429614947286761)
    ·
      refine ⟨3926049499072211210465071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5234732665429614947286761 3926049499072211210465071)
      ·
        refine ⟨5889074248608316815697607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3926049499072211210465071 5889074248608316815697607)
        ·
          refine ⟨8833611372912475223546411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5889074248608316815697607 8833611372912475223546411)
          ·
            refine ⟨13250417059368712835319617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8833611372912475223546411 13250417059368712835319617)
            ·
              refine ⟨9937812794526534626489713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13250417059368712835319617 9937812794526534626489713)
              ·
                refine ⟨7453359595894900969867285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9937812794526534626489713 7453359595894900969867285)
                ·
                  refine ⟨349376231057573482962529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7453359595894900969867285 349376231057573482962529)
                  ·
                    rfl

theorem cell23_6123670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_6123670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123670 prefixEnd_6123670 := by exact prefixLift 6123670
  have htrace : WordTrace (prefixWord ++ tailWord_6123670) baseStart_6123670 baseEnd_6123670 := by
    simpa [prefixWord, tailWord_6123670, baseEnd_6123670] using wordTrace_append hprefix tailTrace_6123670
  have hstable : (prefixWord ++ tailWord_6123670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123670).length < 2 ^ (prefixWord ++ tailWord_6123670).sum := by decide
  have hdescent : baseEnd_6123670 < baseStart_6123670 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123679 : List Nat := [1, 1, 2, 6, 1, 1, 1, 4, 2, 4]
def baseStart_6123679 : Nat := 118140960795 + 6123679 * 2 ^ 59
def prefixEnd_6123679 : Nat := 4983230072969 + 3 ^ 40 * 6123679 * 2
def baseEnd_6123679 : Nat := 1048130233614683937150073

theorem tailTrace_6123679 : CollatzResearch.WordTrace tailWord_6123679 prefixEnd_6123679 1048130233614683937150073 := by
  unfold tailWord_6123679
  simp only [CollatzResearch.WordTrace]
  refine ⟨223348921981964298954646091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148899281321309532636430727 223348921981964298954646091)
  ·
    refine ⟨335023382972946448431969137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223348921981964298954646091 335023382972946448431969137)
    ·
      refine ⟨251267537229709836323976853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335023382972946448431969137 251267537229709836323976853)
      ·
        refine ⟨11778165807642648577686415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 251267537229709836323976853 11778165807642648577686415)
        ·
          refine ⟨17667248711463972866529623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11778165807642648577686415 17667248711463972866529623)
          ·
            refine ⟨26500873067195959299794435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17667248711463972866529623 26500873067195959299794435)
            ·
              refine ⟨39751309600793938949691653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26500873067195959299794435 39751309600793938949691653)
              ·
                refine ⟨7453370550148863553067185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39751309600793938949691653 7453370550148863553067185)
                ·
                  refine ⟨5590027912611647664800389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7453370550148863553067185 5590027912611647664800389)
                  ·
                    refine ⟨1048130233614683937150073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5590027912611647664800389 1048130233614683937150073)
                    ·
                      rfl

theorem cell23_6123679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2, 4].length) (baseStart_6123679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123679 prefixEnd_6123679 := by exact prefixLift 6123679
  have htrace : WordTrace (prefixWord ++ tailWord_6123679) baseStart_6123679 baseEnd_6123679 := by
    simpa [prefixWord, tailWord_6123679, baseEnd_6123679] using wordTrace_append hprefix tailTrace_6123679
  have hstable : (prefixWord ++ tailWord_6123679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123679).length < 2 ^ (prefixWord ++ tailWord_6123679).sum := by decide
  have hdescent : baseEnd_6123679 < baseStart_6123679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123705 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 2, 7]
def baseStart_6123705 : Nat := 118140960795 + 6123705 * 2 ^ 59
def prefixEnd_6123705 : Nat := 4983230072969 + 3 ^ 40 * 6123705 * 2
def baseEnd_6123705 : Nat := 1048134683780356236575033

theorem tailTrace_6123705 : CollatzResearch.WordTrace tailWord_6123705 prefixEnd_6123705 1048134683780356236575033 := by
  unfold tailWord_6123705
  simp only [CollatzResearch.WordTrace]
  refine ⟨223349870279870105395092569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148899913519913403596728379 223349870279870105395092569)
  ·
    refine ⟨167512402709902579046319427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223349870279870105395092569 167512402709902579046319427)
    ·
      refine ⟨251268604064853868569479141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167512402709902579046319427 251268604064853868569479141)
      ·
        refine ⟨47112863262160100356777339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 251268604064853868569479141 47112863262160100356777339)
        ·
          refine ⟨70669294893240150535166009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47112863262160100356777339 70669294893240150535166009)
          ·
            refine ⟨53001971169930112901374507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70669294893240150535166009 53001971169930112901374507)
            ·
              refine ⟨79502956754895169352061761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53001971169930112901374507 79502956754895169352061761)
              ·
                refine ⟨59627217566171377014046321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79502956754895169352061761 59627217566171377014046321)
                ·
                  refine ⟨44720413174628532760534741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59627217566171377014046321 44720413174628532760534741)
                  ·
                    refine ⟨1048134683780356236575033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44720413174628532760534741 1048134683780356236575033)
                    ·
                      rfl

theorem cell23_6123705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 7].length) (baseStart_6123705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123705 prefixEnd_6123705 := by exact prefixLift 6123705
  have htrace : WordTrace (prefixWord ++ tailWord_6123705) baseStart_6123705 baseEnd_6123705 := by
    simpa [prefixWord, tailWord_6123705, baseEnd_6123705] using wordTrace_append hprefix tailTrace_6123705
  have hstable : (prefixWord ++ tailWord_6123705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123705).length < 2 ^ (prefixWord ++ tailWord_6123705).sum := by decide
  have hdescent : baseEnd_6123705 < baseStart_6123705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123736 : List Nat := [2, 1, 2, 2, 4, 1, 3, 2, 2, 1, 3]
def baseStart_6123736 : Nat := 118140960795 + 6123736 * 2 ^ 59
def prefixEnd_6123736 : Nat := 4983230072969 + 3 ^ 40 * 6123736 * 2
def baseEnd_6123736 : Nat := 3144419969241358088437457

theorem tailTrace_6123736 : CollatzResearch.WordTrace tailWord_6123736 prefixEnd_6123736 3144419969241358088437457 := by
  unfold tailWord_6123736
  simp only [CollatzResearch.WordTrace]
  refine ⟨111675500471378898844735531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148900667295171865126314041 111675500471378898844735531)
  ·
    refine ⟨167513250707068348267103297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111675500471378898844735531 167513250707068348267103297)
    ·
      refine ⟨125634938030301261200327473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167513250707068348267103297 125634938030301261200327473)
      ·
        refine ⟨94226203522725945900245605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125634938030301261200327473 94226203522725945900245605)
        ·
          refine ⟨17667413160511114856296051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94226203522725945900245605 17667413160511114856296051)
          ·
            refine ⟨26501119740766672284444077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17667413160511114856296051 26501119740766672284444077)
            ·
              refine ⟨9937919902787502106666529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26501119740766672284444077 9937919902787502106666529)
              ·
                refine ⟨7453439927090626579999897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9937919902787502106666529 7453439927090626579999897)
                ·
                  refine ⟨5590079945317969934999923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7453439927090626579999897 5590079945317969934999923)
                  ·
                    refine ⟨8385119917976954902499885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5590079945317969934999923 8385119917976954902499885)
                    ·
                      refine ⟨3144419969241358088437457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8385119917976954902499885 3144419969241358088437457)
                      ·
                        rfl

theorem cell23_6123736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_6123736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123736 prefixEnd_6123736 := by exact prefixLift 6123736
  have htrace : WordTrace (prefixWord ++ tailWord_6123736) baseStart_6123736 baseEnd_6123736 := by
    simpa [prefixWord, tailWord_6123736, baseEnd_6123736] using wordTrace_append hprefix tailTrace_6123736
  have hstable : (prefixWord ++ tailWord_6123736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123736).length < 2 ^ (prefixWord ++ tailWord_6123736).sum := by decide
  have hdescent : baseEnd_6123736 < baseStart_6123736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123752 : List Nat := [2, 1, 4, 1, 2, 2, 2, 1, 2, 6]
def baseStart_6123752 : Nat := 118140960795 + 6123752 * 2 ^ 59
def prefixEnd_6123752 : Nat := 4983230072969 + 3 ^ 40 * 6123752 * 2
def baseEnd_6123752 : Nat := 1048142728310610008612461

theorem tailTrace_6123752 : CollatzResearch.WordTrace tailWord_6123752 prefixEnd_6123752 1048142728310610008612461 := by
  unfold tailWord_6123752
  simp only [CollatzResearch.WordTrace]
  refine ⟨111675792255349916211026755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148901056340466554948035673 111675792255349916211026755)
  ·
    refine ⟨167513688383024874316540133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111675792255349916211026755 167513688383024874316540133)
    ·
      refine ⟨31408816571817163934351275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167513688383024874316540133 31408816571817163934351275)
      ·
        refine ⟨47113224857725745901526913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31408816571817163934351275 47113224857725745901526913)
        ·
          refine ⟨35334918643294309426145185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47113224857725745901526913 35334918643294309426145185)
          ·
            refine ⟨26501188982470732069608889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35334918643294309426145185 26501188982470732069608889)
            ·
              refine ⟨19875891736853049052206667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26501188982470732069608889 19875891736853049052206667)
              ·
                refine ⟨29813837605279573578310001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19875891736853049052206667 29813837605279573578310001)
                ·
                  refine ⟨22360378203959680183732501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29813837605279573578310001 22360378203959680183732501)
                  ·
                    refine ⟨1048142728310610008612461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22360378203959680183732501 1048142728310610008612461)
                    ·
                      rfl

theorem cell23_6123752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_6123752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123752 prefixEnd_6123752 := by exact prefixLift 6123752
  have htrace : WordTrace (prefixWord ++ tailWord_6123752) baseStart_6123752 baseEnd_6123752 := by
    simpa [prefixWord, tailWord_6123752, baseEnd_6123752] using wordTrace_append hprefix tailTrace_6123752
  have hstable : (prefixWord ++ tailWord_6123752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123752).length < 2 ^ (prefixWord ++ tailWord_6123752).sum := by decide
  have hdescent : baseEnd_6123752 < baseStart_6123752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123799 : List Nat := [1, 1, 3, 4, 1, 4, 1, 1, 7]
def baseStart_6123799 : Nat := 118140960795 + 6123799 * 2 ^ 59
def prefixEnd_6123799 : Nat := 4983230072969 + 3 ^ 40 * 6123799 * 2
def baseEnd_6123799 : Nat := 349383590946954593549963

theorem tailTrace_6123799 : CollatzResearch.WordTrace tailWord_6123799 prefixEnd_6123799 349383590946954593549963 := by
  unfold tailWord_6123799
  simp only [CollatzResearch.WordTrace]
  refine ⟨223353298741529559449014451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148902199161019706299342967 223353298741529559449014451)
  ·
    refine ⟨335029948112294339173521677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223353298741529559449014451 335029948112294339173521677)
    ·
      refine ⟨125636230542110377190070629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335029948112294339173521677 125636230542110377190070629)
      ·
        refine ⟨23556793226645695723138243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125636230542110377190070629 23556793226645695723138243)
        ·
          refine ⟨35335189839968543584707365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23556793226645695723138243 35335189839968543584707365)
          ·
            refine ⟨6625348094994101922132631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35335189839968543584707365 6625348094994101922132631)
            ·
              refine ⟨9938022142491152883198947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6625348094994101922132631 9938022142491152883198947)
              ·
                refine ⟨14907033213736729324798421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9938022142491152883198947 14907033213736729324798421)
                ·
                  refine ⟨349383590946954593549963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14907033213736729324798421 349383590946954593549963)
                  ·
                    rfl

theorem cell23_6123799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 7].length) (baseStart_6123799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123799 prefixEnd_6123799 := by exact prefixLift 6123799
  have htrace : WordTrace (prefixWord ++ tailWord_6123799) baseStart_6123799 baseEnd_6123799 := by
    simpa [prefixWord, tailWord_6123799, baseEnd_6123799] using wordTrace_append hprefix tailTrace_6123799
  have hstable : (prefixWord ++ tailWord_6123799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123799).length < 2 ^ (prefixWord ++ tailWord_6123799).sum := by decide
  have hdescent : baseEnd_6123799 < baseStart_6123799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123810 : List Nat := [3, 3, 1, 1, 3, 1, 4, 1, 2, 2, 2]
def baseStart_6123810 : Nat := 118140960795 + 6123810 * 2 ^ 59
def prefixEnd_6123810 : Nat := 4983230072969 + 3 ^ 40 * 6123810 * 2
def baseEnd_6123810 : Nat := 3144457966809790798912117

theorem tailTrace_6123810 : CollatzResearch.WordTrace tailWord_6123810 prefixEnd_6123810 3144457966809790798912117 := by
  unfold tailWord_6123810
  simp only [CollatzResearch.WordTrace]
  refine ⟨55838424986122427081916221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148902466629659805551776589 55838424986122427081916221)
  ·
    refine ⟨20939409369795910155718583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55838424986122427081916221 20939409369795910155718583)
    ·
      refine ⟨31409114054693865233577875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20939409369795910155718583 31409114054693865233577875)
      ·
        refine ⟨47113671082040797850366813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31409114054693865233577875 47113671082040797850366813)
        ·
          refine ⟨17667626655765299193887555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47113671082040797850366813 17667626655765299193887555)
          ·
            refine ⟨26501439983647948790831333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17667626655765299193887555 26501439983647948790831333)
            ·
              refine ⟨4969019996933990398280875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26501439983647948790831333 4969019996933990398280875)
              ·
                refine ⟨7453529995400985597421313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4969019996933990398280875 7453529995400985597421313)
                ·
                  refine ⟨5590147496550739198065985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7453529995400985597421313 5590147496550739198065985)
                  ·
                    refine ⟨4192610622413054398549489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5590147496550739198065985 4192610622413054398549489)
                    ·
                      refine ⟨3144457966809790798912117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4192610622413054398549489 3144457966809790798912117)
                      ·
                        rfl

theorem cell23_6123810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_6123810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123810 prefixEnd_6123810 := by exact prefixLift 6123810
  have htrace : WordTrace (prefixWord ++ tailWord_6123810) baseStart_6123810 baseEnd_6123810 := by
    simpa [prefixWord, tailWord_6123810, baseEnd_6123810] using wordTrace_append hprefix tailTrace_6123810
  have hstable : (prefixWord ++ tailWord_6123810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123810).length < 2 ^ (prefixWord ++ tailWord_6123810).sum := by decide
  have hdescent : baseEnd_6123810 < baseStart_6123810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123829 : List Nat := [1, 3, 3, 1, 2, 1, 4, 1, 2, 5]
def baseStart_6123829 : Nat := 118140960795 + 6123829 * 2 ^ 59
def prefixEnd_6123829 : Nat := 4983230072969 + 3 ^ 40 * 6123829 * 2
def baseEnd_6123829 : Nat := 1048155907647408741524843

theorem tailTrace_6123829 : CollatzResearch.WordTrace tailWord_6123829 prefixEnd_6123829 1048155907647408741524843 := by
  unfold tailWord_6123829
  simp only [CollatzResearch.WordTrace]
  refine ⟨223354392931420874572606541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148902928620947249715071027 223354392931420874572606541)
  ·
    refine ⟨83757897349282827964727453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223354392931420874572606541 83757897349282827964727453)
    ·
      refine ⟨31409211505981060486772795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83757897349282827964727453 31409211505981060486772795)
      ·
        refine ⟨47113817258971590730159193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31409211505981060486772795 47113817258971590730159193)
        ·
          refine ⟨35335362944228693047619395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47113817258971590730159193 35335362944228693047619395)
          ·
            refine ⟨53003044416343039571429093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35335362944228693047619395 53003044416343039571429093)
            ·
              refine ⟨9938070828064319919642955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53003044416343039571429093 9938070828064319919642955)
              ·
                refine ⟨14907106242096479879464433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9938070828064319919642955 14907106242096479879464433)
                ·
                  refine ⟨11180329681572359909598325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14907106242096479879464433 11180329681572359909598325)
                  ·
                    refine ⟨1048155907647408741524843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11180329681572359909598325 1048155907647408741524843)
                    ·
                      rfl

theorem cell23_6123829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_6123829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123829 prefixEnd_6123829 := by exact prefixLift 6123829
  have htrace : WordTrace (prefixWord ++ tailWord_6123829) baseStart_6123829 baseEnd_6123829 := by
    simpa [prefixWord, tailWord_6123829, baseEnd_6123829] using wordTrace_append hprefix tailTrace_6123829
  have hstable : (prefixWord ++ tailWord_6123829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123829).length < 2 ^ (prefixWord ++ tailWord_6123829).sum := by decide
  have hdescent : baseEnd_6123829 < baseStart_6123829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123832 : List Nat := [2, 1, 2, 1, 3, 1, 2, 3, 1, 3, 4]
def baseStart_6123832 : Nat := 118140960795 + 6123832 * 2 ^ 59
def prefixEnd_6123832 : Nat := 4983230072969 + 3 ^ 40 * 6123832 * 2
def baseEnd_6123832 : Nat := 3144469263384189712837015

theorem tailTrace_6123832 : CollatzResearch.WordTrace tailWord_6123832 prefixEnd_6123832 3144469263384189712837015 := by
  unfold tailWord_6123832
  simp only [CollatzResearch.WordTrace]
  refine ⟨111677251175205003042482875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148903001566940004056643833 111677251175205003042482875)
  ·
    refine ⟨167515876762807504563724313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111677251175205003042482875 167515876762807504563724313)
    ·
      refine ⟨125636907572105628422793235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167515876762807504563724313 125636907572105628422793235)
      ·
        refine ⟨188455361358158442634189853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125636907572105628422793235 188455361358158442634189853)
        ·
          refine ⟨70670760509309415987821195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188455361358158442634189853 70670760509309415987821195)
          ·
            refine ⟨106006140763964123981731793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70670760509309415987821195 106006140763964123981731793)
            ·
              refine ⟨79504605572973092986298845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106006140763964123981731793 79504605572973092986298845)
              ·
                refine ⟨29814227089864909869862067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79504605572973092986298845 29814227089864909869862067)
                ·
                  refine ⟨44721340634797364804793101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29814227089864909869862067 44721340634797364804793101)
                  ·
                    refine ⟨16770502738049011801797413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44721340634797364804793101 16770502738049011801797413)
                    ·
                      refine ⟨3144469263384189712837015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16770502738049011801797413 3144469263384189712837015)
                      ·
                        rfl

theorem cell23_6123832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_6123832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123832 prefixEnd_6123832 := by exact prefixLift 6123832
  have htrace : WordTrace (prefixWord ++ tailWord_6123832) baseStart_6123832 baseEnd_6123832 := by
    simpa [prefixWord, tailWord_6123832, baseEnd_6123832] using wordTrace_append hprefix tailTrace_6123832
  have hstable : (prefixWord ++ tailWord_6123832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123832).length < 2 ^ (prefixWord ++ tailWord_6123832).sum := by decide
  have hdescent : baseEnd_6123832 < baseStart_6123832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123849 : List Nat := [1, 2, 1, 1, 2, 3, 1, 4, 2, 4, 2]
def baseStart_6123849 : Nat := 118140960795 + 6123849 * 2 ^ 59
def prefixEnd_6123849 : Nat := 4983230072969 + 3 ^ 40 * 6123849 * 2
def baseEnd_6123849 : Nat := 3144477992555316146324437

theorem tailTrace_6123849 : CollatzResearch.WordTrace tailWord_6123849 prefixEnd_6123849 3144477992555316146324437 := by
  unfold tailWord_6123849
  simp only [CollatzResearch.WordTrace]
  refine ⟨223355122391348417988334601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148903414927565611992223067 223355122391348417988334601)
  ·
    refine ⟨167516341793511313491250951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223355122391348417988334601 167516341793511313491250951)
    ·
      refine ⟨251274512690266970236876427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167516341793511313491250951 251274512690266970236876427)
      ·
        refine ⟨376911769035400455355314641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251274512690266970236876427 376911769035400455355314641)
        ·
          refine ⟨282683826776550341516485981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376911769035400455355314641 282683826776550341516485981)
          ·
            refine ⟨106006435041206378068682243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 282683826776550341516485981 106006435041206378068682243)
            ·
              refine ⟨159009652561809567103023365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106006435041206378068682243 159009652561809567103023365)
              ·
                refine ⟨29814309855339293831816881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159009652561809567103023365 29814309855339293831816881)
                ·
                  refine ⟨22360732391504470373862661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29814309855339293831816881 22360732391504470373862661)
                  ·
                    refine ⟨4192637323407088195099249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22360732391504470373862661 4192637323407088195099249)
                    ·
                      refine ⟨3144477992555316146324437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4192637323407088195099249 3144477992555316146324437)
                      ·
                        rfl

theorem cell23_6123849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 4, 2].length) (baseStart_6123849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123849 prefixEnd_6123849 := by exact prefixLift 6123849
  have htrace : WordTrace (prefixWord ++ tailWord_6123849) baseStart_6123849 baseEnd_6123849 := by
    simpa [prefixWord, tailWord_6123849, baseEnd_6123849] using wordTrace_append hprefix tailTrace_6123849
  have hstable : (prefixWord ++ tailWord_6123849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123849).length < 2 ^ (prefixWord ++ tailWord_6123849).sum := by decide
  have hdescent : baseEnd_6123849 < baseStart_6123849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123852 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 2, 3, 5]
def baseStart_6123852 : Nat := 118140960795 + 6123852 * 2 ^ 59
def prefixEnd_6123852 : Nat := 4983230072969 + 3 ^ 40 * 6123852 * 2
def baseEnd_6123852 : Nat := 3144479532997279634586923

theorem tailTrace_6123852 : CollatzResearch.WordTrace tailWord_6123852 prefixEnd_6123852 3144479532997279634586923 := by
  unfold tailWord_6123852
  simp only [CollatzResearch.WordTrace]
  refine ⟨111677615905168774750346905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148903487873558366333795873 111677615905168774750346905)
  ·
    refine ⟨83758211928876581062760179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111677615905168774750346905 83758211928876581062760179)
    ·
      refine ⟨125637317893314871594140269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83758211928876581062760179 125637317893314871594140269)
      ·
        refine ⟨47113994209993076847802601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125637317893314871594140269 47113994209993076847802601)
        ·
          refine ⟨35335495657494807635851951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47113994209993076847802601 35335495657494807635851951)
          ·
            refine ⟨53003243486242211453777927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35335495657494807635851951 53003243486242211453777927)
            ·
              refine ⟨79504865229363317180666891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53003243486242211453777927 79504865229363317180666891)
              ·
                refine ⟨119257297844044975771000337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79504865229363317180666891 119257297844044975771000337)
                ·
                  refine ⟨89442973383033731828250253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119257297844044975771000337 89442973383033731828250253)
                  ·
                    refine ⟨33541115018637649435593845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89442973383033731828250253 33541115018637649435593845)
                    ·
                      refine ⟨3144479532997279634586923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33541115018637649435593845 3144479532997279634586923)
                      ·
                        rfl

theorem cell23_6123852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_6123852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123852 prefixEnd_6123852 := by exact prefixLift 6123852
  have htrace : WordTrace (prefixWord ++ tailWord_6123852) baseStart_6123852 baseEnd_6123852 := by
    simpa [prefixWord, tailWord_6123852, baseEnd_6123852] using wordTrace_append hprefix tailTrace_6123852
  have hstable : (prefixWord ++ tailWord_6123852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123852).length < 2 ^ (prefixWord ++ tailWord_6123852).sum := by decide
  have hdescent : baseEnd_6123852 < baseStart_6123852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123893 : List Nat := [1, 3, 4, 1, 2, 1, 1, 5, 1, 4]
def baseStart_6123893 : Nat := 118140960795 + 6123893 * 2 ^ 59
def prefixEnd_6123893 : Nat := 4983230072969 + 3 ^ 40 * 6123893 * 2
def baseEnd_6123893 : Nat := 1048166861901371324724745

theorem tailTrace_6123893 : CollatzResearch.WordTrace tailWord_6123893 prefixEnd_6123893 1048166861901371324724745 := by
  unfold tailWord_6123893
  simp only [CollatzResearch.WordTrace]
  refine ⟨223356727203189013502936333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148904484802126009001957555 223356727203189013502936333)
  ·
    refine ⟨83758772701195880063601125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223356727203189013502936333 83758772701195880063601125)
    ·
      refine ⟨15704769881474227511925211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83758772701195880063601125 15704769881474227511925211)
      ·
        refine ⟨23557154822211341267887817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15704769881474227511925211 23557154822211341267887817)
        ·
          refine ⟨17667866116658505950915863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23557154822211341267887817 17667866116658505950915863)
          ·
            refine ⟨26501799174987758926373795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17667866116658505950915863 26501799174987758926373795)
            ·
              refine ⟨39752698762481638389560693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26501799174987758926373795 39752698762481638389560693)
              ·
                refine ⟨3726815508982653599021315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39752698762481638389560693 3726815508982653599021315)
                ·
                  refine ⟨5590223263473980398531973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3726815508982653599021315 5590223263473980398531973)
                  ·
                    refine ⟨1048166861901371324724745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5590223263473980398531973 1048166861901371324724745)
                    ·
                      rfl

theorem cell23_6123893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_6123893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123893 prefixEnd_6123893 := by exact prefixLift 6123893
  have htrace : WordTrace (prefixWord ++ tailWord_6123893) baseStart_6123893 baseEnd_6123893 := by
    simpa [prefixWord, tailWord_6123893, baseEnd_6123893] using wordTrace_append hprefix tailTrace_6123893
  have hstable : (prefixWord ++ tailWord_6123893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123893).length < 2 ^ (prefixWord ++ tailWord_6123893).sum := by decide
  have hdescent : baseEnd_6123893 < baseStart_6123893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123916 : List Nat := [2, 2, 1, 2, 1, 4, 1, 3, 3, 1, 3]
def baseStart_6123916 : Nat := 118140960795 + 6123916 * 2 ^ 59
def prefixEnd_6123916 : Nat := 4983230072969 + 3 ^ 40 * 6123916 * 2
def baseEnd_6123916 : Nat := 3144512395759167384186629

theorem tailTrace_6123916 : CollatzResearch.WordTrace tailWord_6123916 prefixEnd_6123916 3144512395759167384186629 := by
  unfold tailWord_6123916
  simp only [CollatzResearch.WordTrace]
  refine ⟨111678783041052844215511801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148905044054737125620682401 111678783041052844215511801)
  ·
    refine ⟨83759087280789633161633851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111678783041052844215511801 83759087280789633161633851)
    ·
      refine ⟨125638630921184449742450777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83759087280789633161633851 125638630921184449742450777)
      ·
        refine ⟨94228973190888337306838083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125638630921184449742450777 94228973190888337306838083)
        ·
          refine ⟨141343459786332505960257125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94228973190888337306838083 141343459786332505960257125)
          ·
            refine ⟨26501898709937344867548211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141343459786332505960257125 26501898709937344867548211)
            ·
              refine ⟨39752848064906017301322317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26501898709937344867548211 39752848064906017301322317)
              ·
                refine ⟨14907318024339756487995869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39752848064906017301322317 14907318024339756487995869)
                ·
                  refine ⟨5590244259127408682998451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14907318024339756487995869 5590244259127408682998451)
                  ·
                    refine ⟨8385366388691113024497677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5590244259127408682998451 8385366388691113024497677)
                    ·
                      refine ⟨3144512395759167384186629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8385366388691113024497677 3144512395759167384186629)
                      ·
                        rfl

theorem cell23_6123916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_6123916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123916 prefixEnd_6123916 := by exact prefixLift 6123916
  have htrace : WordTrace (prefixWord ++ tailWord_6123916) baseStart_6123916 baseEnd_6123916 := by
    simpa [prefixWord, tailWord_6123916, baseEnd_6123916] using wordTrace_append hprefix tailTrace_6123916
  have hstable : (prefixWord ++ tailWord_6123916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123916).length < 2 ^ (prefixWord ++ tailWord_6123916).sum := by decide
  have hdescent : baseEnd_6123916 < baseStart_6123916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123936 : List Nat := [2, 1, 1, 4, 1, 4, 2, 2, 1, 5]
def baseStart_6123936 : Nat := 118140960795 + 6123936 * 2 ^ 59
def prefixEnd_6123936 : Nat := 4983230072969 + 3 ^ 40 * 6123936 * 2
def baseEnd_6123936 : Nat := 1048174221790752435312179

theorem tailTrace_6123936 : CollatzResearch.WordTrace tailWord_6123936 prefixEnd_6123936 1048174221790752435312179 := by
  unfold tailWord_6123936
  simp only [CollatzResearch.WordTrace]
  refine ⟨111679147771016615923375831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148905530361355487897834441 111679147771016615923375831)
  ·
    refine ⟨167518721656524923885063747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111679147771016615923375831 167518721656524923885063747)
    ·
      refine ⟨251278082484787385827595621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167518721656524923885063747 251278082484787385827595621)
      ·
        refine ⟨47114640465897634842674179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 251278082484787385827595621 47114640465897634842674179)
        ·
          refine ⟨70671960698846452264011269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47114640465897634842674179 70671960698846452264011269)
          ·
            refine ⟨13250992631033709799502113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70671960698846452264011269 13250992631033709799502113)
            ·
              refine ⟨9938244473275282349626585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13250992631033709799502113 9938244473275282349626585)
              ·
                refine ⟨7453683354956461762219939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9938244473275282349626585 7453683354956461762219939)
                ·
                  refine ⟨11180525032434692643329909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7453683354956461762219939 11180525032434692643329909)
                  ·
                    refine ⟨1048174221790752435312179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11180525032434692643329909 1048174221790752435312179)
                    ·
                      rfl

theorem cell23_6123936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 1, 5].length) (baseStart_6123936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123936 prefixEnd_6123936 := by exact prefixLift 6123936
  have htrace : WordTrace (prefixWord ++ tailWord_6123936) baseStart_6123936 baseEnd_6123936 := by
    simpa [prefixWord, tailWord_6123936, baseEnd_6123936] using wordTrace_append hprefix tailTrace_6123936
  have hstable : (prefixWord ++ tailWord_6123936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123936).length < 2 ^ (prefixWord ++ tailWord_6123936).sum := by decide
  have hdescent : baseEnd_6123936 < baseStart_6123936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123959 : List Nat := [1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 5]
def baseStart_6123959 : Nat := 118140960795 + 6123959 * 2 ^ 59
def prefixEnd_6123959 : Nat := 4983230072969 + 3 ^ 40 * 6123959 * 2
def baseEnd_6123959 : Nat := 3144534475427310715948931

theorem tailTrace_6123959 : CollatzResearch.WordTrace tailWord_6123959 prefixEnd_6123959 3144534475427310715948931 := by
  unfold tailWord_6123959
  simp only [CollatzResearch.WordTrace]
  refine ⟨223359134420949906774838931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148906089613966604516559287 223359134420949906774838931)
  ·
    refine ⟨335038701631424860162258397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223359134420949906774838931 335038701631424860162258397)
    ·
      refine ⟨125639513111784322560846899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335038701631424860162258397 125639513111784322560846899)
      ·
        refine ⟨188459269667676483841270349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125639513111784322560846899 188459269667676483841270349)
        ·
          refine ⟨70672226125378681440476381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188459269667676483841270349 70672226125378681440476381)
          ·
            refine ⟨26502084797017005540178643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70672226125378681440476381 26502084797017005540178643)
            ·
              refine ⟨39753127195525508310267965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26502084797017005540178643 39753127195525508310267965)
              ·
                refine ⟨14907422698322065616350487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39753127195525508310267965 14907422698322065616350487)
                ·
                  refine ⟨22361134047483098424525731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14907422698322065616350487 22361134047483098424525731)
                  ·
                    refine ⟨33541701071224647636788597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22361134047483098424525731 33541701071224647636788597)
                    ·
                      refine ⟨3144534475427310715948931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33541701071224647636788597 3144534475427310715948931)
                      ·
                        rfl

theorem cell23_6123959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_6123959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123959 prefixEnd_6123959 := by exact prefixLift 6123959
  have htrace : WordTrace (prefixWord ++ tailWord_6123959) baseStart_6123959 baseEnd_6123959 := by
    simpa [prefixWord, tailWord_6123959, baseEnd_6123959] using wordTrace_append hprefix tailTrace_6123959
  have hstable : (prefixWord ++ tailWord_6123959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123959).length < 2 ^ (prefixWord ++ tailWord_6123959).sum := by decide
  have hdescent : baseEnd_6123959 < baseStart_6123959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123966 : List Nat := [4, 2, 1, 1, 1, 1, 4, 1, 4, 4]
def baseStart_6123966 : Nat := 118140960795 + 6123966 * 2 ^ 59
def prefixEnd_6123966 : Nat := 4983230072969 + 3 ^ 40 * 6123966 * 2
def baseEnd_6123966 : Nat := 1048179356597297396187133

theorem tailTrace_6123966 : CollatzResearch.WordTrace tailWord_6123966 prefixEnd_6123966 1048179356597297396187133 := by
  unfold tailWord_6123966
  simp only [CollatzResearch.WordTrace]
  refine ⟨27919923716490568371292969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148906259821283031313562501 27919923716490568371292969)
  ·
    refine ⟨20939942787367926278469727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27919923716490568371292969 20939942787367926278469727)
    ·
      refine ⟨31409914181051889417704591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20939942787367926278469727 31409914181051889417704591)
      ·
        refine ⟨47114871271577834126556887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31409914181051889417704591 47114871271577834126556887)
        ·
          refine ⟨70672306907366751189835331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47114871271577834126556887 70672306907366751189835331)
          ·
            refine ⟨106008460361050126784752997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70672306907366751189835331 106008460361050126784752997)
            ·
              refine ⟨19876586317696898772141187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106008460361050126784752997 19876586317696898772141187)
              ·
                refine ⟨29814879476545348158211781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19876586317696898772141187 29814879476545348158211781)
                ·
                  refine ⟨5590289901852252779664709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29814879476545348158211781 5590289901852252779664709)
                  ·
                    refine ⟨1048179356597297396187133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5590289901852252779664709 1048179356597297396187133)
                    ·
                      rfl

theorem cell23_6123966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_6123966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123966 prefixEnd_6123966 := by exact prefixLift 6123966
  have htrace : WordTrace (prefixWord ++ tailWord_6123966) baseStart_6123966 baseEnd_6123966 := by
    simpa [prefixWord, tailWord_6123966, baseEnd_6123966] using wordTrace_append hprefix tailTrace_6123966
  have hstable : (prefixWord ++ tailWord_6123966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123966).length < 2 ^ (prefixWord ++ tailWord_6123966).sum := by decide
  have hdescent : baseEnd_6123966 < baseStart_6123966 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6123990 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2]
def baseStart_6123990 : Nat := 118140960795 + 6123990 * 2 ^ 59
def prefixEnd_6123990 : Nat := 4983230072969 + 3 ^ 40 * 6123990 * 2
def baseEnd_6123990 : Nat := 3144550393327600094661289

theorem tailTrace_6123990 : CollatzResearch.WordTrace tailWord_6123990 prefixEnd_6123990 3144550393327600094661289 := by
  unfold tailWord_6123990
  simp only [CollatzResearch.WordTrace]
  refine ⟨13960016567739849941826089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148906843389225066046144949 13960016567739849941826089)
  ·
    refine ⟨10470012425804887456369567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13960016567739849941826089 10470012425804887456369567)
    ·
      refine ⟨15705018638707331184554351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10470012425804887456369567 15705018638707331184554351)
      ·
        refine ⟨23557527958060996776831527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15705018638707331184554351 23557527958060996776831527)
        ·
          refine ⟨35336291937091495165247291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23557527958060996776831527 35336291937091495165247291)
          ·
            refine ⟨53004437905637242747870937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35336291937091495165247291 53004437905637242747870937)
            ·
              refine ⟨39753328429227932060903203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53004437905637242747870937 39753328429227932060903203)
              ·
                refine ⟨59629992643841898091354805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39753328429227932060903203 59629992643841898091354805)
                ·
                  refine ⟨5590311810360177946064513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59629992643841898091354805 5590311810360177946064513)
                  ·
                    refine ⟨4192733857770133459548385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5590311810360177946064513 4192733857770133459548385)
                    ·
                      refine ⟨3144550393327600094661289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4192733857770133459548385 3144550393327600094661289)
                      ·
                        rfl

theorem cell23_6123990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_6123990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6123990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6123990 prefixEnd_6123990 := by exact prefixLift 6123990
  have htrace : WordTrace (prefixWord ++ tailWord_6123990) baseStart_6123990 baseEnd_6123990 := by
    simpa [prefixWord, tailWord_6123990, baseEnd_6123990] using wordTrace_append hprefix tailTrace_6123990
  have hstable : (prefixWord ++ tailWord_6123990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6123990).length < 2 ^ (prefixWord ++ tailWord_6123990).sum := by decide
  have hdescent : baseEnd_6123990 < baseStart_6123990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6123990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124010 : List Nat := [3, 1, 3, 1, 3, 2, 3, 1, 1, 2, 3]
def baseStart_6124010 : Nat := 118140960795 + 6124010 * 2 ^ 59
def prefixEnd_6124010 : Nat := 4983230072969 + 3 ^ 40 * 6124010 * 2
def baseEnd_6124010 : Nat := 3144560662940690016411197

theorem tailTrace_6124010 : CollatzResearch.WordTrace tailWord_6124010 prefixEnd_6124010 3144560662940690016411197 := by
  unfold tailWord_6124010
  simp only [CollatzResearch.WordTrace]
  refine ⟨55840248635941285621236371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148907329695843428323296989 55840248635941285621236371)
  ·
    refine ⟨83760372953911928431854557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55840248635941285621236371 83760372953911928431854557)
    ·
      refine ⟨31410139857716973161945459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83760372953911928431854557 31410139857716973161945459)
      ·
        refine ⟨47115209786575459742918189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31410139857716973161945459 47115209786575459742918189)
        ·
          refine ⟨17668203669965797403594321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47115209786575459742918189 17668203669965797403594321)
          ·
            refine ⟨13251152752474348052695741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17668203669965797403594321 13251152752474348052695741)
            ·
              refine ⟨4969182282177880519760903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13251152752474348052695741 4969182282177880519760903)
              ·
                refine ⟨7453773423266820779641355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4969182282177880519760903 7453773423266820779641355)
                ·
                  refine ⟨11180660134900231169462033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7453773423266820779641355 11180660134900231169462033)
                  ·
                    refine ⟨8385495101175173377096525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11180660134900231169462033 8385495101175173377096525)
                    ·
                      refine ⟨3144560662940690016411197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8385495101175173377096525 3144560662940690016411197)
                      ·
                        rfl

theorem cell23_6124010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_6124010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124010 prefixEnd_6124010 := by exact prefixLift 6124010
  have htrace : WordTrace (prefixWord ++ tailWord_6124010) baseStart_6124010 baseEnd_6124010 := by
    simpa [prefixWord, tailWord_6124010, baseEnd_6124010] using wordTrace_append hprefix tailTrace_6124010
  have hstable : (prefixWord ++ tailWord_6124010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124010).length < 2 ^ (prefixWord ++ tailWord_6124010).sum := by decide
  have hdescent : baseEnd_6124010 < baseStart_6124010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124029 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 1, 5, 4]
def baseStart_6124029 : Nat := 118140960795 + 6124029 * 2 ^ 59
def prefixEnd_6124029 : Nat := 4983230072969 + 3 ^ 40 * 6124029 * 2
def baseEnd_6124029 : Nat := 3144570419073125442073609

theorem tailTrace_6124029 : CollatzResearch.WordTrace tailWord_6124029 prefixEnd_6124029 3144570419073125442073609 := by
  unfold tailWord_6124029
  simp only [CollatzResearch.WordTrace]
  refine ⟨223361687530696308729887141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148907791687130872486591427 223361687530696308729887141)
  ·
    refine ⟨41880316412005557886853839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223361687530696308729887141 41880316412005557886853839)
    ·
      refine ⟨62820474618008336830280759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41880316412005557886853839 62820474618008336830280759)
      ·
        refine ⟨94230711927012505245421139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62820474618008336830280759 94230711927012505245421139)
        ·
          refine ⟨141346067890518757868131709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94230711927012505245421139 141346067890518757868131709)
          ·
            refine ⟨53004775458944534200549391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141346067890518757868131709 53004775458944534200549391)
            ·
              refine ⟨79507163188416801300824087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53004775458944534200549391 79507163188416801300824087)
              ·
                refine ⟨119260744782625201951236131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79507163188416801300824087 119260744782625201951236131)
                ·
                  refine ⟨178891117173937802926854197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119260744782625201951236131 178891117173937802926854197)
                  ·
                    refine ⟨16771042235056669024392581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 178891117173937802926854197 16771042235056669024392581)
                    ·
                      refine ⟨3144570419073125442073609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16771042235056669024392581 3144570419073125442073609)
                      ·
                        rfl

theorem cell23_6124029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_6124029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124029 prefixEnd_6124029 := by exact prefixLift 6124029
  have htrace : WordTrace (prefixWord ++ tailWord_6124029) baseStart_6124029 baseEnd_6124029 := by
    simpa [prefixWord, tailWord_6124029, baseEnd_6124029] using wordTrace_append hprefix tailTrace_6124029
  have hstable : (prefixWord ++ tailWord_6124029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124029).length < 2 ^ (prefixWord ++ tailWord_6124029).sum := by decide
  have hdescent : baseEnd_6124029 < baseStart_6124029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124033 : List Nat := [1, 2, 4, 1, 3, 1, 1, 2, 3, 3, 2]
def baseStart_6124033 : Nat := 118140960795 + 6124033 * 2 ^ 59
def prefixEnd_6124033 : Nat := 4983230072969 + 3 ^ 40 * 6124033 * 2
def baseEnd_6124033 : Nat := 3144572472995743426423591

theorem tailTrace_6124033 : CollatzResearch.WordTrace tailWord_6124033 prefixEnd_6124033 3144572472995743426423591 := by
  unfold tailWord_6124033
  simp only [CollatzResearch.WordTrace]
  refine ⟨223361833422681817413032753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148907888948454544942021835 223361833422681817413032753)
  ·
    refine ⟨167521375067011363059774565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223361833422681817413032753 167521375067011363059774565)
    ·
      refine ⟨31410257825064630573707731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167521375067011363059774565 31410257825064630573707731)
      ·
        refine ⟨47115386737596945860561597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31410257825064630573707731 47115386737596945860561597)
        ·
          refine ⟨17668270026598854697710599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47115386737596945860561597 17668270026598854697710599)
          ·
            refine ⟨26502405039898282046565899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17668270026598854697710599 26502405039898282046565899)
            ·
              refine ⟨39753607559847423069848849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26502405039898282046565899 39753607559847423069848849)
              ·
                refine ⟨29815205669885567302386637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39753607559847423069848849 29815205669885567302386637)
                ·
                  refine ⟨11180702126207087738394989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29815205669885567302386637 11180702126207087738394989)
                  ·
                    refine ⟨4192763297327657901898121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11180702126207087738394989 4192763297327657901898121)
                    ·
                      refine ⟨3144572472995743426423591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4192763297327657901898121 3144572472995743426423591)
                      ·
                        rfl

theorem cell23_6124033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_6124033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124033 prefixEnd_6124033 := by exact prefixLift 6124033
  have htrace : WordTrace (prefixWord ++ tailWord_6124033) baseStart_6124033 baseEnd_6124033 := by
    simpa [prefixWord, tailWord_6124033, baseEnd_6124033] using wordTrace_append hprefix tailTrace_6124033
  have hstable : (prefixWord ++ tailWord_6124033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124033).length < 2 ^ (prefixWord ++ tailWord_6124033).sum := by decide
  have hdescent : baseEnd_6124033 < baseStart_6124033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124049 : List Nat := [1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 5]
def baseStart_6124049 : Nat := 118140960795 + 6124049 * 2 ^ 59
def prefixEnd_6124049 : Nat := 4983230072969 + 3 ^ 40 * 6124049 * 2
def baseEnd_6124049 : Nat := 3144580688686215363823517

theorem tailTrace_6124049 : CollatzResearch.WordTrace tailWord_6124049 prefixEnd_6124049 3144580688686215363823517 := by
  unfold tailWord_6124049
  simp only [CollatzResearch.WordTrace]
  refine ⟨223362416990623852145615201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148908277993749234763743467 223362416990623852145615201)
  ·
    refine ⟨167521812742967889109211401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223362416990623852145615201 167521812742967889109211401)
    ·
      refine ⟨125641359557225916831908551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167521812742967889109211401 125641359557225916831908551)
      ·
        refine ⟨188462039335838875247862827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125641359557225916831908551 188462039335838875247862827)
        ·
          refine ⟨282693059003758312871794241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188462039335838875247862827 282693059003758312871794241)
          ·
            refine ⟨212019794252818734653845681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282693059003758312871794241 212019794252818734653845681)
            ·
              refine ⟨159014845689614050990384261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212019794252818734653845681 159014845689614050990384261)
              ·
                refine ⟨29815283566802634560697049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159014845689614050990384261 29815283566802634560697049)
                ·
                  refine ⟨22361462675101975920522787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29815283566802634560697049 22361462675101975920522787)
                  ·
                    refine ⟨33542194012652963880784181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22361462675101975920522787 33542194012652963880784181)
                    ·
                      refine ⟨3144580688686215363823517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33542194012652963880784181 3144580688686215363823517)
                      ·
                        rfl

theorem cell23_6124049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_6124049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124049 prefixEnd_6124049 := by exact prefixLift 6124049
  have htrace : WordTrace (prefixWord ++ tailWord_6124049) baseStart_6124049 baseEnd_6124049 := by
    simpa [prefixWord, tailWord_6124049, baseEnd_6124049] using wordTrace_append hprefix tailTrace_6124049
  have hstable : (prefixWord ++ tailWord_6124049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124049).length < 2 ^ (prefixWord ++ tailWord_6124049).sum := by decide
  have hdescent : baseEnd_6124049 < baseStart_6124049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124063 : List Nat := [1, 1, 2, 4, 1, 1, 1, 4, 4, 2, 2]
def baseStart_6124063 : Nat := 118140960795 + 6124063 * 2 ^ 59
def prefixEnd_6124063 : Nat := 4983230072969 + 3 ^ 40 * 6124063 * 2
def baseEnd_6124063 : Nat := 3144587877415378309048453

theorem tailTrace_6124063 : CollatzResearch.WordTrace tailWord_6124063 prefixEnd_6124063 3144587877415378309048453 := by
  unfold tailWord_6124063
  simp only [CollatzResearch.WordTrace]
  refine ⟨223362927612573132536624843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148908618408382088357749895 223362927612573132536624843)
  ·
    refine ⟨335044391418859698804937265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223362927612573132536624843 335044391418859698804937265)
    ·
      refine ⟨251283293564144774103702949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335044391418859698804937265 251283293564144774103702949)
      ·
        refine ⟨47115617543277145144444303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 251283293564144774103702949 47115617543277145144444303)
        ·
          refine ⟨70673426314915717716666455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47115617543277145144444303 70673426314915717716666455)
          ·
            refine ⟨106010139472373576574999683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70673426314915717716666455 106010139472373576574999683)
            ·
              refine ⟨159015209208560364862499525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106010139472373576574999683 159015209208560364862499525)
              ·
                refine ⟨29815351726605068411718661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159015209208560364862499525 29815351726605068411718661)
                ·
                  refine ⟨5590378448738450327197249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29815351726605068411718661 5590378448738450327197249)
                  ·
                    refine ⟨4192783836553837745397937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5590378448738450327197249 4192783836553837745397937)
                    ·
                      refine ⟨3144587877415378309048453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4192783836553837745397937 3144587877415378309048453)
                      ·
                        rfl

theorem cell23_6124063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_6124063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124063 prefixEnd_6124063 := by exact prefixLift 6124063
  have htrace : WordTrace (prefixWord ++ tailWord_6124063) baseStart_6124063 baseEnd_6124063 := by
    simpa [prefixWord, tailWord_6124063, baseEnd_6124063] using wordTrace_append hprefix tailTrace_6124063
  have hstable : (prefixWord ++ tailWord_6124063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124063).length < 2 ^ (prefixWord ++ tailWord_6124063).sum := by decide
  have hdescent : baseEnd_6124063 < baseStart_6124063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124067 : List Nat := [1, 1, 1, 4, 4, 3, 2, 1, 1, 3, 2]
def baseStart_6124067 : Nat := 118140960795 + 6124067 * 2 ^ 59
def prefixEnd_6124067 : Nat := 4983230072969 + 3 ^ 40 * 6124067 * 2
def baseEnd_6124067 : Nat := 3144589931337996293398435

theorem tailTrace_6124067 : CollatzResearch.WordTrace tailWord_6124067 prefixEnd_6124067 3144589931337996293398435 := by
  unfold tailWord_6124067
  simp only [CollatzResearch.WordTrace]
  refine ⟨223363073504558641219770455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148908715669705760813180303 223363073504558641219770455)
  ·
    refine ⟨335044610256837961829655683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223363073504558641219770455 335044610256837961829655683)
    ·
      refine ⟨502566915385256942744483525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335044610256837961829655683 502566915385256942744483525)
      ·
        refine ⟨94231296634735676764590661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 502566915385256942744483525 94231296634735676764590661)
        ·
          refine ⟨17668368119012939393360749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94231296634735676764590661 17668368119012939393360749)
          ·
            refine ⟨6625638044629852272510281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17668368119012939393360749 6625638044629852272510281)
            ·
              refine ⟨4969228533472389204382711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6625638044629852272510281 4969228533472389204382711)
              ·
                refine ⟨7453842800208583806574067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4969228533472389204382711 7453842800208583806574067)
                ·
                  refine ⟨11180764200312875709861101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7453842800208583806574067 11180764200312875709861101)
                  ·
                    refine ⟨4192786575117328391197913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11180764200312875709861101 4192786575117328391197913)
                    ·
                      refine ⟨3144589931337996293398435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4192786575117328391197913 3144589931337996293398435)
                      ·
                        rfl

theorem cell23_6124067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 1, 3, 2].length) (baseStart_6124067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124067 prefixEnd_6124067 := by exact prefixLift 6124067
  have htrace : WordTrace (prefixWord ++ tailWord_6124067) baseStart_6124067 baseEnd_6124067 := by
    simpa [prefixWord, tailWord_6124067, baseEnd_6124067] using wordTrace_append hprefix tailTrace_6124067
  have hstable : (prefixWord ++ tailWord_6124067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124067).length < 2 ^ (prefixWord ++ tailWord_6124067).sum := by decide
  have hdescent : baseEnd_6124067 < baseStart_6124067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124080 : List Nat := [2, 1, 1, 1, 2, 3, 5, 2, 2, 2, 2]
def baseStart_6124080 : Nat := 118140960795 + 6124080 * 2 ^ 59
def prefixEnd_6124080 : Nat := 4983230072969 + 3 ^ 40 * 6124080 * 2
def baseEnd_6124080 : Nat := 3144596606586504742535875

theorem tailTrace_6124080 : CollatzResearch.WordTrace tailWord_6124080 prefixEnd_6124080 3144596606586504742535875 := by
  unfold tailWord_6124080
  simp only [CollatzResearch.WordTrace]
  refine ⟨111681773826755772219996847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148909031769007696293329129 111681773826755772219996847)
  ·
    refine ⟨167522660740133658329995271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111681773826755772219996847 167522660740133658329995271)
    ·
      refine ⟨251283991110200487494992907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167522660740133658329995271 251283991110200487494992907)
      ·
        refine ⟨376925986665300731242489361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251283991110200487494992907 376925986665300731242489361)
        ·
          refine ⟨282694489998975548431867021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376925986665300731242489361 282694489998975548431867021)
          ·
            refine ⟨106010433749615830661950133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 282694489998975548431867021 106010433749615830661950133)
            ·
              refine ⟨9938478164026484124557825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106010433749615830661950133 9938478164026484124557825)
              ·
                refine ⟨7453858623019863093418369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9938478164026484124557825 7453858623019863093418369)
                ·
                  refine ⟨5590393967264897320063777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7453858623019863093418369 5590393967264897320063777)
                  ·
                    refine ⟨4192795475448672990047833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5590393967264897320063777 4192795475448672990047833)
                    ·
                      refine ⟨3144596606586504742535875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4192795475448672990047833 3144596606586504742535875)
                      ·
                        rfl

theorem cell23_6124080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 2, 2, 2].length) (baseStart_6124080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124080 prefixEnd_6124080 := by exact prefixLift 6124080
  have htrace : WordTrace (prefixWord ++ tailWord_6124080) baseStart_6124080 baseEnd_6124080 := by
    simpa [prefixWord, tailWord_6124080, baseEnd_6124080] using wordTrace_append hprefix tailTrace_6124080
  have hstable : (prefixWord ++ tailWord_6124080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124080).length < 2 ^ (prefixWord ++ tailWord_6124080).sum := by decide
  have hdescent : baseEnd_6124080 < baseStart_6124080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124096 : List Nat := [2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 3]
def baseStart_6124096 : Nat := 118140960795 + 6124096 * 2 ^ 59
def prefixEnd_6124096 : Nat := 4983230072969 + 3 ^ 40 * 6124096 * 2
def baseEnd_6124096 : Nat := 3144604822276976679935801

theorem tailTrace_6124096 : CollatzResearch.WordTrace tailWord_6124096 prefixEnd_6124096 3144604822276976679935801 := by
  unfold tailWord_6124096
  simp only [CollatzResearch.WordTrace]
  refine ⟨111682065610726789586288071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148909420814302386115050761 111682065610726789586288071)
  ·
    refine ⟨167523098416090184379432107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111682065610726789586288071 167523098416090184379432107)
    ·
      refine ⟨251284647624135276569148161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167523098416090184379432107 251284647624135276569148161)
      ·
        refine ⟨188463485718101457426861121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251284647624135276569148161 188463485718101457426861121)
        ·
          refine ⟨141347614288576093070145841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188463485718101457426861121 141347614288576093070145841)
          ·
            refine ⟨106010710716432069802609381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141347614288576093070145841 106010710716432069802609381)
            ·
              refine ⟨19877008259331013087989259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106010710716432069802609381 19877008259331013087989259)
              ·
                refine ⟨29815512388996519631983889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19877008259331013087989259 29815512388996519631983889)
                ·
                  refine ⟨22361634291747389723987917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29815512388996519631983889 22361634291747389723987917)
                  ·
                    refine ⟨8385612859405271146495469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22361634291747389723987917 8385612859405271146495469)
                    ·
                      refine ⟨3144604822276976679935801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8385612859405271146495469 3144604822276976679935801)
                      ·
                        rfl

theorem cell23_6124096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 3].length) (baseStart_6124096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124096 prefixEnd_6124096 := by exact prefixLift 6124096
  have htrace : WordTrace (prefixWord ++ tailWord_6124096) baseStart_6124096 baseEnd_6124096 := by
    simpa [prefixWord, tailWord_6124096, baseEnd_6124096] using wordTrace_append hprefix tailTrace_6124096
  have hstable : (prefixWord ++ tailWord_6124096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124096).length < 2 ^ (prefixWord ++ tailWord_6124096).sum := by decide
  have hdescent : baseEnd_6124096 < baseStart_6124096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124116 : List Nat := [2, 4, 1, 1, 1, 3, 2, 1, 1, 7]
def baseStart_6124116 : Nat := 118140960795 + 6124116 * 2 ^ 59
def prefixEnd_6124116 : Nat := 4983230072969 + 3 ^ 40 * 6124116 * 2
def baseEnd_6124116 : Nat := 1048205030630022200561903

theorem tailTrace_6124116 : CollatzResearch.WordTrace tailWord_6124116 prefixEnd_6124116 1048205030630022200561903 := by
  unfold tailWord_6124116
  simp only [CollatzResearch.WordTrace]
  refine ⟨111682430340690561294152101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148909907120920748392202801 111682430340690561294152101)
  ·
    refine ⟨20940455688879480242653519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111682430340690561294152101 20940455688879480242653519)
    ·
      refine ⟨31410683533319220363980279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20940455688879480242653519 31410683533319220363980279)
      ·
        refine ⟨47116025299978830545970419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31410683533319220363980279 47116025299978830545970419)
        ·
          refine ⟨70674037949968245818955629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47116025299978830545970419 70674037949968245818955629)
          ·
            refine ⟨26502764231238092182108361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70674037949968245818955629 26502764231238092182108361)
            ·
              refine ⟨19877073173428569136581271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26502764231238092182108361 19877073173428569136581271)
              ·
                refine ⟨29815609760142853704871907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19877073173428569136581271 29815609760142853704871907)
                ·
                  refine ⟨44723414640214280557307861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29815609760142853704871907 44723414640214280557307861)
                  ·
                    refine ⟨1048205030630022200561903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44723414640214280557307861 1048205030630022200561903)
                    ·
                      rfl

theorem cell23_6124116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_6124116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124116 prefixEnd_6124116 := by exact prefixLift 6124116
  have htrace : WordTrace (prefixWord ++ tailWord_6124116) baseStart_6124116 baseEnd_6124116 := by
    simpa [prefixWord, tailWord_6124116, baseEnd_6124116] using wordTrace_append hprefix tailTrace_6124116
  have hstable : (prefixWord ++ tailWord_6124116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124116).length < 2 ^ (prefixWord ++ tailWord_6124116).sum := by decide
  have hdescent : baseEnd_6124116 < baseStart_6124116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124133 : List Nat := [1, 3, 1, 3, 4, 1, 1, 2, 2, 5]
def baseStart_6124133 : Nat := 118140960795 + 6124133 * 2 ^ 59
def prefixEnd_6124133 : Nat := 4983230072969 + 3 ^ 40 * 6124133 * 2
def baseEnd_6124133 : Nat := 1048207940353731011724377

theorem tailTrace_6124133 : CollatzResearch.WordTrace tailWord_6124133 prefixEnd_6124133 1048207940353731011724377 := by
  unfold tailWord_6124133
  simp only [CollatzResearch.WordTrace]
  refine ⟨223365480722319534491673053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148910320481546356327782035 223365480722319534491673053)
  ·
    refine ⟨83762055270869825434377395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223365480722319534491673053 83762055270869825434377395)
    ·
      refine ⟨125643082906304738151566093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83762055270869825434377395 125643082906304738151566093)
      ·
        refine ⟨47116156089864276806837285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125643082906304738151566093 47116156089864276806837285)
        ·
          refine ⟨8834279266849551901281991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47116156089864276806837285 8834279266849551901281991)
          ·
            refine ⟨13251418900274327851922987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8834279266849551901281991 13251418900274327851922987)
            ·
              refine ⟨19877128350411491777884481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13251418900274327851922987 19877128350411491777884481)
              ·
                refine ⟨14907846262808618833413361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19877128350411491777884481 14907846262808618833413361)
                ·
                  refine ⟨11180884697106464125060021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14907846262808618833413361 11180884697106464125060021)
                  ·
                    refine ⟨1048207940353731011724377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11180884697106464125060021 1048207940353731011724377)
                    ·
                      rfl

theorem cell23_6124133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 5].length) (baseStart_6124133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124133 prefixEnd_6124133 := by exact prefixLift 6124133
  have htrace : WordTrace (prefixWord ++ tailWord_6124133) baseStart_6124133 baseEnd_6124133 := by
    simpa [prefixWord, tailWord_6124133, baseEnd_6124133] using wordTrace_append hprefix tailTrace_6124133
  have hstable : (prefixWord ++ tailWord_6124133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124133).length < 2 ^ (prefixWord ++ tailWord_6124133).sum := by decide
  have hdescent : baseEnd_6124133 < baseStart_6124133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124139 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 5]
def baseStart_6124139 : Nat := 118140960795 + 6124139 * 2 ^ 59
def prefixEnd_6124139 : Nat := 4983230072969 + 3 ^ 40 * 6124139 * 2
def baseEnd_6124139 : Nat := 3144626901945120011698103

theorem tailTrace_6124139 : CollatzResearch.WordTrace tailWord_6124139 prefixEnd_6124139 3144626901945120011698103 := by
  unfold tailWord_6124139
  simp only [CollatzResearch.WordTrace]
  refine ⟨223365699560297797516391471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148910466373531865010927647 223365699560297797516391471)
  ·
    refine ⟨335048549340446696274587207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223365699560297797516391471 335048549340446696274587207)
    ·
      refine ⟨502572824010670044411880811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335048549340446696274587207 502572824010670044411880811)
      ·
        refine ⟨753859236016005066617821217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502572824010670044411880811 753859236016005066617821217)
        ·
          refine ⟨565394427012003799963365913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 753859236016005066617821217 565394427012003799963365913)
          ·
            refine ⟨424045820259002849972524435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 565394427012003799963365913 424045820259002849972524435)
            ·
              refine ⟨636068730388504274958786653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 424045820259002849972524435 636068730388504274958786653)
              ·
                refine ⟨238525773895689103109544995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 636068730388504274958786653 238525773895689103109544995)
                ·
                  refine ⟨357788660843533654664317493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 238525773895689103109544995 357788660843533654664317493)
                  ·
                    refine ⟨33542686954081280124779765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 357788660843533654664317493 33542686954081280124779765)
                    ·
                      refine ⟨3144626901945120011698103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33542686954081280124779765 3144626901945120011698103)
                      ·
                        rfl

theorem cell23_6124139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 5].length) (baseStart_6124139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124139 prefixEnd_6124139 := by exact prefixLift 6124139
  have htrace : WordTrace (prefixWord ++ tailWord_6124139) baseStart_6124139 baseEnd_6124139 := by
    simpa [prefixWord, tailWord_6124139, baseEnd_6124139] using wordTrace_append hprefix tailTrace_6124139
  have hstable : (prefixWord ++ tailWord_6124139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124139).length < 2 ^ (prefixWord ++ tailWord_6124139).sum := by decide
  have hdescent : baseEnd_6124139 < baseStart_6124139 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124156 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 3, 4, 3]
def baseStart_6124156 : Nat := 118140960795 + 6124156 * 2 ^ 59
def prefixEnd_6124156 : Nat := 4983230072969 + 3 ^ 40 * 6124156 * 2
def baseEnd_6124156 : Nat := 3144635631116246445185525

theorem tailTrace_6124156 : CollatzResearch.WordTrace tailWord_6124156 prefixEnd_6124156 3144635631116246445185525 := by
  unfold tailWord_6124156
  simp only [CollatzResearch.WordTrace]
  refine ⟨111683159800618104709880161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148910879734157472946506881 111683159800618104709880161)
  ·
    refine ⟨83762369850463578532410121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111683159800618104709880161 83762369850463578532410121)
    ·
      refine ⟨62821777387847683899307591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83762369850463578532410121 62821777387847683899307591)
      ·
        refine ⟨94232666081771525848961387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62821777387847683899307591 94232666081771525848961387)
        ·
          refine ⟨141348999122657288773442081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94232666081771525848961387 141348999122657288773442081)
          ·
            refine ⟨106011749341992966580081561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141348999122657288773442081 106011749341992966580081561)
            ·
              refine ⟨79508812006494724935061171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106011749341992966580081561 79508812006494724935061171)
              ·
                refine ⟨119263218009742087402591757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79508812006494724935061171 119263218009742087402591757)
                ·
                  refine ⟨44723706753653282775971909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119263218009742087402591757 44723706753653282775971909)
                  ·
                    refine ⟨8385695016309990520494733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44723706753653282775971909 8385695016309990520494733)
                    ·
                      refine ⟨3144635631116246445185525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8385695016309990520494733 3144635631116246445185525)
                      ·
                        rfl

theorem cell23_6124156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_6124156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124156 prefixEnd_6124156 := by exact prefixLift 6124156
  have htrace : WordTrace (prefixWord ++ tailWord_6124156) baseStart_6124156 baseEnd_6124156 := by
    simpa [prefixWord, tailWord_6124156, baseEnd_6124156] using wordTrace_append hprefix tailTrace_6124156
  have hstable : (prefixWord ++ tailWord_6124156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124156).length < 2 ^ (prefixWord ++ tailWord_6124156).sum := by decide
  have hdescent : baseEnd_6124156 < baseStart_6124156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124159 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 10]
def baseStart_6124159 : Nat := 118140960795 + 6124159 * 2 ^ 59
def prefixEnd_6124159 : Nat := 4983230072969 + 3 ^ 40 * 6124159 * 2
def baseEnd_6124159 : Nat := 349404130173134437049779

theorem tailTrace_6124159 : CollatzResearch.WordTrace tailWord_6124159 prefixEnd_6124159 349404130173134437049779 := by
  unfold tailWord_6124159
  simp only [CollatzResearch.WordTrace]
  refine ⟨223366429020225340932119531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148910952680150227288079687 223366429020225340932119531)
  ·
    refine ⟨335049643530338011398179297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223366429020225340932119531 335049643530338011398179297)
    ·
      refine ⟨251287232647753508548634473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335049643530338011398179297 251287232647753508548634473)
      ·
        refine ⟨188465424485815131411475855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251287232647753508548634473 188465424485815131411475855)
        ·
          refine ⟨282698136728722697117213783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188465424485815131411475855 282698136728722697117213783)
          ·
            refine ⟨424047205093084045675820675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282698136728722697117213783 424047205093084045675820675)
            ·
              refine ⟨636070807639626068513731013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 424047205093084045675820675 636070807639626068513731013)
              ·
                refine ⟨119263276432429887846324565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 636070807639626068513731013 119263276432429887846324565)
                ·
                  refine ⟨349404130173134437049779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 119263276432429887846324565 349404130173134437049779)
                  ·
                    rfl

theorem cell23_6124159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 10].length) (baseStart_6124159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124159 prefixEnd_6124159 := by exact prefixLift 6124159
  have htrace : WordTrace (prefixWord ++ tailWord_6124159) baseStart_6124159 baseEnd_6124159 := by
    simpa [prefixWord, tailWord_6124159, baseEnd_6124159] using wordTrace_append hprefix tailTrace_6124159
  have hstable : (prefixWord ++ tailWord_6124159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124159).length < 2 ^ (prefixWord ++ tailWord_6124159).sum := by decide
  have hdescent : baseEnd_6124159 < baseStart_6124159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124170 : List Nat := [3, 1, 2, 3, 3, 1, 2, 1, 2, 1, 4]
def baseStart_6124170 : Nat := 118140960795 + 6124170 * 2 ^ 59
def prefixEnd_6124170 : Nat := 4983230072969 + 3 ^ 40 * 6124170 * 2
def baseEnd_6124170 : Nat := 3144642819845409390410461

theorem tailTrace_6124170 : CollatzResearch.WordTrace tailWord_6124170 prefixEnd_6124170 3144642819845409390410461 := by
  unfold tailWord_6124170
  simp only [CollatzResearch.WordTrace]
  refine ⟨55841707555796372452692491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148911220148790326540513309 55841707555796372452692491)
  ·
    refine ⟨83762561333694558679038737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55841707555796372452692491 83762561333694558679038737)
    ·
      refine ⟨62821921000270919009279053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83762561333694558679038737 62821921000270919009279053)
      ·
        refine ⟨23558220375101594628479645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62821921000270919009279053 23558220375101594628479645)
        ·
          refine ⟨8834332640663097985679867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23558220375101594628479645 8834332640663097985679867)
          ·
            refine ⟨13251498960994646978519801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8834332640663097985679867 13251498960994646978519801)
            ·
              refine ⟨9938624220745985233889851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13251498960994646978519801 9938624220745985233889851)
              ·
                refine ⟨14907936331118977850834777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9938624220745985233889851 14907936331118977850834777)
                ·
                  refine ⟨11180952248339233388126083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14907936331118977850834777 11180952248339233388126083)
                  ·
                    refine ⟨16771428372508850082189125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11180952248339233388126083 16771428372508850082189125)
                    ·
                      refine ⟨3144642819845409390410461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16771428372508850082189125 3144642819845409390410461)
                      ·
                        rfl

theorem cell23_6124170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_6124170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124170 prefixEnd_6124170 := by exact prefixLift 6124170
  have htrace : WordTrace (prefixWord ++ tailWord_6124170) baseStart_6124170 baseEnd_6124170 := by
    simpa [prefixWord, tailWord_6124170, baseEnd_6124170] using wordTrace_append hprefix tailTrace_6124170
  have hstable : (prefixWord ++ tailWord_6124170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124170).length < 2 ^ (prefixWord ++ tailWord_6124170).sum := by decide
  have hdescent : baseEnd_6124170 < baseStart_6124170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124190 : List Nat := [4, 3, 1, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_6124190 : Nat := 118140960795 + 6124190 * 2 ^ 59
def prefixEnd_6124190 : Nat := 4983230072969 + 3 ^ 40 * 6124190 * 2
def baseEnd_6124190 : Nat := 3144653089458499312160369

theorem tailTrace_6124190 : CollatzResearch.WordTrace tailWord_6124190 prefixEnd_6124190 3144653089458499312160369 := by
  unfold tailWord_6124190
  simp only [CollatzResearch.WordTrace]
  refine ⟨27920944960389129153312253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148911706455408688817665349 27920944960389129153312253)
  ·
    refine ⟨10470354360145923432492095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27920944960389129153312253 10470354360145923432492095)
    ·
      refine ⟨15705531540218885148738143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10470354360145923432492095 15705531540218885148738143)
      ·
        refine ⟨23558297310328327723107215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15705531540218885148738143 23558297310328327723107215)
        ·
          refine ⟨35337445965492491584660823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23558297310328327723107215 35337445965492491584660823)
          ·
            refine ⟨53006168948238737376991235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35337445965492491584660823 53006168948238737376991235)
            ·
              refine ⟨79509253422358106065486853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53006168948238737376991235 79509253422358106065486853)
              ·
                refine ⟨14907985016692144887278785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79509253422358106065486853 14907985016692144887278785)
                ·
                  refine ⟨11180988762519108665459089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14907985016692144887278785 11180988762519108665459089)
                  ·
                    refine ⟨8385741571889331499094317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11180988762519108665459089 8385741571889331499094317)
                    ·
                      refine ⟨3144653089458499312160369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8385741571889331499094317 3144653089458499312160369)
                      ·
                        rfl

theorem cell23_6124190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_6124190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124190 prefixEnd_6124190 := by exact prefixLift 6124190
  have htrace : WordTrace (prefixWord ++ tailWord_6124190) baseStart_6124190 baseEnd_6124190 := by
    simpa [prefixWord, tailWord_6124190, baseEnd_6124190] using wordTrace_append hprefix tailTrace_6124190
  have hstable : (prefixWord ++ tailWord_6124190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124190).length < 2 ^ (prefixWord ++ tailWord_6124190).sum := by decide
  have hdescent : baseEnd_6124190 < baseStart_6124190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124196 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 1, 2, 6]
def baseStart_6124196 : Nat := 118140960795 + 6124196 * 2 ^ 59
def prefixEnd_6124196 : Nat := 4983230072969 + 3 ^ 40 * 6124196 * 2
def baseEnd_6124196 : Nat := 3144656170342426288685341

theorem tailTrace_6124196 : CollatzResearch.WordTrace tailWord_6124196 prefixEnd_6124196 3144656170342426288685341 := by
  unfold tailWord_6124196
  simp only [CollatzResearch.WordTrace]
  refine ⟨111683889260545648125608221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148911852347394197500810961 111683889260545648125608221)
  ·
    refine ⟨41881458472704618047103083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111683889260545648125608221 41881458472704618047103083)
    ·
      refine ⟨62822187709056927070654625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41881458472704618047103083 62822187709056927070654625)
      ·
        refine ⟨47116640781792695302990969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62822187709056927070654625 47116640781792695302990969)
        ·
          refine ⟨35337480586344521477243227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47116640781792695302990969 35337480586344521477243227)
          ·
            refine ⟨53006220879516782215864841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35337480586344521477243227 53006220879516782215864841)
            ·
              refine ⟨39754665659637586661898631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53006220879516782215864841 39754665659637586661898631)
              ·
                refine ⟨59631998489456379992847947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39754665659637586661898631 59631998489456379992847947)
                ·
                  refine ⟨89447997734184569989271921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59631998489456379992847947 89447997734184569989271921)
                  ·
                    refine ⟨67085998300638427491953941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89447997734184569989271921 67085998300638427491953941)
                    ·
                      refine ⟨3144656170342426288685341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67085998300638427491953941 3144656170342426288685341)
                      ·
                        rfl

theorem cell23_6124196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_6124196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124196 prefixEnd_6124196 := by exact prefixLift 6124196
  have htrace : WordTrace (prefixWord ++ tailWord_6124196) baseStart_6124196 baseEnd_6124196 := by
    simpa [prefixWord, tailWord_6124196, baseEnd_6124196] using wordTrace_append hprefix tailTrace_6124196
  have hstable : (prefixWord ++ tailWord_6124196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124196).length < 2 ^ (prefixWord ++ tailWord_6124196).sum := by decide
  have hdescent : baseEnd_6124196 < baseStart_6124196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124220 : List Nat := [2, 2, 2, 3, 1, 1, 3, 2, 3, 1, 3]
def baseStart_6124220 : Nat := 118140960795 + 6124220 * 2 ^ 59
def prefixEnd_6124220 : Nat := 4983230072969 + 3 ^ 40 * 6124220 * 2
def baseEnd_6124220 : Nat := 3144668493878134194785231

theorem tailTrace_6124220 : CollatzResearch.WordTrace tailWord_6124220 prefixEnd_6124220 3144668493878134194785231 := by
  unfold tailWord_6124220
  simp only [CollatzResearch.WordTrace]
  refine ⟨111684326936502174175045057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148912435915336232233393409 111684326936502174175045057)
  ·
    refine ⟨83763245202376630631283793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111684326936502174175045057 83763245202376630631283793)
    ·
      refine ⟨62822433901782472973462845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83763245202376630631283793 62822433901782472973462845)
      ·
        refine ⟨23558412713168427365048567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62822433901782472973462845 23558412713168427365048567)
        ·
          refine ⟨35337619069752641047572851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23558412713168427365048567 35337619069752641047572851)
          ·
            refine ⟨53006428604628961571359277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35337619069752641047572851 53006428604628961571359277)
            ·
              refine ⟨19877410726735860589259729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53006428604628961571359277 19877410726735860589259729)
              ·
                refine ⟨14908058045051895441944797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19877410726735860589259729 14908058045051895441944797)
                ·
                  refine ⟨5590521766894460790729299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14908058045051895441944797 5590521766894460790729299)
                  ·
                    refine ⟨8385782650341691186093949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5590521766894460790729299 8385782650341691186093949)
                    ·
                      refine ⟨3144668493878134194785231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8385782650341691186093949 3144668493878134194785231)
                      ·
                        rfl

theorem cell23_6124220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_6124220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124220 prefixEnd_6124220 := by exact prefixLift 6124220
  have htrace : WordTrace (prefixWord ++ tailWord_6124220) baseStart_6124220 baseEnd_6124220 := by
    simpa [prefixWord, tailWord_6124220, baseEnd_6124220] using wordTrace_append hprefix tailTrace_6124220
  have hstable : (prefixWord ++ tailWord_6124220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124220).length < 2 ^ (prefixWord ++ tailWord_6124220).sum := by decide
  have hdescent : baseEnd_6124220 < baseStart_6124220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124256 : List Nat := [2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 6]
def baseStart_6124256 : Nat := 118140960795 + 6124256 * 2 ^ 59
def prefixEnd_6124256 : Nat := 4983230072969 + 3 ^ 40 * 6124256 * 2
def baseEnd_6124256 : Nat := 3144686979181696053935065

theorem tailTrace_6124256 : CollatzResearch.WordTrace tailWord_6124256 prefixEnd_6124256 3144686979181696053935065 := by
  unfold tailWord_6124256
  simp only [CollatzResearch.WordTrace]
  refine ⟨111684983450436963249200311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148913311267249284332267081 111684983450436963249200311)
  ·
    refine ⟨167527475175655444873800467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111684983450436963249200311 167527475175655444873800467)
    ·
      refine ⟨251291212763483167310700701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167527475175655444873800467 251291212763483167310700701)
      ·
        refine ⟨94234204786306187741512763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251291212763483167310700701 94234204786306187741512763)
        ·
          refine ⟨141351307179459281612269145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94234204786306187741512763 141351307179459281612269145)
          ·
            refine ⟨106013480384594461209201859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141351307179459281612269145 106013480384594461209201859)
            ·
              refine ⟨159020220576891691813802789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106013480384594461209201859 159020220576891691813802789)
              ·
                refine ⟨29816291358167192215088023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159020220576891691813802789 29816291358167192215088023)
                ·
                  refine ⟨44724437037250788322632035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29816291358167192215088023 44724437037250788322632035)
                  ·
                    refine ⟨67086655555876182483948053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44724437037250788322632035 67086655555876182483948053)
                    ·
                      refine ⟨3144686979181696053935065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67086655555876182483948053 3144686979181696053935065)
                      ·
                        rfl

theorem cell23_6124256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_6124256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124256 prefixEnd_6124256 := by exact prefixLift 6124256
  have htrace : WordTrace (prefixWord ++ tailWord_6124256) baseStart_6124256 baseEnd_6124256 := by
    simpa [prefixWord, tailWord_6124256, baseEnd_6124256] using wordTrace_append hprefix tailTrace_6124256
  have hstable : (prefixWord ++ tailWord_6124256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124256).length < 2 ^ (prefixWord ++ tailWord_6124256).sum := by decide
  have hdescent : baseEnd_6124256 < baseStart_6124256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124266 : List Nat := [3, 1, 3, 1, 1, 1, 1, 12]
def baseStart_6124266 : Nat := 118140960795 + 6124266 * 2 ^ 59
def prefixEnd_6124266 : Nat := 4983230072969 + 3 ^ 40 * 6124266 * 2
def baseEnd_6124266 : Nat := 116470078295860778326297

theorem tailTrace_6124266 : CollatzResearch.WordTrace tailWord_6124266 prefixEnd_6124266 116470078295860778326297 := by
  unfold tailWord_6124266
  simp only [CollatzResearch.WordTrace]
  refine ⟨55842582907709424551566163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148913554420558465470843101 55842582907709424551566163)
  ·
    refine ⟨83763874361564136827349245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55842582907709424551566163 83763874361564136827349245)
    ·
      refine ⟨31411452885586551310255967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83763874361564136827349245 31411452885586551310255967)
      ·
        refine ⟨47117179328379826965383951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31411452885586551310255967 47117179328379826965383951)
        ·
          refine ⟨70675768992569740448075927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47117179328379826965383951 70675768992569740448075927)
          ·
            refine ⟨106013653488854610672113891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70675768992569740448075927 106013653488854610672113891)
            ·
              refine ⟨159020480233281916008170837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106013653488854610672113891 159020480233281916008170837)
              ·
                refine ⟨116470078295860778326297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 159020480233281916008170837 116470078295860778326297)
                ·
                  rfl

theorem cell23_6124266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 12].length) (baseStart_6124266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124266 prefixEnd_6124266 := by exact prefixLift 6124266
  have htrace : WordTrace (prefixWord ++ tailWord_6124266) baseStart_6124266 baseEnd_6124266 := by
    simpa [prefixWord, tailWord_6124266, baseEnd_6124266] using wordTrace_append hprefix tailTrace_6124266
  have hstable : (prefixWord ++ tailWord_6124266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124266).length < 2 ^ (prefixWord ++ tailWord_6124266).sum := by decide
  have hdescent : baseEnd_6124266 < baseStart_6124266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124270 : List Nat := [4, 1, 2, 1, 1, 5, 1, 1, 1, 6]
def baseStart_6124270 : Nat := 118140960795 + 6124270 * 2 ^ 59
def prefixEnd_6124270 : Nat := 4983230072969 + 3 ^ 40 * 6124270 * 2
def baseEnd_6124270 : Nat := 1048231389303619666386667

theorem tailTrace_6124270 : CollatzResearch.WordTrace tailWord_6124270 prefixEnd_6124270 1048231389303619666386667 := by
  unfold tailWord_6124270
  simp only [CollatzResearch.WordTrace]
  refine ⟨27921309690352900861176283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148913651681882137926273509 27921309690352900861176283)
  ·
    refine ⟨41881964535529351291764425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27921309690352900861176283 41881964535529351291764425)
    ·
      refine ⟨31411473401647013468823319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41881964535529351291764425 31411473401647013468823319)
      ·
        refine ⟨47117210102470520203234979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31411473401647013468823319 47117210102470520203234979)
        ·
          refine ⟨70675815153705780304852469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47117210102470520203234979 70675815153705780304852469)
          ·
            refine ⟨6625857670659916903579919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70675815153705780304852469 6625857670659916903579919)
            ·
              refine ⟨9938786505989875355369879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6625857670659916903579919 9938786505989875355369879)
              ·
                refine ⟨14908179758984813033054819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9938786505989875355369879 14908179758984813033054819)
                ·
                  refine ⟨22362269638477219549582229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14908179758984813033054819 22362269638477219549582229)
                  ·
                    refine ⟨1048231389303619666386667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22362269638477219549582229 1048231389303619666386667)
                    ·
                      rfl

theorem cell23_6124270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_6124270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124270 prefixEnd_6124270 := by exact prefixLift 6124270
  have htrace : WordTrace (prefixWord ++ tailWord_6124270) baseStart_6124270 baseEnd_6124270 := by
    simpa [prefixWord, tailWord_6124270, baseEnd_6124270] using wordTrace_append hprefix tailTrace_6124270
  have hstable : (prefixWord ++ tailWord_6124270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124270).length < 2 ^ (prefixWord ++ tailWord_6124270).sum := by decide
  have hdescent : baseEnd_6124270 < baseStart_6124270 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124280 : List Nat := [2, 1, 2, 1, 1, 2, 6, 2, 1, 2, 3]
def baseStart_6124280 : Nat := 118140960795 + 6124280 * 2 ^ 59
def prefixEnd_6124280 : Nat := 4983230072969 + 3 ^ 40 * 6124280 * 2
def baseEnd_6124280 : Nat := 3144699302717403960034955

theorem tailTrace_6124280 : CollatzResearch.WordTrace tailWord_6124280 prefixEnd_6124280 3144699302717403960034955 := by
  unfold tailWord_6124280
  simp only [CollatzResearch.WordTrace]
  refine ⟨111685421126393489298637147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148913894835191319064849529 111685421126393489298637147)
  ·
    refine ⟨167528131689590233947955721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111685421126393489298637147 167528131689590233947955721)
    ·
      refine ⟨125646098767192675460966791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167528131689590233947955721 125646098767192675460966791)
      ·
        refine ⟨188469148150789013191450187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125646098767192675460966791 188469148150789013191450187)
        ·
          refine ⟨282703722226183519787175281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188469148150789013191450187 282703722226183519787175281)
          ·
            refine ⟨212027791669637639840381461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282703722226183519787175281 212027791669637639840381461)
            ·
              refine ⟨9938802734514264367517881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 212027791669637639840381461 9938802734514264367517881)
              ·
                refine ⟨7454102050885698275638411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9938802734514264367517881 7454102050885698275638411)
                ·
                  refine ⟨11181153076328547413457617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7454102050885698275638411 11181153076328547413457617)
                  ·
                    refine ⟨8385864807246410560093213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11181153076328547413457617 8385864807246410560093213)
                    ·
                      refine ⟨3144699302717403960034955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8385864807246410560093213 3144699302717403960034955)
                      ·
                        rfl

theorem cell23_6124280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 1, 2, 3].length) (baseStart_6124280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124280 prefixEnd_6124280 := by exact prefixLift 6124280
  have htrace : WordTrace (prefixWord ++ tailWord_6124280) baseStart_6124280 baseEnd_6124280 := by
    simpa [prefixWord, tailWord_6124280, baseEnd_6124280] using wordTrace_append hprefix tailTrace_6124280
  have hstable : (prefixWord ++ tailWord_6124280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124280).length < 2 ^ (prefixWord ++ tailWord_6124280).sum := by decide
  have hdescent : baseEnd_6124280 < baseStart_6124280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124293 : List Nat := [1, 3, 1, 1, 2, 1, 1, 6, 1, 3, 3]
def baseStart_6124293 : Nat := 118140960795 + 6124293 * 2 ^ 59
def prefixEnd_6124293 : Nat := 4983230072969 + 3 ^ 40 * 6124293 * 2
def baseEnd_6124293 : Nat := 3144705977965912409172395

theorem tailTrace_6124293 : CollatzResearch.WordTrace tailWord_6124293 prefixEnd_6124293 3144705977965912409172395 := by
  unfold tailWord_6124293
  simp only [CollatzResearch.WordTrace]
  refine ⟨223371316401739881817497533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148914210934493254544998355 223371316401739881817497533)
  ·
    refine ⟨83764243650652455681561575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223371316401739881817497533 83764243650652455681561575)
    ·
      refine ⟨125646365475978683522342363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83764243650652455681561575 125646365475978683522342363)
      ·
        refine ⟨188469548213968025283513545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125646365475978683522342363 188469548213968025283513545)
        ·
          refine ⟨141352161160476018962635159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188469548213968025283513545 141352161160476018962635159)
          ·
            refine ⟨212028241740714028443952739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141352161160476018962635159 212028241740714028443952739)
            ·
              refine ⟨318042362611071042665929109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212028241740714028443952739 318042362611071042665929109)
              ·
                refine ⟨14908235747393955124965427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 318042362611071042665929109 14908235747393955124965427)
                ·
                  refine ⟨22362353621090932687448141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14908235747393955124965427 22362353621090932687448141)
                  ·
                    refine ⟨8385882607909099757793053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22362353621090932687448141 8385882607909099757793053)
                    ·
                      refine ⟨3144705977965912409172395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8385882607909099757793053 3144705977965912409172395)
                      ·
                        rfl

theorem cell23_6124293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 3, 3].length) (baseStart_6124293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124293 prefixEnd_6124293 := by exact prefixLift 6124293
  have htrace : WordTrace (prefixWord ++ tailWord_6124293) baseStart_6124293 baseEnd_6124293 := by
    simpa [prefixWord, tailWord_6124293, baseEnd_6124293] using wordTrace_append hprefix tailTrace_6124293
  have hstable : (prefixWord ++ tailWord_6124293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124293).length < 2 ^ (prefixWord ++ tailWord_6124293).sum := by decide
  have hdescent : baseEnd_6124293 < baseStart_6124293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124311 : List Nat := [1, 1, 3, 4, 4, 1, 1, 1, 3, 2, 2]
def baseStart_6124311 : Nat := 118140960795 + 6124311 * 2 ^ 59
def prefixEnd_6124311 : Nat := 4983230072969 + 3 ^ 40 * 6124311 * 2
def baseEnd_6124311 : Nat := 3144715220617693338747313

theorem tailTrace_6124311 : CollatzResearch.WordTrace tailWord_6124311 prefixEnd_6124311 3144715220617693338747313 := by
  unfold tailWord_6124311
  simp only [CollatzResearch.WordTrace]
  refine ⟨223371972915674670891652787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148914648610449780594435191 223371972915674670891652787)
  ·
    refine ⟨335057959373512006337479181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223371972915674670891652787 335057959373512006337479181)
    ·
      refine ⟨125646734765067002376554693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335057959373512006337479181 125646734765067002376554693)
      ·
        refine ⟨23558762768450062945604005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125646734765067002376554693 23558762768450062945604005)
        ·
          refine ⟨4417268019084386802300751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23558762768450062945604005 4417268019084386802300751)
          ·
            refine ⟨6625902028626580203451127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4417268019084386802300751 6625902028626580203451127)
            ·
              refine ⟨9938853042939870305176691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6625902028626580203451127 9938853042939870305176691)
              ·
                refine ⟨14908279564409805457765037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9938853042939870305176691 14908279564409805457765037)
                ·
                  refine ⟨5590604836653677046661889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14908279564409805457765037 5590604836653677046661889)
                  ·
                    refine ⟨4192953627490257784996417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5590604836653677046661889 4192953627490257784996417)
                    ·
                      refine ⟨3144715220617693338747313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4192953627490257784996417 3144715220617693338747313)
                      ·
                        rfl

theorem cell23_6124311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_6124311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124311 prefixEnd_6124311 := by exact prefixLift 6124311
  have htrace : WordTrace (prefixWord ++ tailWord_6124311) baseStart_6124311 baseEnd_6124311 := by
    simpa [prefixWord, tailWord_6124311, baseEnd_6124311] using wordTrace_append hprefix tailTrace_6124311
  have hstable : (prefixWord ++ tailWord_6124311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124311).length < 2 ^ (prefixWord ++ tailWord_6124311).sum := by decide
  have hdescent : baseEnd_6124311 < baseStart_6124311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124373 : List Nat := [1, 3, 2, 2, 2, 1, 2, 3, 7]
def baseStart_6124373 : Nat := 118140960795 + 6124373 * 2 ^ 59
def prefixEnd_6124373 : Nat := 4983230072969 + 3 ^ 40 * 6124373 * 2
def baseEnd_6124373 : Nat := 349416339602030232908003

theorem tailTrace_6124373 : CollatzResearch.WordTrace tailWord_6124373 prefixEnd_6124373 349416339602030232908003 := by
  unfold tailWord_6124373
  simp only [CollatzResearch.WordTrace]
  refine ⟨223374234241450055480409773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148916156160966703653606515 223374234241450055480409773)
  ·
    refine ⟨83765337840543770805153665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223374234241450055480409773 83765337840543770805153665)
    ·
      refine ⟨62824003380407828103865249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83765337840543770805153665 62824003380407828103865249)
      ·
        refine ⟨47118002535305871077898937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62824003380407828103865249 47118002535305871077898937)
        ·
          refine ⟨35338501901479403308424203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47118002535305871077898937 35338501901479403308424203)
          ·
            refine ⟨53007752852219104962636305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35338501901479403308424203 53007752852219104962636305)
            ·
              refine ⟨39755814639164328721977229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53007752852219104962636305 39755814639164328721977229)
              ·
                refine ⟨14908430489686623270741461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39755814639164328721977229 14908430489686623270741461)
                ·
                  refine ⟨349416339602030232908003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14908430489686623270741461 349416339602030232908003)
                  ·
                    rfl

theorem cell23_6124373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 7].length) (baseStart_6124373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124373 prefixEnd_6124373 := by exact prefixLift 6124373
  have htrace : WordTrace (prefixWord ++ tailWord_6124373) baseStart_6124373 baseEnd_6124373 := by
    simpa [prefixWord, tailWord_6124373, baseEnd_6124373] using wordTrace_append hprefix tailTrace_6124373
  have hstable : (prefixWord ++ tailWord_6124373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124373).length < 2 ^ (prefixWord ++ tailWord_6124373).sum := by decide
  have hdescent : baseEnd_6124373 < baseStart_6124373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124380 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_6124380 : Nat := 118140960795 + 6124380 * 2 ^ 59
def prefixEnd_6124380 : Nat := 4983230072969 + 3 ^ 40 * 6124380 * 2
def baseEnd_6124380 : Nat := 3144750650782853568784495

theorem tailTrace_6124380 : CollatzResearch.WordTrace tailWord_6124380 prefixEnd_6124380 3144750650782853568784495 := by
  unfold tailWord_6124380
  simp only [CollatzResearch.WordTrace]
  refine ⟨111687244776212347837957297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148916326368283130450609729 111687244776212347837957297)
  ·
    refine ⟨83765433582159260878467973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111687244776212347837957297 83765433582159260878467973)
    ·
      refine ⟨15706018796654861414712745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83765433582159260878467973 15706018796654861414712745)
      ·
        refine ⟨11779514097491146061034559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15706018796654861414712745 11779514097491146061034559)
        ·
          refine ⟨17669271146236719091551839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11779514097491146061034559 17669271146236719091551839)
          ·
            refine ⟨26503906719355078637327759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17669271146236719091551839 26503906719355078637327759)
            ·
              refine ⟨39755860079032617955991639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26503906719355078637327759 39755860079032617955991639)
              ·
                refine ⟨59633790118548926933987459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39755860079032617955991639 59633790118548926933987459)
                ·
                  refine ⟨89450685177823390400981189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59633790118548926933987459 89450685177823390400981189)
                  ·
                    refine ⟨16772003470841885700183973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89450685177823390400981189 16772003470841885700183973)
                    ·
                      refine ⟨3144750650782853568784495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16772003470841885700183973 3144750650782853568784495)
                      ·
                        rfl

theorem cell23_6124380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_6124380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124380 prefixEnd_6124380 := by exact prefixLift 6124380
  have htrace : WordTrace (prefixWord ++ tailWord_6124380) baseStart_6124380 baseEnd_6124380 := by
    simpa [prefixWord, tailWord_6124380, baseEnd_6124380] using wordTrace_append hprefix tailTrace_6124380
  have hstable : (prefixWord ++ tailWord_6124380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124380).length < 2 ^ (prefixWord ++ tailWord_6124380).sum := by decide
  have hdescent : baseEnd_6124380 < baseStart_6124380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124413 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 3, 2, 5]
def baseStart_6124413 : Nat := 118140960795 + 6124413 * 2 ^ 59
def prefixEnd_6124413 : Nat := 4983230072969 + 3 ^ 40 * 6124413 * 2
def baseEnd_6124413 : Nat := 3144767595644451939671843

theorem tailTrace_6124413 : CollatzResearch.WordTrace tailWord_6124413 prefixEnd_6124413 3144767595644451939671843 := by
  unfold tailWord_6124413
  simp only [CollatzResearch.WordTrace]
  refine ⟨223375693161305142311865893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148917128774203428207910595 223375693161305142311865893)
  ·
    refine ⟨41882942467744714183474855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223375693161305142311865893 41882942467744714183474855)
    ·
      refine ⟨62824413701617071275212283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41882942467744714183474855 62824413701617071275212283)
      ·
        refine ⟨94236620552425606912818425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62824413701617071275212283 94236620552425606912818425)
        ·
          refine ⟨70677465414319205184613819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94236620552425606912818425 70677465414319205184613819)
          ·
            refine ⟨106016198121478807776920729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70677465414319205184613819 106016198121478807776920729)
            ·
              refine ⟨79512148591109105832690547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106016198121478807776920729 79512148591109105832690547)
              ·
                refine ⟨119268222886663658749035821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79512148591109105832690547 119268222886663658749035821)
                ·
                  refine ⟨44725583582498872030888433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119268222886663658749035821 44725583582498872030888433)
                  ·
                    refine ⟨33544187686874154023166325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44725583582498872030888433 33544187686874154023166325)
                    ·
                      refine ⟨3144767595644451939671843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33544187686874154023166325 3144767595644451939671843)
                      ·
                        rfl

theorem cell23_6124413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_6124413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124413 prefixEnd_6124413 := by exact prefixLift 6124413
  have htrace : WordTrace (prefixWord ++ tailWord_6124413) baseStart_6124413 baseEnd_6124413 := by
    simpa [prefixWord, tailWord_6124413, baseEnd_6124413] using wordTrace_append hprefix tailTrace_6124413
  have hstable : (prefixWord ++ tailWord_6124413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124413).length < 2 ^ (prefixWord ++ tailWord_6124413).sum := by decide
  have hdescent : baseEnd_6124413 < baseStart_6124413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124418 : List Nat := [3, 4, 2, 2, 1, 1, 1, 1, 4, 2, 2]
def baseStart_6124418 : Nat := 118140960795 + 6124418 * 2 ^ 59
def prefixEnd_6124418 : Nat := 4983230072969 + 3 ^ 40 * 6124418 * 2
def baseEnd_6124418 : Nat := 3144770163047724420109321

theorem tailTrace_6124418 : CollatzResearch.WordTrace tailWord_6124418 prefixEnd_6124418 3144770163047724420109321 := by
  unfold tailWord_6124418
  simp only [CollatzResearch.WordTrace]
  refine ⟨55843968881571757041449477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148917250350858018777198605 55843968881571757041449477)
  ·
    refine ⟨10470744165294704445271777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55843968881571757041449477 10470744165294704445271777)
    ·
      refine ⟨7853058123971028333953833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10470744165294704445271777 7853058123971028333953833)
      ·
        refine ⟨5889793592978271250465375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7853058123971028333953833 5889793592978271250465375)
        ·
          refine ⟨8834690389467406875698063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5889793592978271250465375 8834690389467406875698063)
          ·
            refine ⟨13252035584201110313547095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8834690389467406875698063 13252035584201110313547095)
            ·
              refine ⟨19878053376301665470320643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13252035584201110313547095 19878053376301665470320643)
              ·
                refine ⟨29817080064452498205480965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19878053376301665470320643 29817080064452498205480965)
                ·
                  refine ⟨5590702512084843413527681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29817080064452498205480965 5590702512084843413527681)
                  ·
                    refine ⟨4193026884063632560145761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5590702512084843413527681 4193026884063632560145761)
                    ·
                      refine ⟨3144770163047724420109321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4193026884063632560145761 3144770163047724420109321)
                      ·
                        rfl

theorem cell23_6124418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_6124418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124418 prefixEnd_6124418 := by exact prefixLift 6124418
  have htrace : WordTrace (prefixWord ++ tailWord_6124418) baseStart_6124418 baseEnd_6124418 := by
    simpa [prefixWord, tailWord_6124418, baseEnd_6124418] using wordTrace_append hprefix tailTrace_6124418
  have hstable : (prefixWord ++ tailWord_6124418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124418).length < 2 ^ (prefixWord ++ tailWord_6124418).sum := by decide
  have hdescent : baseEnd_6124418 < baseStart_6124418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124467 : List Nat := [1, 1, 1, 2, 3, 1, 2, 7, 1, 4]
def baseStart_6124467 : Nat := 118140960795 + 6124467 * 2 ^ 59
def prefixEnd_6124467 : Nat := 4983230072969 + 3 ^ 40 * 6124467 * 2
def baseEnd_6124467 : Nat := 1048265107866598242798865

theorem tailTrace_6124467 : CollatzResearch.WordTrace tailWord_6124467 prefixEnd_6124467 1048265107866598242798865 := by
  unfold tailWord_6124467
  simp only [CollatzResearch.WordTrace]
  refine ⟨223377662703109509534331655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148918441802073006356221103 223377662703109509534331655)
  ·
    refine ⟨335066494054664264301497483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223377662703109509534331655 335066494054664264301497483)
    ·
      refine ⟨502599741081996396452246225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335066494054664264301497483 502599741081996396452246225)
      ·
        refine ⟨376949805811497297339184669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 502599741081996396452246225 376949805811497297339184669)
        ·
          refine ⟨141356177179311486502194251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 376949805811497297339184669 141356177179311486502194251)
          ·
            refine ⟨212034265768967229753291377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141356177179311486502194251 212034265768967229753291377)
            ·
              refine ⟨159025699326725422314968533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212034265768967229753291377 159025699326725422314968533)
              ·
                refine ⟨3727164827970127085507075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 159025699326725422314968533 3727164827970127085507075)
                ·
                  refine ⟨5590747241955190628260613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3727164827970127085507075 5590747241955190628260613)
                  ·
                    refine ⟨1048265107866598242798865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5590747241955190628260613 1048265107866598242798865)
                    ·
                      rfl

theorem cell23_6124467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7, 1, 4].length) (baseStart_6124467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124467 prefixEnd_6124467 := by exact prefixLift 6124467
  have htrace : WordTrace (prefixWord ++ tailWord_6124467) baseStart_6124467 baseEnd_6124467 := by
    simpa [prefixWord, tailWord_6124467, baseEnd_6124467] using wordTrace_append hprefix tailTrace_6124467
  have hstable : (prefixWord ++ tailWord_6124467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124467).length < 2 ^ (prefixWord ++ tailWord_6124467).sum := by decide
  have hdescent : baseEnd_6124467 < baseStart_6124467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124486 : List Nat := [6, 1, 3, 1, 2, 1, 2, 1, 2, 2, 2]
def baseStart_6124486 : Nat := 118140960795 + 6124486 * 2 ^ 59
def prefixEnd_6124486 : Nat := 4983230072969 + 3 ^ 40 * 6124486 * 2
def baseEnd_6124486 : Nat := 3144805079732230154059009

theorem tailTrace_6124486 : CollatzResearch.WordTrace tailWord_6124486 prefixEnd_6124486 3144805079732230154059009 := by
  unfold tailWord_6124486
  simp only [CollatzResearch.WordTrace]
  refine ⟨6980573615313771118102291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 148918903793360450519515541 6980573615313771118102291)
  ·
    refine ⟨10470860422970656677153437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6980573615313771118102291 10470860422970656677153437)
    ·
      refine ⟨3926572658613996253932539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10470860422970656677153437 3926572658613996253932539)
      ·
        refine ⟨5889858987920994380898809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3926572658613996253932539 5889858987920994380898809)
        ·
          refine ⟨4417394240940745785674107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5889858987920994380898809 4417394240940745785674107)
          ·
            refine ⟨6626091361411118678511161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4417394240940745785674107 6626091361411118678511161)
            ·
              refine ⟨4969568521058339008883371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6626091361411118678511161 4969568521058339008883371)
              ·
                refine ⟨7454352781587508513325057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4969568521058339008883371 7454352781587508513325057)
                ·
                  refine ⟨5590764586190631384993793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7454352781587508513325057 5590764586190631384993793)
                  ·
                    refine ⟨4193073439642973538745345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5590764586190631384993793 4193073439642973538745345)
                    ·
                      refine ⟨3144805079732230154059009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4193073439642973538745345 3144805079732230154059009)
                      ·
                        rfl

theorem cell23_6124486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_6124486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124486 prefixEnd_6124486 := by exact prefixLift 6124486
  have htrace : WordTrace (prefixWord ++ tailWord_6124486) baseStart_6124486 baseEnd_6124486 := by
    simpa [prefixWord, tailWord_6124486, baseEnd_6124486] using wordTrace_append hprefix tailTrace_6124486
  have hstable : (prefixWord ++ tailWord_6124486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124486).length < 2 ^ (prefixWord ++ tailWord_6124486).sum := by decide
  have hdescent : baseEnd_6124486 < baseStart_6124486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124503 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 7]
def baseStart_6124503 : Nat := 118140960795 + 6124503 * 2 ^ 59
def prefixEnd_6124503 : Nat := 4983230072969 + 3 ^ 40 * 6124503 * 2
def baseEnd_6124503 : Nat := 3144813808903356587546429

theorem tailTrace_6124503 : CollatzResearch.WordTrace tailWord_6124503 prefixEnd_6124503 3144813808903356587546429 := by
  unfold tailWord_6124503
  simp only [CollatzResearch.WordTrace]
  refine ⟨223378975730979087682642163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148919317153986058455094775 223378975730979087682642163)
  ·
    refine ⟨335068463596468631523963245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223378975730979087682642163 335068463596468631523963245)
    ·
      refine ⟨125650673848675736821486217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335068463596468631523963245 125650673848675736821486217)
      ·
        refine ⟨94238005386506802616114663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125650673848675736821486217 94238005386506802616114663)
        ·
          refine ⟨141357008079760203924171995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94238005386506802616114663 141357008079760203924171995)
          ·
            refine ⟨212035512119640305886257993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141357008079760203924171995 212035512119640305886257993)
            ·
              refine ⟨159026634089730229414693495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212035512119640305886257993 159026634089730229414693495)
              ·
                refine ⟨238539951134595344122040243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159026634089730229414693495 238539951134595344122040243)
                ·
                  refine ⟨357809926701893016183060365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 238539951134595344122040243 357809926701893016183060365)
                  ·
                    refine ⟨134178722513209881068647637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 357809926701893016183060365 134178722513209881068647637)
                    ·
                      refine ⟨3144813808903356587546429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 134178722513209881068647637 3144813808903356587546429)
                      ·
                        rfl

theorem cell23_6124503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_6124503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124503 prefixEnd_6124503 := by exact prefixLift 6124503
  have htrace : WordTrace (prefixWord ++ tailWord_6124503) baseStart_6124503 baseEnd_6124503 := by
    simpa [prefixWord, tailWord_6124503, baseEnd_6124503] using wordTrace_append hprefix tailTrace_6124503
  have hstable : (prefixWord ++ tailWord_6124503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124503).length < 2 ^ (prefixWord ++ tailWord_6124503).sum := by decide
  have hdescent : baseEnd_6124503 < baseStart_6124503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124577 : List Nat := [1, 2, 3, 2, 3, 1, 2, 2, 1, 2, 4]
def baseStart_6124577 : Nat := 118140960795 + 6124577 * 2 ^ 59
def prefixEnd_6124577 : Nat := 4983230072969 + 3 ^ 40 * 6124577 * 2
def baseEnd_6124577 : Nat := 3144851806471789298021089

theorem tailTrace_6124577 : CollatzResearch.WordTrace tailWord_6124577 prefixEnd_6124577 3144851806471789298021089 := by
  unfold tailWord_6124577
  simp only [CollatzResearch.WordTrace]
  refine ⟨223381674732710998320835985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148921116488473998880557323 223381674732710998320835985)
  ·
    refine ⟨167536256049533248740626989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223381674732710998320835985 167536256049533248740626989)
    ·
      refine ⟨62826096018574968277735121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167536256049533248740626989 62826096018574968277735121)
      ·
        refine ⟨47119572013931226208301341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62826096018574968277735121 47119572013931226208301341)
        ·
          refine ⟨17669839505224209828113003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47119572013931226208301341 17669839505224209828113003)
          ·
            refine ⟨26504759257836314742169505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17669839505224209828113003 26504759257836314742169505)
            ·
              refine ⟨19878569443377236056627129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26504759257836314742169505 19878569443377236056627129)
              ·
                refine ⟨14908927082532927042470347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19878569443377236056627129 14908927082532927042470347)
                ·
                  refine ⟨22363390623799390563705521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14908927082532927042470347 22363390623799390563705521)
                  ·
                    refine ⟨16772542967849542922779141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22363390623799390563705521 16772542967849542922779141)
                    ·
                      refine ⟨3144851806471789298021089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16772542967849542922779141 3144851806471789298021089)
                      ·
                        rfl

theorem cell23_6124577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_6124577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124577 prefixEnd_6124577 := by exact prefixLift 6124577
  have htrace : WordTrace (prefixWord ++ tailWord_6124577) baseStart_6124577 baseEnd_6124577 := by
    simpa [prefixWord, tailWord_6124577, baseEnd_6124577] using wordTrace_append hprefix tailTrace_6124577
  have hstable : (prefixWord ++ tailWord_6124577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124577).length < 2 ^ (prefixWord ++ tailWord_6124577).sum := by decide
  have hdescent : baseEnd_6124577 < baseStart_6124577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124598 : List Nat := [5, 1, 2, 1, 1, 3, 2, 1, 3, 2, 2]
def baseStart_6124598 : Nat := 118140960795 + 6124598 * 2 ^ 59
def prefixEnd_6124598 : Nat := 4983230072969 + 3 ^ 40 * 6124598 * 2
def baseEnd_6124598 : Nat := 3144862589565533715858493

theorem tailTrace_6124598 : CollatzResearch.WordTrace tailWord_6124598 prefixEnd_6124598 3144862589565533715858493 := by
  unfold tailWord_6124598
  simp only [CollatzResearch.WordTrace]
  refine ⟨13961402541602182431709403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148921627110423279271566965 13961402541602182431709403)
  ·
    refine ⟨20942103812403273647564105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13961402541602182431709403 20942103812403273647564105)
    ·
      refine ⟨15706577859302455235673079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20942103812403273647564105 15706577859302455235673079)
      ·
        refine ⟨23559866788953682853509619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15706577859302455235673079 23559866788953682853509619)
        ·
          refine ⟨35339800183430524280264429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23559866788953682853509619 35339800183430524280264429)
          ·
            refine ⟨13252425068786446605099161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35339800183430524280264429 13252425068786446605099161)
            ·
              refine ⟨9939318801589834953824371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13252425068786446605099161 9939318801589834953824371)
              ·
                refine ⟨14908978202384752430736557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9939318801589834953824371 14908978202384752430736557)
                ·
                  refine ⟨5590866825894282161526209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14908978202384752430736557 5590866825894282161526209)
                  ·
                    refine ⟨4193150119420711621144657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5590866825894282161526209 4193150119420711621144657)
                    ·
                      refine ⟨3144862589565533715858493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4193150119420711621144657 3144862589565533715858493)
                      ·
                        rfl

theorem cell23_6124598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_6124598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124598 prefixEnd_6124598 := by exact prefixLift 6124598
  have htrace : WordTrace (prefixWord ++ tailWord_6124598) baseStart_6124598 baseEnd_6124598 := by
    simpa [prefixWord, tailWord_6124598, baseEnd_6124598] using wordTrace_append hprefix tailTrace_6124598
  have hstable : (prefixWord ++ tailWord_6124598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124598).length < 2 ^ (prefixWord ++ tailWord_6124598).sum := by decide
  have hdescent : baseEnd_6124598 < baseStart_6124598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124665 : List Nat := [1, 2, 1, 3, 6, 1, 2, 1, 2, 1, 3]
def baseStart_6124665 : Nat := 118140960795 + 6124665 * 2 ^ 59
def prefixEnd_6124665 : Nat := 4983230072969 + 3 ^ 40 * 6124665 * 2
def baseEnd_6124665 : Nat := 3144896992769384953720685

theorem tailTrace_6124665 : CollatzResearch.WordTrace tailWord_6124665 prefixEnd_6124665 3144896992769384953720685 := by
  unfold tailWord_6124665
  simp only [CollatzResearch.WordTrace]
  refine ⟨223384884356392189350039449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148923256237594792900026299 223384884356392189350039449)
  ·
    refine ⟨167538663267294142012529587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223384884356392189350039449 167538663267294142012529587)
    ·
      refine ⟨251307994900941213018794381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167538663267294142012529587 251307994900941213018794381)
      ·
        refine ⟨94240498087852954882047893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251307994900941213018794381 94240498087852954882047893)
        ·
          refine ⟨4417523347868107260095995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 94240498087852954882047893 4417523347868107260095995)
          ·
            refine ⟨6626285021802160890143993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4417523347868107260095995 6626285021802160890143993)
            ·
              refine ⟨4969713766351620667607995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6626285021802160890143993 4969713766351620667607995)
              ·
                refine ⟨7454570649527431001411993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4969713766351620667607995 7454570649527431001411993)
                ·
                  refine ⟨5590927987145573251058995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7454570649527431001411993 5590927987145573251058995)
                  ·
                    refine ⟨8386391980718359876588493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5590927987145573251058995 8386391980718359876588493)
                    ·
                      refine ⟨3144896992769384953720685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8386391980718359876588493 3144896992769384953720685)
                      ·
                        rfl

theorem cell23_6124665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 2, 1, 3].length) (baseStart_6124665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124665 prefixEnd_6124665 := by exact prefixLift 6124665
  have htrace : WordTrace (prefixWord ++ tailWord_6124665) baseStart_6124665 baseEnd_6124665 := by
    simpa [prefixWord, tailWord_6124665, baseEnd_6124665] using wordTrace_append hprefix tailTrace_6124665
  have hstable : (prefixWord ++ tailWord_6124665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124665).length < 2 ^ (prefixWord ++ tailWord_6124665).sum := by decide
  have hdescent : baseEnd_6124665 < baseStart_6124665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124711 : List Nat := [1, 1, 6, 2, 1, 2, 1, 4, 5]
def baseStart_6124711 : Nat := 118140960795 + 6124711 * 2 ^ 59
def prefixEnd_6124711 : Nat := 4983230072969 + 3 ^ 40 * 6124711 * 2
def baseEnd_6124711 : Nat := 349435623653276863749497

theorem tailTrace_6124711 : CollatzResearch.WordTrace tailWord_6124711 prefixEnd_6124711 349435623653276863749497 := by
  unfold tailWord_6124711
  simp only [CollatzResearch.WordTrace]
  refine ⟨223386562114225539206213987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148924374742817026137475991 223386562114225539206213987)
  ·
    refine ⟨335079843171338308809320981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223386562114225539206213987 335079843171338308809320981)
    ·
      refine ⟨15706867648656483225436921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 335079843171338308809320981 15706867648656483225436921)
      ·
        refine ⟨11780150736492362419077691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15706867648656483225436921 11780150736492362419077691)
        ·
          refine ⟨17670226104738543628616537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11780150736492362419077691 17670226104738543628616537)
          ·
            refine ⟨13252669578553907721462403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17670226104738543628616537 13252669578553907721462403)
            ·
              refine ⟨19879004367830861582193605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13252669578553907721462403 19879004367830861582193605)
              ·
                refine ⟨3727313318968286546661301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19879004367830861582193605 3727313318968286546661301)
                ·
                  refine ⟨349435623653276863749497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3727313318968286546661301 349435623653276863749497)
                  ·
                    rfl

theorem cell23_6124711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4, 5].length) (baseStart_6124711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124711 prefixEnd_6124711 := by exact prefixLift 6124711
  have htrace : WordTrace (prefixWord ++ tailWord_6124711) baseStart_6124711 baseEnd_6124711 := by
    simpa [prefixWord, tailWord_6124711, baseEnd_6124711] using wordTrace_append hprefix tailTrace_6124711
  have hstable : (prefixWord ++ tailWord_6124711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124711).length < 2 ^ (prefixWord ++ tailWord_6124711).sum := by decide
  have hdescent : baseEnd_6124711 < baseStart_6124711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124727 : List Nat := [1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 4]
def baseStart_6124727 : Nat := 118140960795 + 6124727 * 2 ^ 59
def prefixEnd_6124727 : Nat := 4983230072969 + 3 ^ 40 * 6124727 * 2
def baseEnd_6124727 : Nat := 3144928828569963711145399

theorem tailTrace_6124727 : CollatzResearch.WordTrace tailWord_6124727 prefixEnd_6124727 3144928828569963711145399 := by
  unfold tailWord_6124727
  simp only [CollatzResearch.WordTrace]
  refine ⟨223387145682167573938796435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148924763788111715959197623 223387145682167573938796435)
  ·
    refine ⟨335080718523251360908194653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223387145682167573938796435 335080718523251360908194653)
    ·
      refine ⟨125655269446219260340572995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335080718523251360908194653 125655269446219260340572995)
      ·
        refine ⟨188482904169328890510859493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125655269446219260340572995 188482904169328890510859493)
        ·
          refine ⟨35340544531749166970786155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188482904169328890510859493 35340544531749166970786155)
          ·
            refine ⟨53010816797623750456179233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35340544531749166970786155 53010816797623750456179233)
            ·
              refine ⟨39758112598217812842134425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53010816797623750456179233 39758112598217812842134425)
              ·
                refine ⟨29818584448663359631600819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39758112598217812842134425 29818584448663359631600819)
                ·
                  refine ⟨44727876672995039447401229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29818584448663359631600819 44727876672995039447401229)
                  ·
                    refine ⟨16772953752373139792775461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44727876672995039447401229 16772953752373139792775461)
                    ·
                      refine ⟨3144928828569963711145399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16772953752373139792775461 3144928828569963711145399)
                      ·
                        rfl

theorem cell23_6124727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_6124727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124727 prefixEnd_6124727 := by exact prefixLift 6124727
  have htrace : WordTrace (prefixWord ++ tailWord_6124727) baseStart_6124727 baseEnd_6124727 := by
    simpa [prefixWord, tailWord_6124727, baseEnd_6124727] using wordTrace_append hprefix tailTrace_6124727
  have hstable : (prefixWord ++ tailWord_6124727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124727).length < 2 ^ (prefixWord ++ tailWord_6124727).sum := by decide
  have hdescent : baseEnd_6124727 < baseStart_6124727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124744 : List Nat := [2, 1, 3, 1, 2, 1, 5, 1, 2, 1, 4]
def baseStart_6124744 : Nat := 118140960795 + 6124744 * 2 ^ 59
def prefixEnd_6124744 : Nat := 4983230072969 + 3 ^ 40 * 6124744 * 2
def baseEnd_6124744 : Nat := 3144937557741090144632821

theorem tailTrace_6124744 : CollatzResearch.WordTrace tailWord_6124744 prefixEnd_6124744 3144937557741090144632821 := by
  unfold tailWord_6124744
  simp only [CollatzResearch.WordTrace]
  refine ⟨111693882861552992921082643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148925177148737323894776857 111693882861552992921082643)
  ·
    refine ⟨167540824292329489381623965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111693882861552992921082643 167540824292329489381623965)
    ·
      refine ⟨62827809109623558518108987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167540824292329489381623965 62827809109623558518108987)
      ·
        refine ⟨94241713664435337777163481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62827809109623558518108987 94241713664435337777163481)
        ·
          refine ⟨70681285248326503332872611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94241713664435337777163481 70681285248326503332872611)
          ·
            refine ⟨106021927872489754999308917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70681285248326503332872611 106021927872489754999308917)
            ·
              refine ⟨9939555738045914531185211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106021927872489754999308917 9939555738045914531185211)
              ·
                refine ⟨14909333607068871796777817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9939555738045914531185211 14909333607068871796777817)
                ·
                  refine ⟨11182000205301653847583363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14909333607068871796777817 11182000205301653847583363)
                  ·
                    refine ⟨16773000307952480771375045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11182000205301653847583363 16773000307952480771375045)
                    ·
                      refine ⟨3144937557741090144632821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16773000307952480771375045 3144937557741090144632821)
                      ·
                        rfl

theorem cell23_6124744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_6124744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124744 prefixEnd_6124744 := by exact prefixLift 6124744
  have htrace : WordTrace (prefixWord ++ tailWord_6124744) baseStart_6124744 baseEnd_6124744 := by
    simpa [prefixWord, tailWord_6124744, baseEnd_6124744] using wordTrace_append hprefix tailTrace_6124744
  have hstable : (prefixWord ++ tailWord_6124744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124744).length < 2 ^ (prefixWord ++ tailWord_6124744).sum := by decide
  have hdescent : baseEnd_6124744 < baseStart_6124744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124754 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 5, 4]
def baseStart_6124754 : Nat := 118140960795 + 6124754 * 2 ^ 59
def prefixEnd_6124754 : Nat := 4983230072969 + 3 ^ 40 * 6124754 * 2
def baseEnd_6124754 : Nat := 1048314230849211701835925

theorem tailTrace_6124754 : CollatzResearch.WordTrace tailWord_6124754 prefixEnd_6124754 1048314230849211701835925 := by
  unfold tailWord_6124754
  simp only [CollatzResearch.WordTrace]
  refine ⟨55847032613267439387507329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148925420302046505033352877 55847032613267439387507329)
  ·
    refine ⟨41885274459950579540630497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55847032613267439387507329 41885274459950579540630497)
    ·
      refine ⟨31413955844962934655472873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41885274459950579540630497 31413955844962934655472873)
      ·
        refine ⟨23560466883722200991604655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31413955844962934655472873 23560466883722200991604655)
        ·
          refine ⟨35340700325583301487406983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23560466883722200991604655 35340700325583301487406983)
          ·
            refine ⟨53011050488374952231110475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35340700325583301487406983 53011050488374952231110475)
            ·
              refine ⟨79516575732562428346665713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53011050488374952231110475 79516575732562428346665713)
              ·
                refine ⟨59637431799421821259999285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79516575732562428346665713 59637431799421821259999285)
                ·
                  refine ⟨5591009231195795743124933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59637431799421821259999285 5591009231195795743124933)
                  ·
                    refine ⟨1048314230849211701835925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5591009231195795743124933 1048314230849211701835925)
                    ·
                      rfl

theorem cell23_6124754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_6124754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124754 prefixEnd_6124754 := by exact prefixLift 6124754
  have htrace : WordTrace (prefixWord ++ tailWord_6124754) baseStart_6124754 baseEnd_6124754 := by
    simpa [prefixWord, tailWord_6124754, baseEnd_6124754] using wordTrace_append hprefix tailTrace_6124754
  have hstable : (prefixWord ++ tailWord_6124754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124754).length < 2 ^ (prefixWord ++ tailWord_6124754).sum := by decide
  have hdescent : baseEnd_6124754 < baseStart_6124754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124777 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 4, 5, 3]
def baseStart_6124777 : Nat := 118140960795 + 6124777 * 2 ^ 59
def prefixEnd_6124777 : Nat := 4983230072969 + 3 ^ 40 * 6124777 * 2
def baseEnd_6124777 : Nat := 3144954502602688515520169

theorem tailTrace_6124777 : CollatzResearch.WordTrace tailWord_6124777 prefixEnd_6124777 3144954502602688515520169 := by
  unfold tailWord_6124777
  simp only [CollatzResearch.WordTrace]
  refine ⟨223388969331986432478116585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148925979554657621652077723 223388969331986432478116585)
  ·
    refine ⟨167541726998989824358587439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223388969331986432478116585 167541726998989824358587439)
    ·
      refine ⟨251312590498484736537881159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167541726998989824358587439 251312590498484736537881159)
      ·
        refine ⟨376968885747727104806821739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251312590498484736537881159 376968885747727104806821739)
        ·
          refine ⟨565453328621590657210232609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376968885747727104806821739 565453328621590657210232609)
          ·
            refine ⟨424089996466192992907674457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 565453328621590657210232609 424089996466192992907674457)
            ·
              refine ⟨318067497349644744680755843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 424089996466192992907674457 318067497349644744680755843)
              ·
                refine ⟨477101246024467117021133765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318067497349644744680755843 477101246024467117021133765)
                ·
                  refine ⟨89456483629587584441462581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 477101246024467117021133765 89456483629587584441462581)
                  ·
                    refine ⟨8386545340273836041387117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 89456483629587584441462581 8386545340273836041387117)
                    ·
                      refine ⟨3144954502602688515520169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8386545340273836041387117 3144954502602688515520169)
                      ·
                        rfl

theorem cell23_6124777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 5, 3].length) (baseStart_6124777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124777 prefixEnd_6124777 := by exact prefixLift 6124777
  have htrace : WordTrace (prefixWord ++ tailWord_6124777) baseStart_6124777 baseEnd_6124777 := by
    simpa [prefixWord, tailWord_6124777, baseEnd_6124777] using wordTrace_append hprefix tailTrace_6124777
  have hstable : (prefixWord ++ tailWord_6124777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124777).length < 2 ^ (prefixWord ++ tailWord_6124777).sum := by decide
  have hdescent : baseEnd_6124777 < baseStart_6124777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124828 : List Nat := [2, 2, 3, 1, 1, 1, 2, 6, 1, 1, 3]
def baseStart_6124828 : Nat := 118140960795 + 6124828 * 2 ^ 59
def prefixEnd_6124828 : Nat := 4983230072969 + 3 ^ 40 * 6124828 * 2
def baseEnd_6124828 : Nat := 3144980690116067815982435

theorem tailTrace_6124828 : CollatzResearch.WordTrace tailWord_6124828 prefixEnd_6124828 3144980690116067815982435 := by
  unfold tailWord_6124828
  simp only [CollatzResearch.WordTrace]
  refine ⟨111695414727400834094111569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148927219636534445458815425 111695414727400834094111569)
  ·
    refine ⟨83771561045550625570583677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111695414727400834094111569 83771561045550625570583677)
    ·
      refine ⟨31414335392081484588968879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83771561045550625570583677 31414335392081484588968879)
      ·
        refine ⟨47121503088122226883453319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31414335392081484588968879 47121503088122226883453319)
        ·
          refine ⟨70682254632183340325179979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47121503088122226883453319 70682254632183340325179979)
          ·
            refine ⟨106023381948275010487769969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70682254632183340325179979 106023381948275010487769969)
            ·
              refine ⟨79517536461206257865827477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106023381948275010487769969 79517536461206257865827477)
              ·
                refine ⟨3727384521619043337460663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79517536461206257865827477 3727384521619043337460663)
                ·
                  refine ⟨5591076782428565006190995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3727384521619043337460663 5591076782428565006190995)
                  ·
                    refine ⟨8386615173642847509286493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5591076782428565006190995 8386615173642847509286493)
                    ·
                      refine ⟨3144980690116067815982435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8386615173642847509286493 3144980690116067815982435)
                      ·
                        rfl

theorem cell23_6124828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_6124828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124828 prefixEnd_6124828 := by exact prefixLift 6124828
  have htrace : WordTrace (prefixWord ++ tailWord_6124828) baseStart_6124828 baseEnd_6124828 := by
    simpa [prefixWord, tailWord_6124828, baseEnd_6124828] using wordTrace_append hprefix tailTrace_6124828
  have hstable : (prefixWord ++ tailWord_6124828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124828).length < 2 ^ (prefixWord ++ tailWord_6124828).sum := by decide
  have hdescent : baseEnd_6124828 < baseStart_6124828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124851 : List Nat := [1, 1, 1, 2, 5, 2, 3, 2, 1, 1, 4]
def baseStart_6124851 : Nat := 118140960795 + 6124851 * 2 ^ 59
def prefixEnd_6124851 : Nat := 4983230072969 + 3 ^ 40 * 6124851 * 2
def baseEnd_6124851 : Nat := 3144992500171121225994829

theorem tailTrace_6124851 : CollatzResearch.WordTrace tailWord_6124851 prefixEnd_6124851 3144992500171121225994829 := by
  unfold tailWord_6124851
  simp only [CollatzResearch.WordTrace]
  refine ⟨223391668333718343116310407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148927778889145562077540271 223391668333718343116310407)
  ·
    refine ⟨335087502500577514674465611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223391668333718343116310407 335087502500577514674465611)
    ·
      refine ⟨502631253750866272011698417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335087502500577514674465611 502631253750866272011698417)
      ·
        refine ⟨376973440313149704008773813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 502631253750866272011698417 376973440313149704008773813)
        ·
          refine ⟨35341260029357784750822545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 376973440313149704008773813 35341260029357784750822545)
          ·
            refine ⟨26505945022018338563116909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35341260029357784750822545 26505945022018338563116909)
            ·
              refine ⟨9939729383256876961168841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26505945022018338563116909 9939729383256876961168841)
              ·
                refine ⟨7454797037442657720876631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9939729383256876961168841 7454797037442657720876631)
                ·
                  refine ⟨11182195556163986581314947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7454797037442657720876631 11182195556163986581314947)
                  ·
                    refine ⟨16773293334245979871972421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11182195556163986581314947 16773293334245979871972421)
                    ·
                      refine ⟨3144992500171121225994829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16773293334245979871972421 3144992500171121225994829)
                      ·
                        rfl

theorem cell23_6124851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 1, 4].length) (baseStart_6124851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124851 prefixEnd_6124851 := by exact prefixLift 6124851
  have htrace : WordTrace (prefixWord ++ tailWord_6124851) baseStart_6124851 baseEnd_6124851 := by
    simpa [prefixWord, tailWord_6124851, baseEnd_6124851] using wordTrace_append hprefix tailTrace_6124851
  have hstable : (prefixWord ++ tailWord_6124851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124851).length < 2 ^ (prefixWord ++ tailWord_6124851).sum := by decide
  have hdescent : baseEnd_6124851 < baseStart_6124851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124864 : List Nat := [2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 4]
def baseStart_6124864 : Nat := 118140960795 + 6124864 * 2 ^ 59
def prefixEnd_6124864 : Nat := 4983230072969 + 3 ^ 40 * 6124864 * 2
def baseEnd_6124864 : Nat := 3144999175419629675132269

theorem tailTrace_6124864 : CollatzResearch.WordTrace tailWord_6124864 prefixEnd_6124864 3144999175419629675132269 := by
  unfold tailWord_6124864
  simp only [CollatzResearch.WordTrace]
  refine ⟨111696071241335623168266823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148928094988447497557689097 111696071241335623168266823)
  ·
    refine ⟨167544106862003434752400235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111696071241335623168266823 167544106862003434752400235)
    ·
      refine ⟨251316160293005152128600353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167544106862003434752400235 251316160293005152128600353)
      ·
        refine ⟨188487120219753864096450265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251316160293005152128600353 188487120219753864096450265)
        ·
          refine ⟨141365340164815398072337699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188487120219753864096450265 141365340164815398072337699)
          ·
            refine ⟨212048010247223097108506549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141365340164815398072337699 212048010247223097108506549)
            ·
              refine ⟨19879500960677165353922489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 212048010247223097108506549 19879500960677165353922489)
              ·
                refine ⟨14909625720507874015441867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19879500960677165353922489 14909625720507874015441867)
                ·
                  refine ⟨22364438580761811023162801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14909625720507874015441867 22364438580761811023162801)
                  ·
                    refine ⟨16773328935571358267372101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22364438580761811023162801 16773328935571358267372101)
                    ·
                      refine ⟨3144999175419629675132269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16773328935571358267372101 3144999175419629675132269)
                      ·
                        rfl

theorem cell23_6124864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_6124864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124864 prefixEnd_6124864 := by exact prefixLift 6124864
  have htrace : WordTrace (prefixWord ++ tailWord_6124864) baseStart_6124864 baseEnd_6124864 := by
    simpa [prefixWord, tailWord_6124864, baseEnd_6124864] using wordTrace_append hprefix tailTrace_6124864
  have hstable : (prefixWord ++ tailWord_6124864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124864).length < 2 ^ (prefixWord ++ tailWord_6124864).sum := by decide
  have hdescent : baseEnd_6124864 < baseStart_6124864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124871 : List Nat := [1, 1, 4, 1, 2, 5, 1, 1, 1, 1, 5]
def baseStart_6124871 : Nat := 118140960795 + 6124871 * 2 ^ 59
def prefixEnd_6124871 : Nat := 4983230072969 + 3 ^ 40 * 6124871 * 2
def baseEnd_6124871 : Nat := 3145002769784211147744737

theorem tailTrace_6124871 : CollatzResearch.WordTrace tailWord_6124871 prefixEnd_6124871 3145002769784211147744737 := by
  unfold tailWord_6124871
  simp only [CollatzResearch.WordTrace]
  refine ⟨223392397793645886532038467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148928265195763924354692311 223392397793645886532038467)
  ·
    refine ⟨335088596690468829798057701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223392397793645886532038467 335088596690468829798057701)
    ·
      refine ⟨62829111879462905587135819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 335088596690468829798057701 62829111879462905587135819)
      ·
        refine ⟨94243667819194358380703729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62829111879462905587135819 94243667819194358380703729)
        ·
          refine ⟨70682750864395768785527797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94243667819194358380703729 70682750864395768785527797)
          ·
            refine ⟨6626507893537103323643231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70682750864395768785527797 6626507893537103323643231)
            ·
              refine ⟨9939761840305654985464847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6626507893537103323643231 9939761840305654985464847)
              ·
                refine ⟨14909642760458482478197271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9939761840305654985464847 14909642760458482478197271)
                ·
                  refine ⟨22364464140687723717295907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14909642760458482478197271 22364464140687723717295907)
                  ·
                    refine ⟨33546696211031585575943861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22364464140687723717295907 33546696211031585575943861)
                    ·
                      refine ⟨3145002769784211147744737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33546696211031585575943861 3145002769784211147744737)
                      ·
                        rfl

theorem cell23_6124871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_6124871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124871 prefixEnd_6124871 := by exact prefixLift 6124871
  have htrace : WordTrace (prefixWord ++ tailWord_6124871) baseStart_6124871 baseEnd_6124871 := by
    simpa [prefixWord, tailWord_6124871, baseEnd_6124871] using wordTrace_append hprefix tailTrace_6124871
  have hstable : (prefixWord ++ tailWord_6124871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124871).length < 2 ^ (prefixWord ++ tailWord_6124871).sum := by decide
  have hdescent : baseEnd_6124871 < baseStart_6124871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124901 : List Nat := [1, 3, 1, 3, 1, 2, 4, 1, 1, 3, 3]
def baseStart_6124901 : Nat := 118140960795 + 6124901 * 2 ^ 59
def prefixEnd_6124901 : Nat := 4983230072969 + 3 ^ 40 * 6124901 * 2
def baseEnd_6124901 : Nat := 3145018174203846030369599

theorem tailTrace_6124901 : CollatzResearch.WordTrace tailWord_6124901 prefixEnd_6124901 3145018174203846030369599 := by
  unfold tailWord_6124901
  simp only [CollatzResearch.WordTrace]
  refine ⟨223393491983537201655630557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148928994655691467770420371 223393491983537201655630557)
  ·
    refine ⟨83772559493826450620861459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223393491983537201655630557 83772559493826450620861459)
    ·
      refine ⟨125658839240739675931292189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83772559493826450620861459 125658839240739675931292189)
      ·
        refine ⟨47122064715277378474234571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125658839240739675931292189 47122064715277378474234571)
        ·
          refine ⟨70683097072916067711351857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47122064715277378474234571 70683097072916067711351857)
          ·
            refine ⟨53012322804687050783513893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70683097072916067711351857 53012322804687050783513893)
            ·
              refine ⟨9939810525878822021908855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53012322804687050783513893 9939810525878822021908855)
              ·
                refine ⟨14909715788818233032863283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9939810525878822021908855 14909715788818233032863283)
                ·
                  refine ⟨22364573683227349549294925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14909715788818233032863283 22364573683227349549294925)
                  ·
                    refine ⟨8386715131210256080985597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22364573683227349549294925 8386715131210256080985597)
                    ·
                      refine ⟨3145018174203846030369599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8386715131210256080985597 3145018174203846030369599)
                      ·
                        rfl

theorem cell23_6124901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_6124901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124901 prefixEnd_6124901 := by exact prefixLift 6124901
  have htrace : WordTrace (prefixWord ++ tailWord_6124901) baseStart_6124901 baseEnd_6124901 := by
    simpa [prefixWord, tailWord_6124901, baseEnd_6124901] using wordTrace_append hprefix tailTrace_6124901
  have hstable : (prefixWord ++ tailWord_6124901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124901).length < 2 ^ (prefixWord ++ tailWord_6124901).sum := by decide
  have hdescent : baseEnd_6124901 < baseStart_6124901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124907 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 10]
def baseStart_6124907 : Nat := 118140960795 + 6124907 * 2 ^ 59
def prefixEnd_6124907 : Nat := 4983230072969 + 3 ^ 40 * 6124907 * 2
def baseEnd_6124907 : Nat := 3145021255087773006894571

theorem tailTrace_6124907 : CollatzResearch.WordTrace tailWord_6124907 prefixEnd_6124907 3145021255087773006894571 := by
  unfold tailWord_6124907
  simp only [CollatzResearch.WordTrace]
  refine ⟨223393710821515464680348975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148929140547676976453565983 223393710821515464680348975)
  ·
    refine ⟨335090566232273197020523463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223393710821515464680348975 335090566232273197020523463)
    ·
      refine ⟨502635849348409795530785195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335090566232273197020523463 502635849348409795530785195)
      ·
        refine ⟨753953774022614693296177793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502635849348409795530785195 753953774022614693296177793)
        ·
          refine ⟨565465330516961019972133345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 753953774022614693296177793 565465330516961019972133345)
          ·
            refine ⟨424098997887720764979100009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 565465330516961019972133345 424098997887720764979100009)
            ·
              refine ⟨318074248415790573734325007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 424098997887720764979100009 318074248415790573734325007)
              ·
                refine ⟨477111372623685860601487511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318074248415790573734325007 477111372623685860601487511)
                ·
                  refine ⟨715667058935528790902231267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 477111372623685860601487511 715667058935528790902231267)
                  ·
                    refine ⟨1073500588403293186353346901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 715667058935528790902231267 1073500588403293186353346901)
                    ·
                      refine ⟨3145021255087773006894571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1073500588403293186353346901 3145021255087773006894571)
                      ·
                        rfl

theorem cell23_6124907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 10].length) (baseStart_6124907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124907 prefixEnd_6124907 := by exact prefixLift 6124907
  have htrace : WordTrace (prefixWord ++ tailWord_6124907) baseStart_6124907 baseEnd_6124907 := by
    simpa [prefixWord, tailWord_6124907, baseEnd_6124907] using wordTrace_append hprefix tailTrace_6124907
  have hstable : (prefixWord ++ tailWord_6124907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124907).length < 2 ^ (prefixWord ++ tailWord_6124907).sum := by decide
  have hdescent : baseEnd_6124907 < baseStart_6124907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124911 : List Nat := [1, 1, 2, 1, 3, 1, 3, 3, 3, 3, 2]
def baseStart_6124911 : Nat := 118140960795 + 6124911 * 2 ^ 59
def prefixEnd_6124911 : Nat := 4983230072969 + 3 ^ 40 * 6124911 * 2
def baseEnd_6124911 : Nat := 3145023309010390991244553

theorem tailTrace_6124911 : CollatzResearch.WordTrace tailWord_6124911 prefixEnd_6124911 3145023309010390991244553 := by
  unfold tailWord_6124911
  simp only [CollatzResearch.WordTrace]
  refine ⟨223393856713500973363494587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148929237809000648908996391 223393856713500973363494587)
  ·
    refine ⟨335090785070251460045241881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223393856713500973363494587 335090785070251460045241881)
    ·
      refine ⟨251318088802688595033931411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335090785070251460045241881 251318088802688595033931411)
      ·
        refine ⟨376977133204032892550897117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251318088802688595033931411 376977133204032892550897117)
        ·
          refine ⟨141366424951512334706586419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 376977133204032892550897117 141366424951512334706586419)
          ·
            refine ⟨212049637427268502059879629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141366424951512334706586419 212049637427268502059879629)
            ·
              refine ⟨79518614035225688272454861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212049637427268502059879629 79518614035225688272454861)
              ·
                refine ⟨29819480263209633102170573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79518614035225688272454861 29819480263209633102170573)
                ·
                  refine ⟨11182305098703612413313965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29819480263209633102170573 11182305098703612413313965)
                  ·
                    refine ⟨4193364412013854654992737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11182305098703612413313965 4193364412013854654992737)
                    ·
                      refine ⟨3145023309010390991244553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4193364412013854654992737 3145023309010390991244553)
                      ·
                        rfl

theorem cell23_6124911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 3, 2].length) (baseStart_6124911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124911 prefixEnd_6124911 := by exact prefixLift 6124911
  have htrace : WordTrace (prefixWord ++ tailWord_6124911) baseStart_6124911 baseEnd_6124911 := by
    simpa [prefixWord, tailWord_6124911, baseEnd_6124911] using wordTrace_append hprefix tailTrace_6124911
  have hstable : (prefixWord ++ tailWord_6124911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124911).length < 2 ^ (prefixWord ++ tailWord_6124911).sum := by decide
  have hdescent : baseEnd_6124911 < baseStart_6124911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124914 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 2, 2, 5]
def baseStart_6124914 : Nat := 118140960795 + 6124914 * 2 ^ 59
def prefixEnd_6124914 : Nat := 4983230072969 + 3 ^ 40 * 6124914 * 2
def baseEnd_6124914 : Nat := 3145024849452354479507039

theorem tailTrace_6124914 : CollatzResearch.WordTrace tailWord_6124914 prefixEnd_6124914 3145024849452354479507039 := by
  unfold tailWord_6124914
  simp only [CollatzResearch.WordTrace]
  refine ⟨55848491533122526218963449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148929310754993403250569197 55848491533122526218963449)
  ·
    refine ⟨41886368649841894664222587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55848491533122526218963449 41886368649841894664222587)
    ·
      refine ⟨62829552974762841996333881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41886368649841894664222587 62829552974762841996333881)
      ·
        refine ⟨47122164731072131497250411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62829552974762841996333881 47122164731072131497250411)
        ·
          refine ⟨70683247096608197245875617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47122164731072131497250411 70683247096608197245875617)
          ·
            refine ⟨53012435322456147934406713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70683247096608197245875617 53012435322456147934406713)
            ·
              refine ⟨39759326491842110950805035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53012435322456147934406713 39759326491842110950805035)
              ·
                refine ⟨59638989737763166426207553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39759326491842110950805035 59638989737763166426207553)
                ·
                  refine ⟨44729242303322374819655665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59638989737763166426207553 44729242303322374819655665)
                  ·
                    refine ⟨33546931727491781114741749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44729242303322374819655665 33546931727491781114741749)
                    ·
                      refine ⟨3145024849452354479507039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33546931727491781114741749 3145024849452354479507039)
                      ·
                        rfl

theorem cell23_6124914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_6124914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124914 prefixEnd_6124914 := by exact prefixLift 6124914
  have htrace : WordTrace (prefixWord ++ tailWord_6124914) baseStart_6124914 baseEnd_6124914 := by
    simpa [prefixWord, tailWord_6124914, baseEnd_6124914] using wordTrace_append hprefix tailTrace_6124914
  have hstable : (prefixWord ++ tailWord_6124914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124914).length < 2 ^ (prefixWord ++ tailWord_6124914).sum := by decide
  have hdescent : baseEnd_6124914 < baseStart_6124914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124935 : List Nat := [1, 1, 4, 2, 2, 4, 1, 2, 2, 1, 3]
def baseStart_6124935 : Nat := 118140960795 + 6124935 * 2 ^ 59
def prefixEnd_6124935 : Nat := 4983230072969 + 3 ^ 40 * 6124935 * 2
def baseEnd_6124935 : Nat := 3145035632546098897344443

theorem tailTrace_6124935 : CollatzResearch.WordTrace tailWord_6124935 prefixEnd_6124935 3145035632546098897344443 := by
  unfold tailWord_6124935
  simp only [CollatzResearch.WordTrace]
  refine ⟨223394732065414025462368259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148929821376942683641578839 223394732065414025462368259)
  ·
    refine ⟨335092098098121038193552389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223394732065414025462368259 335092098098121038193552389)
    ·
      refine ⟨62829768393397694661291073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 335092098098121038193552389 62829768393397694661291073)
      ·
        refine ⟨47122326295048270995968305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62829768393397694661291073 47122326295048270995968305)
        ·
          refine ⟨35341744721286203246976229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47122326295048270995968305 35341744721286203246976229)
          ·
            refine ⟨6626577135241163108808043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35341744721286203246976229 6626577135241163108808043)
            ·
              refine ⟨9939865702861744663212065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6626577135241163108808043 9939865702861744663212065)
              ·
                refine ⟨7454899277146308497409049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9939865702861744663212065 7454899277146308497409049)
                ·
                  refine ⟨5591174457859731373056787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7454899277146308497409049 5591174457859731373056787)
                  ·
                    refine ⟨8386761686789597059585181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5591174457859731373056787 8386761686789597059585181)
                    ·
                      refine ⟨3145035632546098897344443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8386761686789597059585181 3145035632546098897344443)
                      ·
                        rfl

theorem cell23_6124935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_6124935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124935 prefixEnd_6124935 := by exact prefixLift 6124935
  have htrace : WordTrace (prefixWord ++ tailWord_6124935) baseStart_6124935 baseEnd_6124935 := by
    simpa [prefixWord, tailWord_6124935, baseEnd_6124935] using wordTrace_append hprefix tailTrace_6124935
  have hstable : (prefixWord ++ tailWord_6124935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124935).length < 2 ^ (prefixWord ++ tailWord_6124935).sum := by decide
  have hdescent : baseEnd_6124935 < baseStart_6124935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6124952 : List Nat := [2, 1, 2, 5, 2, 1, 3, 1, 2, 1, 3]
def baseStart_6124952 : Nat := 118140960795 + 6124952 * 2 ^ 59
def prefixEnd_6124952 : Nat := 4983230072969 + 3 ^ 40 * 6124952 * 2
def baseEnd_6124952 : Nat := 3145044361717225330831865

theorem tailTrace_6124952 : CollatzResearch.WordTrace tailWord_6124952 prefixEnd_6124952 3145044361717225330831865 := by
  unfold tailWord_6124952
  simp only [CollatzResearch.WordTrace]
  refine ⟨111697676053176218682868555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148930234737568291577158073 111697676053176218682868555)
  ·
    refine ⟨167546514079764328024302833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111697676053176218682868555 167546514079764328024302833)
    ·
      refine ⟨125659885559823246018227125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167546514079764328024302833 125659885559823246018227125)
      ·
        refine ⟨11780614271233429314208793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125659885559823246018227125 11780614271233429314208793)
        ·
          refine ⟨8835460703425071985656595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11780614271233429314208793 8835460703425071985656595)
          ·
            refine ⟨13253191055137607978484893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8835460703425071985656595 13253191055137607978484893)
            ·
              refine ⟨4969946645676602991931835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13253191055137607978484893 4969946645676602991931835)
              ·
                refine ⟨7454919968514904487897753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4969946645676602991931835 7454919968514904487897753)
                ·
                  refine ⟨5591189976386178365923315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7454919968514904487897753 5591189976386178365923315)
                  ·
                    refine ⟨8386784964579267548884973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5591189976386178365923315 8386784964579267548884973)
                    ·
                      refine ⟨3145044361717225330831865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8386784964579267548884973 3145044361717225330831865)
                      ·
                        rfl

theorem cell23_6124952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_6124952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6124952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6124952 prefixEnd_6124952 := by exact prefixLift 6124952
  have htrace : WordTrace (prefixWord ++ tailWord_6124952) baseStart_6124952 baseEnd_6124952 := by
    simpa [prefixWord, tailWord_6124952, baseEnd_6124952] using wordTrace_append hprefix tailTrace_6124952
  have hstable : (prefixWord ++ tailWord_6124952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6124952).length < 2 ^ (prefixWord ++ tailWord_6124952).sum := by decide
  have hdescent : baseEnd_6124952 < baseStart_6124952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6124952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125001 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 2, 5, 2]
def baseStart_6125001 : Nat := 118140960795 + 6125001 * 2 ^ 59
def prefixEnd_6125001 : Nat := 4983230072969 + 3 ^ 40 * 6125001 * 2
def baseEnd_6125001 : Nat := 3145069522269295639119139

theorem tailTrace_6125001 : CollatzResearch.WordTrace tailWord_6125001 prefixEnd_6125001 3145069522269295639119139 := by
  unfold tailWord_6125001
  simp only [CollatzResearch.WordTrace]
  refine ⟨223397139283174918734270857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148931426188783279156180571 223397139283174918734270857)
  ·
    refine ⟨167547854462381189050703143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223397139283174918734270857 167547854462381189050703143)
    ·
      refine ⟨251321781693571783576054715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167547854462381189050703143 251321781693571783576054715)
      ·
        refine ⟨376982672540357675364082073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251321781693571783576054715 376982672540357675364082073)
        ·
          refine ⟨282737004405268256523061555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376982672540357675364082073 282737004405268256523061555)
          ·
            refine ⟨424105506607902384784592333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282737004405268256523061555 424105506607902384784592333)
            ·
              refine ⟨159039564977963394294222125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 424105506607902384784592333 159039564977963394294222125)
              ·
                refine ⟨59639836866736272860333297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159039564977963394294222125 59639836866736272860333297)
                ·
                  refine ⟨44729877650052204645249973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59639836866736272860333297 44729877650052204645249973)
                  ·
                    refine ⟨4193426029692394185492185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44729877650052204645249973 4193426029692394185492185)
                    ·
                      refine ⟨3145069522269295639119139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4193426029692394185492185 3145069522269295639119139)
                      ·
                        rfl

theorem cell23_6125001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 5, 2].length) (baseStart_6125001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125001 prefixEnd_6125001 := by exact prefixLift 6125001
  have htrace : WordTrace (prefixWord ++ tailWord_6125001) baseStart_6125001 baseEnd_6125001 := by
    simpa [prefixWord, tailWord_6125001, baseEnd_6125001] using wordTrace_append hprefix tailTrace_6125001
  have hstable : (prefixWord ++ tailWord_6125001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125001).length < 2 ^ (prefixWord ++ tailWord_6125001).sum := by decide
  have hdescent : baseEnd_6125001 < baseStart_6125001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125141 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 5, 1, 5]
def baseStart_6125141 : Nat := 118140960795 + 6125141 * 2 ^ 59
def prefixEnd_6125141 : Nat := 4983230072969 + 3 ^ 40 * 6125141 * 2
def baseEnd_6125141 : Nat := 3145141409560925091368495

theorem tailTrace_6125141 : CollatzResearch.WordTrace tailWord_6125141 prefixEnd_6125141 3145141409560925091368495 := by
  unfold tailWord_6125141
  simp only [CollatzResearch.WordTrace]
  refine ⟨223402245502667722644367277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148934830335111815096244851 223402245502667722644367277)
  ·
    refine ⟨83775842063500395991637729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223402245502667722644367277 83775842063500395991637729)
    ·
      refine ⟨62831881547625296993728297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83775842063500395991637729 62831881547625296993728297)
      ·
        refine ⟨47123911160718972745296223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62831881547625296993728297 47123911160718972745296223)
        ·
          refine ⟨70685866741078459117944335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47123911160718972745296223 70685866741078459117944335)
          ·
            refine ⟨106028800111617688676916503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70685866741078459117944335 106028800111617688676916503)
            ·
              refine ⟨159043200167426533015374755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106028800111617688676916503 159043200167426533015374755)
              ·
                refine ⟨238564800251139799523062133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159043200167426533015374755 238564800251139799523062133)
                ·
                  refine ⟨22365450023544356205287075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 238564800251139799523062133 22365450023544356205287075)
                  ·
                    refine ⟨33548175035316534307930613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22365450023544356205287075 33548175035316534307930613)
                    ·
                      refine ⟨3145141409560925091368495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33548175035316534307930613 3145141409560925091368495)
                      ·
                        rfl

theorem cell23_6125141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_6125141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125141 prefixEnd_6125141 := by exact prefixLift 6125141
  have htrace : WordTrace (prefixWord ++ tailWord_6125141) baseStart_6125141 baseEnd_6125141 := by
    simpa [prefixWord, tailWord_6125141, baseEnd_6125141] using wordTrace_append hprefix tailTrace_6125141
  have hstable : (prefixWord ++ tailWord_6125141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125141).length < 2 ^ (prefixWord ++ tailWord_6125141).sum := by decide
  have hdescent : baseEnd_6125141 < baseStart_6125141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125166 : List Nat := [4, 1, 2, 2, 3, 1, 3, 2, 1, 1, 3]
def baseStart_6125166 : Nat := 118140960795 + 6125166 * 2 ^ 59
def prefixEnd_6125166 : Nat := 4983230072969 + 3 ^ 40 * 6125166 * 2
def baseEnd_6125166 : Nat := 3145154246577287493555881

theorem tailTrace_6125166 : CollatzResearch.WordTrace tailWord_6125166 prefixEnd_6125166 3145154246577287493555881 := by
  unfold tailWord_6125166
  simp only [CollatzResearch.WordTrace]
  refine ⟨27925394665947143989253419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148935438218384767942684901 27925394665947143989253419)
  ·
    refine ⟨41888091998920715983880129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27925394665947143989253419 41888091998920715983880129)
    ·
      refine ⟨31416068999190536987910097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41888091998920715983880129 31416068999190536987910097)
      ·
        refine ⟨23562051749392902740932573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31416068999190536987910097 23562051749392902740932573)
        ·
          refine ⟨8835769406022338527849715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23562051749392902740932573 8835769406022338527849715)
          ·
            refine ⟨13253654109033507791774573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8835769406022338527849715 13253654109033507791774573)
            ·
              refine ⟨4970120290887565421915465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13253654109033507791774573 4970120290887565421915465)
              ·
                refine ⟨3727590218165674066436599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4970120290887565421915465 3727590218165674066436599)
                ·
                  refine ⟨5591385327248511099654899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3727590218165674066436599 5591385327248511099654899)
                  ·
                    refine ⟨8387077990872766649482349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5591385327248511099654899 8387077990872766649482349)
                    ·
                      refine ⟨3145154246577287493555881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8387077990872766649482349 3145154246577287493555881)
                      ·
                        rfl

theorem cell23_6125166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_6125166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125166 prefixEnd_6125166 := by exact prefixLift 6125166
  have htrace : WordTrace (prefixWord ++ tailWord_6125166) baseStart_6125166 baseEnd_6125166 := by
    simpa [prefixWord, tailWord_6125166, baseEnd_6125166] using wordTrace_append hprefix tailTrace_6125166
  have hstable : (prefixWord ++ tailWord_6125166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125166).length < 2 ^ (prefixWord ++ tailWord_6125166).sum := by decide
  have hdescent : baseEnd_6125166 < baseStart_6125166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125192 : List Nat := [2, 1, 3, 5, 1, 1, 1, 1, 3, 2, 3]
def baseStart_6125192 : Nat := 118140960795 + 6125192 * 2 ^ 59
def prefixEnd_6125192 : Nat := 4983230072969 + 3 ^ 40 * 6125192 * 2
def baseEnd_6125192 : Nat := 3145167597074304391830761

theorem tailTrace_6125192 : CollatzResearch.WordTrace tailWord_6125192 prefixEnd_6125192 3145167597074304391830761 := by
  unfold tailWord_6125192
  simp only [CollatzResearch.WordTrace]
  refine ⟨111702052812741479177236915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148936070416988638902982553 111702052812741479177236915)
  ·
    refine ⟨167553079219112218765855373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111702052812741479177236915 167553079219112218765855373)
    ·
      refine ⟨62832404707167082037195765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167553079219112218765855373 62832404707167082037195765)
      ·
        refine ⟨5890537941296913940987103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62832404707167082037195765 5890537941296913940987103)
        ·
          refine ⟨8835806911945370911480655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5890537941296913940987103 8835806911945370911480655)
          ·
            refine ⟨13253710367918056367220983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8835806911945370911480655 13253710367918056367220983)
            ·
              refine ⟨19880565551877084550831475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13253710367918056367220983 19880565551877084550831475)
              ·
                refine ⟨29820848327815626826247213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19880565551877084550831475 29820848327815626826247213)
                ·
                  refine ⟨11182818122930860059842705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29820848327815626826247213 11182818122930860059842705)
                  ·
                    refine ⟨8387113592198145044882029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11182818122930860059842705 8387113592198145044882029)
                    ·
                      refine ⟨3145167597074304391830761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8387113592198145044882029 3145167597074304391830761)
                      ·
                        rfl

theorem cell23_6125192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_6125192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125192 prefixEnd_6125192 := by exact prefixLift 6125192
  have htrace : WordTrace (prefixWord ++ tailWord_6125192) baseStart_6125192 baseEnd_6125192 := by
    simpa [prefixWord, tailWord_6125192, baseEnd_6125192] using wordTrace_append hprefix tailTrace_6125192
  have hstable : (prefixWord ++ tailWord_6125192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125192).length < 2 ^ (prefixWord ++ tailWord_6125192).sum := by decide
  have hdescent : baseEnd_6125192 < baseStart_6125192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125201 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 5]
def baseStart_6125201 : Nat := 118140960795 + 6125201 * 2 ^ 59
def prefixEnd_6125201 : Nat := 4983230072969 + 3 ^ 40 * 6125201 * 2
def baseEnd_6125201 : Nat := 3145172218400194856618219

theorem tailTrace_6125201 : CollatzResearch.WordTrace tailWord_6125201 prefixEnd_6125201 3145172218400194856618219 := by
  unfold tailWord_6125201
  simp only [CollatzResearch.WordTrace]
  refine ⟨223404433882450352891551457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148936289254966901927700971 223404433882450352891551457)
  ·
    refine ⟨167553325411837764668663593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223404433882450352891551457 167553325411837764668663593)
    ·
      refine ⟨125664994058878323501497695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167553325411837764668663593 125664994058878323501497695)
      ·
        refine ⟨188497491088317485252246543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125664994058878323501497695 188497491088317485252246543)
        ·
          refine ⟨282746236632476227878369815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188497491088317485252246543 282746236632476227878369815)
          ·
            refine ⟨424119354948714341817554723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282746236632476227878369815 424119354948714341817554723)
            ·
              refine ⟨636179032423071512726332085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 424119354948714341817554723 636179032423071512726332085)
              ·
                refine ⟨59641784289662954318093633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 636179032423071512726332085 59641784289662954318093633)
                ·
                  refine ⟨44731338217247215738570225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59641784289662954318093633 44731338217247215738570225)
                  ·
                    refine ⟨33548503662935411803927669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44731338217247215738570225 33548503662935411803927669)
                    ·
                      refine ⟨3145172218400194856618219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33548503662935411803927669 3145172218400194856618219)
                      ·
                        rfl

theorem cell23_6125201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_6125201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125201 prefixEnd_6125201 := by exact prefixLift 6125201
  have htrace : WordTrace (prefixWord ++ tailWord_6125201) baseStart_6125201 baseEnd_6125201 := by
    simpa [prefixWord, tailWord_6125201, baseEnd_6125201] using wordTrace_append hprefix tailTrace_6125201
  have hstable : (prefixWord ++ tailWord_6125201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125201).length < 2 ^ (prefixWord ++ tailWord_6125201).sum := by decide
  have hdescent : baseEnd_6125201 < baseStart_6125201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125248 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 3]
def baseStart_6125248 : Nat := 118140960795 + 6125248 * 2 ^ 59
def prefixEnd_6125248 : Nat := 4983230072969 + 3 ^ 40 * 6125248 * 2
def baseEnd_6125248 : Nat := 3145196351990956172730503

theorem tailTrace_6125248 : CollatzResearch.WordTrace tailWord_6125248 prefixEnd_6125248 3145196351990956172730503 := by
  unfold tailWord_6125248
  simp only [CollatzResearch.WordTrace]
  refine ⟨111703074056640039959256199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148937432075520053279008265 111703074056640039959256199)
  ·
    refine ⟨167554611084960059938884299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111703074056640039959256199 167554611084960059938884299)
    ·
      refine ⟨251331916627440089908326449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167554611084960059938884299 251331916627440089908326449)
      ·
        refine ⟨188498937470580067431244837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251331916627440089908326449 188498937470580067431244837)
        ·
          refine ⟨35343550775733762643358407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188498937470580067431244837 35343550775733762643358407)
          ·
            refine ⟨53015326163600643965037611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35343550775733762643358407 53015326163600643965037611)
            ·
              refine ⟨79522989245400965947556417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53015326163600643965037611 79522989245400965947556417)
              ·
                refine ⟨59642241934050724460667313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79522989245400965947556417 59642241934050724460667313)
                ·
                  refine ⟨44731681450538043345500485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59642241934050724460667313 44731681450538043345500485)
                  ·
                    refine ⟨8387190271975883127281341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44731681450538043345500485 8387190271975883127281341)
                    ·
                      refine ⟨3145196351990956172730503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8387190271975883127281341 3145196351990956172730503)
                      ·
                        rfl

theorem cell23_6125248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 3].length) (baseStart_6125248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125248 prefixEnd_6125248 := by exact prefixLift 6125248
  have htrace : WordTrace (prefixWord ++ tailWord_6125248) baseStart_6125248 baseEnd_6125248 := by
    simpa [prefixWord, tailWord_6125248, baseEnd_6125248] using wordTrace_append hprefix tailTrace_6125248
  have hstable : (prefixWord ++ tailWord_6125248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125248).length < 2 ^ (prefixWord ++ tailWord_6125248).sum := by decide
  have hdescent : baseEnd_6125248 < baseStart_6125248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125262 : List Nat := [4, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2]
def baseStart_6125262 : Nat := 118140960795 + 6125262 * 2 ^ 59
def prefixEnd_6125262 : Nat := 4983230072969 + 3 ^ 40 * 6125262 * 2
def baseEnd_6125262 : Nat := 3145203540720119117955439

theorem tailTrace_6125262 : CollatzResearch.WordTrace tailWord_6125262 prefixEnd_6125262 3145203540720119117955439 := by
  unfold tailWord_6125262
  simp only [CollatzResearch.WordTrace]
  refine ⟨27925832341903670038690255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148937772490152906873014693 27925832341903670038690255)
  ·
    refine ⟨41888748512855505058035383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27925832341903670038690255 41888748512855505058035383)
    ·
      refine ⟨62833122769283257587053075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41888748512855505058035383 62833122769283257587053075)
      ·
        refine ⟨94249684153924886380579613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62833122769283257587053075 94249684153924886380579613)
        ·
          refine ⟨35343631557721832392717355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94249684153924886380579613 35343631557721832392717355)
          ·
            refine ⟨53015447336582748589076033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35343631557721832392717355 53015447336582748589076033)
            ·
              refine ⟨39761585502437061441807025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53015447336582748589076033 39761585502437061441807025)
              ·
                refine ⟨29821189126827796081355269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39761585502437061441807025 29821189126827796081355269)
                ·
                  refine ⟨5591472961280211765254113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29821189126827796081355269 5591472961280211765254113)
                  ·
                    refine ⟨4193604720960158823940585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5591472961280211765254113 4193604720960158823940585)
                    ·
                      refine ⟨3145203540720119117955439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4193604720960158823940585 3145203540720119117955439)
                      ·
                        rfl

theorem cell23_6125262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2].length) (baseStart_6125262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125262 prefixEnd_6125262 := by exact prefixLift 6125262
  have htrace : WordTrace (prefixWord ++ tailWord_6125262) baseStart_6125262 baseEnd_6125262 := by
    simpa [prefixWord, tailWord_6125262, baseEnd_6125262] using wordTrace_append hprefix tailTrace_6125262
  have hstable : (prefixWord ++ tailWord_6125262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125262).length < 2 ^ (prefixWord ++ tailWord_6125262).sum := by decide
  have hdescent : baseEnd_6125262 < baseStart_6125262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125266 : List Nat := [3, 2, 2, 2, 2, 3, 2, 1, 1, 3, 2]
def baseStart_6125266 : Nat := 118140960795 + 6125266 * 2 ^ 59
def prefixEnd_6125266 : Nat := 4983230072969 + 3 ^ 40 * 6125266 * 2
def baseEnd_6125266 : Nat := 3145205594642737102305421

theorem tailTrace_6125266 : CollatzResearch.WordTrace tailWord_6125266 prefixEnd_6125266 3145205594642737102305421 := by
  unfold tailWord_6125266
  simp only [CollatzResearch.WordTrace]
  refine ⟨55851701156803717248166913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148937869751476579328445101 55851701156803717248166913)
  ·
    refine ⟨41888775867602787936125185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55851701156803717248166913 41888775867602787936125185)
    ·
      refine ⟨31416581900702090952093889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41888775867602787936125185 31416581900702090952093889)
      ·
        refine ⟨23562436425526568214070417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31416581900702090952093889 23562436425526568214070417)
        ·
          refine ⟨17671827319144926160552813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23562436425526568214070417 17671827319144926160552813)
          ·
            refine ⟨6626935244679347310207305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17671827319144926160552813 6626935244679347310207305)
            ·
              refine ⟨4970201433509510482655479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6626935244679347310207305 4970201433509510482655479)
              ·
                refine ⟨7455302150264265723983219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4970201433509510482655479 7455302150264265723983219)
                ·
                  refine ⟨11182953225396398585974829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7455302150264265723983219 11182953225396398585974829)
                  ·
                    refine ⟨4193607459523649469740561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11182953225396398585974829 4193607459523649469740561)
                    ·
                      refine ⟨3145205594642737102305421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4193607459523649469740561 3145205594642737102305421)
                      ·
                        rfl

theorem cell23_6125266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_6125266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125266 prefixEnd_6125266 := by exact prefixLift 6125266
  have htrace : WordTrace (prefixWord ++ tailWord_6125266) baseStart_6125266 baseEnd_6125266 := by
    simpa [prefixWord, tailWord_6125266, baseEnd_6125266] using wordTrace_append hprefix tailTrace_6125266
  have hstable : (prefixWord ++ tailWord_6125266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125266).length < 2 ^ (prefixWord ++ tailWord_6125266).sum := by decide
  have hdescent : baseEnd_6125266 < baseStart_6125266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125285 : List Nat := [1, 3, 1, 4, 1, 1, 1, 6, 5]
def baseStart_6125285 : Nat := 118140960795 + 6125285 * 2 ^ 59
def prefixEnd_6125285 : Nat := 4983230072969 + 3 ^ 40 * 6125285 * 2
def baseEnd_6125285 : Nat := 349468372308352503107537

theorem tailTrace_6125285 : CollatzResearch.WordTrace tailWord_6125285 prefixEnd_6125285 349468372308352503107537 := by
  unfold tailWord_6125285
  simp only [CollatzResearch.WordTrace]
  refine ⟨223407497614146035237609309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148938331742764023491739539 223407497614146035237609309)
  ·
    refine ⟨83777811605304763214103491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223407497614146035237609309 83777811605304763214103491)
    ·
      refine ⟨125666717407957144821155237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83777811605304763214103491 125666717407957144821155237)
      ·
        refine ⟨23562509513991964653966607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125666717407957144821155237 23562509513991964653966607)
        ·
          refine ⟨35343764270987946980949911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23562509513991964653966607 35343764270987946980949911)
          ·
            refine ⟨53015646406481920471424867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35343764270987946980949911 53015646406481920471424867)
            ·
              refine ⟨79523469609722880707137301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53015646406481920471424867 79523469609722880707137301)
              ·
                refine ⟨3727662637955760033147061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79523469609722880707137301 3727662637955760033147061)
                ·
                  refine ⟨349468372308352503107537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3727662637955760033147061 349468372308352503107537)
                  ·
                    rfl

theorem cell23_6125285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6, 5].length) (baseStart_6125285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125285 prefixEnd_6125285 := by exact prefixLift 6125285
  have htrace : WordTrace (prefixWord ++ tailWord_6125285) baseStart_6125285 baseEnd_6125285 := by
    simpa [prefixWord, tailWord_6125285, baseEnd_6125285] using wordTrace_append hprefix tailTrace_6125285
  have hstable : (prefixWord ++ tailWord_6125285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125285).length < 2 ^ (prefixWord ++ tailWord_6125285).sum := by decide
  have hdescent : baseEnd_6125285 < baseStart_6125285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125298 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 3, 7]
def baseStart_6125298 : Nat := 118140960795 + 6125298 * 2 ^ 59
def prefixEnd_6125298 : Nat := 4983230072969 + 3 ^ 40 * 6125298 * 2
def baseEnd_6125298 : Nat := 1048407342007893659035091

theorem tailTrace_6125298 : CollatzResearch.WordTrace tailWord_6125298 prefixEnd_6125298 1048407342007893659035091 := by
  unfold tailWord_6125298
  simp only [CollatzResearch.WordTrace]
  refine ⟨55851992940774734614458137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148938647842065958971888365 55851992940774734614458137)
  ·
    refine ⟨41888994705581050960843603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55851992940774734614458137 41888994705581050960843603)
    ·
      refine ⟨62833492058371576441265405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41888994705581050960843603 62833492058371576441265405)
      ·
        refine ⟨23562559521889341165474527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62833492058371576441265405 23562559521889341165474527)
        ·
          refine ⟨35343839282834011748211791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23562559521889341165474527 35343839282834011748211791)
          ·
            refine ⟨53015758924251017622317687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35343839282834011748211791 53015758924251017622317687)
            ·
              refine ⟨79523638386376526433476531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53015758924251017622317687 79523638386376526433476531)
              ·
                refine ⟨119285457579564789650214797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79523638386376526433476531 119285457579564789650214797)
                ·
                  refine ⟨44732046592336796118830549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119285457579564789650214797 44732046592336796118830549)
                  ·
                    refine ⟨1048407342007893659035091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44732046592336796118830549 1048407342007893659035091)
                    ·
                      rfl

theorem cell23_6125298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_6125298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125298 prefixEnd_6125298 := by exact prefixLift 6125298
  have htrace : WordTrace (prefixWord ++ tailWord_6125298) baseStart_6125298 baseEnd_6125298 := by
    simpa [prefixWord, tailWord_6125298, baseEnd_6125298] using wordTrace_append hprefix tailTrace_6125298
  have hstable : (prefixWord ++ tailWord_6125298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125298).length < 2 ^ (prefixWord ++ tailWord_6125298).sum := by decide
  have hdescent : baseEnd_6125298 < baseStart_6125298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125319 : List Nat := [1, 1, 4, 4, 2, 2, 1, 3, 5]
def baseStart_6125319 : Nat := 118140960795 + 6125319 * 2 ^ 59
def prefixEnd_6125319 : Nat := 4983230072969 + 3 ^ 40 * 6125319 * 2
def baseEnd_6125319 : Nat := 349470312124158377215853

theorem tailTrace_6125319 : CollatzResearch.WordTrace tailWord_6125319 prefixEnd_6125319 349470312124158377215853 := by
  unfold tailWord_6125319
  simp only [CollatzResearch.WordTrace]
  refine ⟨223408737696022859044347011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148939158464015239362898007 223408737696022859044347011)
  ·
    refine ⟨335113106544034288566520517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223408737696022859044347011 335113106544034288566520517)
    ·
      refine ⟨62833707477006429106222597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 335113106544034288566520517 62833707477006429106222597)
      ·
        refine ⟨11781320151938705457416737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62833707477006429106222597 11781320151938705457416737)
        ·
          refine ⟨8835990113954029093062553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11781320151938705457416737 8835990113954029093062553)
          ·
            refine ⟨6626992585465521819796915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8835990113954029093062553 6626992585465521819796915)
            ·
              refine ⟨9940488878198282729695373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6626992585465521819796915 9940488878198282729695373)
              ·
                refine ⟨3727683329324356023635765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9940488878198282729695373 3727683329324356023635765)
                ·
                  refine ⟨349470312124158377215853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3727683329324356023635765 349470312124158377215853)
                  ·
                    rfl

theorem cell23_6125319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3, 5].length) (baseStart_6125319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125319 prefixEnd_6125319 := by exact prefixLift 6125319
  have htrace : WordTrace (prefixWord ++ tailWord_6125319) baseStart_6125319 baseEnd_6125319 := by
    simpa [prefixWord, tailWord_6125319, baseEnd_6125319] using wordTrace_append hprefix tailTrace_6125319
  have hstable : (prefixWord ++ tailWord_6125319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125319).length < 2 ^ (prefixWord ++ tailWord_6125319).sum := by decide
  have hdescent : baseEnd_6125319 < baseStart_6125319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125335 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 4]
def baseStart_6125335 : Nat := 118140960795 + 6125335 * 2 ^ 59
def prefixEnd_6125335 : Nat := 4983230072969 + 3 ^ 40 * 6125335 * 2
def baseEnd_6125335 : Nat := 3145241024807897332342603

theorem tailTrace_6125335 : CollatzResearch.WordTrace tailWord_6125335 prefixEnd_6125335 3145241024807897332342603 := by
  unfold tailWord_6125335
  simp only [CollatzResearch.WordTrace]
  refine ⟨223409321263964893776929459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148939547509309929184619639 223409321263964893776929459)
  ·
    refine ⟨335113981895947340665394189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223409321263964893776929459 335113981895947340665394189)
    ·
      refine ⟨125667743210980252749522821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335113981895947340665394189 125667743210980252749522821)
      ·
        refine ⟨23562701852058797390535529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125667743210980252749522821 23562701852058797390535529)
        ·
          refine ⟨17672026389044098042901647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23562701852058797390535529 17672026389044098042901647)
          ·
            refine ⟨26508039583566147064352471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17672026389044098042901647 26508039583566147064352471)
            ·
              refine ⟨39762059375349220596528707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26508039583566147064352471 39762059375349220596528707)
              ·
                refine ⟨59643089063023830894793061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39762059375349220596528707 59643089063023830894793061)
                ·
                  refine ⟨11183079199316968292773699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59643089063023830894793061 11183079199316968292773699)
                  ·
                    refine ⟨16774618798975452439160549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11183079199316968292773699 16774618798975452439160549)
                    ·
                      refine ⟨3145241024807897332342603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16774618798975452439160549 3145241024807897332342603)
                      ·
                        rfl

theorem cell23_6125335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_6125335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125335 prefixEnd_6125335 := by exact prefixLift 6125335
  have htrace : WordTrace (prefixWord ++ tailWord_6125335) baseStart_6125335 baseEnd_6125335 := by
    simpa [prefixWord, tailWord_6125335, baseEnd_6125335] using wordTrace_append hprefix tailTrace_6125335
  have hstable : (prefixWord ++ tailWord_6125335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125335).length < 2 ^ (prefixWord ++ tailWord_6125335).sum := by decide
  have hdescent : baseEnd_6125335 < baseStart_6125335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125369 : List Nat := [1, 2, 1, 7, 1, 1, 2, 1, 2, 1, 4]
def baseStart_6125369 : Nat := 118140960795 + 6125369 * 2 ^ 59
def prefixEnd_6125369 : Nat := 4983230072969 + 3 ^ 40 * 6125369 * 2
def baseEnd_6125369 : Nat := 3145258483150150199317447

theorem tailTrace_6125369 : CollatzResearch.WordTrace tailWord_6125369 prefixEnd_6125369 3145258483150150199317447 := by
  unfold tailWord_6125369
  simp only [CollatzResearch.WordTrace]
  refine ⟨223410561345841717583667161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148940374230561145055778107 223410561345841717583667161)
  ·
    refine ⟨167557921009381288187750371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223410561345841717583667161 167557921009381288187750371)
    ·
      refine ⟨251336881514071932281625557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167557921009381288187750371 251336881514071932281625557)
      ·
        refine ⟨5890708160486060912850599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 251336881514071932281625557 5890708160486060912850599)
        ·
          refine ⟨8836062240729091369275899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5890708160486060912850599 8836062240729091369275899)
          ·
            refine ⟨13254093361093637053913849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8836062240729091369275899 13254093361093637053913849)
            ·
              refine ⟨9940570020820227790435387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13254093361093637053913849 9940570020820227790435387)
              ·
                refine ⟨14910855031230341685653081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9940570020820227790435387 14910855031230341685653081)
                ·
                  refine ⟨11183141273422756264239811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14910855031230341685653081 11183141273422756264239811)
                  ·
                    refine ⟨16774711910134134396359717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11183141273422756264239811 16774711910134134396359717)
                    ·
                      refine ⟨3145258483150150199317447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16774711910134134396359717 3145258483150150199317447)
                      ·
                        rfl

theorem cell23_6125369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_6125369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125369 prefixEnd_6125369 := by exact prefixLift 6125369
  have htrace : WordTrace (prefixWord ++ tailWord_6125369) baseStart_6125369 baseEnd_6125369 := by
    simpa [prefixWord, tailWord_6125369, baseEnd_6125369] using wordTrace_append hprefix tailTrace_6125369
  have hstable : (prefixWord ++ tailWord_6125369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125369).length < 2 ^ (prefixWord ++ tailWord_6125369).sum := by decide
  have hdescent : baseEnd_6125369 < baseStart_6125369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125389 : List Nat := [1, 6, 1, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_6125389 : Nat := 118140960795 + 6125389 * 2 ^ 59
def prefixEnd_6125389 : Nat := 4983230072969 + 3 ^ 40 * 6125389 * 2
def baseEnd_6125389 : Nat := 3145268752763240121067355

theorem tailTrace_6125389 : CollatzResearch.WordTrace tailWord_6125389 prefixEnd_6125389 3145268752763240121067355 := by
  unfold tailWord_6125389
  simp only [CollatzResearch.WordTrace]
  refine ⟨223411290805769260999395221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148940860537179507332930147 223411290805769260999395221)
  ·
    refine ⟨10472404256520434109346651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 223411290805769260999395221 10472404256520434109346651)
    ·
      refine ⟨15708606384780651164019977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10472404256520434109346651 15708606384780651164019977)
      ·
        refine ⟨11781454788585488373014983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15708606384780651164019977 11781454788585488373014983)
        ·
          refine ⟨17672182182878232559522475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11781454788585488373014983 17672182182878232559522475)
          ·
            refine ⟨26508273274317348839283713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17672182182878232559522475 26508273274317348839283713)
            ·
              refine ⟨19881204955738011629462785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26508273274317348839283713 19881204955738011629462785)
              ·
                refine ⟨14910903716803508722097089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19881204955738011629462785 14910903716803508722097089)
                ·
                  refine ⟨11183177787602631541572817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14910903716803508722097089 11183177787602631541572817)
                  ·
                    refine ⟨8387383340701973656179613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11183177787602631541572817 8387383340701973656179613)
                    ·
                      refine ⟨3145268752763240121067355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8387383340701973656179613 3145268752763240121067355)
                      ·
                        rfl

theorem cell23_6125389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_6125389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125389 prefixEnd_6125389 := by exact prefixLift 6125389
  have htrace : WordTrace (prefixWord ++ tailWord_6125389) baseStart_6125389 baseEnd_6125389 := by
    simpa [prefixWord, tailWord_6125389, baseEnd_6125389] using wordTrace_append hprefix tailTrace_6125389
  have hstable : (prefixWord ++ tailWord_6125389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125389).length < 2 ^ (prefixWord ++ tailWord_6125389).sum := by decide
  have hdescent : baseEnd_6125389 < baseStart_6125389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125395 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 5, 5, 2]
def baseStart_6125395 : Nat := 118140960795 + 6125395 * 2 ^ 59
def prefixEnd_6125395 : Nat := 4983230072969 + 3 ^ 40 * 6125395 * 2
def baseEnd_6125395 : Nat := 3145271833647167097592327

theorem tailTrace_6125395 : CollatzResearch.WordTrace tailWord_6125395 prefixEnd_6125395 3145271833647167097592327 := by
  unfold tailWord_6125395
  simp only [CollatzResearch.WordTrace]
  refine ⟨223411509643747524024113639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148941006429165016016075759 223411509643747524024113639)
  ·
    refine ⟨335117264465621286036170459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223411509643747524024113639 335117264465621286036170459)
    ·
      refine ⟨502675896698431929054255689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335117264465621286036170459 502675896698431929054255689)
      ·
        refine ⟨377006922523823946790691767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 502675896698431929054255689 377006922523823946790691767)
        ·
          refine ⟨565510383785735920186037651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377006922523823946790691767 565510383785735920186037651)
          ·
            refine ⟨848265575678603880279056477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565510383785735920186037651 848265575678603880279056477)
            ·
              refine ⟨318099590879476455104646179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 848265575678603880279056477 318099590879476455104646179)
              ·
                refine ⟨477149386319214682656969269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318099590879476455104646179 477149386319214682656969269)
                ·
                  refine ⟨44732754967426376499090869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 477149386319214682656969269 44732754967426376499090869)
                  ·
                    refine ⟨4193695778196222796789769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44732754967426376499090869 4193695778196222796789769)
                    ·
                      refine ⟨3145271833647167097592327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4193695778196222796789769 3145271833647167097592327)
                      ·
                        rfl

theorem cell23_6125395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 5, 2].length) (baseStart_6125395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125395 prefixEnd_6125395 := by exact prefixLift 6125395
  have htrace : WordTrace (prefixWord ++ tailWord_6125395) baseStart_6125395 baseEnd_6125395 := by
    simpa [prefixWord, tailWord_6125395, baseEnd_6125395] using wordTrace_append hprefix tailTrace_6125395
  have hstable : (prefixWord ++ tailWord_6125395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125395).length < 2 ^ (prefixWord ++ tailWord_6125395).sum := by decide
  have hdescent : baseEnd_6125395 < baseStart_6125395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125396 : List Nat := [2, 4, 1, 1, 3, 1, 4, 2, 1, 4]
def baseStart_6125396 : Nat := 118140960795 + 6125396 * 2 ^ 59
def prefixEnd_6125396 : Nat := 4983230072969 + 3 ^ 40 * 6125396 * 2
def baseEnd_6125396 : Nat := 1048424115709273864559941

theorem tailTrace_6125396 : CollatzResearch.WordTrace tailWord_6125396 prefixEnd_6125396 1048424115709273864559941 := by
  unfold tailWord_6125396
  simp only [CollatzResearch.WordTrace]
  refine ⟨111705773058371950597450021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148941030744495934129933361 111705773058371950597450021)
  ·
    refine ⟨20944832448444740737021879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111705773058371950597450021 20944832448444740737021879)
    ·
      refine ⟨31417248672667111105532819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20944832448444740737021879 31417248672667111105532819)
      ·
        refine ⟨47125873009000666658299229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31417248672667111105532819 47125873009000666658299229)
        ·
          refine ⟨17672202378375249996862211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47125873009000666658299229 17672202378375249996862211)
          ·
            refine ⟨26508303567562874995293317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17672202378375249996862211 26508303567562874995293317)
            ·
              refine ⟨4970306918918039061617497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26508303567562874995293317 4970306918918039061617497)
              ·
                refine ⟨3727730189188529296213123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4970306918918039061617497 3727730189188529296213123)
                ·
                  refine ⟨5591595283782793944319685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3727730189188529296213123 5591595283782793944319685)
                  ·
                    refine ⟨1048424115709273864559941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5591595283782793944319685 1048424115709273864559941)
                    ·
                      rfl

theorem cell23_6125396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_6125396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125396 prefixEnd_6125396 := by exact prefixLift 6125396
  have htrace : WordTrace (prefixWord ++ tailWord_6125396) baseStart_6125396 baseEnd_6125396 := by
    simpa [prefixWord, tailWord_6125396, baseEnd_6125396] using wordTrace_append hprefix tailTrace_6125396
  have hstable : (prefixWord ++ tailWord_6125396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125396).length < 2 ^ (prefixWord ++ tailWord_6125396).sum := by decide
  have hdescent : baseEnd_6125396 < baseStart_6125396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125402 : List Nat := [3, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3]
def baseStart_6125402 : Nat := 118140960795 + 6125402 * 2 ^ 59
def prefixEnd_6125402 : Nat := 4983230072969 + 3 ^ 40 * 6125402 * 2
def baseEnd_6125402 : Nat := 3145275428011748570204795

theorem tailTrace_6125402 : CollatzResearch.WordTrace tailWord_6125402 prefixEnd_6125402 3145275428011748570204795 := by
  unfold tailWord_6125402
  simp only [CollatzResearch.WordTrace]
  refine ⟨55852941238680541054904615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148941176636481442813078973 55852941238680541054904615)
  ·
    refine ⟨83779411858020811582356923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55852941238680541054904615 83779411858020811582356923)
    ·
      refine ⟨125669117787031217373535385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83779411858020811582356923 125669117787031217373535385)
      ·
        refine ⟨94251838340273413030151539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125669117787031217373535385 94251838340273413030151539)
        ·
          refine ⟨141377757510410119545227309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94251838340273413030151539 141377757510410119545227309)
          ·
            refine ⟨53016659066403794829460241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141377757510410119545227309 53016659066403794829460241)
            ·
              refine ⟨39762494299802846122095181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53016659066403794829460241 39762494299802846122095181)
              ·
                refine ⟨14910935362426067295785693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39762494299802846122095181 14910935362426067295785693)
                ·
                  refine ⟨5591600760909775235919635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14910935362426067295785693 5591600760909775235919635)
                  ·
                    refine ⟨8387401141364662853879453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5591600760909775235919635 8387401141364662853879453)
                    ·
                      refine ⟨3145275428011748570204795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8387401141364662853879453 3145275428011748570204795)
                      ·
                        rfl

theorem cell23_6125402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_6125402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125402 prefixEnd_6125402 := by exact prefixLift 6125402
  have htrace : WordTrace (prefixWord ++ tailWord_6125402) baseStart_6125402 baseEnd_6125402 := by
    simpa [prefixWord, tailWord_6125402, baseEnd_6125402] using wordTrace_append hprefix tailTrace_6125402
  have hstable : (prefixWord ++ tailWord_6125402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125402).length < 2 ^ (prefixWord ++ tailWord_6125402).sum := by decide
  have hdescent : baseEnd_6125402 < baseStart_6125402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125422 : List Nat := [4, 1, 2, 3, 1, 1, 2, 1, 3, 5]
def baseStart_6125422 : Nat := 118140960795 + 6125422 * 2 ^ 59
def prefixEnd_6125422 : Nat := 4983230072969 + 3 ^ 40 * 6125422 * 2
def baseEnd_6125422 : Nat := 1048428565874946163984901

theorem tailTrace_6125422 : CollatzResearch.WordTrace tailWord_6125422 prefixEnd_6125422 1048428565874946163984901 := by
  unfold tailWord_6125422
  simp only [CollatzResearch.WordTrace]
  refine ⟨27926561801831213454418315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148941662943099805090231013 27926561801831213454418315)
  ·
    refine ⟨41889842702746820181627473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27926561801831213454418315 41889842702746820181627473)
    ·
      refine ⟨31417382027060115136220605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41889842702746820181627473 31417382027060115136220605)
      ·
        refine ⟨11781518260147543176082727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31417382027060115136220605 11781518260147543176082727)
        ·
          refine ⟨17672277390221314764124091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11781518260147543176082727 17672277390221314764124091)
          ·
            refine ⟨26508416085331972146186137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17672277390221314764124091 26508416085331972146186137)
            ·
              refine ⟨19881312063998979109639603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26508416085331972146186137 19881312063998979109639603)
              ·
                refine ⟨29821968095998468664459405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19881312063998979109639603 29821968095998468664459405)
                ·
                  refine ⟨11183238035999425749172277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29821968095998468664459405 11183238035999425749172277)
                  ·
                    refine ⟨1048428565874946163984901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11183238035999425749172277 1048428565874946163984901)
                    ·
                      rfl

theorem cell23_6125422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_6125422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125422 prefixEnd_6125422 := by exact prefixLift 6125422
  have htrace : WordTrace (prefixWord ++ tailWord_6125422) baseStart_6125422 baseEnd_6125422 := by
    simpa [prefixWord, tailWord_6125422, baseEnd_6125422] using wordTrace_append hprefix tailTrace_6125422
  have hstable : (prefixWord ++ tailWord_6125422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125422).length < 2 ^ (prefixWord ++ tailWord_6125422).sum := by decide
  have hdescent : baseEnd_6125422 < baseStart_6125422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125425 : List Nat := [1, 2, 2, 2, 1, 3, 1, 3, 3, 1, 4]
def baseStart_6125425 : Nat := 118140960795 + 6125425 * 2 ^ 59
def prefixEnd_6125425 : Nat := 4983230072969 + 3 ^ 40 * 6125425 * 2
def baseEnd_6125425 : Nat := 3145287238066801980217189

theorem tailTrace_6125425 : CollatzResearch.WordTrace tailWord_6125425 prefixEnd_6125425 3145287238066801980217189 := by
  unfold tailWord_6125425
  simp only [CollatzResearch.WordTrace]
  refine ⟨223412603833638839147705729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148941735889092559431803819 223412603833638839147705729)
  ·
    refine ⟨167559452875229129360779297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223412603833638839147705729 167559452875229129360779297)
    ·
      refine ⟨125669589656421847020584473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167559452875229129360779297 125669589656421847020584473)
      ·
        refine ⟨94252192242316385265438355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125669589656421847020584473 94252192242316385265438355)
        ·
          refine ⟨141378288363474577898157533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94252192242316385265438355 141378288363474577898157533)
          ·
            refine ⟨53016858136302966711809075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141378288363474577898157533 53016858136302966711809075)
            ·
              refine ⟨79525287204454450067713613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53016858136302966711809075 79525287204454450067713613)
              ·
                refine ⟨29821982701670418775392605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79525287204454450067713613 29821982701670418775392605)
                ·
                  refine ⟨11183243513126407040772227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29821982701670418775392605 11183243513126407040772227)
                  ·
                    refine ⟨16774865269689610561158341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11183243513126407040772227 16774865269689610561158341)
                    ·
                      refine ⟨3145287238066801980217189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16774865269689610561158341 3145287238066801980217189)
                      ·
                        rfl

theorem cell23_6125425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_6125425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125425 prefixEnd_6125425 := by exact prefixLift 6125425
  have htrace : WordTrace (prefixWord ++ tailWord_6125425) baseStart_6125425 baseEnd_6125425 := by
    simpa [prefixWord, tailWord_6125425, baseEnd_6125425] using wordTrace_append hprefix tailTrace_6125425
  have hstable : (prefixWord ++ tailWord_6125425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125425).length < 2 ^ (prefixWord ++ tailWord_6125425).sum := by decide
  have hdescent : baseEnd_6125425 < baseStart_6125425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125435 : List Nat := [1, 1, 1, 1, 1, 5, 1, 4, 4, 4]
def baseStart_6125435 : Nat := 118140960795 + 6125435 * 2 ^ 59
def prefixEnd_6125435 : Nat := 4983230072969 + 3 ^ 40 * 6125435 * 2
def baseEnd_6125435 : Nat := 1048430790957782313697381

theorem tailTrace_6125435 : CollatzResearch.WordTrace tailWord_6125435 prefixEnd_6125435 1048430790957782313697381 := by
  unfold tailWord_6125435
  simp only [CollatzResearch.WordTrace]
  refine ⟨223412968563602610855569759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148941979042401740570379839 223412968563602610855569759)
  ·
    refine ⟨335119452845403916283354639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223412968563602610855569759 335119452845403916283354639)
    ·
      refine ⟨502679179268105874425031959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335119452845403916283354639 502679179268105874425031959)
      ·
        refine ⟨754018768902158811637547939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502679179268105874425031959 754018768902158811637547939)
        ·
          refine ⟨1131028153353238217456321909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754018768902158811637547939 1131028153353238217456321909)
          ·
            refine ⟨106033889376866082886530179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1131028153353238217456321909 106033889376866082886530179)
            ·
              refine ⟨159050834065299124329795269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106033889376866082886530179 159050834065299124329795269)
              ·
                refine ⟨29822031387243585811836613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159050834065299124329795269 29822031387243585811836613)
                ·
                  refine ⟨5591630885108172339719365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29822031387243585811836613 5591630885108172339719365)
                  ·
                    refine ⟨1048430790957782313697381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5591630885108172339719365 1048430790957782313697381)
                    ·
                      rfl

theorem cell23_6125435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4, 4].length) (baseStart_6125435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125435 prefixEnd_6125435 := by exact prefixLift 6125435
  have htrace : WordTrace (prefixWord ++ tailWord_6125435) baseStart_6125435 baseEnd_6125435 := by
    simpa [prefixWord, tailWord_6125435, baseEnd_6125435] using wordTrace_append hprefix tailTrace_6125435
  have hstable : (prefixWord ++ tailWord_6125435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125435).length < 2 ^ (prefixWord ++ tailWord_6125435).sum := by decide
  have hdescent : baseEnd_6125435 < baseStart_6125435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125445 : List Nat := [1, 3, 1, 1, 3, 2, 2, 3, 1, 1, 5]
def baseStart_6125445 : Nat := 118140960795 + 6125445 * 2 ^ 59
def prefixEnd_6125445 : Nat := 4983230072969 + 3 ^ 40 * 6125445 * 2
def baseEnd_6125445 : Nat := 3145297507679891901967097

theorem tailTrace_6125445 : CollatzResearch.WordTrace tailWord_6125445 prefixEnd_6125445 3145297507679891901967097 := by
  unfold tailWord_6125445
  simp only [CollatzResearch.WordTrace]
  refine ⟨223413333293566382563433789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148942222195710921708955859 223413333293566382563433789)
  ·
    refine ⟨83779999985087393461287671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223413333293566382563433789 83779999985087393461287671)
    ·
      refine ⟨125669999977631090191931507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83779999985087393461287671 125669999977631090191931507)
      ·
        refine ⟨188504999966446635287897261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125669999977631090191931507 188504999966446635287897261)
        ·
          refine ⟨70689374987417488232961473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188504999966446635287897261 70689374987417488232961473)
          ·
            refine ⟨53017031240563116174721105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70689374987417488232961473 53017031240563116174721105)
            ·
              refine ⟨39762773430422337131040829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53017031240563116174721105 39762773430422337131040829)
              ·
                refine ⟨14911040036408376424140311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39762773430422337131040829 14911040036408376424140311)
                ·
                  refine ⟨22366560054612564636210467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14911040036408376424140311 22366560054612564636210467)
                  ·
                    refine ⟨33549840081918846954315701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22366560054612564636210467 33549840081918846954315701)
                    ·
                      refine ⟨3145297507679891901967097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33549840081918846954315701 3145297507679891901967097)
                      ·
                        rfl

theorem cell23_6125445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_6125445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125445 prefixEnd_6125445 := by exact prefixLift 6125445
  have htrace : WordTrace (prefixWord ++ tailWord_6125445) baseStart_6125445 baseEnd_6125445 := by
    simpa [prefixWord, tailWord_6125445, baseEnd_6125445] using wordTrace_append hprefix tailTrace_6125445
  have hstable : (prefixWord ++ tailWord_6125445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125445).length < 2 ^ (prefixWord ++ tailWord_6125445).sum := by decide
  have hdescent : baseEnd_6125445 < baseStart_6125445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125479 : List Nat := [1, 1, 6, 1, 2, 1, 1, 4, 1, 2, 3]
def baseStart_6125479 : Nat := 118140960795 + 6125479 * 2 ^ 59
def prefixEnd_6125479 : Nat := 4983230072969 + 3 ^ 40 * 6125479 * 2
def baseEnd_6125479 : Nat := 3145314966022144768941941

theorem tailTrace_6125479 : CollatzResearch.WordTrace tailWord_6125479 prefixEnd_6125479 3145314966022144768941941 := by
  unfold tailWord_6125479
  simp only [CollatzResearch.WordTrace]
  refine ⟨223414573375443206370171491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148943048916962137580114327 223414573375443206370171491)
  ·
    refine ⟨335121860063164809555257237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223414573375443206370171491 335121860063164809555257237)
    ·
      refine ⟨15708837190460850447902683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 335121860063164809555257237 15708837190460850447902683)
      ·
        refine ⟨23563255785691275671854025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15708837190460850447902683 23563255785691275671854025)
        ·
          refine ⟨17672441839268456753890519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23563255785691275671854025 17672441839268456753890519)
          ·
            refine ⟨26508662758902685130835779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17672441839268456753890519 26508662758902685130835779)
            ·
              refine ⟨39762994138354027696253669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26508662758902685130835779 39762994138354027696253669)
              ·
                refine ⟨7455561400941380193047563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39762994138354027696253669 7455561400941380193047563)
                ·
                  refine ⟨11183342101412070289571345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7455561400941380193047563 11183342101412070289571345)
                  ·
                    refine ⟨8387506576059052717178509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11183342101412070289571345 8387506576059052717178509)
                    ·
                      refine ⟨3145314966022144768941941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8387506576059052717178509 3145314966022144768941941)
                      ·
                        rfl

theorem cell23_6125479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_6125479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125479 prefixEnd_6125479 := by exact prefixLift 6125479
  have htrace : WordTrace (prefixWord ++ tailWord_6125479) baseStart_6125479 baseEnd_6125479 := by
    simpa [prefixWord, tailWord_6125479, baseEnd_6125479] using wordTrace_append hprefix tailTrace_6125479
  have hstable : (prefixWord ++ tailWord_6125479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125479).length < 2 ^ (prefixWord ++ tailWord_6125479).sum := by decide
  have hdescent : baseEnd_6125479 < baseStart_6125479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125493 : List Nat := [1, 3, 3, 2, 1, 2, 3, 3, 1, 2, 2]
def baseStart_6125493 : Nat := 118140960795 + 6125493 * 2 ^ 59
def prefixEnd_6125493 : Nat := 4983230072969 + 3 ^ 40 * 6125493 * 2
def baseEnd_6125493 : Nat := 3145322154751307714166877

theorem tailTrace_6125493 : CollatzResearch.WordTrace tailWord_6125493 prefixEnd_6125493 3145322154751307714166877 := by
  unfold tailWord_6125493
  simp only [CollatzResearch.WordTrace]
  refine ⟨223415083997392486761181133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148943389331594991174120755 223415083997392486761181133)
  ·
    refine ⟨83780656499022182535442925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223415083997392486761181133 83780656499022182535442925)
    ·
      refine ⟨31417746187133318450791097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83780656499022182535442925 31417746187133318450791097)
      ·
        refine ⟨23563309640349988838093323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31417746187133318450791097 23563309640349988838093323)
        ·
          refine ⟨35344964460524983257139985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23563309640349988838093323 35344964460524983257139985)
          ·
            refine ⟨26508723345393737442854989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35344964460524983257139985 26508723345393737442854989)
            ·
              refine ⟨9940771254522651541070621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26508723345393737442854989 9940771254522651541070621)
              ·
                refine ⟨3727789220445994327901483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9940771254522651541070621 3727789220445994327901483)
                ·
                  refine ⟨5591683830668991491852225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3727789220445994327901483 5591683830668991491852225)
                  ·
                    refine ⟨4193762873001743618889169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5591683830668991491852225 4193762873001743618889169)
                    ·
                      refine ⟨3145322154751307714166877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4193762873001743618889169 3145322154751307714166877)
                      ·
                        rfl

theorem cell23_6125493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_6125493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125493 prefixEnd_6125493 := by exact prefixLift 6125493
  have htrace : WordTrace (prefixWord ++ tailWord_6125493) baseStart_6125493 baseEnd_6125493 := by
    simpa [prefixWord, tailWord_6125493, baseEnd_6125493] using wordTrace_append hprefix tailTrace_6125493
  have hstable : (prefixWord ++ tailWord_6125493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125493).length < 2 ^ (prefixWord ++ tailWord_6125493).sum := by decide
  have hdescent : baseEnd_6125493 < baseStart_6125493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125515 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 4]
def baseStart_6125515 : Nat := 118140960795 + 6125515 * 2 ^ 59
def prefixEnd_6125515 : Nat := 4983230072969 + 3 ^ 40 * 6125515 * 2
def baseEnd_6125515 : Nat := 3145333451325706628091775

theorem tailTrace_6125515 : CollatzResearch.WordTrace tailWord_6125515 prefixEnd_6125515 3145333451325706628091775 := by
  unfold tailWord_6125515
  simp only [CollatzResearch.WordTrace]
  refine ⟨223415886403312784518481999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148943924268875189678987999 223415886403312784518481999)
  ·
    refine ⟨335123829604969176777722999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223415886403312784518481999 335123829604969176777722999)
    ·
      refine ⟨502685744407453765166584499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335123829604969176777722999 502685744407453765166584499)
      ·
        refine ⟨754028616611180647749876749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502685744407453765166584499 754028616611180647749876749)
        ·
          refine ⟨282760731229192742906203781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 754028616611180647749876749 282760731229192742906203781)
          ·
            refine ⟨53017637105473639294913209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 282760731229192742906203781 53017637105473639294913209)
            ·
              refine ⟨39763227829105229471184907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53017637105473639294913209 39763227829105229471184907)
              ·
                refine ⟨59644841743657844206777361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39763227829105229471184907 59644841743657844206777361)
                ·
                  refine ⟨44733631307743383155083021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59644841743657844206777361 44733631307743383155083021)
                  ·
                    refine ⟨16775111740403768683156133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44733631307743383155083021 16775111740403768683156133)
                    ·
                      refine ⟨3145333451325706628091775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16775111740403768683156133 3145333451325706628091775)
                      ·
                        rfl

theorem cell23_6125515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 4].length) (baseStart_6125515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125515 prefixEnd_6125515 := by exact prefixLift 6125515
  have htrace : WordTrace (prefixWord ++ tailWord_6125515) baseStart_6125515 baseEnd_6125515 := by
    simpa [prefixWord, tailWord_6125515, baseEnd_6125515] using wordTrace_append hprefix tailTrace_6125515
  have hstable : (prefixWord ++ tailWord_6125515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125515).length < 2 ^ (prefixWord ++ tailWord_6125515).sum := by decide
  have hdescent : baseEnd_6125515 < baseStart_6125515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125553 : List Nat := [1, 2, 2, 2, 5, 1, 3, 1, 1, 3, 2]
def baseStart_6125553 : Nat := 118140960795 + 6125553 * 2 ^ 59
def prefixEnd_6125553 : Nat := 4983230072969 + 3 ^ 40 * 6125553 * 2
def baseEnd_6125553 : Nat := 3145352963590577479416601

theorem tailTrace_6125553 : CollatzResearch.WordTrace tailWord_6125553 prefixEnd_6125553 3145352963590577479416601 := by
  unfold tailWord_6125553
  simp only [CollatzResearch.WordTrace]
  refine ⟨223417272377175117008365313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148944848251450078005576875 223417272377175117008365313)
  ·
    refine ⟨167562954282881337756273985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223417272377175117008365313 167562954282881337756273985)
    ·
      refine ⟨125672215712161003317205489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167562954282881337756273985 125672215712161003317205489)
      ·
        refine ⟨94254161784120752487904117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125672215712161003317205489 94254161784120752487904117)
        ·
          refine ⟨8836327667261320545741011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94254161784120752487904117 8836327667261320545741011)
          ·
            refine ⟨13254491500891980818611517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8836327667261320545741011 13254491500891980818611517)
            ·
              refine ⟨4970434312834492806979319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13254491500891980818611517 4970434312834492806979319)
              ·
                refine ⟨7455651469251739210468979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4970434312834492806979319 7455651469251739210468979)
                ·
                  refine ⟨11183477203877608815703469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7455651469251739210468979 11183477203877608815703469)
                  ·
                    refine ⟨4193803951454103305888801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11183477203877608815703469 4193803951454103305888801)
                    ·
                      refine ⟨3145352963590577479416601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4193803951454103305888801 3145352963590577479416601)
                      ·
                        rfl

theorem cell23_6125553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 1, 3, 2].length) (baseStart_6125553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125553 prefixEnd_6125553 := by exact prefixLift 6125553
  have htrace : WordTrace (prefixWord ++ tailWord_6125553) baseStart_6125553 baseEnd_6125553 := by
    simpa [prefixWord, tailWord_6125553, baseEnd_6125553] using wordTrace_append hprefix tailTrace_6125553
  have hstable : (prefixWord ++ tailWord_6125553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125553).length < 2 ^ (prefixWord ++ tailWord_6125553).sum := by decide
  have hdescent : baseEnd_6125553 < baseStart_6125553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125565 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 1, 2, 7]
def baseStart_6125565 : Nat := 118140960795 + 6125565 * 2 ^ 59
def prefixEnd_6125565 : Nat := 4983230072969 + 3 ^ 40 * 6125565 * 2
def baseEnd_6125565 : Nat := 3145359125358431432466545

theorem tailTrace_6125565 : CollatzResearch.WordTrace tailWord_6125565 prefixEnd_6125565 3145359125358431432466545 := by
  unfold tailWord_6125565
  simp only [CollatzResearch.WordTrace]
  refine ⟨223417710053131643057802149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148945140035421095371868099 223417710053131643057802149)
  ·
    refine ⟨41890820634962183073337903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223417710053131643057802149 41890820634962183073337903)
    ·
      refine ⟨62836230952443274610006855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41890820634962183073337903 62836230952443274610006855)
      ·
        refine ⟨94254346428664911915010283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62836230952443274610006855 94254346428664911915010283)
        ·
          refine ⟨141381519642997367872515425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94254346428664911915010283 141381519642997367872515425)
          ·
            refine ⟨106036139732248025904386569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141381519642997367872515425 106036139732248025904386569)
            ·
              refine ⟨79527104799186019428289927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106036139732248025904386569 79527104799186019428289927)
              ·
                refine ⟨119290657198779029142434891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79527104799186019428289927 119290657198779029142434891)
                ·
                  refine ⟨178935985798168543713652337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119290657198779029142434891 178935985798168543713652337)
                  ·
                    refine ⟨134201989348626407785239253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 178935985798168543713652337 134201989348626407785239253)
                    ·
                      refine ⟨3145359125358431432466545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 134201989348626407785239253 3145359125358431432466545)
                      ·
                        rfl

theorem cell23_6125565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_6125565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125565 prefixEnd_6125565 := by exact prefixLift 6125565
  have htrace : WordTrace (prefixWord ++ tailWord_6125565) baseStart_6125565 baseEnd_6125565 := by
    simpa [prefixWord, tailWord_6125565, baseEnd_6125565] using wordTrace_append hprefix tailTrace_6125565
  have hstable : (prefixWord ++ tailWord_6125565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125565).length < 2 ^ (prefixWord ++ tailWord_6125565).sum := by decide
  have hdescent : baseEnd_6125565 < baseStart_6125565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125595 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 5]
def baseStart_6125595 : Nat := 118140960795 + 6125595 * 2 ^ 59
def prefixEnd_6125595 : Nat := 4983230072969 + 3 ^ 40 * 6125595 * 2
def baseEnd_6125595 : Nat := 3145374529778066315091407

theorem tailTrace_6125595 : CollatzResearch.WordTrace tailWord_6125595 prefixEnd_6125595 3145374529778066315091407 := by
  unfold tailWord_6125595
  simp only [CollatzResearch.WordTrace]
  refine ⟨223418804243022958181394239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148945869495348638787596159 223418804243022958181394239)
  ·
    refine ⟨335128206364534437272091359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223418804243022958181394239 335128206364534437272091359)
    ·
      refine ⟨502692309546801655908137039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335128206364534437272091359 502692309546801655908137039)
      ·
        refine ⟨754038464320202483862205559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502692309546801655908137039 754038464320202483862205559)
        ·
          refine ⟨1131057696480303725793308339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754038464320202483862205559 1131057696480303725793308339)
          ·
            refine ⟨1696586544720455588689962509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131057696480303725793308339 1696586544720455588689962509)
            ·
              refine ⟨636219954270170845758735941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1696586544720455588689962509 636219954270170845758735941)
              ·
                refine ⟨119291241425657033579762989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 636219954270170845758735941 119291241425657033579762989)
                ·
                  refine ⟨44734215534621387592411121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119291241425657033579762989 44734215534621387592411121)
                  ·
                    refine ⟨33550661650966040694308341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44734215534621387592411121 33550661650966040694308341)
                    ·
                      refine ⟨3145374529778066315091407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33550661650966040694308341 3145374529778066315091407)
                      ·
                        rfl

theorem cell23_6125595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 5].length) (baseStart_6125595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125595 prefixEnd_6125595 := by exact prefixLift 6125595
  have htrace : WordTrace (prefixWord ++ tailWord_6125595) baseStart_6125595 baseEnd_6125595 := by
    simpa [prefixWord, tailWord_6125595, baseEnd_6125595] using wordTrace_append hprefix tailTrace_6125595
  have hstable : (prefixWord ++ tailWord_6125595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125595).length < 2 ^ (prefixWord ++ tailWord_6125595).sum := by decide
  have hdescent : baseEnd_6125595 < baseStart_6125595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125602 : List Nat := [3, 3, 1, 1, 1, 2, 3, 1, 1, 7]
def baseStart_6125602 : Nat := 118140960795 + 6125602 * 2 ^ 59
def prefixEnd_6125602 : Nat := 4983230072969 + 3 ^ 40 * 6125602 * 2
def baseEnd_6125602 : Nat := 1048459374714215929234625

theorem tailTrace_6125602 : CollatzResearch.WordTrace tailWord_6125602 prefixEnd_6125602 1048459374714215929234625 := by
  unfold tailWord_6125602
  simp only [CollatzResearch.WordTrace]
  refine ⟨55854764888499399594224765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148946039702665065584599373 55854764888499399594224765)
  ·
    refine ⟨20945536833187274847834287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55854764888499399594224765 20945536833187274847834287)
    ·
      refine ⟨31418305249780912271751431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20945536833187274847834287 31418305249780912271751431)
      ·
        refine ⟨47127457874671368407627147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31418305249780912271751431 47127457874671368407627147)
        ·
          refine ⟨70691186812007052611440721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47127457874671368407627147 70691186812007052611440721)
          ·
            refine ⟨53018390109005289458580541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70691186812007052611440721 53018390109005289458580541)
            ·
              refine ⟨19881896290876983546967703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53018390109005289458580541 19881896290876983546967703)
              ·
                refine ⟨29822844436315475320451555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19881896290876983546967703 29822844436315475320451555)
                ·
                  refine ⟨44734266654473212980677333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29822844436315475320451555 44734266654473212980677333)
                  ·
                    refine ⟨1048459374714215929234625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44734266654473212980677333 1048459374714215929234625)
                    ·
                      rfl

theorem cell23_6125602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_6125602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125602 prefixEnd_6125602 := by exact prefixLift 6125602
  have htrace : WordTrace (prefixWord ++ tailWord_6125602) baseStart_6125602 baseEnd_6125602 := by
    simpa [prefixWord, tailWord_6125602, baseEnd_6125602] using wordTrace_append hprefix tailTrace_6125602
  have hstable : (prefixWord ++ tailWord_6125602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125602).length < 2 ^ (prefixWord ++ tailWord_6125602).sum := by decide
  have hdescent : baseEnd_6125602 < baseStart_6125602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125639 : List Nat := [1, 1, 4, 1, 3, 1, 1, 3, 2, 4, 2]
def baseStart_6125639 : Nat := 118140960795 + 6125639 * 2 ^ 59
def prefixEnd_6125639 : Nat := 4983230072969 + 3 ^ 40 * 6125639 * 2
def baseEnd_6125639 : Nat := 3145397122926864142941205

theorem tailTrace_6125639 : CollatzResearch.WordTrace tailWord_6125639 prefixEnd_6125639 3145397122926864142941205 := by
  unfold tailWord_6125639
  simp only [CollatzResearch.WordTrace]
  refine ⟨223420409054863553695995971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148946939369909035797330647 223420409054863553695995971)
  ·
    refine ⟨335130613582295330543993957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223420409054863553695995971 335130613582295330543993957)
    ·
      refine ⟨62836990046680374476998867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 335130613582295330543993957 62836990046680374476998867)
      ·
        refine ⟨94255485070020561715498301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62836990046680374476998867 94255485070020561715498301)
        ·
          refine ⟨35345806901257710643311863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94255485070020561715498301 35345806901257710643311863)
          ·
            refine ⟨53018710351886565964967795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35345806901257710643311863 53018710351886565964967795)
            ·
              refine ⟨79528065527829848947451693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53018710351886565964967795 79528065527829848947451693)
              ·
                refine ⟨29823024572936193355294385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79528065527829848947451693 29823024572936193355294385)
                ·
                  refine ⟨22367268429702145016470789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29823024572936193355294385 22367268429702145016470789)
                  ·
                    refine ⟨4193862830569152190588273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22367268429702145016470789 4193862830569152190588273)
                    ·
                      refine ⟨3145397122926864142941205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4193862830569152190588273 3145397122926864142941205)
                      ·
                        rfl

theorem cell23_6125639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 4, 2].length) (baseStart_6125639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125639 prefixEnd_6125639 := by exact prefixLift 6125639
  have htrace : WordTrace (prefixWord ++ tailWord_6125639) baseStart_6125639 baseEnd_6125639 := by
    simpa [prefixWord, tailWord_6125639, baseEnd_6125639] using wordTrace_append hprefix tailTrace_6125639
  have hstable : (prefixWord ++ tailWord_6125639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125639).length < 2 ^ (prefixWord ++ tailWord_6125639).sum := by decide
  have hdescent : baseEnd_6125639 < baseStart_6125639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125652 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_6125652 : Nat := 118140960795 + 6125652 * 2 ^ 59
def prefixEnd_6125652 : Nat := 4983230072969 + 3 ^ 40 * 6125652 * 2
def baseEnd_6125652 : Nat := 3145403798175372592078645

theorem tailTrace_6125652 : CollatzResearch.WordTrace tailWord_6125652 prefixEnd_6125652 3145403798175372592078645 := by
  unfold tailWord_6125652
  simp only [CollatzResearch.WordTrace]
  refine ⟨111710441601908228458109605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148947255469210971277479473 111710441601908228458109605)
  ·
    refine ⟨20945707800357792835895551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111710441601908228458109605 20945707800357792835895551)
    ·
      refine ⟨31418561700536689253843327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20945707800357792835895551 31418561700536689253843327)
      ·
        refine ⟨47127842550805033880764991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31418561700536689253843327 47127842550805033880764991)
        ·
          refine ⟨70691763826207550821147487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47127842550805033880764991 70691763826207550821147487)
          ·
            refine ⟨106037645739311326231721231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70691763826207550821147487 106037645739311326231721231)
            ·
              refine ⟨159056468608966989347581847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106037645739311326231721231 159056468608966989347581847)
              ·
                refine ⟨238584702913450484021372771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159056468608966989347581847 238584702913450484021372771)
                ·
                  refine ⟨357877054370175726032059157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 238584702913450484021372771 357877054370175726032059157)
                  ·
                    refine ⟨16775486923601987157752773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 357877054370175726032059157 16775486923601987157752773)
                    ·
                      refine ⟨3145403798175372592078645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16775486923601987157752773 3145403798175372592078645)
                      ·
                        rfl

theorem cell23_6125652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_6125652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125652 prefixEnd_6125652 := by exact prefixLift 6125652
  have htrace : WordTrace (prefixWord ++ tailWord_6125652) baseStart_6125652 baseEnd_6125652 := by
    simpa [prefixWord, tailWord_6125652, baseEnd_6125652] using wordTrace_append hprefix tailTrace_6125652
  have hstable : (prefixWord ++ tailWord_6125652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125652).length < 2 ^ (prefixWord ++ tailWord_6125652).sum := by decide
  have hdescent : baseEnd_6125652 < baseStart_6125652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125756 : List Nat := [2, 2, 2, 3, 3, 1, 2, 1, 1, 6]
def baseStart_6125756 : Nat := 118140960795 + 6125756 * 2 ^ 59
def prefixEnd_6125756 : Nat := 4983230072969 + 3 ^ 40 * 6125756 * 2
def baseEnd_6125756 : Nat := 1048485733387813395059389

theorem tailTrace_6125756 : CollatzResearch.WordTrace tailWord_6125756 prefixEnd_6125756 1048485733387813395059389 := by
  unfold tailWord_6125756
  simp only [CollatzResearch.WordTrace]
  refine ⟨111712338197719841339002561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148949784263626455118670081 111712338197719841339002561)
  ·
    refine ⟨83784253648289881004251921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111712338197719841339002561 83784253648289881004251921)
    ·
      refine ⟨62838190236217410753188941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83784253648289881004251921 62838190236217410753188941)
      ·
        refine ⟨23564321338581529032445853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62838190236217410753188941 23564321338581529032445853)
        ·
          refine ⟨8836620501968073387167195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23564321338581529032445853 8836620501968073387167195)
          ·
            refine ⟨13254930752952110080750793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8836620501968073387167195 13254930752952110080750793)
            ·
              refine ⟨9941198064714082560563095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13254930752952110080750793 9941198064714082560563095)
              ·
                refine ⟨14911797097071123840844643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9941198064714082560563095 14911797097071123840844643)
                ·
                  refine ⟨22367695645606685761266965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14911797097071123840844643 22367695645606685761266965)
                  ·
                    refine ⟨1048485733387813395059389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22367695645606685761266965 1048485733387813395059389)
                    ·
                      rfl

theorem cell23_6125756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_6125756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125756 prefixEnd_6125756 := by exact prefixLift 6125756
  have htrace : WordTrace (prefixWord ++ tailWord_6125756) baseStart_6125756 baseEnd_6125756 := by
    simpa [prefixWord, tailWord_6125756, baseEnd_6125756] using wordTrace_append hprefix tailTrace_6125756
  have hstable : (prefixWord ++ tailWord_6125756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125756).length < 2 ^ (prefixWord ++ tailWord_6125756).sum := by decide
  have hdescent : baseEnd_6125756 < baseStart_6125756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125823 : List Nat := [1, 1, 2, 2, 1, 4, 4, 2, 1, 3, 2]
def baseStart_6125823 : Nat := 118140960795 + 6125823 * 2 ^ 59
def prefixEnd_6125823 : Nat := 4983230072969 + 3 ^ 40 * 6125823 * 2
def baseEnd_6125823 : Nat := 3145491603367291423040359

theorem tailTrace_6125823 : CollatzResearch.WordTrace tailWord_6125823 prefixEnd_6125823 3145491603367291423040359 := by
  unfold tailWord_6125823
  simp only [CollatzResearch.WordTrace]
  refine ⟨223427120086196953120694123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148951413390797968747129415 223427120086196953120694123)
  ·
    refine ⟨335140680129295429681041185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223427120086196953120694123 335140680129295429681041185)
    ·
      refine ⟨251355510096971572260780889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335140680129295429681041185 251355510096971572260780889)
      ·
        refine ⟨188516632572728679195585667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251355510096971572260780889 188516632572728679195585667)
        ·
          refine ⟨282774948859093018793378501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188516632572728679195585667 282774948859093018793378501)
          ·
            refine ⟨53020302911079941023758469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 282774948859093018793378501 53020302911079941023758469)
            ·
              refine ⟨9941306795827488941954713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53020302911079941023758469 9941306795827488941954713)
              ·
                refine ⟨7455980096870616706466035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9941306795827488941954713 7455980096870616706466035)
                ·
                  refine ⟨11183970145305925059699053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7455980096870616706466035 11183970145305925059699053)
                  ·
                    refine ⟨4193988804489721897387145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11183970145305925059699053 4193988804489721897387145)
                    ·
                      refine ⟨3145491603367291423040359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4193988804489721897387145 3145491603367291423040359)
                      ·
                        rfl

theorem cell23_6125823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 3, 2].length) (baseStart_6125823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125823 prefixEnd_6125823 := by exact prefixLift 6125823
  have htrace : WordTrace (prefixWord ++ tailWord_6125823) baseStart_6125823 baseEnd_6125823 := by
    simpa [prefixWord, tailWord_6125823, baseEnd_6125823] using wordTrace_append hprefix tailTrace_6125823
  have hstable : (prefixWord ++ tailWord_6125823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125823).length < 2 ^ (prefixWord ++ tailWord_6125823).sum := by decide
  have hdescent : baseEnd_6125823 < baseStart_6125823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125826 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_6125826 : Nat := 118140960795 + 6125826 * 2 ^ 59
def prefixEnd_6125826 : Nat := 4983230072969 + 3 ^ 40 * 6125826 * 2
def baseEnd_6125826 : Nat := 3145493143809254911302845

theorem tailTrace_6125826 : CollatzResearch.WordTrace tailWord_6125826 prefixEnd_6125826 3145493143809254911302845 := by
  unfold tailWord_6125826
  simp only [CollatzResearch.WordTrace]
  refine ⟨55856807376296521158263333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148951486336790723088702221 55856807376296521158263333)
  ·
    refine ⟨10473151383055597717174375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55856807376296521158263333 10473151383055597717174375)
    ·
      refine ⟨15709727074583396575761563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10473151383055597717174375 15709727074583396575761563)
      ·
        refine ⟨23564590611875094863642345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15709727074583396575761563 23564590611875094863642345)
        ·
          refine ⟨17673442958906321147731759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23564590611875094863642345 17673442958906321147731759)
          ·
            refine ⟨26510164438359481721597639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17673442958906321147731759 26510164438359481721597639)
            ·
              refine ⟨39765246657539222582396459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26510164438359481721597639 39765246657539222582396459)
              ·
                refine ⟨59647869986308833873594689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39765246657539222582396459 59647869986308833873594689)
                ·
                  refine ⟨44735902489731625405196017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59647869986308833873594689 44735902489731625405196017)
                  ·
                    refine ⟨33551926867298719053897013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44735902489731625405196017 33551926867298719053897013)
                    ·
                      refine ⟨3145493143809254911302845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33551926867298719053897013 3145493143809254911302845)
                      ·
                        rfl

theorem cell23_6125826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_6125826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125826 prefixEnd_6125826 := by exact prefixLift 6125826
  have htrace : WordTrace (prefixWord ++ tailWord_6125826) baseStart_6125826 baseEnd_6125826 := by
    simpa [prefixWord, tailWord_6125826, baseEnd_6125826] using wordTrace_append hprefix tailTrace_6125826
  have hstable : (prefixWord ++ tailWord_6125826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125826).length < 2 ^ (prefixWord ++ tailWord_6125826).sum := by decide
  have hdescent : baseEnd_6125826 < baseStart_6125826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125831 : List Nat := [1, 1, 4, 5, 2, 1, 1, 3, 1, 2, 2]
def baseStart_6125831 : Nat := 118140960795 + 6125831 * 2 ^ 59
def prefixEnd_6125831 : Nat := 4983230072969 + 3 ^ 40 * 6125831 * 2
def baseEnd_6125831 : Nat := 3145495711212527391740323

theorem tailTrace_6125831 : CollatzResearch.WordTrace tailWord_6125831 prefixEnd_6125831 3145495711212527391740323 := by
  unfold tailWord_6125831
  simp only [CollatzResearch.WordTrace]
  refine ⟨223427411870167970486985347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148951607913445313657990231 223427411870167970486985347)
  ·
    refine ⟨335141117805251955730478021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223427411870167970486985347 335141117805251955730478021)
    ·
      refine ⟨62838959588484741699464629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 335141117805251955730478021 62838959588484741699464629)
      ·
        refine ⟨5891152461420444534324809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62838959588484741699464629 5891152461420444534324809)
        ·
          refine ⟨4418364346065333400743607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5891152461420444534324809 4418364346065333400743607)
          ·
            refine ⟨6627546519098000101115411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4418364346065333400743607 6627546519098000101115411)
            ·
              refine ⟨9941319778647000151673117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6627546519098000101115411 9941319778647000151673117)
              ·
                refine ⟨3727994916992625056877419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9941319778647000151673117 3727994916992625056877419)
                ·
                  refine ⟨5591992375488937585316129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3727994916992625056877419 5591992375488937585316129)
                  ·
                    refine ⟨4193994281616703188987097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5591992375488937585316129 4193994281616703188987097)
                    ·
                      refine ⟨3145495711212527391740323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4193994281616703188987097 3145495711212527391740323)
                      ·
                        rfl

theorem cell23_6125831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_6125831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125831 prefixEnd_6125831 := by exact prefixLift 6125831
  have htrace : WordTrace (prefixWord ++ tailWord_6125831) baseStart_6125831 baseEnd_6125831 := by
    simpa [prefixWord, tailWord_6125831, baseEnd_6125831] using wordTrace_append hprefix tailTrace_6125831
  have hstable : (prefixWord ++ tailWord_6125831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125831).length < 2 ^ (prefixWord ++ tailWord_6125831).sum := by decide
  have hdescent : baseEnd_6125831 < baseStart_6125831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125836 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 3, 4, 2]
def baseStart_6125836 : Nat := 118140960795 + 6125836 * 2 ^ 59
def prefixEnd_6125836 : Nat := 4983230072969 + 3 ^ 40 * 6125836 * 2
def baseEnd_6125836 : Nat := 3145498278615799872177799

theorem tailTrace_6125836 : CollatzResearch.WordTrace tailWord_6125836 prefixEnd_6125836 3145498278615799872177799 := by
  unfold tailWord_6125836
  simp only [CollatzResearch.WordTrace]
  refine ⟨111713797117574928170458681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148951729490099904227278241 111713797117574928170458681)
  ·
    refine ⟨83785347838181196127844011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111713797117574928170458681 83785347838181196127844011)
    ·
      refine ⟨125678021757271794191766017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83785347838181196127844011 125678021757271794191766017)
      ·
        refine ⟨94258516317953845643824513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125678021757271794191766017 94258516317953845643824513)
        ·
          refine ⟨70693887238465384232868385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94258516317953845643824513 70693887238465384232868385)
          ·
            refine ⟨53020415428849038174651289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70693887238465384232868385 53020415428849038174651289)
            ·
              refine ⟨39765311571636778630988467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53020415428849038174651289 39765311571636778630988467)
              ·
                refine ⟨59647967357455167946482701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39765311571636778630988467 59647967357455167946482701)
                ·
                  refine ⟨22367987759045687979931013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59647967357455167946482701 22367987759045687979931013)
                  ·
                    refine ⟨4193997704821066496237065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22367987759045687979931013 4193997704821066496237065)
                    ·
                      refine ⟨3145498278615799872177799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4193997704821066496237065 3145498278615799872177799)
                      ·
                        rfl

theorem cell23_6125836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 3, 4, 2].length) (baseStart_6125836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125836 prefixEnd_6125836 := by exact prefixLift 6125836
  have htrace : WordTrace (prefixWord ++ tailWord_6125836) baseStart_6125836 baseEnd_6125836 := by
    simpa [prefixWord, tailWord_6125836, baseEnd_6125836] using wordTrace_append hprefix tailTrace_6125836
  have hstable : (prefixWord ++ tailWord_6125836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125836).length < 2 ^ (prefixWord ++ tailWord_6125836).sum := by decide
  have hdescent : baseEnd_6125836 < baseStart_6125836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125864 : List Nat := [2, 1, 5, 1, 4, 1, 2, 1, 2, 1, 3]
def baseStart_6125864 : Nat := 118140960795 + 6125864 * 2 ^ 59
def prefixEnd_6125864 : Nat := 4983230072969 + 3 ^ 40 * 6125864 * 2
def baseEnd_6125864 : Nat := 3145512656074125762627671

theorem tailTrace_6125864 : CollatzResearch.WordTrace tailWord_6125864 prefixEnd_6125864 3145512656074125762627671 := by
  unfold tailWord_6125864
  simp only [CollatzResearch.WordTrace]
  refine ⟨111714307739524208561468323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148952410319365611415291097 111714307739524208561468323)
  ·
    refine ⟨167571461609286312842202485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111714307739524208561468323 167571461609286312842202485)
    ·
      refine ⟨15709824525870591828956483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167571461609286312842202485 15709824525870591828956483)
      ·
        refine ⟨23564736788805887743434725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15709824525870591828956483 23564736788805887743434725)
        ·
          refine ⟨4418388147901103951894011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23564736788805887743434725 4418388147901103951894011)
          ·
            refine ⟨6627582221851655927841017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4418388147901103951894011 6627582221851655927841017)
            ·
              refine ⟨4970686666388741945880763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6627582221851655927841017 4970686666388741945880763)
              ·
                refine ⟨7456029999583112918821145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4970686666388741945880763 7456029999583112918821145)
                ·
                  refine ⟨5592022499687334689115859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7456029999583112918821145 5592022499687334689115859)
                  ·
                    refine ⟨8388033749531002033673789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5592022499687334689115859 8388033749531002033673789)
                    ·
                      refine ⟨3145512656074125762627671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8388033749531002033673789 3145512656074125762627671)
                      ·
                        rfl

theorem cell23_6125864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_6125864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125864 prefixEnd_6125864 := by exact prefixLift 6125864
  have htrace : WordTrace (prefixWord ++ tailWord_6125864) baseStart_6125864 baseEnd_6125864 := by
    simpa [prefixWord, tailWord_6125864, baseEnd_6125864] using wordTrace_append hprefix tailTrace_6125864
  have hstable : (prefixWord ++ tailWord_6125864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125864).length < 2 ^ (prefixWord ++ tailWord_6125864).sum := by decide
  have hdescent : baseEnd_6125864 < baseStart_6125864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125906 : List Nat := [3, 2, 2, 1, 1, 1, 4, 2, 2, 5]
def baseStart_6125906 : Nat := 118140960795 + 6125906 * 2 ^ 59
def prefixEnd_6125906 : Nat := 4983230072969 + 3 ^ 40 * 6125906 * 2
def baseEnd_6125906 : Nat := 1048511407420538199434159

theorem tailTrace_6125906 : CollatzResearch.WordTrace tailWord_6125906 prefixEnd_6125906 1048511407420538199434159 := by
  unfold tailWord_6125906
  simp only [CollatzResearch.WordTrace]
  refine ⟨55857536836224064573991393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148953431563264172197310381 55857536836224064573991393)
  ·
    refine ⟨41893152627168048430493545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55857536836224064573991393 41893152627168048430493545)
    ·
      refine ⟨31419864470376036322870159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41893152627168048430493545 31419864470376036322870159)
      ·
        refine ⟨47129796705564054484305239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31419864470376036322870159 47129796705564054484305239)
        ·
          refine ⟨70694695058346081726457859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47129796705564054484305239 70694695058346081726457859)
          ·
            refine ⟨106042042587519122589686789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70694695058346081726457859 106042042587519122589686789)
            ·
              refine ⟨19882882985159835485566273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106042042587519122589686789 19882882985159835485566273)
              ·
                refine ⟨14912162238869876614174705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19882882985159835485566273 14912162238869876614174705)
                ·
                  refine ⟨11184121679152407460631029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14912162238869876614174705 11184121679152407460631029)
                  ·
                    refine ⟨1048511407420538199434159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11184121679152407460631029 1048511407420538199434159)
                    ·
                      rfl

theorem cell23_6125906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_6125906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125906 prefixEnd_6125906 := by exact prefixLift 6125906
  have htrace : WordTrace (prefixWord ++ tailWord_6125906) baseStart_6125906 baseEnd_6125906 := by
    simpa [prefixWord, tailWord_6125906, baseEnd_6125906] using wordTrace_append hprefix tailTrace_6125906
  have hstable : (prefixWord ++ tailWord_6125906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125906).length < 2 ^ (prefixWord ++ tailWord_6125906).sum := by decide
  have hdescent : baseEnd_6125906 < baseStart_6125906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125936 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 5, 4]
def baseStart_6125936 : Nat := 118140960795 + 6125936 * 2 ^ 59
def prefixEnd_6125936 : Nat := 4983230072969 + 3 ^ 40 * 6125936 * 2
def baseEnd_6125936 : Nat := 1048516542227083160309113

theorem tailTrace_6125936 : CollatzResearch.WordTrace tailWord_6125936 prefixEnd_6125936 1048516542227083160309113 := by
  unfold tailWord_6125936
  simp only [CollatzResearch.WordTrace]
  refine ⟨111715620767393786709778831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148954161023191715613038441 111715620767393786709778831)
  ·
    refine ⟨167573431151090680064668247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111715620767393786709778831 167573431151090680064668247)
    ·
      refine ⟨251360146726636020097002371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167573431151090680064668247 251360146726636020097002371)
      ·
        refine ⟨377040220089954030145503557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251360146726636020097002371 377040220089954030145503557)
        ·
          refine ⟨70695041266866380652281917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 377040220089954030145503557 70695041266866380652281917)
          ·
            refine ⟨26510640475074892744605719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70695041266866380652281917 26510640475074892744605719)
            ·
              refine ⟨39765960712612339116908579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26510640475074892744605719 39765960712612339116908579)
              ·
                refine ⟨59648941068918508675362869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39765960712612339116908579 59648941068918508675362869)
                ·
                  refine ⟨5592088225211110188315269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59648941068918508675362869 5592088225211110188315269)
                  ·
                    refine ⟨1048516542227083160309113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5592088225211110188315269 1048516542227083160309113)
                    ·
                      rfl

theorem cell23_6125936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 5, 4].length) (baseStart_6125936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125936 prefixEnd_6125936 := by exact prefixLift 6125936
  have htrace : WordTrace (prefixWord ++ tailWord_6125936) baseStart_6125936 baseEnd_6125936 := by
    simpa [prefixWord, tailWord_6125936, baseEnd_6125936] using wordTrace_append hprefix tailTrace_6125936
  have hstable : (prefixWord ++ tailWord_6125936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125936).length < 2 ^ (prefixWord ++ tailWord_6125936).sum := by decide
  have hdescent : baseEnd_6125936 < baseStart_6125936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125939 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 4]
def baseStart_6125939 : Nat := 118140960795 + 6125939 * 2 ^ 59
def prefixEnd_6125939 : Nat := 4983230072969 + 3 ^ 40 * 6125939 * 2
def baseEnd_6125939 : Nat := 3145551167123212969189825

theorem tailTrace_6125939 : CollatzResearch.WordTrace tailWord_6125939 prefixEnd_6125939 3145551167123212969189825 := by
  unfold tailWord_6125939
  simp only [CollatzResearch.WordTrace]
  refine ⟨223431350953776704931916871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148954233969184469954611247 223431350953776704931916871)
  ·
    refine ⟨335147026430665057397875307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223431350953776704931916871 335147026430665057397875307)
    ·
      refine ⟨502720539645997586096812961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335147026430665057397875307 502720539645997586096812961)
      ·
        refine ⟨377040404734498189572609721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 502720539645997586096812961 377040404734498189572609721)
        ·
          refine ⟨282780303550873642179457291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 377040404734498189572609721 282780303550873642179457291)
          ·
            refine ⟨424170455326310463269185937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282780303550873642179457291 424170455326310463269185937)
            ·
              refine ⟨318127841494732847451889453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 424170455326310463269185937 318127841494732847451889453)
              ·
                refine ⟨119297940560524817794458545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 318127841494732847451889453 119297940560524817794458545)
                ·
                  refine ⟨89473455420393613345843909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119297940560524817794458545 89473455420393613345843909)
                  ·
                    refine ⟨16776272891323802502345733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89473455420393613345843909 16776272891323802502345733)
                    ·
                      refine ⟨3145551167123212969189825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16776272891323802502345733 3145551167123212969189825)
                      ·
                        rfl

theorem cell23_6125939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 4].length) (baseStart_6125939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125939 prefixEnd_6125939 := by exact prefixLift 6125939
  have htrace : WordTrace (prefixWord ++ tailWord_6125939) baseStart_6125939 baseEnd_6125939 := by
    simpa [prefixWord, tailWord_6125939, baseEnd_6125939] using wordTrace_append hprefix tailTrace_6125939
  have hstable : (prefixWord ++ tailWord_6125939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125939).length < 2 ^ (prefixWord ++ tailWord_6125939).sum := by decide
  have hdescent : baseEnd_6125939 < baseStart_6125939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125983 : List Nat := [1, 1, 2, 5, 1, 1, 5, 1, 6]
def baseStart_6125983 : Nat := 118140960795 + 6125983 * 2 ^ 59
def prefixEnd_6125983 : Nat := 4983230072969 + 3 ^ 40 * 6125983 * 2
def baseEnd_6125983 : Nat := 349508195585778977448847

theorem tailTrace_6125983 : CollatzResearch.WordTrace tailWord_6125983 prefixEnd_6125983 349508195585778977448847 := by
  unfold tailWord_6125983
  simp only [CollatzResearch.WordTrace]
  refine ⟨223432955765617300446518603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148955303843744866964345735 223432955765617300446518603)
  ·
    refine ⟨335149433648425950669777905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223432955765617300446518603 335149433648425950669777905)
    ·
      refine ⟨251362075236319463002333429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335149433648425950669777905 251362075236319463002333429)
      ·
        refine ⟨23565194553404949656468759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 251362075236319463002333429 23565194553404949656468759)
        ·
          refine ⟨35347791830107424484703139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23565194553404949656468759 35347791830107424484703139)
          ·
            refine ⟨53021687745161136727054709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35347791830107424484703139 53021687745161136727054709)
            ·
              refine ⟨4970783226108856568161379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53021687745161136727054709 4970783226108856568161379)
              ·
                refine ⟨7456174839163284852242069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4970783226108856568161379 7456174839163284852242069)
                ·
                  refine ⟨349508195585778977448847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7456174839163284852242069 349508195585778977448847)
                  ·
                    rfl

theorem cell23_6125983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 6].length) (baseStart_6125983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125983 prefixEnd_6125983 := by exact prefixLift 6125983
  have htrace : WordTrace (prefixWord ++ tailWord_6125983) baseStart_6125983 baseEnd_6125983 := by
    simpa [prefixWord, tailWord_6125983, baseEnd_6125983] using wordTrace_append hprefix tailTrace_6125983
  have hstable : (prefixWord ++ tailWord_6125983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125983).length < 2 ^ (prefixWord ++ tailWord_6125983).sum := by decide
  have hdescent : baseEnd_6125983 < baseStart_6125983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6125986 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_6125986 : Nat := 118140960795 + 6125986 * 2 ^ 59
def prefixEnd_6125986 : Nat := 4983230072969 + 3 ^ 40 * 6125986 * 2
def baseEnd_6125986 : Nat := 3145575300713974285302109

theorem tailTrace_6125986 : CollatzResearch.WordTrace tailWord_6125986 prefixEnd_6125986 3145575300713974285302109 := by
  unfold tailWord_6125986
  simp only [CollatzResearch.WordTrace]
  refine ⟨55858266296151607989719453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148955376789737621305918541 55858266296151607989719453)
  ·
    refine ⟨20946849861056852996144795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55858266296151607989719453 20946849861056852996144795)
    ·
      refine ⟨31420274791585279494217193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20946849861056852996144795 31420274791585279494217193)
      ·
        refine ⟨23565206093688959620662895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31420274791585279494217193 23565206093688959620662895)
        ·
          refine ⟨35347809140533439430994343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23565206093688959620662895 35347809140533439430994343)
          ·
            refine ⟨53021713710800159146491515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35347809140533439430994343 53021713710800159146491515)
            ·
              refine ⟨79532570566200238719737273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53021713710800159146491515 79532570566200238719737273)
              ·
                refine ⟨59649427924650179039802955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79532570566200238719737273 59649427924650179039802955)
                ·
                  refine ⟨89474141886975268559704433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59649427924650179039802955 89474141886975268559704433)
                  ·
                    refine ⟨67105606415231451419778325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89474141886975268559704433 67105606415231451419778325)
                    ·
                      refine ⟨3145575300713974285302109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67105606415231451419778325 3145575300713974285302109)
                      ·
                        rfl

theorem cell23_6125986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_6125986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6125986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6125986 prefixEnd_6125986 := by exact prefixLift 6125986
  have htrace : WordTrace (prefixWord ++ tailWord_6125986) baseStart_6125986 baseEnd_6125986 := by
    simpa [prefixWord, tailWord_6125986, baseEnd_6125986] using wordTrace_append hprefix tailTrace_6125986
  have hstable : (prefixWord ++ tailWord_6125986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6125986).length < 2 ^ (prefixWord ++ tailWord_6125986).sum := by decide
  have hdescent : baseEnd_6125986 < baseStart_6125986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6125986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126013 : List Nat := [1, 4, 1, 2, 2, 2, 2, 3, 1, 5]
def baseStart_6126013 : Nat := 118140960795 + 6126013 * 2 ^ 59
def prefixEnd_6126013 : Nat := 4983230072969 + 3 ^ 40 * 6126013 * 2
def baseEnd_6126013 : Nat := 1048529721563881893221495

theorem tailTrace_6126013 : CollatzResearch.WordTrace tailWord_6126013 prefixEnd_6126013 1048529721563881893221495 := by
  unfold tailWord_6126013
  simp only [CollatzResearch.WordTrace]
  refine ⟨223434049955508615570110693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148956033303672410380073795 223434049955508615570110693)
  ·
    refine ⟨41893884366657865419395755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223434049955508615570110693 41893884366657865419395755)
    ·
      refine ⟨62840826549986798129093633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41893884366657865419395755 62840826549986798129093633)
      ·
        refine ⟨47130619912490098596820225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62840826549986798129093633 47130619912490098596820225)
        ·
          refine ⟨35347964934367573947615169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47130619912490098596820225 35347964934367573947615169)
          ·
            refine ⟨26510973700775680460711377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35347964934367573947615169 26510973700775680460711377)
            ·
              refine ⟨19883230275581760345533533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26510973700775680460711377 19883230275581760345533533)
              ·
                refine ⟨7456211353343160129575075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19883230275581760345533533 7456211353343160129575075)
                ·
                  refine ⟨11184317030014740194362613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7456211353343160129575075 11184317030014740194362613)
                  ·
                    refine ⟨1048529721563881893221495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11184317030014740194362613 1048529721563881893221495)
                    ·
                      rfl

theorem cell23_6126013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_6126013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126013 prefixEnd_6126013 := by exact prefixLift 6126013
  have htrace : WordTrace (prefixWord ++ tailWord_6126013) baseStart_6126013 baseEnd_6126013 := by
    simpa [prefixWord, tailWord_6126013, baseEnd_6126013] using wordTrace_append hprefix tailTrace_6126013
  have hstable : (prefixWord ++ tailWord_6126013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126013).length < 2 ^ (prefixWord ++ tailWord_6126013).sum := by decide
  have hdescent : baseEnd_6126013 < baseStart_6126013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126016 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 4]
def baseStart_6126016 : Nat := 118140960795 + 6126016 * 2 ^ 59
def prefixEnd_6126016 : Nat := 4983230072969 + 3 ^ 40 * 6126016 * 2
def baseEnd_6126016 : Nat := 3145590705133609167926971

theorem tailTrace_6126016 : CollatzResearch.WordTrace tailWord_6126016 prefixEnd_6126016 3145590705133609167926971 := by
  unfold tailWord_6126016
  simp only [CollatzResearch.WordTrace]
  refine ⟨111717079687248873541234951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148956106249665164721646601 111717079687248873541234951)
  ·
    refine ⟨167575619530873310311852427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111717079687248873541234951 167575619530873310311852427)
    ·
      refine ⟨251363429296309965467778641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167575619530873310311852427 251363429296309965467778641)
      ·
        refine ⟨188522571972232474100833981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251363429296309965467778641 188522571972232474100833981)
        ·
          refine ⟨70695964489587177787812743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188522571972232474100833981 70695964489587177787812743)
          ·
            refine ⟨106043946734380766681719115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70695964489587177787812743 106043946734380766681719115)
            ·
              refine ⟨159065920101571150022578673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106043946734380766681719115 159065920101571150022578673)
              ·
                refine ⟨119299440076178362516934005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159065920101571150022578673 119299440076178362516934005)
                ·
                  refine ⟨11184322507141721485962563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119299440076178362516934005 11184322507141721485962563)
                  ·
                    refine ⟨16776483760712582228943845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11184322507141721485962563 16776483760712582228943845)
                    ·
                      refine ⟨3145590705133609167926971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16776483760712582228943845 3145590705133609167926971)
                      ·
                        rfl

theorem cell23_6126016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_6126016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126016 prefixEnd_6126016 := by exact prefixLift 6126016
  have htrace : WordTrace (prefixWord ++ tailWord_6126016) baseStart_6126016 baseEnd_6126016 := by
    simpa [prefixWord, tailWord_6126016, baseEnd_6126016] using wordTrace_append hprefix tailTrace_6126016
  have hstable : (prefixWord ++ tailWord_6126016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126016).length < 2 ^ (prefixWord ++ tailWord_6126016).sum := by decide
  have hdescent : baseEnd_6126016 < baseStart_6126016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126034 : List Nat := [3, 2, 2, 4, 2, 1, 2, 1, 6]
def baseStart_6126034 : Nat := 118140960795 + 6126034 * 2 ^ 59
def prefixEnd_6126034 : Nat := 4983230072969 + 3 ^ 40 * 6126034 * 2
def baseEnd_6126034 : Nat := 349511105309487788611321

theorem tailTrace_6126034 : CollatzResearch.WordTrace tailWord_6126034 prefixEnd_6126034 349511105309487788611321 := by
  unfold tailWord_6126034
  simp only [CollatzResearch.WordTrace]
  refine ⟨55858703972108134039156289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148956543925621690771083437 55858703972108134039156289)
  ·
    refine ⟨41894027979081100529367217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55858703972108134039156289 41894027979081100529367217)
    ·
      refine ⟨31420520984310825397025413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41894027979081100529367217 31420520984310825397025413)
      ·
        refine ⟨5891347684558279761942265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31420520984310825397025413 5891347684558279761942265)
        ·
          refine ⟨4418510763418709821456699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5891347684558279761942265 4418510763418709821456699)
          ·
            refine ⟨6627766145128064732185049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4418510763418709821456699 6627766145128064732185049)
            ·
              refine ⟨4970824608846048549138787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6627766145128064732185049 4970824608846048549138787)
              ·
                refine ⟨7456236913269072823708181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4970824608846048549138787 7456236913269072823708181)
                ·
                  refine ⟨349511105309487788611321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7456236913269072823708181 349511105309487788611321)
                  ·
                    rfl

theorem cell23_6126034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 6].length) (baseStart_6126034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126034 prefixEnd_6126034 := by exact prefixLift 6126034
  have htrace : WordTrace (prefixWord ++ tailWord_6126034) baseStart_6126034 baseEnd_6126034 := by
    simpa [prefixWord, tailWord_6126034, baseEnd_6126034] using wordTrace_append hprefix tailTrace_6126034
  have hstable : (prefixWord ++ tailWord_6126034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126034).length < 2 ^ (prefixWord ++ tailWord_6126034).sum := by decide
  have hdescent : baseEnd_6126034 < baseStart_6126034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126056 : List Nat := [2, 1, 4, 1, 1, 3, 2, 9]
def baseStart_6126056 : Nat := 118140960795 + 6126056 * 2 ^ 59
def prefixEnd_6126056 : Nat := 4983230072969 + 3 ^ 40 * 6126056 * 2
def baseEnd_6126056 : Nat := 116504120161473667089881

theorem tailTrace_6126056 : CollatzResearch.WordTrace tailWord_6126056 prefixEnd_6126056 116504120161473667089881 := by
  unfold tailWord_6126056
  simp only [CollatzResearch.WordTrace]
  refine ⟨111717809147176416956963011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148957078862901889275950681 111717809147176416956963011)
  ·
    refine ⟨167576713720764625435444517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111717809147176416956963011 167576713720764625435444517)
    ·
      refine ⟨31420633822643367269145847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167576713720764625435444517 31420633822643367269145847)
      ·
        refine ⟨47130950733965050903718771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31420633822643367269145847 47130950733965050903718771)
        ·
          refine ⟨70696426100947576355578157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47130950733965050903718771 70696426100947576355578157)
          ·
            refine ⟨26511159787855341133341809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70696426100947576355578157 26511159787855341133341809)
            ·
              refine ⟨19883369840891505850006357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26511159787855341133341809 19883369840891505850006357)
              ·
                refine ⟨116504120161473667089881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19883369840891505850006357 116504120161473667089881)
                ·
                  rfl

theorem cell23_6126056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 9].length) (baseStart_6126056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126056 prefixEnd_6126056 := by exact prefixLift 6126056
  have htrace : WordTrace (prefixWord ++ tailWord_6126056) baseStart_6126056 baseEnd_6126056 := by
    simpa [prefixWord, tailWord_6126056, baseEnd_6126056] using wordTrace_append hprefix tailTrace_6126056
  have hstable : (prefixWord ++ tailWord_6126056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126056).length < 2 ^ (prefixWord ++ tailWord_6126056).sum := by decide
  have hdescent : baseEnd_6126056 < baseStart_6126056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126067 : List Nat := [1, 1, 1, 2, 2, 2, 4, 5, 1, 2, 2]
def baseStart_6126067 : Nat := 118140960795 + 6126067 * 2 ^ 59
def prefixEnd_6126067 : Nat := 4983230072969 + 3 ^ 40 * 6126067 * 2
def baseEnd_6126067 : Nat := 3145616892646988468389237

theorem tailTrace_6126067 : CollatzResearch.WordTrace tailWord_6126067 prefixEnd_6126067 3145616892646988468389237 := by
  unfold tailWord_6126067
  simp only [CollatzResearch.WordTrace]
  refine ⟨223436019497312982792576455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148957346331541988528384303 223436019497312982792576455)
  ·
    refine ⟨335154029245969474188864683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223436019497312982792576455 335154029245969474188864683)
    ·
      refine ⟨502731043868954211283297025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335154029245969474188864683 502731043868954211283297025)
      ·
        refine ⟨377048282901715658462472769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 502731043868954211283297025 377048282901715658462472769)
        ·
          refine ⟨282786212176286743846854577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 377048282901715658462472769 282786212176286743846854577)
          ·
            refine ⟨212089659132215057885140933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282786212176286743846854577 212089659132215057885140933)
            ·
              refine ⟨39766811087290323353463925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 212089659132215057885140933 39766811087290323353463925)
              ·
                refine ⟨3728138539433467814387243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39766811087290323353463925 3728138539433467814387243)
                ·
                  refine ⟨5592207809150201721580865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3728138539433467814387243 5592207809150201721580865)
                  ·
                    refine ⟨4194155856862651291185649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5592207809150201721580865 4194155856862651291185649)
                    ·
                      refine ⟨3145616892646988468389237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4194155856862651291185649 3145616892646988468389237)
                      ·
                        rfl

theorem cell23_6126067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5, 1, 2, 2].length) (baseStart_6126067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126067 prefixEnd_6126067 := by exact prefixLift 6126067
  have htrace : WordTrace (prefixWord ++ tailWord_6126067) baseStart_6126067 baseEnd_6126067 := by
    simpa [prefixWord, tailWord_6126067, baseEnd_6126067] using wordTrace_append hprefix tailTrace_6126067
  have hstable : (prefixWord ++ tailWord_6126067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126067).length < 2 ^ (prefixWord ++ tailWord_6126067).sum := by decide
  have hdescent : baseEnd_6126067 < baseStart_6126067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126134 : List Nat := [5, 1, 2, 1, 2, 1, 3, 2, 2, 1, 3]
def baseStart_6126134 : Nat := 118140960795 + 6126134 * 2 ^ 59
def prefixEnd_6126134 : Nat := 4983230072969 + 3 ^ 40 * 6126134 * 2
def baseEnd_6126134 : Nat := 3145651295850839706251429

theorem tailTrace_6126134 : CollatzResearch.WordTrace tailWord_6126134 prefixEnd_6126134 3145651295850839706251429 := by
  unfold tailWord_6126134
  simp only [CollatzResearch.WordTrace]
  refine ⟨13964903949254390827204091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148958975458713502156843637 13964903949254390827204091)
  ·
    refine ⟨20947355923881586240806137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13964903949254390827204091 20947355923881586240806137)
    ·
      refine ⟨15710516942911189680604603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20947355923881586240806137 15710516942911189680604603)
      ·
        refine ⟨23565775414366784520906905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15710516942911189680604603 23565775414366784520906905)
        ·
          refine ⟨17674331560775088390680179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23565775414366784520906905 17674331560775088390680179)
          ·
            refine ⟨26511497341162632586020269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17674331560775088390680179 26511497341162632586020269)
            ·
              refine ⟨9941811502935987219757601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26511497341162632586020269 9941811502935987219757601)
              ·
                refine ⟨7456358627201990414818201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9941811502935987219757601 7456358627201990414818201)
                ·
                  refine ⟨5592268970401492811113651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7456358627201990414818201 5592268970401492811113651)
                  ·
                    refine ⟨8388403455602239216670477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5592268970401492811113651 8388403455602239216670477)
                    ·
                      refine ⟨3145651295850839706251429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8388403455602239216670477 3145651295850839706251429)
                      ·
                        rfl

theorem cell23_6126134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_6126134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126134 prefixEnd_6126134 := by exact prefixLift 6126134
  have htrace : WordTrace (prefixWord ++ tailWord_6126134) baseStart_6126134 baseEnd_6126134 := by
    simpa [prefixWord, tailWord_6126134, baseEnd_6126134] using wordTrace_append hprefix tailTrace_6126134
  have hstable : (prefixWord ++ tailWord_6126134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126134).length < 2 ^ (prefixWord ++ tailWord_6126134).sum := by decide
  have hdescent : baseEnd_6126134 < baseStart_6126134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126197 : List Nat := [1, 3, 4, 2, 2, 2, 1, 1, 7]
def baseStart_6126197 : Nat := 118140960795 + 6126197 * 2 ^ 59
def prefixEnd_6126197 : Nat := 4983230072969 + 3 ^ 40 * 6126197 * 2
def baseEnd_6126197 : Nat := 349520405014674773307071

theorem tailTrace_6126197 : CollatzResearch.WordTrace tailWord_6126197 prefixEnd_6126197 349520405014674773307071 := by
  unfold tailWord_6126197
  simp only [CollatzResearch.WordTrace]
  refine ⟨223440760986842014994808845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148960507324561343329872563 223440760986842014994808845)
  ·
    refine ⟨83790285370065755623053317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223440760986842014994808845 83790285370065755623053317)
    ·
      refine ⟨15710678506887329179322497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83790285370065755623053317 15710678506887329179322497)
      ·
        refine ⟨11783008880165496884491873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15710678506887329179322497 11783008880165496884491873)
        ·
          refine ⟨8837256660124122663368905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11783008880165496884491873 8837256660124122663368905)
          ·
            refine ⟨6627942495093091997526679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8837256660124122663368905 6627942495093091997526679)
            ·
              refine ⟨9941913742639637996290019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6627942495093091997526679 9941913742639637996290019)
              ·
                refine ⟨14912870613959456994435029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9941913742639637996290019 14912870613959456994435029)
                ·
                  refine ⟨349520405014674773307071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14912870613959456994435029 349520405014674773307071)
                  ·
                    rfl

theorem cell23_6126197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 7].length) (baseStart_6126197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126197 prefixEnd_6126197 := by exact prefixLift 6126197
  have htrace : WordTrace (prefixWord ++ tailWord_6126197) baseStart_6126197 baseEnd_6126197 := by
    simpa [prefixWord, tailWord_6126197, baseEnd_6126197] using wordTrace_append hprefix tailTrace_6126197
  have hstable : (prefixWord ++ tailWord_6126197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126197).length < 2 ^ (prefixWord ++ tailWord_6126197).sum := by decide
  have hdescent : baseEnd_6126197 < baseStart_6126197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126270 : List Nat := [4, 2, 1, 1, 2, 1, 1, 5, 6]
def baseStart_6126270 : Nat := 118140960795 + 6126270 * 2 ^ 59
def prefixEnd_6126270 : Nat := 4983230072969 + 3 ^ 40 * 6126270 * 2
def baseEnd_6126270 : Nat := 349524569913316797127867

theorem tailTrace_6126270 : CollatzResearch.WordTrace tailWord_6126270 prefixEnd_6126270 349524569913316797127867 := by
  unfold tailWord_6126270
  simp only [CollatzResearch.WordTrace]
  refine ⟨27930427939447193557777033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148962282343718365641477509 27930427939447193557777033)
  ·
    refine ⟨20947820954585395168332775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27930427939447193557777033 20947820954585395168332775)
    ·
      refine ⟨31421731431878092752499163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20947820954585395168332775 31421731431878092752499163)
      ·
        refine ⟨47132597147817139128748745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31421731431878092752499163 47132597147817139128748745)
        ·
          refine ⟨35349447860862854346561559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47132597147817139128748745 35349447860862854346561559)
          ·
            refine ⟨53024171791294281519842339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35349447860862854346561559 53024171791294281519842339)
            ·
              refine ⟨79536257686941422279763509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53024171791294281519842339 79536257686941422279763509)
              ·
                refine ⟨7456524158150758338727829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79536257686941422279763509 7456524158150758338727829)
                ·
                  refine ⟨349524569913316797127867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7456524158150758338727829 349524569913316797127867)
                  ·
                    rfl

theorem cell23_6126270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_6126270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126270 prefixEnd_6126270 := by exact prefixLift 6126270
  have htrace : WordTrace (prefixWord ++ tailWord_6126270) baseStart_6126270 baseEnd_6126270 := by
    simpa [prefixWord, tailWord_6126270, baseEnd_6126270] using wordTrace_append hprefix tailTrace_6126270
  have hstable : (prefixWord ++ tailWord_6126270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126270).length < 2 ^ (prefixWord ++ tailWord_6126270).sum := by decide
  have hdescent : baseEnd_6126270 < baseStart_6126270 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126278 : List Nat := [6, 1, 2, 1, 3, 1, 1, 1, 2, 5]
def baseStart_6126278 : Nat := 118140960795 + 6126278 * 2 ^ 59
def prefixEnd_6126278 : Nat := 4983230072969 + 3 ^ 40 * 6126278 * 2
def baseEnd_6126278 : Nat := 1048575079021695714283589

theorem tailTrace_6126278 : CollatzResearch.WordTrace tailWord_6126278 prefixEnd_6126278 1048575079021695714283589 := by
  unfold tailWord_6126278
  simp only [CollatzResearch.WordTrace]
  refine ⟨6982616103110892682140859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 148962476866365710552338325 6982616103110892682140859)
  ·
    refine ⟨10473924154666339023211289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6982616103110892682140859 10473924154666339023211289)
    ·
      refine ⟨7855443115999754267408467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10473924154666339023211289 7855443115999754267408467)
      ·
        refine ⟨11783164673999631401112701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7855443115999754267408467 11783164673999631401112701)
        ·
          refine ⟨4418686752749861775417263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11783164673999631401112701 4418686752749861775417263)
          ·
            refine ⟨6628030129124792663125895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4418686752749861775417263 6628030129124792663125895)
            ·
              refine ⟨9942045193687188994688843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6628030129124792663125895 9942045193687188994688843)
              ·
                refine ⟨14913067790530783492033265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9942045193687188994688843 14913067790530783492033265)
                ·
                  refine ⟨11184800842898087619024949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14913067790530783492033265 11184800842898087619024949)
                  ·
                    refine ⟨1048575079021695714283589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11184800842898087619024949 1048575079021695714283589)
                    ·
                      rfl

theorem cell23_6126278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_6126278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126278 prefixEnd_6126278 := by exact prefixLift 6126278
  have htrace : WordTrace (prefixWord ++ tailWord_6126278) baseStart_6126278 baseEnd_6126278 := by
    simpa [prefixWord, tailWord_6126278, baseEnd_6126278] using wordTrace_append hprefix tailTrace_6126278
  have hstable : (prefixWord ++ tailWord_6126278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126278).length < 2 ^ (prefixWord ++ tailWord_6126278).sum := by decide
  have hdescent : baseEnd_6126278 < baseStart_6126278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126284 : List Nat := [2, 2, 1, 5, 1, 3, 1, 1, 2, 2, 3]
def baseStart_6126284 : Nat := 118140960795 + 6126284 * 2 ^ 59
def prefixEnd_6126284 : Nat := 4983230072969 + 3 ^ 40 * 6126284 * 2
def baseEnd_6126284 : Nat := 3145728317949014119375739

theorem tailTrace_6126284 : CollatzResearch.WordTrace tailWord_6126284 prefixEnd_6126284 3145728317949014119375739 := by
  unfold tailWord_6126284
  simp only [CollatzResearch.WordTrace]
  refine ⟨111721967068763414426612953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148962622758351219235483937 111721967068763414426612953)
  ·
    refine ⟨83791475301572560819959715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111721967068763414426612953 83791475301572560819959715)
    ·
      refine ⟨125687212952358841229939573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83791475301572560819959715 125687212952358841229939573)
      ·
        refine ⟨11783176214283641365306835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125687212952358841229939573 11783176214283641365306835)
        ·
          refine ⟨17674764321425462047960253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11783176214283641365306835 17674764321425462047960253)
          ·
            refine ⟨6628036620534548267985095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17674764321425462047960253 6628036620534548267985095)
            ·
              refine ⟨9942054930801822401977643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6628036620534548267985095 9942054930801822401977643)
              ·
                refine ⟨14913082396202733602966465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9942054930801822401977643 14913082396202733602966465)
                ·
                  refine ⟨11184811797152050202224849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14913082396202733602966465 11184811797152050202224849)
                  ·
                    refine ⟨8388608847864037651668637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11184811797152050202224849 8388608847864037651668637)
                    ·
                      refine ⟨3145728317949014119375739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8388608847864037651668637 3145728317949014119375739)
                      ·
                        rfl

theorem cell23_6126284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_6126284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126284 prefixEnd_6126284 := by exact prefixLift 6126284
  have htrace : WordTrace (prefixWord ++ tailWord_6126284) baseStart_6126284 baseEnd_6126284 := by
    simpa [prefixWord, tailWord_6126284, baseEnd_6126284] using wordTrace_append hprefix tailTrace_6126284
  have hstable : (prefixWord ++ tailWord_6126284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126284).length < 2 ^ (prefixWord ++ tailWord_6126284).sum := by decide
  have hdescent : baseEnd_6126284 < baseStart_6126284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126313 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 3, 6]
def baseStart_6126313 : Nat := 118140960795 + 6126313 * 2 ^ 59
def prefixEnd_6126313 : Nat := 4983230072969 + 3 ^ 40 * 6126313 * 2
def baseEnd_6126313 : Nat := 1048581069629331501971035

theorem tailTrace_6126313 : CollatzResearch.WordTrace tailWord_6126313 prefixEnd_6126313 1048581069629331501971035 := by
  unfold tailWord_6126313
  simp only [CollatzResearch.WordTrace]
  refine ⟨223444991854421766806031593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148963327902947844537354395 223444991854421766806031593)
  ·
    refine ⟨167583743890816325104523695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223444991854421766806031593 167583743890816325104523695)
    ·
      refine ⟨251375615836224487656785543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167583743890816325104523695 251375615836224487656785543)
      ·
        refine ⟨377063423754336731485178315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251375615836224487656785543 377063423754336731485178315)
        ·
          refine ⟨565595135631505097227767473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377063423754336731485178315 565595135631505097227767473)
          ·
            refine ⟨424196351723628822920825605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 565595135631505097227767473 424196351723628822920825605)
            ·
              refine ⟨79536815948180404297654801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 424196351723628822920825605 79536815948180404297654801)
              ·
                refine ⟨59652611961135303223241101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79536815948180404297654801 59652611961135303223241101)
                ·
                  refine ⟨22369729485425738708715413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59652611961135303223241101 22369729485425738708715413)
                  ·
                    refine ⟨1048581069629331501971035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22369729485425738708715413 1048581069629331501971035)
                    ·
                      rfl

theorem cell23_6126313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 6].length) (baseStart_6126313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126313 prefixEnd_6126313 := by exact prefixLift 6126313
  have htrace : WordTrace (prefixWord ++ tailWord_6126313) baseStart_6126313 baseEnd_6126313 := by
    simpa [prefixWord, tailWord_6126313, baseEnd_6126313] using wordTrace_append hprefix tailTrace_6126313
  have hstable : (prefixWord ++ tailWord_6126313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126313).length < 2 ^ (prefixWord ++ tailWord_6126313).sum := by decide
  have hdescent : baseEnd_6126313 < baseStart_6126313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126330 : List Nat := [3, 1, 1, 1, 1, 3, 5, 1, 1, 6]
def baseStart_6126330 : Nat := 118140960795 + 6126330 * 2 ^ 59
def prefixEnd_6126330 : Nat := 4983230072969 + 3 ^ 40 * 6126330 * 2
def baseEnd_6126330 : Nat := 1048583979353040313133509

theorem tailTrace_6126330 : CollatzResearch.WordTrace tailWord_6126330 prefixEnd_6126330 1048583979353040313133509 := by
  unfold tailWord_6126330
  simp only [CollatzResearch.WordTrace]
  refine ⟨55861402973840044677350111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148963741263573452472933629 55861402973840044677350111)
  ·
    refine ⟨83792104460760067016025167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55861402973840044677350111 83792104460760067016025167)
    ·
      refine ⟨125688156691140100524037751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83792104460760067016025167 125688156691140100524037751)
      ·
        refine ⟨188532235036710150786056627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125688156691140100524037751 188532235036710150786056627)
        ·
          refine ⟨282798352555065226179084941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188532235036710150786056627 282798352555065226179084941)
          ·
            refine ⟨106049382208149459817156853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 282798352555065226179084941 106049382208149459817156853)
            ·
              refine ⟨9942129582014011857858455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106049382208149459817156853 9942129582014011857858455)
              ·
                refine ⟨14913194373021017786787683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9942129582014011857858455 14913194373021017786787683)
                ·
                  refine ⟨22369791559531526680181525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14913194373021017786787683 22369791559531526680181525)
                  ·
                    refine ⟨1048583979353040313133509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22369791559531526680181525 1048583979353040313133509)
                    ·
                      rfl

theorem cell23_6126330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 1, 6].length) (baseStart_6126330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126330 prefixEnd_6126330 := by exact prefixLift 6126330
  have htrace : WordTrace (prefixWord ++ tailWord_6126330) baseStart_6126330 baseEnd_6126330 := by
    simpa [prefixWord, tailWord_6126330, baseEnd_6126330] using wordTrace_append hprefix tailTrace_6126330
  have hstable : (prefixWord ++ tailWord_6126330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126330).length < 2 ^ (prefixWord ++ tailWord_6126330).sum := by decide
  have hdescent : baseEnd_6126330 < baseStart_6126330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126334 : List Nat := [4, 2, 2, 1, 2, 2, 2, 2, 1, 5]
def baseStart_6126334 : Nat := 118140960795 + 6126334 * 2 ^ 59
def prefixEnd_6126334 : Nat := 4983230072969 + 3 ^ 40 * 6126334 * 2
def baseEnd_6126334 : Nat := 1048584663993912974583503

theorem tailTrace_6126334 : CollatzResearch.WordTrace tailWord_6126334 prefixEnd_6126334 1048584663993912974583503 := by
  unfold tailWord_6126334
  simp only [CollatzResearch.WordTrace]
  refine ⟨27930719723418210924068257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148963838524897124928364037 27930719723418210924068257)
  ·
    refine ⟨20948039792563658193051193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27930719723418210924068257 20948039792563658193051193)
    ·
      refine ⟨15711029844422743644788395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20948039792563658193051193 15711029844422743644788395)
      ·
        refine ⟨23566544766634115467182593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15711029844422743644788395 23566544766634115467182593)
        ·
          refine ⟨17674908574975586600386945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23566544766634115467182593 17674908574975586600386945)
          ·
            refine ⟨13256181431231689950290209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17674908574975586600386945 13256181431231689950290209)
            ·
              refine ⟨9942136073423767462717657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13256181431231689950290209 9942136073423767462717657)
              ·
                refine ⟨7456602055067825597038243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9942136073423767462717657 7456602055067825597038243)
                ·
                  refine ⟨11184903082601738395557365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7456602055067825597038243 11184903082601738395557365)
                  ·
                    refine ⟨1048584663993912974583503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11184903082601738395557365 1048584663993912974583503)
                    ·
                      rfl

theorem cell23_6126334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_6126334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126334 prefixEnd_6126334 := by exact prefixLift 6126334
  have htrace : WordTrace (prefixWord ++ tailWord_6126334) baseStart_6126334 baseEnd_6126334 := by
    simpa [prefixWord, tailWord_6126334, baseEnd_6126334] using wordTrace_append hprefix tailTrace_6126334
  have hstable : (prefixWord ++ tailWord_6126334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126334).length < 2 ^ (prefixWord ++ tailWord_6126334).sum := by decide
  have hdescent : baseEnd_6126334 < baseStart_6126334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126340 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_6126340 : Nat := 118140960795 + 6126340 * 2 ^ 59
def prefixEnd_6126340 : Nat := 4983230072969 + 3 ^ 40 * 6126340 * 2
def baseEnd_6126340 : Nat := 3145757072865665900275481

theorem tailTrace_6126340 : CollatzResearch.WordTrace tailWord_6126340 prefixEnd_6126340 3145757072865665900275481 := by
  unfold tailWord_6126340
  simp only [CollatzResearch.WordTrace]
  refine ⟨111722988312661975208632237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148963984416882633611509649 111722988312661975208632237)
  ·
    refine ⟨41896120617248240703237089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111722988312661975208632237 41896120617248240703237089)
    ·
      refine ⟨31422090462936180527427817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41896120617248240703237089 31422090462936180527427817)
      ·
        refine ⟨23566567847202135395570863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31422090462936180527427817 23566567847202135395570863)
        ·
          refine ⟨35349851770803203093356295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23566567847202135395570863 35349851770803203093356295)
          ·
            refine ⟨53024777656204804640034443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35349851770803203093356295 53024777656204804640034443)
            ·
              refine ⟨79537166484307206960051665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53024777656204804640034443 79537166484307206960051665)
              ·
                refine ⟨59652874863230405220038749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79537166484307206960051665 59652874863230405220038749)
                ·
                  refine ⟨22369828073711401957514531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59652874863230405220038749 22369828073711401957514531)
                  ·
                    refine ⟨33554742110567102936271797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22369828073711401957514531 33554742110567102936271797)
                    ·
                      refine ⟨3145757072865665900275481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33554742110567102936271797 3145757072865665900275481)
                      ·
                        rfl

theorem cell23_6126340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_6126340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126340 prefixEnd_6126340 := by exact prefixLift 6126340
  have htrace : WordTrace (prefixWord ++ tailWord_6126340) baseStart_6126340 baseEnd_6126340 := by
    simpa [prefixWord, tailWord_6126340, baseEnd_6126340] using wordTrace_append hprefix tailTrace_6126340
  have hstable : (prefixWord ++ tailWord_6126340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126340).length < 2 ^ (prefixWord ++ tailWord_6126340).sum := by decide
  have hdescent : baseEnd_6126340 < baseStart_6126340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126350 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4]
def baseStart_6126350 : Nat := 118140960795 + 6126350 * 2 ^ 59
def prefixEnd_6126350 : Nat := 4983230072969 + 3 ^ 40 * 6126350 * 2
def baseEnd_6126350 : Nat := 3145762207672210861150435

theorem tailTrace_6126350 : CollatzResearch.WordTrace tailWord_6126350 prefixEnd_6126350 3145762207672210861150435 := by
  unfold tailWord_6126350
  simp only [CollatzResearch.WordTrace]
  refine ⟨27930792669410965265641063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148964227570191814750085669 27930792669410965265641063)
  ·
    refine ⟨41896189004116447898461595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27930792669410965265641063 41896189004116447898461595)
    ·
      refine ⟨62844283506174671847692393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41896189004116447898461595 62844283506174671847692393)
      ·
        refine ⟨47133212629631003885769295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62844283506174671847692393 47133212629631003885769295)
        ·
          refine ⟨70699818944446505828653943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47133212629631003885769295 70699818944446505828653943)
          ·
            refine ⟨106049728416669758742980915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70699818944446505828653943 106049728416669758742980915)
            ·
              refine ⟨159074592625004638114471373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106049728416669758742980915 159074592625004638114471373)
              ·
                refine ⟨59652972234376739292926765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159074592625004638114471373 59652972234376739292926765)
                ·
                  refine ⟨22369864587891277234847537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59652972234376739292926765 22369864587891277234847537)
                  ·
                    refine ⟨16777398440918457926135653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22369864587891277234847537 16777398440918457926135653)
                    ·
                      refine ⟨3145762207672210861150435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16777398440918457926135653 3145762207672210861150435)
                      ·
                        rfl

theorem cell23_6126350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_6126350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126350 prefixEnd_6126350 := by exact prefixLift 6126350
  have htrace : WordTrace (prefixWord ++ tailWord_6126350) baseStart_6126350 baseEnd_6126350 := by
    simpa [prefixWord, tailWord_6126350, baseEnd_6126350] using wordTrace_append hprefix tailTrace_6126350
  have hstable : (prefixWord ++ tailWord_6126350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126350).length < 2 ^ (prefixWord ++ tailWord_6126350).sum := by decide
  have hdescent : baseEnd_6126350 < baseStart_6126350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126357 : List Nat := [1, 3, 2, 1, 2, 2, 1, 5, 1, 2, 3]
def baseStart_6126357 : Nat := 118140960795 + 6126357 * 2 ^ 59
def prefixEnd_6126357 : Nat := 4983230072969 + 3 ^ 40 * 6126357 * 2
def baseEnd_6126357 : Nat := 3145765802036792333762903

theorem tailTrace_6126357 : CollatzResearch.WordTrace tailWord_6126357 prefixEnd_6126357 3145765802036792333762903 := by
  unfold tailWord_6126357
  simp only [CollatzResearch.WordTrace]
  refine ⟨223446596666262362320633325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148964397777508241547088883 223446596666262362320633325)
  ·
    refine ⟨83792473749848385870237497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223446596666262362320633325 83792473749848385870237497)
    ·
      refine ⟨62844355312386289402678123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83792473749848385870237497 62844355312386289402678123)
      ·
        refine ⟨94266532968579434104017185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62844355312386289402678123 94266532968579434104017185)
        ·
          refine ⟨70699899726434575578012889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94266532968579434104017185 70699899726434575578012889)
          ·
            refine ⟨53024924794825931683509667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70699899726434575578012889 53024924794825931683509667)
            ·
              refine ⟨79537387192238897525264501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53024924794825931683509667 79537387192238897525264501)
              ·
                refine ⟨7456630049272396642993547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79537387192238897525264501 7456630049272396642993547)
                ·
                  refine ⟨11184945073908594964490321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7456630049272396642993547 11184945073908594964490321)
                  ·
                    refine ⟨8388708805431446223367741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11184945073908594964490321 8388708805431446223367741)
                    ·
                      refine ⟨3145765802036792333762903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8388708805431446223367741 3145765802036792333762903)
                      ·
                        rfl

theorem cell23_6126357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_6126357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126357 prefixEnd_6126357 := by exact prefixLift 6126357
  have htrace : WordTrace (prefixWord ++ tailWord_6126357) baseStart_6126357 baseEnd_6126357 := by
    simpa [prefixWord, tailWord_6126357, baseEnd_6126357] using wordTrace_append hprefix tailTrace_6126357
  have hstable : (prefixWord ++ tailWord_6126357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126357).length < 2 ^ (prefixWord ++ tailWord_6126357).sum := by decide
  have hdescent : baseEnd_6126357 < baseStart_6126357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126363 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 6]
def baseStart_6126363 : Nat := 118140960795 + 6126363 * 2 ^ 59
def prefixEnd_6126363 : Nat := 4983230072969 + 3 ^ 40 * 6126363 * 2
def baseEnd_6126363 : Nat := 3145768882920719310287875

theorem tailTrace_6126363 : CollatzResearch.WordTrace tailWord_6126363 prefixEnd_6126363 3145768882920719310287875 := by
  unfold tailWord_6126363
  simp only [CollatzResearch.WordTrace]
  refine ⟨223446815504240625345351743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148964543669493750230234495 223446815504240625345351743)
  ·
    refine ⟨335170223256360938018027615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223446815504240625345351743 335170223256360938018027615)
    ·
      refine ⟨502755334884541407027041423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335170223256360938018027615 502755334884541407027041423)
      ·
        refine ⟨754133002326812110540562135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502755334884541407027041423 754133002326812110540562135)
        ·
          refine ⟨1131199503490218165810843203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754133002326812110540562135 1131199503490218165810843203)
          ·
            refine ⟨1696799255235327248716264805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131199503490218165810843203 1696799255235327248716264805)
            ·
              refine ⟨318149860356623859134299651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1696799255235327248716264805 318149860356623859134299651)
              ·
                refine ⟨477224790534935788701449477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318149860356623859134299651 477224790534935788701449477)
                ·
                  refine ⟨89479648225300460381521777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 477224790534935788701449477 89479648225300460381521777)
                  ·
                    refine ⟨67109736168975345286141333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89479648225300460381521777 67109736168975345286141333)
                    ·
                      refine ⟨3145768882920719310287875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67109736168975345286141333 3145768882920719310287875)
                      ·
                        rfl

theorem cell23_6126363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 6].length) (baseStart_6126363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126363 prefixEnd_6126363 := by exact prefixLift 6126363
  have htrace : WordTrace (prefixWord ++ tailWord_6126363) baseStart_6126363 baseEnd_6126363 := by
    simpa [prefixWord, tailWord_6126363, baseEnd_6126363] using wordTrace_append hprefix tailTrace_6126363
  have hstable : (prefixWord ++ tailWord_6126363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126363).length < 2 ^ (prefixWord ++ tailWord_6126363).sum := by decide
  have hdescent : baseEnd_6126363 < baseStart_6126363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126365 : List Nat := [1, 4, 2, 4, 1, 1, 3, 2, 1, 1, 3]
def baseStart_6126365 : Nat := 118140960795 + 6126365 * 2 ^ 59
def prefixEnd_6126365 : Nat := 4983230072969 + 3 ^ 40 * 6126365 * 2
def baseEnd_6126365 : Nat := 3145769909882028302462867

theorem tailTrace_6126365 : CollatzResearch.WordTrace tailWord_6126365 prefixEnd_6126365 3145769909882028302462867 := by
  unfold tailWord_6126365
  simp only [CollatzResearch.WordTrace]
  refine ⟨223446888450233379686924549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148964592300155586457949699 223446888450233379686924549)
  ·
    refine ⟨41896291584418758691298353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223446888450233379686924549 41896291584418758691298353)
    ·
      refine ⟨31422218688314069018473765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41896291584418758691298353 31422218688314069018473765)
      ·
        refine ⟨5891666004058887940963831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31422218688314069018473765 5891666004058887940963831)
        ·
          refine ⟨8837499006088331911445747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5891666004058887940963831 8837499006088331911445747)
          ·
            refine ⟨13256248509132497867168621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8837499006088331911445747 13256248509132497867168621)
            ·
              refine ⟨4971093190924686700188233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13256248509132497867168621 4971093190924686700188233)
              ·
                refine ⟨3728319893193515025141175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4971093190924686700188233 3728319893193515025141175)
                ·
                  refine ⟨5592479839790272537711763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3728319893193515025141175 5592479839790272537711763)
                  ·
                    refine ⟨8388719759685408806567645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5592479839790272537711763 8388719759685408806567645)
                    ·
                      refine ⟨3145769909882028302462867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8388719759685408806567645 3145769909882028302462867)
                      ·
                        rfl

theorem cell23_6126365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_6126365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126365 prefixEnd_6126365 := by exact prefixLift 6126365
  have htrace : WordTrace (prefixWord ++ tailWord_6126365) baseStart_6126365 baseEnd_6126365 := by
    simpa [prefixWord, tailWord_6126365, baseEnd_6126365] using wordTrace_append hprefix tailTrace_6126365
  have hstable : (prefixWord ++ tailWord_6126365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126365).length < 2 ^ (prefixWord ++ tailWord_6126365).sum := by decide
  have hdescent : baseEnd_6126365 < baseStart_6126365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126388 : List Nat := [2, 5, 1, 1, 4, 1, 1, 2, 1, 1, 4]
def baseStart_6126388 : Nat := 118140960795 + 6126388 * 2 ^ 59
def prefixEnd_6126388 : Nat := 4983230072969 + 3 ^ 40 * 6126388 * 2
def baseEnd_6126388 : Nat := 3145781719937081712475261

theorem tailTrace_6126388 : CollatzResearch.WordTrace tailWord_6126388 prefixEnd_6126388 3145781719937081712475261 := by
  unfold tailWord_6126388
  simp only [CollatzResearch.WordTrace]
  refine ⟨111723863664575027307505909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148965151552766703076674545 111723863664575027307505909)
  ·
    refine ⟨10474112218553908810078679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111723863664575027307505909 10474112218553908810078679)
    ·
      refine ⟨15711168327830863215118019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10474112218553908810078679 15711168327830863215118019)
      ·
        refine ⟨23566752491746294822677029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15711168327830863215118019 23566752491746294822677029)
        ·
          refine ⟨4418766092202430279251943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23566752491746294822677029 4418766092202430279251943)
          ·
            refine ⟨6628149138303645418877915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4418766092202430279251943 6628149138303645418877915)
            ·
              refine ⟨9942223707455468128316873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6628149138303645418877915 9942223707455468128316873)
              ·
                refine ⟨7456667780591601096237655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9942223707455468128316873 7456667780591601096237655)
                ·
                  refine ⟨11185001670887401644356483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7456667780591601096237655 11185001670887401644356483)
                  ·
                    refine ⟨16777502506331102466534725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11185001670887401644356483 16777502506331102466534725)
                    ·
                      refine ⟨3145781719937081712475261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16777502506331102466534725 3145781719937081712475261)
                      ·
                        rfl

theorem cell23_6126388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_6126388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126388 prefixEnd_6126388 := by exact prefixLift 6126388
  have htrace : WordTrace (prefixWord ++ tailWord_6126388) baseStart_6126388 baseEnd_6126388 := by
    simpa [prefixWord, tailWord_6126388, baseEnd_6126388] using wordTrace_append hprefix tailTrace_6126388
  have hstable : (prefixWord ++ tailWord_6126388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126388).length < 2 ^ (prefixWord ++ tailWord_6126388).sum := by decide
  have hdescent : baseEnd_6126388 < baseStart_6126388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126414 : List Nat := [4, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2]
def baseStart_6126414 : Nat := 118140960795 + 6126414 * 2 ^ 59
def prefixEnd_6126414 : Nat := 4983230072969 + 3 ^ 40 * 6126414 * 2
def baseEnd_6126414 : Nat := 3145795070434098610750141

theorem tailTrace_6126414 : CollatzResearch.WordTrace tailWord_6126414 prefixEnd_6126414 3145795070434098610750141 := by
  unfold tailWord_6126414
  simp only [CollatzResearch.WordTrace]
  refine ⟨27931084453381982631932287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148965783751370574036972197 27931084453381982631932287)
  ·
    refine ⟨41896626680072973947898431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27931084453381982631932287 41896626680072973947898431)
    ·
      refine ⟨62844940020109460921847647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41896626680072973947898431 62844940020109460921847647)
      ·
        refine ⟨94267410030164191382771471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62844940020109460921847647 94267410030164191382771471)
        ·
          refine ⟨141401115045246287074157207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94267410030164191382771471 141401115045246287074157207)
          ·
            refine ⟨212101672567869430611235811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141401115045246287074157207 212101672567869430611235811)
            ·
              refine ⟨318152508851804145916853717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212101672567869430611235811 318152508851804145916853717)
              ·
                refine ⟨7456699426214159669926259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 318152508851804145916853717 7456699426214159669926259)
                ·
                  refine ⟨11185049139321239504889389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7456699426214159669926259 11185049139321239504889389)
                  ·
                    refine ⟨4194393427245464814333521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11185049139321239504889389 4194393427245464814333521)
                    ·
                      refine ⟨3145795070434098610750141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4194393427245464814333521 3145795070434098610750141)
                      ·
                        rfl

theorem cell23_6126414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2].length) (baseStart_6126414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126414 prefixEnd_6126414 := by exact prefixLift 6126414
  have htrace : WordTrace (prefixWord ++ tailWord_6126414) baseStart_6126414 baseEnd_6126414 := by
    simpa [prefixWord, tailWord_6126414, baseEnd_6126414] using wordTrace_append hprefix tailTrace_6126414
  have hstable : (prefixWord ++ tailWord_6126414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126414).length < 2 ^ (prefixWord ++ tailWord_6126414).sum := by decide
  have hdescent : baseEnd_6126414 < baseStart_6126414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126444 : List Nat := [2, 2, 1, 1, 4, 1, 4, 1, 1, 4, 2]
def baseStart_6126444 : Nat := 118140960795 + 6126444 * 2 ^ 59
def prefixEnd_6126444 : Nat := 4983230072969 + 3 ^ 40 * 6126444 * 2
def baseEnd_6126444 : Nat := 3145810474853733493375003

theorem tailTrace_6126444 : CollatzResearch.WordTrace tailWord_6126444 prefixEnd_6126444 3145810474853733493375003 := by
  unfold tailWord_6126444
  simp only [CollatzResearch.WordTrace]
  refine ⟨111724884908473588089525193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148966513211298117452700257 111724884908473588089525193)
  ·
    refine ⟨83793663681355191067143895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111724884908473588089525193 83793663681355191067143895)
    ·
      refine ⟨125690495522032786600715843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83793663681355191067143895 125690495522032786600715843)
      ·
        refine ⟨188535743283049179901073765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125690495522032786600715843 188535743283049179901073765)
        ·
          refine ⟨35350451865571721231451331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188535743283049179901073765 35350451865571721231451331)
          ·
            refine ⟨53025677798357581847176997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35350451865571721231451331 53025677798357581847176997)
            ·
              refine ⟨9942314587192046596345687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53025677798357581847176997 9942314587192046596345687)
              ·
                refine ⟨14913471880788069894518531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9942314587192046596345687 14913471880788069894518531)
                ·
                  refine ⟨22370207821182104841777797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14913471880788069894518531 22370207821182104841777797)
                  ·
                    refine ⟨4194413966471644657833337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22370207821182104841777797 4194413966471644657833337)
                    ·
                      refine ⟨3145810474853733493375003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4194413966471644657833337 3145810474853733493375003)
                      ·
                        rfl

theorem cell23_6126444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 4, 2].length) (baseStart_6126444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126444 prefixEnd_6126444 := by exact prefixLift 6126444
  have htrace : WordTrace (prefixWord ++ tailWord_6126444) baseStart_6126444 baseEnd_6126444 := by
    simpa [prefixWord, tailWord_6126444, baseEnd_6126444] using wordTrace_append hprefix tailTrace_6126444
  have hstable : (prefixWord ++ tailWord_6126444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126444).length < 2 ^ (prefixWord ++ tailWord_6126444).sum := by decide
  have hdescent : baseEnd_6126444 < baseStart_6126444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126450 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 9]
def baseStart_6126450 : Nat := 118140960795 + 6126450 * 2 ^ 59
def prefixEnd_6126450 : Nat := 4983230072969 + 3 ^ 40 * 6126450 * 2
def baseEnd_6126450 : Nat := 349534839526406718877775

theorem tailTrace_6126450 : CollatzResearch.WordTrace tailWord_6126450 prefixEnd_6126450 349534839526406718877775 := by
  unfold tailWord_6126450
  simp only [CollatzResearch.WordTrace]
  refine ⟨55862497163731359800942201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148966659103283626135845869 55862497163731359800942201)
  ·
    refine ⟨41896872872798519850706651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55862497163731359800942201 41896872872798519850706651)
    ·
      refine ⟨62845309309197779776059977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41896872872798519850706651 62845309309197779776059977)
      ·
        refine ⟨47133981981898334832044983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62845309309197779776059977 47133981981898334832044983)
        ·
          refine ⟨70700972972847502248067475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47133981981898334832044983 70700972972847502248067475)
          ·
            refine ⟨106051459459271253372101213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70700972972847502248067475 106051459459271253372101213)
            ·
              refine ⟨39769297297226720014537955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106051459459271253372101213 39769297297226720014537955)
              ·
                refine ⟨59653945945840080021806933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39769297297226720014537955 59653945945840080021806933)
                ·
                  refine ⟨349534839526406718877775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59653945945840080021806933 349534839526406718877775)
                  ·
                    rfl

theorem cell23_6126450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 9].length) (baseStart_6126450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126450 prefixEnd_6126450 := by exact prefixLift 6126450
  have htrace : WordTrace (prefixWord ++ tailWord_6126450) baseStart_6126450 baseEnd_6126450 := by
    simpa [prefixWord, tailWord_6126450, baseEnd_6126450] using wordTrace_append hprefix tailTrace_6126450
  have hstable : (prefixWord ++ tailWord_6126450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126450).length < 2 ^ (prefixWord ++ tailWord_6126450).sum := by decide
  have hdescent : baseEnd_6126450 < baseStart_6126450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126484 : List Nat := [2, 4, 2, 1, 1, 1, 1, 6, 5]
def baseStart_6126484 : Nat := 118140960795 + 6126484 * 2 ^ 59
def prefixEnd_6126484 : Nat := 4983230072969 + 3 ^ 40 * 6126484 * 2
def baseEnd_6126484 : Nat := 349536779342212592986091

theorem tailTrace_6126484 : CollatzResearch.WordTrace tailWord_6126484 prefixEnd_6126484 349536779342212592986091 := by
  unfold tailWord_6126484
  simp only [CollatzResearch.WordTrace]
  refine ⟨111725614368401131505253253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148967485824534842007004337 111725614368401131505253253)
  ·
    refine ⟨20948552694075212157234985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111725614368401131505253253 20948552694075212157234985)
    ·
      refine ⟨15711414520556409117926239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20948552694075212157234985 15711414520556409117926239)
      ·
        refine ⟨23567121780834613676889359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15711414520556409117926239 23567121780834613676889359)
        ·
          refine ⟨35350682671251920515334039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23567121780834613676889359 35350682671251920515334039)
          ·
            refine ⟨53026024006877880773001059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35350682671251920515334039 53026024006877880773001059)
            ·
              refine ⟨79539036010316821159501589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53026024006877880773001059 79539036010316821159501589)
              ·
                refine ⟨3728392312983600991851637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79539036010316821159501589 3728392312983600991851637)
                ·
                  refine ⟨349536779342212592986091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3728392312983600991851637 349536779342212592986091)
                  ·
                    rfl

theorem cell23_6126484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_6126484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126484 prefixEnd_6126484 := by exact prefixLift 6126484
  have htrace : WordTrace (prefixWord ++ tailWord_6126484) baseStart_6126484 baseEnd_6126484 := by
    simpa [prefixWord, tailWord_6126484, baseEnd_6126484] using wordTrace_append hprefix tailTrace_6126484
  have hstable : (prefixWord ++ tailWord_6126484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126484).length < 2 ^ (prefixWord ++ tailWord_6126484).sum := by decide
  have hdescent : baseEnd_6126484 < baseStart_6126484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126497 : List Nat := [1, 2, 3, 4, 1, 1, 1, 2, 1, 7]
def baseStart_6126497 : Nat := 118140960795 + 6126497 * 2 ^ 59
def prefixEnd_6126497 : Nat := 4983230072969 + 3 ^ 40 * 6126497 * 2
def baseEnd_6126497 : Nat := 1048612563109473928670753

theorem tailTrace_6126497 : CollatzResearch.WordTrace tailWord_6126497 prefixEnd_6126497 1048612563109473928670753 := by
  unfold tailWord_6126497
  simp only [CollatzResearch.WordTrace]
  refine ⟨223451702885755166230729745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148967801923836777487153163 223451702885755166230729745)
  ·
    refine ⟨167588777164316374673047309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223451702885755166230729745 167588777164316374673047309)
    ·
      refine ⟨62845791436618640502392741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167588777164316374673047309 62845791436618640502392741)
      ·
        refine ⟨11783585894365995094198639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62845791436618640502392741 11783585894365995094198639)
        ·
          refine ⟨17675378841548992641297959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11783585894365995094198639 17675378841548992641297959)
          ·
            refine ⟨26513068262323488961946939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17675378841548992641297959 26513068262323488961946939)
            ·
              refine ⟨39769602393485233442920409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26513068262323488961946939 39769602393485233442920409)
              ·
                refine ⟨29827201795113925082190307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39769602393485233442920409 29827201795113925082190307)
                ·
                  refine ⟨44740802692670887623285461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29827201795113925082190307 44740802692670887623285461)
                  ·
                    refine ⟨1048612563109473928670753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44740802692670887623285461 1048612563109473928670753)
                    ·
                      rfl

theorem cell23_6126497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_6126497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126497 prefixEnd_6126497 := by exact prefixLift 6126497
  have htrace : WordTrace (prefixWord ++ tailWord_6126497) baseStart_6126497 baseEnd_6126497 := by
    simpa [prefixWord, tailWord_6126497, baseEnd_6126497] using wordTrace_append hprefix tailTrace_6126497
  have hstable : (prefixWord ++ tailWord_6126497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126497).length < 2 ^ (prefixWord ++ tailWord_6126497).sum := by decide
  have hdescent : baseEnd_6126497 < baseStart_6126497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126517 : List Nat := [1, 3, 3, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_6126517 : Nat := 118140960795 + 6126517 * 2 ^ 59
def prefixEnd_6126517 : Nat := 4983230072969 + 3 ^ 40 * 6126517 * 2
def baseEnd_6126517 : Nat := 3145847958941511707762167

theorem tailTrace_6126517 : CollatzResearch.WordTrace tailWord_6126517 prefixEnd_6126517 3145847958941511707762167 := by
  unfold tailWord_6126517
  simp only [CollatzResearch.WordTrace]
  refine ⟨223452432345682709646457805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148968288230455139764305203 223452432345682709646457805)
  ·
    refine ⟨83794662129631016117421677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223452432345682709646457805 83794662129631016117421677)
    ·
      refine ⟨31422998298611631044033129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83794662129631016117421677 31422998298611631044033129)
      ·
        refine ⟨23567248723958723283024847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31422998298611631044033129 23567248723958723283024847)
        ·
          refine ⟨35350873085938084924537271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23567248723958723283024847 35350873085938084924537271)
          ·
            refine ⟨53026309628907127386805907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35350873085938084924537271 53026309628907127386805907)
            ·
              refine ⟨79539464443360691080208861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53026309628907127386805907 79539464443360691080208861)
              ·
                refine ⟨29827299166260259155078323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79539464443360691080208861 29827299166260259155078323)
                ·
                  refine ⟨44740948749390388732617485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29827299166260259155078323 44740948749390388732617485)
                  ·
                    refine ⟨16777855781021395774731557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44740948749390388732617485 16777855781021395774731557)
                    ·
                      refine ⟨3145847958941511707762167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16777855781021395774731557 3145847958941511707762167)
                      ·
                        rfl

theorem cell23_6126517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_6126517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126517 prefixEnd_6126517 := by exact prefixLift 6126517
  have htrace : WordTrace (prefixWord ++ tailWord_6126517) baseStart_6126517 baseEnd_6126517 := by
    simpa [prefixWord, tailWord_6126517, baseEnd_6126517] using wordTrace_append hprefix tailTrace_6126517
  have hstable : (prefixWord ++ tailWord_6126517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126517).length < 2 ^ (prefixWord ++ tailWord_6126517).sum := by decide
  have hdescent : baseEnd_6126517 < baseStart_6126517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126617 : List Nat := [1, 2, 1, 2, 1, 1, 5, 3, 1, 6]
def baseStart_6126617 : Nat := 118140960795 + 6126617 * 2 ^ 59
def prefixEnd_6126617 : Nat := 4983230072969 + 3 ^ 40 * 6126617 * 2
def baseEnd_6126617 : Nat := 1048633102335653772170569

theorem tailTrace_6126617 : CollatzResearch.WordTrace tailWord_6126617 prefixEnd_6126617 1048633102335653772170569 := by
  unfold tailWord_6126617
  simp only [CollatzResearch.WordTrace]
  refine ⟨223456079645320426725098105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148970719763546951150065403 223456079645320426725098105)
  ·
    refine ⟨167592059733990320043823579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223456079645320426725098105 167592059733990320043823579)
    ·
      refine ⟨251388089600985480065735369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167592059733990320043823579 251388089600985480065735369)
      ·
        refine ⟨188541067200739110049301527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251388089600985480065735369 188541067200739110049301527)
        ·
          refine ⟨282811600801108665073952291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188541067200739110049301527 282811600801108665073952291)
          ·
            refine ⟨424217401201662997610928437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282811600801108665073952291 424217401201662997610928437)
            ·
              refine ⟨39770381362655906026024541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 424217401201662997610928437 39770381362655906026024541)
              ·
                refine ⟨14913893010995964759759203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39770381362655906026024541 14913893010995964759759203)
                ·
                  refine ⟨22370839516493947139638805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14913893010995964759759203 22370839516493947139638805)
                  ·
                    refine ⟨1048633102335653772170569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22370839516493947139638805 1048633102335653772170569)
                    ·
                      rfl

theorem cell23_6126617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 6].length) (baseStart_6126617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126617 prefixEnd_6126617 := by exact prefixLift 6126617
  have htrace : WordTrace (prefixWord ++ tailWord_6126617) baseStart_6126617 baseEnd_6126617 := by
    simpa [prefixWord, tailWord_6126617, baseEnd_6126617] using wordTrace_append hprefix tailTrace_6126617
  have hstable : (prefixWord ++ tailWord_6126617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126617).length < 2 ^ (prefixWord ++ tailWord_6126617).sum := by decide
  have hdescent : baseEnd_6126617 < baseStart_6126617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126628 : List Nat := [2, 3, 1, 4, 1, 1, 3, 1, 2, 3, 2]
def baseStart_6126628 : Nat := 118140960795 + 6126628 * 2 ^ 59
def prefixEnd_6126628 : Nat := 4983230072969 + 3 ^ 40 * 6126628 * 2
def baseEnd_6126628 : Nat := 3145904955294160773474157

theorem tailTrace_6126628 : CollatzResearch.WordTrace tailWord_6126628 prefixEnd_6126628 3145904955294160773474157 := by
  unfold tailWord_6126628
  simp only [CollatzResearch.WordTrace]
  refine ⟨111728240424140287801874269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148970987232187050402499025 111728240424140287801874269)
  ·
    refine ⟨41898090159052607925702851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111728240424140287801874269 41898090159052607925702851)
    ·
      refine ⟨62847135238578911888554277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41898090159052607925702851 62847135238578911888554277)
      ·
        refine ⟨11783837857233545979103927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62847135238578911888554277 11783837857233545979103927)
        ·
          refine ⟨17675756785850318968655891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11783837857233545979103927 17675756785850318968655891)
          ·
            refine ⟨26513635178775478452983837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17675756785850318968655891 26513635178775478452983837)
            ·
              refine ⟨9942613192040804419868939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26513635178775478452983837 9942613192040804419868939)
              ·
                refine ⟨14913919788061206629803409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9942613192040804419868939 14913919788061206629803409)
                ·
                  refine ⟨11185439841045904972352557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14913919788061206629803409 11185439841045904972352557)
                  ·
                    refine ⟨4194539940392214364632209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11185439841045904972352557 4194539940392214364632209)
                    ·
                      refine ⟨3145904955294160773474157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4194539940392214364632209 3145904955294160773474157)
                      ·
                        rfl

theorem cell23_6126628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_6126628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126628 prefixEnd_6126628 := by exact prefixLift 6126628
  have htrace : WordTrace (prefixWord ++ tailWord_6126628) baseStart_6126628 baseEnd_6126628 := by
    simpa [prefixWord, tailWord_6126628, baseEnd_6126628] using wordTrace_append hprefix tailTrace_6126628
  have hstable : (prefixWord ++ tailWord_6126628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126628).length < 2 ^ (prefixWord ++ tailWord_6126628).sum := by decide
  have hdescent : baseEnd_6126628 < baseStart_6126628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126641 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 5, 2, 2]
def baseStart_6126641 : Nat := 118140960795 + 6126641 * 2 ^ 59
def prefixEnd_6126641 : Nat := 4983230072969 + 3 ^ 40 * 6126641 * 2
def baseEnd_6126641 : Nat := 3145911630542669222611597

theorem tailTrace_6126641 : CollatzResearch.WordTrace tailWord_6126641 prefixEnd_6126641 3145911630542669222611597 := by
  unfold tailWord_6126641
  simp only [CollatzResearch.WordTrace]
  refine ⟨223456954997233478823971777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148971303331488985882647851 223456954997233478823971777)
  ·
    refine ⟨167592716247925109117978833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223456954997233478823971777 167592716247925109117978833)
    ·
      refine ⟨125694537185943831838484125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167592716247925109117978833 125694537185943831838484125)
      ·
        refine ⟨47135451444728936939431547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125694537185943831838484125 47135451444728936939431547)
        ·
          refine ⟨70703177167093405409147321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47135451444728936939431547 70703177167093405409147321)
          ·
            refine ⟨53027382875320054056860491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70703177167093405409147321 53027382875320054056860491)
            ·
              refine ⟨79541074312980081085290737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53027382875320054056860491 79541074312980081085290737)
              ·
                refine ⟨59655805734735060813968053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79541074312980081085290737 59655805734735060813968053)
                ·
                  refine ⟨5592731787631411951309505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59655805734735060813968053 5592731787631411951309505)
                  ·
                    refine ⟨4194548840723558963482129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5592731787631411951309505 4194548840723558963482129)
                    ·
                      refine ⟨3145911630542669222611597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4194548840723558963482129 3145911630542669222611597)
                      ·
                        rfl

theorem cell23_6126641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_6126641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126641 prefixEnd_6126641 := by exact prefixLift 6126641
  have htrace : WordTrace (prefixWord ++ tailWord_6126641) baseStart_6126641 baseEnd_6126641 := by
    simpa [prefixWord, tailWord_6126641, baseEnd_6126641] using wordTrace_append hprefix tailTrace_6126641
  have hstable : (prefixWord ++ tailWord_6126641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126641).length < 2 ^ (prefixWord ++ tailWord_6126641).sum := by decide
  have hdescent : baseEnd_6126641 < baseStart_6126641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126687 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 5]
def baseStart_6126687 : Nat := 118140960795 + 6126687 * 2 ^ 59
def prefixEnd_6126687 : Nat := 4983230072969 + 3 ^ 40 * 6126687 * 2
def baseEnd_6126687 : Nat := 3145935250652776042636385

theorem tailTrace_6126687 : CollatzResearch.WordTrace tailWord_6126687 prefixEnd_6126687 3145935250652776042636385 := by
  unfold tailWord_6126687
  simp only [CollatzResearch.WordTrace]
  refine ⟨223458632755066828680146315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148972421836711219120097543 223458632755066828680146315)
  ·
    refine ⟨335187949132600243020219473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223458632755066828680146315 335187949132600243020219473)
    ·
      refine ⟨251390961849450182265164605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335187949132600243020219473 251390961849450182265164605)
      ·
        refine ⟨94271610693543818349436727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251390961849450182265164605 94271610693543818349436727)
        ·
          refine ⟨141407416040315727524155091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94271610693543818349436727 141407416040315727524155091)
          ·
            refine ⟨212111124060473591286232637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141407416040315727524155091 212111124060473591286232637)
            ·
              refine ⟨79541671522677596732337239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212111124060473591286232637 79541671522677596732337239)
              ·
                refine ⟨119312507284016395098505859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79541671522677596732337239 119312507284016395098505859)
                ·
                  refine ⟨178968760926024592647758789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119312507284016395098505859 178968760926024592647758789)
                  ·
                    refine ⟨33556642673629611121454773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 178968760926024592647758789 33556642673629611121454773)
                    ·
                      refine ⟨3145935250652776042636385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33556642673629611121454773 3145935250652776042636385)
                      ·
                        rfl

theorem cell23_6126687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_6126687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126687 prefixEnd_6126687 := by exact prefixLift 6126687
  have htrace : WordTrace (prefixWord ++ tailWord_6126687) baseStart_6126687 baseEnd_6126687 := by
    simpa [prefixWord, tailWord_6126687, baseEnd_6126687] using wordTrace_append hprefix tailTrace_6126687
  have hstable : (prefixWord ++ tailWord_6126687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126687).length < 2 ^ (prefixWord ++ tailWord_6126687).sum := by decide
  have hdescent : baseEnd_6126687 < baseStart_6126687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126709 : List Nat := [1, 3, 4, 3, 2, 1, 1, 1, 3, 2, 2]
def baseStart_6126709 : Nat := 118140960795 + 6126709 * 2 ^ 59
def prefixEnd_6126709 : Nat := 4983230072969 + 3 ^ 40 * 6126709 * 2
def baseEnd_6126709 : Nat := 3145946547227174956561285

theorem tailTrace_6126709 : CollatzResearch.WordTrace tailWord_6126709 prefixEnd_6126709 3145946547227174956561285 := by
  unfold tailWord_6126709
  simp only [CollatzResearch.WordTrace]
  refine ⟨223459435160987126437447181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148972956773991417624964787 223459435160987126437447181)
  ·
    refine ⟨83797288185370172414042693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223459435160987126437447181 83797288185370172414042693)
    ·
      refine ⟨15711991534756907327633005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83797288185370172414042693 15711991534756907327633005)
      ·
        refine ⟨5891996825533840247862377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15711991534756907327633005 5891996825533840247862377)
        ·
          refine ⟨4418997619150380185896783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5891996825533840247862377 4418997619150380185896783)
          ·
            refine ⟨6628496428725570278845175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4418997619150380185896783 6628496428725570278845175)
            ·
              refine ⟨9942744643088355418267763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6628496428725570278845175 9942744643088355418267763)
              ·
                refine ⟨14914116964632533127401645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9942744643088355418267763 14914116964632533127401645)
                ·
                  refine ⟨5592793861737199922775617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14914116964632533127401645 5592793861737199922775617)
                  ·
                    refine ⟨4194595396302899942081713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5592793861737199922775617 4194595396302899942081713)
                    ·
                      refine ⟨3145946547227174956561285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4194595396302899942081713 3145946547227174956561285)
                      ·
                        rfl

theorem cell23_6126709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_6126709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126709 prefixEnd_6126709 := by exact prefixLift 6126709
  have htrace : WordTrace (prefixWord ++ tailWord_6126709) baseStart_6126709 baseEnd_6126709 := by
    simpa [prefixWord, tailWord_6126709, baseEnd_6126709] using wordTrace_append hprefix tailTrace_6126709
  have hstable : (prefixWord ++ tailWord_6126709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126709).length < 2 ^ (prefixWord ++ tailWord_6126709).sum := by decide
  have hdescent : baseEnd_6126709 < baseStart_6126709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126747 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 7]
def baseStart_6126747 : Nat := 118140960795 + 6126747 * 2 ^ 59
def prefixEnd_6126747 : Nat := 4983230072969 + 3 ^ 40 * 6126747 * 2
def baseEnd_6126747 : Nat := 3145966059492045807886109

theorem tailTrace_6126747 : CollatzResearch.WordTrace tailWord_6126747 prefixEnd_6126747 3145966059492045807886109 := by
  unfold tailWord_6126747
  simp only [CollatzResearch.WordTrace]
  refine ⟨223460821134849458927330495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148973880756566305951553663 223460821134849458927330495)
  ·
    refine ⟨335191231702274188390995743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223460821134849458927330495 335191231702274188390995743)
    ·
      refine ⟨502786847553411282586493615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335191231702274188390995743 502786847553411282586493615)
      ·
        refine ⟨754180271330116923879740423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502786847553411282586493615 754180271330116923879740423)
        ·
          refine ⟨1131270406995175385819610635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754180271330116923879740423 1131270406995175385819610635)
          ·
            refine ⟨1696905610492763078729415953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131270406995175385819610635 1696905610492763078729415953)
            ·
              refine ⟨1272679207869572309047061965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1696905610492763078729415953 1272679207869572309047061965)
              ·
                refine ⟨477254702951089615892648237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1272679207869572309047061965 477254702951089615892648237)
                ·
                  refine ⟨178970513606658605959743089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 477254702951089615892648237 178970513606658605959743089)
                  ·
                    refine ⟨134227885204993954469807317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 178970513606658605959743089 134227885204993954469807317)
                    ·
                      refine ⟨3145966059492045807886109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 134227885204993954469807317 3145966059492045807886109)
                      ·
                        rfl

theorem cell23_6126747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 7].length) (baseStart_6126747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126747 prefixEnd_6126747 := by exact prefixLift 6126747
  have htrace : WordTrace (prefixWord ++ tailWord_6126747) baseStart_6126747 baseEnd_6126747 := by
    simpa [prefixWord, tailWord_6126747, baseEnd_6126747] using wordTrace_append hprefix tailTrace_6126747
  have hstable : (prefixWord ++ tailWord_6126747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126747).length < 2 ^ (prefixWord ++ tailWord_6126747).sum := by decide
  have hdescent : baseEnd_6126747 < baseStart_6126747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126748 : List Nat := [2, 2, 3, 2, 1, 3, 1, 2, 1, 4, 2]
def baseStart_6126748 : Nat := 118140960795 + 6126748 * 2 ^ 59
def prefixEnd_6126748 : Nat := 4983230072969 + 3 ^ 40 * 6126748 * 2
def baseEnd_6126748 : Nat := 3145966572972700303973605

theorem tailTrace_6126748 : CollatzResearch.WordTrace tailWord_6126748 prefixEnd_6126748 3145966572972700303973605 := by
  unfold tailWord_6126748
  simp only [CollatzResearch.WordTrace]
  refine ⟨111730428803922918049058449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148973905071897224065411265 111730428803922918049058449)
  ·
    refine ⟨83797821602942188536793837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111730428803922918049058449 83797821602942188536793837)
    ·
      refine ⟨31424183101103320701297689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83797821602942188536793837 31424183101103320701297689)
      ·
        refine ⟨23568137325827490525973267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31424183101103320701297689 23568137325827490525973267)
        ·
          refine ⟨35352205988741235788959901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23568137325827490525973267 35352205988741235788959901)
          ·
            refine ⟨13257077245777963420859963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35352205988741235788959901 13257077245777963420859963)
            ·
              refine ⟨19885615868666945131289945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13257077245777963420859963 19885615868666945131289945)
              ·
                refine ⟨14914211901500208848467459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19885615868666945131289945 14914211901500208848467459)
                ·
                  refine ⟨22371317852250313272701189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14914211901500208848467459 22371317852250313272701189)
                  ·
                    refine ⟨4194622097296933738631473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22371317852250313272701189 4194622097296933738631473)
                    ·
                      refine ⟨3145966572972700303973605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4194622097296933738631473 3145966572972700303973605)
                      ·
                        rfl

theorem cell23_6126748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_6126748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126748 prefixEnd_6126748 := by exact prefixLift 6126748
  have htrace : WordTrace (prefixWord ++ tailWord_6126748) baseStart_6126748 baseEnd_6126748 := by
    simpa [prefixWord, tailWord_6126748, baseEnd_6126748] using wordTrace_append hprefix tailTrace_6126748
  have hstable : (prefixWord ++ tailWord_6126748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126748).length < 2 ^ (prefixWord ++ tailWord_6126748).sum := by decide
  have hdescent : baseEnd_6126748 < baseStart_6126748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126882 : List Nat := [3, 3, 1, 1, 5, 1, 1, 1, 3, 4]
def baseStart_6126882 : Nat := 118140960795 + 6126882 * 2 ^ 59
def prefixEnd_6126882 : Nat := 4983230072969 + 3 ^ 40 * 6126882 * 2
def baseEnd_6126882 : Nat := 1048678459793467593232663

theorem tailTrace_6126882 : CollatzResearch.WordTrace tailWord_6126882 prefixEnd_6126882 1048678459793467593232663 := by
  unfold tailWord_6126882
  simp only [CollatzResearch.WordTrace]
  refine ⟨55866436247340094245873725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148977163326240251322329933 55866436247340094245873725)
  ·
    refine ⟨20949913592752535342202647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55866436247340094245873725 20949913592752535342202647)
    ·
      refine ⟨31424870389128803013303971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20949913592752535342202647 31424870389128803013303971)
      ·
        refine ⟨47137305583693204519955957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31424870389128803013303971 47137305583693204519955957)
        ·
          refine ⟨4419122398471237923745871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47137305583693204519955957 4419122398471237923745871)
          ·
            refine ⟨6628683597706856885618807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4419122398471237923745871 6628683597706856885618807)
            ·
              refine ⟨9943025396560285328428211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6628683597706856885618807 9943025396560285328428211)
              ·
                refine ⟨14914538094840427992642317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9943025396560285328428211 14914538094840427992642317)
                ·
                  refine ⟨5592951785565160497240869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14914538094840427992642317 5592951785565160497240869)
                  ·
                    refine ⟨1048678459793467593232663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5592951785565160497240869 1048678459793467593232663)
                    ·
                      rfl

theorem cell23_6126882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_6126882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126882 prefixEnd_6126882 := by exact prefixLift 6126882
  have htrace : WordTrace (prefixWord ++ tailWord_6126882) baseStart_6126882 baseEnd_6126882 := by
    simpa [prefixWord, tailWord_6126882, baseEnd_6126882] using wordTrace_append hprefix tailTrace_6126882
  have hstable : (prefixWord ++ tailWord_6126882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126882).length < 2 ^ (prefixWord ++ tailWord_6126882).sum := by decide
  have hdescent : baseEnd_6126882 < baseStart_6126882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126908 : List Nat := [2, 2, 2, 2, 1, 3, 3, 2, 1, 5]
def baseStart_6126908 : Nat := 118140960795 + 6126908 * 2 ^ 59
def prefixEnd_6126908 : Nat := 4983230072969 + 3 ^ 40 * 6126908 * 2
def baseEnd_6126908 : Nat := 1048682909959139892657623

theorem tailTrace_6126908 : CollatzResearch.WordTrace tailWord_6126908 prefixEnd_6126908 1048682909959139892657623 := by
  unfold tailWord_6126908
  simp only [CollatzResearch.WordTrace]
  refine ⟨111733346643633091711970689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148977795524844122282627585 111733346643633091711970689)
  ·
    refine ⟨83800009982724818783978017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111733346643633091711970689 83800009982724818783978017)
    ·
      refine ⟨62850007487043614087983513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83800009982724818783978017 62850007487043614087983513)
      ·
        refine ⟨47137505615282710565987635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62850007487043614087983513 47137505615282710565987635)
        ·
          refine ⟨70706258422924065848981453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47137505615282710565987635 70706258422924065848981453)
          ·
            refine ⟨26514846908596524693368045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70706258422924065848981453 26514846908596524693368045)
            ·
              refine ⟨9943067590723696760013017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26514846908596524693368045 9943067590723696760013017)
              ·
                refine ⟨7457300693042772570009763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9943067590723696760013017 7457300693042772570009763)
                ·
                  refine ⟨11185951039564158855014645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7457300693042772570009763 11185951039564158855014645)
                  ·
                    refine ⟨1048682909959139892657623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11185951039564158855014645 1048682909959139892657623)
                    ·
                      rfl

theorem cell23_6126908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_6126908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126908 prefixEnd_6126908 := by exact prefixLift 6126908
  have htrace : WordTrace (prefixWord ++ tailWord_6126908) baseStart_6126908 baseEnd_6126908 := by
    simpa [prefixWord, tailWord_6126908, baseEnd_6126908] using wordTrace_append hprefix tailTrace_6126908
  have hstable : (prefixWord ++ tailWord_6126908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126908).length < 2 ^ (prefixWord ++ tailWord_6126908).sum := by decide
  have hdescent : baseEnd_6126908 < baseStart_6126908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126921 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 6, 4]
def baseStart_6126921 : Nat := 118140960795 + 6126921 * 2 ^ 59
def prefixEnd_6126921 : Nat := 4983230072969 + 3 ^ 40 * 6126921 * 2
def baseEnd_6126921 : Nat := 1048685135041976042370103

theorem tailTrace_6126921 : CollatzResearch.WordTrace tailWord_6126921 prefixEnd_6126921 1048685135041976042370103 := by
  unfold tailWord_6126921
  simp only [CollatzResearch.WordTrace]
  refine ⟨223467167436219086644164617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148978111624146057762776411 223467167436219086644164617)
  ·
    refine ⟨167600375577164314983123463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223467167436219086644164617 167600375577164314983123463)
    ·
      refine ⟨251400563365746472474685195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167600375577164314983123463 251400563365746472474685195)
      ·
        refine ⟨377100845048619708712027793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251400563365746472474685195 377100845048619708712027793)
        ·
          refine ⟨282825633786464781534020845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 377100845048619708712027793 282825633786464781534020845)
          ·
            refine ⟨106059612669924293075257817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 282825633786464781534020845 106059612669924293075257817)
            ·
              refine ⟨79544709502443219806443363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106059612669924293075257817 79544709502443219806443363)
              ·
                refine ⟨119317064253664829709665045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79544709502443219806443363 119317064253664829709665045)
                ·
                  refine ⟨5592987386890538892640549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 119317064253664829709665045 5592987386890538892640549)
                  ·
                    refine ⟨1048685135041976042370103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5592987386890538892640549 1048685135041976042370103)
                    ·
                      rfl

theorem cell23_6126921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6, 4].length) (baseStart_6126921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126921 prefixEnd_6126921 := by exact prefixLift 6126921
  have htrace : WordTrace (prefixWord ++ tailWord_6126921) baseStart_6126921 baseEnd_6126921 := by
    simpa [prefixWord, tailWord_6126921, baseEnd_6126921] using wordTrace_append hprefix tailTrace_6126921
  have hstable : (prefixWord ++ tailWord_6126921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126921).length < 2 ^ (prefixWord ++ tailWord_6126921).sum := by decide
  have hdescent : baseEnd_6126921 < baseStart_6126921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126938 : List Nat := [3, 1, 1, 2, 1, 2, 3, 4, 2, 4]
def baseStart_6126938 : Nat := 118140960795 + 6126938 * 2 ^ 59
def prefixEnd_6126938 : Nat := 4983230072969 + 3 ^ 40 * 6126938 * 2
def baseEnd_6126938 : Nat := 1048688044765684853532577

theorem tailTrace_6126938 : CollatzResearch.WordTrace tailWord_6126938 prefixEnd_6126938 1048688044765684853532577 := by
  unfold tailWord_6126938
  simp only [CollatzResearch.WordTrace]
  refine ⟨55866946869289374636883367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148978524984771665698355645 55866946869289374636883367)
  ·
    refine ⟨83800420303934061955325051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55866946869289374636883367 83800420303934061955325051)
    ·
      refine ⟨125700630455901092932987577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83800420303934061955325051 125700630455901092932987577)
      ·
        refine ⟨94275472841925819699740683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125700630455901092932987577 94275472841925819699740683)
        ·
          refine ⟨141413209262888729549611025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94275472841925819699740683 141413209262888729549611025)
          ·
            refine ⟨106059906947166547162208269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141413209262888729549611025 106059906947166547162208269)
            ·
              refine ⟨39772465105187455185828101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106059906947166547162208269 39772465105187455185828101)
              ·
                refine ⟨7457337207222647847342769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39772465105187455185828101 7457337207222647847342769)
                ·
                  refine ⟨5593002905416985885507077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7457337207222647847342769 5593002905416985885507077)
                  ·
                    refine ⟨1048688044765684853532577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5593002905416985885507077 1048688044765684853532577)
                    ·
                      rfl

theorem cell23_6126938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 2, 4].length) (baseStart_6126938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126938 prefixEnd_6126938 := by exact prefixLift 6126938
  have htrace : WordTrace (prefixWord ++ tailWord_6126938) baseStart_6126938 baseEnd_6126938 := by
    simpa [prefixWord, tailWord_6126938, baseEnd_6126938] using wordTrace_append hprefix tailTrace_6126938
  have hstable : (prefixWord ++ tailWord_6126938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126938).length < 2 ^ (prefixWord ++ tailWord_6126938).sum := by decide
  have hdescent : baseEnd_6126938 < baseStart_6126938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126948 : List Nat := [2, 3, 1, 1, 3, 2, 1, 2, 3, 2, 3]
def baseStart_6126948 : Nat := 118140960795 + 6126948 * 2 ^ 59
def prefixEnd_6126948 : Nat := 4983230072969 + 3 ^ 40 * 6126948 * 2
def baseEnd_6126948 : Nat := 3146069269103599521472685

theorem tailTrace_6126948 : CollatzResearch.WordTrace tailWord_6126948 prefixEnd_6126948 3146069269103599521472685 := by
  unfold tailWord_6126948
  simp only [CollatzResearch.WordTrace]
  refine ⟨111734076103560635127698749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148978768138080846836931665 111734076103560635127698749)
  ·
    refine ⟨41900278538835238172887031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111734076103560635127698749 41900278538835238172887031)
    ·
      refine ⟨62850417808252857259330547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41900278538835238172887031 62850417808252857259330547)
      ·
        refine ⟨94275626712379285888995821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62850417808252857259330547 94275626712379285888995821)
        ·
          refine ⟨35353360017142232208373433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94275626712379285888995821 35353360017142232208373433)
          ·
            refine ⟨26515020012856674156280075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35353360017142232208373433 26515020012856674156280075)
            ·
              refine ⟨39772530019285011234420113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26515020012856674156280075 39772530019285011234420113)
              ·
                refine ⟨29829397514463758425815085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39772530019285011234420113 29829397514463758425815085)
                ·
                  refine ⟨11186024067923909409680657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29829397514463758425815085 11186024067923909409680657)
                  ·
                    refine ⟨8389518050942932057260493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11186024067923909409680657 8389518050942932057260493)
                    ·
                      refine ⟨3146069269103599521472685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8389518050942932057260493 3146069269103599521472685)
                      ·
                        rfl

theorem cell23_6126948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_6126948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126948 prefixEnd_6126948 := by exact prefixLift 6126948
  have htrace : WordTrace (prefixWord ++ tailWord_6126948) baseStart_6126948 baseEnd_6126948 := by
    simpa [prefixWord, tailWord_6126948, baseEnd_6126948] using wordTrace_append hprefix tailTrace_6126948
  have hstable : (prefixWord ++ tailWord_6126948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126948).length < 2 ^ (prefixWord ++ tailWord_6126948).sum := by decide
  have hdescent : baseEnd_6126948 < baseStart_6126948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6126979 : List Nat := [1, 1, 1, 3, 5, 2, 2, 3, 1, 2, 2]
def baseStart_6126979 : Nat := 118140960795 + 6126979 * 2 ^ 59
def prefixEnd_6126979 : Nat := 4983230072969 + 3 ^ 40 * 6126979 * 2
def baseEnd_6126979 : Nat := 3146085187003888900185043

theorem tailTrace_6126979 : CollatzResearch.WordTrace tailWord_6126979 prefixEnd_6126979 3146085187003888900185043 := by
  unfold tailWord_6126979
  simp only [CollatzResearch.WordTrace]
  refine ⟨223469282870008962549775991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148979521913339308366517327 223469282870008962549775991)
  ·
    refine ⟨335203924305013443824663987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223469282870008962549775991 335203924305013443824663987)
    ·
      refine ⟨502805886457520165736995981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335203924305013443824663987 502805886457520165736995981)
      ·
        refine ⟨188552207421570062151373493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 502805886457520165736995981 188552207421570062151373493)
        ·
          refine ⟨17676769445772193326691265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 188552207421570062151373493 17676769445772193326691265)
          ·
            refine ⟨13257577084329144995018449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17676769445772193326691265 13257577084329144995018449)
            ·
              refine ⟨9943182813246858746263837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13257577084329144995018449 9943182813246858746263837)
              ·
                refine ⟨3728693554967572029848939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9943182813246858746263837 3728693554967572029848939)
                ·
                  refine ⟨5593040332451358044773409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3728693554967572029848939 5593040332451358044773409)
                  ·
                    refine ⟨4194780249338518533580057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5593040332451358044773409 4194780249338518533580057)
                    ·
                      refine ⟨3146085187003888900185043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4194780249338518533580057 3146085187003888900185043)
                      ·
                        rfl

theorem cell23_6126979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3, 1, 2, 2].length) (baseStart_6126979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6126979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6126979 prefixEnd_6126979 := by exact prefixLift 6126979
  have htrace : WordTrace (prefixWord ++ tailWord_6126979) baseStart_6126979 baseEnd_6126979 := by
    simpa [prefixWord, tailWord_6126979, baseEnd_6126979] using wordTrace_append hprefix tailTrace_6126979
  have hstable : (prefixWord ++ tailWord_6126979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6126979).length < 2 ^ (prefixWord ++ tailWord_6126979).sum := by decide
  have hdescent : baseEnd_6126979 < baseStart_6126979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6126979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127011 : List Nat := [1, 1, 1, 4, 1, 3, 1, 3, 2, 6]
def baseStart_6127011 : Nat := 118140960795 + 6127011 * 2 ^ 59
def prefixEnd_6127011 : Nat := 4983230072969 + 3 ^ 40 * 6127011 * 2
def baseEnd_6127011 : Nat := 1048700539461610924994965

theorem tailTrace_6127011 : CollatzResearch.WordTrace tailWord_6127011 prefixEnd_6127011 1048700539461610924994965 := by
  unfold tailWord_6127011
  simp only [CollatzResearch.WordTrace]
  refine ⟨223470450005893032014940887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148980300003928688009960591 223470450005893032014940887)
  ·
    refine ⟨335205675008839548022411331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223470450005893032014940887 335205675008839548022411331)
    ·
      refine ⟨502808512513259322033616997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335205675008839548022411331 502808512513259322033616997)
      ·
        refine ⟨94276596096236122881303187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 502808512513259322033616997 94276596096236122881303187)
        ·
          refine ⟨141414894144354184321954781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94276596096236122881303187 141414894144354184321954781)
          ·
            refine ⟨53030585304132819120733043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141414894144354184321954781 53030585304132819120733043)
            ·
              refine ⟨79545877956199228681099565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53030585304132819120733043 79545877956199228681099565)
              ·
                refine ⟨29829704233574710755412337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79545877956199228681099565 29829704233574710755412337)
                ·
                  refine ⟨22372278175181033066559253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29829704233574710755412337 22372278175181033066559253)
                  ·
                    refine ⟨1048700539461610924994965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22372278175181033066559253 1048700539461610924994965)
                    ·
                      rfl

theorem cell23_6127011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 6].length) (baseStart_6127011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127011 prefixEnd_6127011 := by exact prefixLift 6127011
  have htrace : WordTrace (prefixWord ++ tailWord_6127011) baseStart_6127011 baseEnd_6127011 := by
    simpa [prefixWord, tailWord_6127011, baseEnd_6127011] using wordTrace_append hprefix tailTrace_6127011
  have hstable : (prefixWord ++ tailWord_6127011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127011).length < 2 ^ (prefixWord ++ tailWord_6127011).sum := by decide
  have hdescent : baseEnd_6127011 < baseStart_6127011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127038 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3]
def baseStart_6127038 : Nat := 118140960795 + 6127038 * 2 ^ 59
def prefixEnd_6127038 : Nat := 4983230072969 + 3 ^ 40 * 6127038 * 2
def baseEnd_6127038 : Nat := 3146115482362504169347271

theorem tailTrace_6127038 : CollatzResearch.WordTrace tailWord_6127038 prefixEnd_6127038 3146115482362504169347271 := by
  unfold tailWord_6127038
  simp only [CollatzResearch.WordTrace]
  refine ⟨27933929347099401953271721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148980956517863477084115845 27933929347099401953271721)
  ·
    refine ⟨20950447010324551464953791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27933929347099401953271721 20950447010324551464953791)
    ·
      refine ⟨31425670515486827197430687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20950447010324551464953791 31425670515486827197430687)
      ·
        refine ⟨47138505773230240796146031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31425670515486827197430687 47138505773230240796146031)
        ·
          refine ⟨70707758659845361194219047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47138505773230240796146031 70707758659845361194219047)
          ·
            refine ⟨106061637989768041791328571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70707758659845361194219047 106061637989768041791328571)
            ·
              refine ⟨159092456984652062686992857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106061637989768041791328571 159092456984652062686992857)
              ·
                refine ⟨119319342738489047015244643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159092456984652062686992857 119319342738489047015244643)
                ·
                  refine ⟨178979014107733570522866965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119319342738489047015244643 178979014107733570522866965)
                  ·
                    refine ⟨8389641286300011118259389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 178979014107733570522866965 8389641286300011118259389)
                    ·
                      refine ⟨3146115482362504169347271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8389641286300011118259389 3146115482362504169347271)
                      ·
                        rfl

theorem cell23_6127038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_6127038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127038 prefixEnd_6127038 := by exact prefixLift 6127038
  have htrace : WordTrace (prefixWord ++ tailWord_6127038) baseStart_6127038 baseEnd_6127038 := by
    simpa [prefixWord, tailWord_6127038, baseEnd_6127038] using wordTrace_append hprefix tailTrace_6127038
  have hstable : (prefixWord ++ tailWord_6127038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127038).length < 2 ^ (prefixWord ++ tailWord_6127038).sum := by decide
  have hdescent : baseEnd_6127038 < baseStart_6127038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127052 : List Nat := [2, 2, 1, 4, 2, 1, 2, 1, 4, 2, 2]
def baseStart_6127052 : Nat := 118140960795 + 6127052 * 2 ^ 59
def prefixEnd_6127052 : Nat := 4983230072969 + 3 ^ 40 * 6127052 * 2
def baseEnd_6127052 : Nat := 3146122671091667114572207

theorem tailTrace_6127052 : CollatzResearch.WordTrace tailWord_6127052 prefixEnd_6127052 3146122671091667114572207 := by
  unfold tailWord_6127052
  simp only [CollatzResearch.WordTrace]
  refine ⟨111735972699372248008591705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148981296932496330678122273 111735972699372248008591705)
  ·
    refine ⟨83801979524529186006443779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111735972699372248008591705 83801979524529186006443779)
    ·
      refine ⟨125702969286793779009665669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83801979524529186006443779 125702969286793779009665669)
      ·
        refine ⟨23569306741273833564312313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125702969286793779009665669 23569306741273833564312313)
        ·
          refine ⟨17676980055955375173234235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23569306741273833564312313 17676980055955375173234235)
          ·
            refine ⟨26515470083933062759851353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17676980055955375173234235 26515470083933062759851353)
            ·
              refine ⟨19886602562949797069888515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26515470083933062759851353 19886602562949797069888515)
              ·
                refine ⟨29829903844424695604832773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19886602562949797069888515 29829903844424695604832773)
                ·
                  refine ⟨5593106970829630425906145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29829903844424695604832773 5593106970829630425906145)
                  ·
                    refine ⟨4194830228122222819429609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5593106970829630425906145 4194830228122222819429609)
                    ·
                      refine ⟨3146122671091667114572207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4194830228122222819429609 3146122671091667114572207)
                      ·
                        rfl

theorem cell23_6127052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_6127052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127052 prefixEnd_6127052 := by exact prefixLift 6127052
  have htrace : WordTrace (prefixWord ++ tailWord_6127052) baseStart_6127052 baseEnd_6127052 := by
    simpa [prefixWord, tailWord_6127052, baseEnd_6127052] using wordTrace_append hprefix tailTrace_6127052
  have hstable : (prefixWord ++ tailWord_6127052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127052).length < 2 ^ (prefixWord ++ tailWord_6127052).sum := by decide
  have hdescent : baseEnd_6127052 < baseStart_6127052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127069 : List Nat := [1, 4, 3, 1, 1, 3, 1, 3, 2, 2, 2]
def baseStart_6127069 : Nat := 118140960795 + 6127069 * 2 ^ 59
def prefixEnd_6127069 : Nat := 4983230072969 + 3 ^ 40 * 6127069 * 2
def baseEnd_6127069 : Nat := 3146131400262793548059629

theorem tailTrace_6127069 : CollatzResearch.WordTrace tailWord_6127069 prefixEnd_6127069 3146131400262793548059629 := by
  unfold tailWord_6127069
  simp only [CollatzResearch.WordTrace]
  refine ⟨223472565439682907920552261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148981710293121938613701507 223472565439682907920552261)
  ·
    refine ⟨41901106019940545235103549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223472565439682907920552261 41901106019940545235103549)
    ·
      refine ⟨15712914757477704463163831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41901106019940545235103549 15712914757477704463163831)
      ·
        refine ⟨23569372136216556694745747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15712914757477704463163831 23569372136216556694745747)
        ·
          refine ⟨35354058204324835042118621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23569372136216556694745747 35354058204324835042118621)
          ·
            refine ⟨13257771826621813140794483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35354058204324835042118621 13257771826621813140794483)
            ·
              refine ⟨19886657739932719711191725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13257771826621813140794483 19886657739932719711191725)
              ·
                refine ⟨7457496652474769891696897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19886657739932719711191725 7457496652474769891696897)
                ·
                  refine ⟨5593122489356077418772673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7457496652474769891696897 5593122489356077418772673)
                  ·
                    refine ⟨4194841867017058064079505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5593122489356077418772673 4194841867017058064079505)
                    ·
                      refine ⟨3146131400262793548059629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4194841867017058064079505 3146131400262793548059629)
                      ·
                        rfl

theorem cell23_6127069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_6127069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127069 prefixEnd_6127069 := by exact prefixLift 6127069
  have htrace : WordTrace (prefixWord ++ tailWord_6127069) baseStart_6127069 baseEnd_6127069 := by
    simpa [prefixWord, tailWord_6127069, baseEnd_6127069] using wordTrace_append hprefix tailTrace_6127069
  have hstable : (prefixWord ++ tailWord_6127069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127069).length < 2 ^ (prefixWord ++ tailWord_6127069).sum := by decide
  have hdescent : baseEnd_6127069 < baseStart_6127069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127088 : List Nat := [2, 1, 1, 1, 3, 4, 1, 3, 2, 5]
def baseStart_6127088 : Nat := 118140960795 + 6127088 * 2 ^ 59
def prefixEnd_6127088 : Nat := 4983230072969 + 3 ^ 40 * 6127088 * 2
def baseEnd_6127088 : Nat := 1048713718798409657907347

theorem tailTrace_6127088 : CollatzResearch.WordTrace tailWord_6127088 prefixEnd_6127088 1048713718798409657907347 := by
  unfold tailWord_6127088
  simp only [CollatzResearch.WordTrace]
  refine ⟨111736629213307037082746959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148982172284409382776995945 111736629213307037082746959)
  ·
    refine ⟨167604943819960555624120439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111736629213307037082746959 167604943819960555624120439)
    ·
      refine ⟨251407415729940833436180659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167604943819960555624120439 251407415729940833436180659)
      ·
        refine ⟨377111123594911250154270989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251407415729940833436180659 377111123594911250154270989)
        ·
          refine ⟨141416671348091718807851621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 377111123594911250154270989 141416671348091718807851621)
          ·
            refine ⟨26515625877767197276472179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141416671348091718807851621 26515625877767197276472179)
            ·
              refine ⟨39773438816650795914708269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26515625877767197276472179 39773438816650795914708269)
              ·
                refine ⟨14915039556244048468015601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39773438816650795914708269 14915039556244048468015601)
                ·
                  refine ⟨11186279667183036351011701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14915039556244048468015601 11186279667183036351011701)
                  ·
                    refine ⟨1048713718798409657907347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11186279667183036351011701 1048713718798409657907347)
                    ·
                      rfl

theorem cell23_6127088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 2, 5].length) (baseStart_6127088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127088 prefixEnd_6127088 := by exact prefixLift 6127088
  have htrace : WordTrace (prefixWord ++ tailWord_6127088) baseStart_6127088 baseEnd_6127088 := by
    simpa [prefixWord, tailWord_6127088, baseEnd_6127088] using wordTrace_append hprefix tailTrace_6127088
  have hstable : (prefixWord ++ tailWord_6127088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127088).length < 2 ^ (prefixWord ++ tailWord_6127088).sum := by decide
  have hdescent : baseEnd_6127088 < baseStart_6127088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127125 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 1, 6, 2]
def baseStart_6127125 : Nat := 118140960795 + 6127125 * 2 ^ 59
def prefixEnd_6127125 : Nat := 4983230072969 + 3 ^ 40 * 6127125 * 2
def baseEnd_6127125 : Nat := 3146160155179445328959371

theorem tailTrace_6127125 : CollatzResearch.WordTrace tailWord_6127125 prefixEnd_6127125 3146160155179445328959371 := by
  unfold tailWord_6127125
  simp only [CollatzResearch.WordTrace]
  refine ⟨223474607927480029484590829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148983071951653352989727219 223474607927480029484590829)
  ·
    refine ⟨83802977972805011056721561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223474607927480029484590829 83802977972805011056721561)
    ·
      refine ⟨62852233479603758292541171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83802977972805011056721561 62852233479603758292541171)
      ·
        refine ⟨94278350219405637438811757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62852233479603758292541171 94278350219405637438811757)
        ·
          refine ⟨35354381332277114039554409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94278350219405637438811757 35354381332277114039554409)
          ·
            refine ⟨26515785999207835529665807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35354381332277114039554409 26515785999207835529665807)
            ·
              refine ⟨39773678998811753294498711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26515785999207835529665807 39773678998811753294498711)
              ·
                refine ⟨59660518498217629941748067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39773678998811753294498711 59660518498217629941748067)
                ·
                  refine ⟨89490777747326444912622101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59660518498217629941748067 89490777747326444912622101)
                  ·
                    refine ⟨4194880206905927105279161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89490777747326444912622101 4194880206905927105279161)
                    ·
                      refine ⟨3146160155179445328959371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4194880206905927105279161 3146160155179445328959371)
                      ·
                        rfl

theorem cell23_6127125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 6, 2].length) (baseStart_6127125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127125 prefixEnd_6127125 := by exact prefixLift 6127125
  have htrace : WordTrace (prefixWord ++ tailWord_6127125) baseStart_6127125 baseEnd_6127125 := by
    simpa [prefixWord, tailWord_6127125, baseEnd_6127125] using wordTrace_append hprefix tailTrace_6127125
  have hstable : (prefixWord ++ tailWord_6127125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127125).length < 2 ^ (prefixWord ++ tailWord_6127125).sum := by decide
  have hdescent : baseEnd_6127125 < baseStart_6127125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127165 : List Nat := [1, 4, 1, 3, 3, 1, 1, 1, 8]
def baseStart_6127165 : Nat := 118140960795 + 6127165 * 2 ^ 59
def prefixEnd_6127165 : Nat := 4983230072969 + 3 ^ 40 * 6127165 * 2
def baseEnd_6127165 : Nat := 349575632711736130273243

theorem tailTrace_6127165 : CollatzResearch.WordTrace tailWord_6127165 prefixEnd_6127165 349575632711736130273243 := by
  unfold tailWord_6127165
  simp only [CollatzResearch.WordTrace]
  refine ⟨223476066847335116316046949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148984044564890077544031299 223476066847335116316046949)
  ·
    refine ⟨41901762533875334309258803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223476066847335116316046949 41901762533875334309258803)
    ·
      refine ⟨62852643800813001463888205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41901762533875334309258803 62852643800813001463888205)
      ·
        refine ⟨23569741425304875548958077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62852643800813001463888205 23569741425304875548958077)
        ·
          refine ⟨8838653034489328330859279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23569741425304875548958077 8838653034489328330859279)
          ·
            refine ⟨13257979551733992496288919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8838653034489328330859279 13257979551733992496288919)
            ·
              refine ⟨19886969327600988744433379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13257979551733992496288919 19886969327600988744433379)
              ·
                refine ⟨29830453991401483116650069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19886969327600988744433379 29830453991401483116650069)
                ·
                  refine ⟨349575632711736130273243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29830453991401483116650069 349575632711736130273243)
                  ·
                    rfl

theorem cell23_6127165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 8].length) (baseStart_6127165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127165 prefixEnd_6127165 := by exact prefixLift 6127165
  have htrace : WordTrace (prefixWord ++ tailWord_6127165) baseStart_6127165 baseEnd_6127165 := by
    simpa [prefixWord, tailWord_6127165, baseEnd_6127165] using wordTrace_append hprefix tailTrace_6127165
  have hstable : (prefixWord ++ tailWord_6127165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127165).length < 2 ^ (prefixWord ++ tailWord_6127165).sum := by decide
  have hdescent : baseEnd_6127165 < baseStart_6127165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127185 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 3, 5, 2]
def baseStart_6127185 : Nat := 118140960795 + 6127185 * 2 ^ 59
def prefixEnd_6127185 : Nat := 4983230072969 + 3 ^ 40 * 6127185 * 2
def baseEnd_6127185 : Nat := 3146190964018715094209095

theorem tailTrace_6127185 : CollatzResearch.WordTrace tailWord_6127185 prefixEnd_6127185 3146190964018715094209095 := by
  unfold tailWord_6127185
  simp only [CollatzResearch.WordTrace]
  refine ⟨223476796307262659731775009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148984530871508439821183339 223476796307262659731775009)
  ·
    refine ⟨167607597230446994798831257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223476796307262659731775009 167607597230446994798831257)
    ·
      refine ⟨125705697922835246099123443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167607597230446994798831257 125705697922835246099123443)
      ·
        refine ⟨188558546884252869148685165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125705697922835246099123443 188558546884252869148685165)
        ·
          refine ⟨70709455081594825930756937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188558546884252869148685165 70709455081594825930756937)
          ·
            refine ⟨53032091311196119448067703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70709455081594825930756937 53032091311196119448067703)
            ·
              refine ⟨79548136966794179172101555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53032091311196119448067703 79548136966794179172101555)
              ·
                refine ⟨119322205450191268758152333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79548136966794179172101555 119322205450191268758152333)
                ·
                  refine ⟨44745827043821725784307125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119322205450191268758152333 44745827043821725784307125)
                  ·
                    refine ⟨4194921285358286792278793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44745827043821725784307125 4194921285358286792278793)
                    ·
                      refine ⟨3146190964018715094209095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4194921285358286792278793 3146190964018715094209095)
                      ·
                        rfl

theorem cell23_6127185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 5, 2].length) (baseStart_6127185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127185 prefixEnd_6127185 := by exact prefixLift 6127185
  have htrace : WordTrace (prefixWord ++ tailWord_6127185) baseStart_6127185 baseEnd_6127185 := by
    simpa [prefixWord, tailWord_6127185, baseEnd_6127185] using wordTrace_append hprefix tailTrace_6127185
  have hstable : (prefixWord ++ tailWord_6127185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127185).length < 2 ^ (prefixWord ++ tailWord_6127185).sum := by decide
  have hdescent : baseEnd_6127185 < baseStart_6127185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127209 : List Nat := [1, 2, 1, 1, 1, 4, 5, 3, 1, 1, 3]
def baseStart_6127209 : Nat := 118140960795 + 6127209 * 2 ^ 59
def prefixEnd_6127209 : Nat := 4983230072969 + 3 ^ 40 * 6127209 * 2
def baseEnd_6127209 : Nat := 3146203287554423000308985

theorem tailTrace_6127209 : CollatzResearch.WordTrace tailWord_6127209 prefixEnd_6127209 3146203287554423000308985 := by
  unfold tailWord_6127209
  simp only [CollatzResearch.WordTrace]
  refine ⟨223477671659175711830648681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148985114439450474553765787 223477671659175711830648681)
  ·
    refine ⟨167608253744381783872986511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223477671659175711830648681 167608253744381783872986511)
    ·
      refine ⟨251412380616572675809479767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167608253744381783872986511 251412380616572675809479767)
      ·
        refine ⟨377118570924859013714219651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251412380616572675809479767 377118570924859013714219651)
        ·
          refine ⟨565677856387288520571329477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377118570924859013714219651 565677856387288520571329477)
          ·
            refine ⟨106064598072616597607124277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 565677856387288520571329477 106064598072616597607124277)
            ·
              refine ⟨9943556069307806025667901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106064598072616597607124277 9943556069307806025667901)
              ·
                refine ⟨3728833525990427259625463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9943556069307806025667901 3728833525990427259625463)
                ·
                  refine ⟨5593250288985640889438195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3728833525990427259625463 5593250288985640889438195)
                  ·
                    refine ⟨8389875433478461334157293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5593250288985640889438195 8389875433478461334157293)
                    ·
                      refine ⟨3146203287554423000308985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8389875433478461334157293 3146203287554423000308985)
                      ·
                        rfl

theorem cell23_6127209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3, 1, 1, 3].length) (baseStart_6127209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127209 prefixEnd_6127209 := by exact prefixLift 6127209
  have htrace : WordTrace (prefixWord ++ tailWord_6127209) baseStart_6127209 baseEnd_6127209 := by
    simpa [prefixWord, tailWord_6127209, baseEnd_6127209] using wordTrace_append hprefix tailTrace_6127209
  have hstable : (prefixWord ++ tailWord_6127209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127209).length < 2 ^ (prefixWord ++ tailWord_6127209).sum := by decide
  have hdescent : baseEnd_6127209 < baseStart_6127209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127225 : List Nat := [1, 2, 1, 3, 3, 1, 1, 3, 4, 4]
def baseStart_6127225 : Nat := 118140960795 + 6127225 * 2 ^ 59
def prefixEnd_6127225 : Nat := 4983230072969 + 3 ^ 40 * 6127225 * 2
def baseEnd_6127225 : Nat := 1048737167748298312569637

theorem tailTrace_6127225 : CollatzResearch.WordTrace tailWord_6127225 prefixEnd_6127225 1048737167748298312569637 := by
  unfold tailWord_6127225
  simp only [CollatzResearch.WordTrace]
  refine ⟨223478255227117746563231129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148985503484745164375487419 223478255227117746563231129)
  ·
    refine ⟨167608691420338309922423347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223478255227117746563231129 167608691420338309922423347)
    ·
      refine ⟨251413037130507464883635021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167608691420338309922423347 251413037130507464883635021)
      ·
        refine ⟨94279888923940299331363133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251413037130507464883635021 94279888923940299331363133)
        ·
          refine ⟨35354958346477612249261175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94279888923940299331363133 35354958346477612249261175)
          ·
            refine ⟨53032437519716418373891763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35354958346477612249261175 53032437519716418373891763)
            ·
              refine ⟨79548656279574627560837645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53032437519716418373891763 79548656279574627560837645)
              ·
                refine ⟨29830746104840485335314117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79548656279574627560837645 29830746104840485335314117)
                ·
                  refine ⟨5593264894657591000371397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29830746104840485335314117 5593264894657591000371397)
                  ·
                    refine ⟨1048737167748298312569637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5593264894657591000371397 1048737167748298312569637)
                    ·
                      rfl

theorem cell23_6127225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4, 4].length) (baseStart_6127225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127225 prefixEnd_6127225 := by exact prefixLift 6127225
  have htrace : WordTrace (prefixWord ++ tailWord_6127225) baseStart_6127225 baseEnd_6127225 := by
    simpa [prefixWord, tailWord_6127225, baseEnd_6127225] using wordTrace_append hprefix tailTrace_6127225
  have hstable : (prefixWord ++ tailWord_6127225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127225).length < 2 ^ (prefixWord ++ tailWord_6127225).sum := by decide
  have hdescent : baseEnd_6127225 < baseStart_6127225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127235 : List Nat := [1, 1, 1, 3, 3, 1, 1, 4, 3, 2, 3]
def baseStart_6127235 : Nat := 118140960795 + 6127235 * 2 ^ 59
def prefixEnd_6127235 : Nat := 4983230072969 + 3 ^ 40 * 6127235 * 2
def baseEnd_6127235 : Nat := 3146216638051439898583865

theorem tailTrace_6127235 : CollatzResearch.WordTrace tailWord_6127235 prefixEnd_6127235 3146216638051439898583865 := by
  unfold tailWord_6127235
  simp only [CollatzResearch.WordTrace]
  refine ⟨223478619957081518271095159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148985746638054345514063439 223478619957081518271095159)
  ·
    refine ⟨335217929935622277406642739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223478619957081518271095159 335217929935622277406642739)
    ·
      refine ⟨502826894903433416109964109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335217929935622277406642739 502826894903433416109964109)
      ·
        refine ⟨188560085588787531041236541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 502826894903433416109964109 188560085588787531041236541)
        ·
          refine ⟨70710032095795324140463703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188560085588787531041236541 70710032095795324140463703)
          ·
            refine ⟨106065048143692986210695555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70710032095795324140463703 106065048143692986210695555)
            ·
              refine ⟨159097572215539479316043333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106065048143692986210695555 159097572215539479316043333)
              ·
                refine ⟨29830794790413652371758125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159097572215539479316043333 29830794790413652371758125)
                ·
                  refine ⟨11186548046405119639409297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29830794790413652371758125 11186548046405119639409297)
                  ·
                    refine ⟨8389911034803839729556973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11186548046405119639409297 8389911034803839729556973)
                    ·
                      refine ⟨3146216638051439898583865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8389911034803839729556973 3146216638051439898583865)
                      ·
                        rfl

theorem cell23_6127235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2, 3].length) (baseStart_6127235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127235 prefixEnd_6127235 := by exact prefixLift 6127235
  have htrace : WordTrace (prefixWord ++ tailWord_6127235) baseStart_6127235 baseEnd_6127235 := by
    simpa [prefixWord, tailWord_6127235, baseEnd_6127235] using wordTrace_append hprefix tailTrace_6127235
  have hstable : (prefixWord ++ tailWord_6127235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127235).length < 2 ^ (prefixWord ++ tailWord_6127235).sum := by decide
  have hdescent : baseEnd_6127235 < baseStart_6127235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127262 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_6127262 : Nat := 118140960795 + 6127262 * 2 ^ 59
def prefixEnd_6127262 : Nat := 4983230072969 + 3 ^ 40 * 6127262 * 2
def baseEnd_6127262 : Nat := 3146230502029111292946241

theorem tailTrace_6127262 : CollatzResearch.WordTrace tailWord_6127262 prefixEnd_6127262 3146230502029111292946241 := by
  unfold tailWord_6127262
  simp only [CollatzResearch.WordTrace]
  refine ⟨27934950590997962735291005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148986403151989134588218693 27934950590997962735291005)
  ·
    refine ⟨10475606471624236025734127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27934950590997962735291005 10475606471624236025734127)
    ·
      refine ⟨15713409707436354038601191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10475606471624236025734127 15713409707436354038601191)
      ·
        refine ⟨23570114561154531057901787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15713409707436354038601191 23570114561154531057901787)
        ·
          refine ⟨35355171841731796586852681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23570114561154531057901787 35355171841731796586852681)
          ·
            refine ⟨26516378881298847440139511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35355171841731796586852681 26516378881298847440139511)
            ·
              refine ⟨39774568321948271160209267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26516378881298847440139511 39774568321948271160209267)
              ·
                refine ⟨59661852482922406740313901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39774568321948271160209267 59661852482922406740313901)
                ·
                  refine ⟨22373194681095902527617713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59661852482922406740313901 22373194681095902527617713)
                  ·
                    refine ⟨16779896010821926895713285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22373194681095902527617713 16779896010821926895713285)
                    ·
                      refine ⟨3146230502029111292946241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16779896010821926895713285 3146230502029111292946241)
                      ·
                        rfl

theorem cell23_6127262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_6127262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127262 prefixEnd_6127262 := by exact prefixLift 6127262
  have htrace : WordTrace (prefixWord ++ tailWord_6127262) baseStart_6127262 baseEnd_6127262 := by
    simpa [prefixWord, tailWord_6127262, baseEnd_6127262] using wordTrace_append hprefix tailTrace_6127262
  have hstable : (prefixWord ++ tailWord_6127262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127262).length < 2 ^ (prefixWord ++ tailWord_6127262).sum := by decide
  have hdescent : baseEnd_6127262 < baseStart_6127262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127272 : List Nat := [2, 1, 7, 1, 12]
def baseStart_6127272 : Nat := 118140960795 + 6127272 * 2 ^ 59
def prefixEnd_6127272 : Nat := 4983230072969 + 3 ^ 40 * 6127272 * 2
def baseEnd_6127272 : Nat := 4315823918841778125955

theorem tailTrace_6127272 : CollatzResearch.WordTrace tailWord_6127272 prefixEnd_6127272 4315823918841778125955 := by
  unfold tailWord_6127272
  simp only [CollatzResearch.WordTrace]
  refine ⟨111739984728973736795096035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148986646305298315726794713 111739984728973736795096035)
  ·
    refine ⟨167609977093460605192644053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111739984728973736795096035 167609977093460605192644053)
    ·
      refine ⟨3928358838127982934202595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 167609977093460605192644053 3928358838127982934202595)
      ·
        refine ⟨5892538257191974401303893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3928358838127982934202595 5892538257191974401303893)
        ·
          refine ⟨4315823918841778125955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5892538257191974401303893 4315823918841778125955)
          ·
            rfl

theorem cell23_6127272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 12].length) (baseStart_6127272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127272 prefixEnd_6127272 := by exact prefixLift 6127272
  have htrace : WordTrace (prefixWord ++ tailWord_6127272) baseStart_6127272 baseEnd_6127272 := by
    simpa [prefixWord, tailWord_6127272, baseEnd_6127272] using wordTrace_append hprefix tailTrace_6127272
  have hstable : (prefixWord ++ tailWord_6127272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127272).length < 2 ^ (prefixWord ++ tailWord_6127272).sum := by decide
  have hdescent : baseEnd_6127272 < baseStart_6127272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127282 : List Nat := [3, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3]
def baseStart_6127282 : Nat := 118140960795 + 6127282 * 2 ^ 59
def prefixEnd_6127282 : Nat := 4983230072969 + 3 ^ 40 * 6127282 * 2
def baseEnd_6127282 : Nat := 3146240771642201214696149

theorem tailTrace_6127282 : CollatzResearch.WordTrace tailWord_6127282 prefixEnd_6127282 3146240771642201214696149 := by
  unfold tailWord_6127282
  simp only [CollatzResearch.WordTrace]
  refine ⟨55870083546977811324514025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148986889458607496865370733 55870083546977811324514025)
  ·
    refine ⟨41902562660233358493385519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55870083546977811324514025 41902562660233358493385519)
    ·
      refine ⟨62853843990350037740078279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41902562660233358493385519 62853843990350037740078279)
      ·
        refine ⟨94280765985525056610117419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62853843990350037740078279 94280765985525056610117419)
        ·
          refine ⟨141421148978287584915176129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94280765985525056610117419 141421148978287584915176129)
          ·
            refine ⟨106065861733715688686382097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141421148978287584915176129 106065861733715688686382097)
            ·
              refine ⟨79549396300286766514786573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106065861733715688686382097 79549396300286766514786573)
              ·
                refine ⟨29831023612607537443044965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79549396300286766514786573 29831023612607537443044965)
                ·
                  refine ⟨5593316927363913270570931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29831023612607537443044965 5593316927363913270570931)
                  ·
                    refine ⟨8389975391045869905856397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5593316927363913270570931 8389975391045869905856397)
                    ·
                      refine ⟨3146240771642201214696149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8389975391045869905856397 3146240771642201214696149)
                      ·
                        rfl

theorem cell23_6127282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_6127282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127282 prefixEnd_6127282 := by exact prefixLift 6127282
  have htrace : WordTrace (prefixWord ++ tailWord_6127282) baseStart_6127282 baseEnd_6127282 := by
    simpa [prefixWord, tailWord_6127282, baseEnd_6127282] using wordTrace_append hprefix tailTrace_6127282
  have hstable : (prefixWord ++ tailWord_6127282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127282).length < 2 ^ (prefixWord ++ tailWord_6127282).sum := by decide
  have hdescent : baseEnd_6127282 < baseStart_6127282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127345 : List Nat := [1, 2, 2, 2, 2, 3, 1, 3, 7]
def baseStart_6127345 : Nat := 118140960795 + 6127345 * 2 ^ 59
def prefixEnd_6127345 : Nat := 4983230072969 + 3 ^ 40 * 6127345 * 2
def baseEnd_6127345 : Nat := 349585902324826052023151

theorem tailTrace_6127345 : CollatzResearch.WordTrace tailWord_6127345 prefixEnd_6127345 349585902324826052023151 := by
  unfold tailWord_6127345
  simp only [CollatzResearch.WordTrace]
  refine ⟨223482631986683007057599489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148988421324455338038399659 223482631986683007057599489)
  ·
    refine ⟨167611973990012255293199617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223482631986683007057599489 167611973990012255293199617)
    ·
      refine ⟨125708980492509191469899713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167611973990012255293199617 125708980492509191469899713)
      ·
        refine ⟨94281735369381893602424785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125708980492509191469899713 94281735369381893602424785)
        ·
          refine ⟨70711301527036420201818589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94281735369381893602424785 70711301527036420201818589)
          ·
            refine ⟨26516738072638657575681971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70711301527036420201818589 26516738072638657575681971)
            ·
              refine ⟨39775107108957986363522957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26516738072638657575681971 39775107108957986363522957)
              ·
                refine ⟨14915665165859244886321109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39775107108957986363522957 14915665165859244886321109)
                ·
                  refine ⟨349585902324826052023151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14915665165859244886321109 349585902324826052023151)
                  ·
                    rfl

theorem cell23_6127345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 7].length) (baseStart_6127345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127345 prefixEnd_6127345 := by exact prefixLift 6127345
  have htrace : WordTrace (prefixWord ++ tailWord_6127345) baseStart_6127345 baseEnd_6127345 := by
    simpa [prefixWord, tailWord_6127345, baseEnd_6127345] using wordTrace_append hprefix tailTrace_6127345
  have hstable : (prefixWord ++ tailWord_6127345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127345).length < 2 ^ (prefixWord ++ tailWord_6127345).sum := by decide
  have hdescent : baseEnd_6127345 < baseStart_6127345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127355 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 1, 5, 3]
def baseStart_6127355 : Nat := 118140960795 + 6127355 * 2 ^ 59
def prefixEnd_6127355 : Nat := 4983230072969 + 3 ^ 40 * 6127355 * 2
def baseEnd_6127355 : Nat := 3146278255729979429083313

theorem tailTrace_6127355 : CollatzResearch.WordTrace tailWord_6127355 prefixEnd_6127355 3146278255729979429083313 := by
  unfold tailWord_6127355
  simp only [CollatzResearch.WordTrace]
  refine ⟨223482996716646778765463519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148988664477764519176975679 223482996716646778765463519)
  ·
    refine ⟨335224495074970168148195279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223482996716646778765463519 335224495074970168148195279)
    ·
      refine ⟨502836742612455252222292919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335224495074970168148195279 502836742612455252222292919)
      ·
        refine ⟨754255113918682878333439379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502836742612455252222292919 754255113918682878333439379)
        ·
          refine ⟨1131382670878024317500159069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754255113918682878333439379 1131382670878024317500159069)
          ·
            refine ⟨424268501579259119062559651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1131382670878024317500159069 424268501579259119062559651)
            ·
              refine ⟨636402752368888678593839477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 424268501579259119062559651 636402752368888678593839477)
              ·
                refine ⟨59662758034583313618172451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 636402752368888678593839477 59662758034583313618172451)
                ·
                  refine ⟨89494137051874970427258677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59662758034583313618172451 89494137051874970427258677)
                  ·
                    refine ⟨8390075348613278477555501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 89494137051874970427258677 8390075348613278477555501)
                    ·
                      refine ⟨3146278255729979429083313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8390075348613278477555501 3146278255729979429083313)
                      ·
                        rfl

theorem cell23_6127355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5, 3].length) (baseStart_6127355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127355 prefixEnd_6127355 := by exact prefixLift 6127355
  have htrace : WordTrace (prefixWord ++ tailWord_6127355) baseStart_6127355 baseEnd_6127355 := by
    simpa [prefixWord, tailWord_6127355, baseEnd_6127355] using wordTrace_append hprefix tailTrace_6127355
  have hstable : (prefixWord ++ tailWord_6127355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127355).length < 2 ^ (prefixWord ++ tailWord_6127355).sum := by decide
  have hdescent : baseEnd_6127355 < baseStart_6127355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127362 : List Nat := [3, 4, 1, 1, 1, 1, 1, 4, 7]
def baseStart_6127362 : Nat := 118140960795 + 6127362 * 2 ^ 59
def prefixEnd_6127362 : Nat := 4983230072969 + 3 ^ 40 * 6127362 * 2
def baseEnd_6127362 : Nat := 349586872232728989077309

theorem tailTrace_6127362 : CollatzResearch.WordTrace tailWord_6127362 prefixEnd_6127362 349586872232728989077309 := by
  unfold tailWord_6127362
  simp only [CollatzResearch.WordTrace]
  refine ⟨55870813006905354740242085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148988834685080945973978893 55870813006905354740242085)
  ·
    refine ⟨10475777438794754013795391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55870813006905354740242085 10475777438794754013795391)
    ·
      refine ⟨15713666158192131020693087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10475777438794754013795391 15713666158192131020693087)
      ·
        refine ⟨23570499237288196531039631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15713666158192131020693087 23570499237288196531039631)
        ·
          refine ⟨35355748855932294796559447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23570499237288196531039631 35355748855932294796559447)
          ·
            refine ⟨53033623283898442194839171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35355748855932294796559447 53033623283898442194839171)
            ·
              refine ⟨79550434925847663292258757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53033623283898442194839171 79550434925847663292258757)
              ·
                refine ⟨14915706548596436867298517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79550434925847663292258757 14915706548596436867298517)
                ·
                  refine ⟨349586872232728989077309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14915706548596436867298517 349586872232728989077309)
                  ·
                    rfl

theorem cell23_6127362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_6127362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127362 prefixEnd_6127362 := by exact prefixLift 6127362
  have htrace : WordTrace (prefixWord ++ tailWord_6127362) baseStart_6127362 baseEnd_6127362 := by
    simpa [prefixWord, tailWord_6127362, baseEnd_6127362] using wordTrace_append hprefix tailTrace_6127362
  have hstable : (prefixWord ++ tailWord_6127362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127362).length < 2 ^ (prefixWord ++ tailWord_6127362).sum := by decide
  have hdescent : baseEnd_6127362 < baseStart_6127362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127392 : List Nat := [2, 1, 1, 5, 1, 1, 3, 2, 2, 5]
def baseStart_6127392 : Nat := 118140960795 + 6127392 * 2 ^ 59
def prefixEnd_6127392 : Nat := 4983230072969 + 3 ^ 40 * 6127392 * 2
def baseEnd_6127392 : Nat := 1048765751504731928106881

theorem tailTrace_6127392 : CollatzResearch.WordTrace tailWord_6127392 prefixEnd_6127392 1048765751504731928106881 := by
  unfold tailWord_6127392
  simp only [CollatzResearch.WordTrace]
  refine ⟨111742173108756367042280215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148989564145008489389706953 111742173108756367042280215)
  ·
    refine ⟨167613259663134550563420323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111742173108756367042280215 167613259663134550563420323)
    ·
      refine ⟨251419889494701825845130485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167613259663134550563420323 251419889494701825845130485)
      ·
        refine ⟨23570614640128296172980983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 251419889494701825845130485 23570614640128296172980983)
        ·
          refine ⟨35355921960192444259471475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23570614640128296172980983 35355921960192444259471475)
          ·
            refine ⟨53033882940288666389207213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35355921960192444259471475 53033882940288666389207213)
            ·
              refine ⟨19887706102608249895952705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53033882940288666389207213 19887706102608249895952705)
              ·
                refine ⟨14915779576956187421964529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19887706102608249895952705 14915779576956187421964529)
                ·
                  refine ⟨11186834682717140566473397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14915779576956187421964529 11186834682717140566473397)
                  ·
                    refine ⟨1048765751504731928106881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11186834682717140566473397 1048765751504731928106881)
                    ·
                      rfl

theorem cell23_6127392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 2, 5].length) (baseStart_6127392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127392 prefixEnd_6127392 := by exact prefixLift 6127392
  have htrace : WordTrace (prefixWord ++ tailWord_6127392) baseStart_6127392 baseEnd_6127392 := by
    simpa [prefixWord, tailWord_6127392, baseEnd_6127392] using wordTrace_append hprefix tailTrace_6127392
  have hstable : (prefixWord ++ tailWord_6127392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127392).length < 2 ^ (prefixWord ++ tailWord_6127392).sum := by decide
  have hdescent : baseEnd_6127392 < baseStart_6127392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127396 : List Nat := [2, 3, 1, 3, 2, 2, 3, 2, 5]
def baseStart_6127396 : Nat := 118140960795 + 6127396 * 2 ^ 59
def prefixEnd_6127396 : Nat := 4983230072969 + 3 ^ 40 * 6127396 * 2
def baseEnd_6127396 : Nat := 349588812048534863185625

theorem tailTrace_6127396 : CollatzResearch.WordTrace tailWord_6127396 prefixEnd_6127396 349588812048534863185625 := by
  unfold tailWord_6127396
  simp only [CollatzResearch.WordTrace]
  refine ⟨111742246054749121383853021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148989661406332161845137361 111742246054749121383853021)
  ·
    refine ⟨41903342270530920518944883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111742246054749121383853021 41903342270530920518944883)
    ·
      refine ⟨62855013405796380778417325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41903342270530920518944883 62855013405796380778417325)
      ·
        refine ⟨23570630027173642791906497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62855013405796380778417325 23570630027173642791906497)
        ·
          refine ⟨17677972520380232093929873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23570630027173642791906497 17677972520380232093929873)
          ·
            refine ⟨13258479390285174070447405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17677972520380232093929873 13258479390285174070447405)
            ·
              refine ⟨4971929771356940276417777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13258479390285174070447405 4971929771356940276417777)
              ·
                refine ⟨3728947328517705207313333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4971929771356940276417777 3728947328517705207313333)
                ·
                  refine ⟨349588812048534863185625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3728947328517705207313333 349588812048534863185625)
                  ·
                    rfl

theorem cell23_6127396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2, 5].length) (baseStart_6127396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127396 prefixEnd_6127396 := by exact prefixLift 6127396
  have htrace : WordTrace (prefixWord ++ tailWord_6127396) baseStart_6127396 baseEnd_6127396 := by
    simpa [prefixWord, tailWord_6127396, baseEnd_6127396] using wordTrace_append hprefix tailTrace_6127396
  have hstable : (prefixWord ++ tailWord_6127396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127396).length < 2 ^ (prefixWord ++ tailWord_6127396).sum := by decide
  have hdescent : baseEnd_6127396 < baseStart_6127396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127456 : List Nat := [2, 1, 1, 3, 3, 3, 1, 4, 1, 4]
def baseStart_6127456 : Nat := 118140960795 + 6127456 * 2 ^ 59
def prefixEnd_6127456 : Nat := 4983230072969 + 3 ^ 40 * 6127456 * 2
def baseEnd_6127456 : Nat := 1048776705758694511306783

theorem tailTrace_6127456 : CollatzResearch.WordTrace tailWord_6127456 prefixEnd_6127456 1048776705758694511306783 := by
  unfold tailWord_6127456
  simp only [CollatzResearch.WordTrace]
  refine ⟨111743340244640436507445111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148991120326187248676593481 111743340244640436507445111)
  ·
    refine ⟨167615010366960654761167667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111743340244640436507445111 167615010366960654761167667)
    ·
      refine ⟨251422515550440982141751501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167615010366960654761167667 251422515550440982141751501)
      ·
        refine ⟨94283443331415368303156813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251422515550440982141751501 94283443331415368303156813)
        ·
          refine ⟨35356291249280763113683805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94283443331415368303156813 35356291249280763113683805)
          ·
            refine ⟨13258609218480286167631427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35356291249280763113683805 13258609218480286167631427)
            ·
              refine ⟨19887913827720429251447141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13258609218480286167631427 19887913827720429251447141)
              ·
                refine ⟨3728983842697580484646339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19887913827720429251447141 3728983842697580484646339)
                ·
                  refine ⟨5593475764046370726969509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3728983842697580484646339 5593475764046370726969509)
                  ·
                    refine ⟨1048776705758694511306783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5593475764046370726969509 1048776705758694511306783)
                    ·
                      rfl

theorem cell23_6127456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4, 1, 4].length) (baseStart_6127456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127456 prefixEnd_6127456 := by exact prefixLift 6127456
  have htrace : WordTrace (prefixWord ++ tailWord_6127456) baseStart_6127456 baseEnd_6127456 := by
    simpa [prefixWord, tailWord_6127456, baseEnd_6127456] using wordTrace_append hprefix tailTrace_6127456
  have hstable : (prefixWord ++ tailWord_6127456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127456).length < 2 ^ (prefixWord ++ tailWord_6127456).sum := by decide
  have hdescent : baseEnd_6127456 < baseStart_6127456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127475 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 7]
def baseStart_6127475 : Nat := 118140960795 + 6127475 * 2 ^ 59
def prefixEnd_6127475 : Nat := 4983230072969 + 3 ^ 40 * 6127475 * 2
def baseEnd_6127475 : Nat := 3146339873408518959582761

theorem tailTrace_6127475 : CollatzResearch.WordTrace tailWord_6127475 prefixEnd_6127475 3146339873408518959582761 := by
  unfold tailWord_6127475
  simp only [CollatzResearch.WordTrace]
  refine ⟨223487373476212039259831879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148991582317474692839887919 223487373476212039259831879)
  ·
    refine ⟨335231060214318058889747819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223487373476212039259831879 335231060214318058889747819)
    ·
      refine ⟨502846590321477088334621729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335231060214318058889747819 502846590321477088334621729)
      ·
        refine ⟨377134942741107816250966297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 502846590321477088334621729 377134942741107816250966297)
        ·
          refine ⟨282851207055830862188224723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 377134942741107816250966297 282851207055830862188224723)
          ·
            refine ⟨424276810583746293282337085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282851207055830862188224723 424276810583746293282337085)
            ·
              refine ⟨159103803968904859980876407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 424276810583746293282337085 159103803968904859980876407)
              ·
                refine ⟨238655705953357289971314611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159103803968904859980876407 238655705953357289971314611)
                ·
                  refine ⟨357983558930035934956971917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 238655705953357289971314611 357983558930035934956971917)
                  ·
                    refine ⟨134243834598763475608864469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 357983558930035934956971917 134243834598763475608864469)
                    ·
                      refine ⟨3146339873408518959582761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 134243834598763475608864469 3146339873408518959582761)
                      ·
                        rfl

theorem cell23_6127475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 7].length) (baseStart_6127475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127475 prefixEnd_6127475 := by exact prefixLift 6127475
  have htrace : WordTrace (prefixWord ++ tailWord_6127475) baseStart_6127475 baseEnd_6127475 := by
    simpa [prefixWord, tailWord_6127475, baseEnd_6127475] using wordTrace_append hprefix tailTrace_6127475
  have hstable : (prefixWord ++ tailWord_6127475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127475).length < 2 ^ (prefixWord ++ tailWord_6127475).sum := by decide
  have hdescent : baseEnd_6127475 < baseStart_6127475 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6127482 : List Nat := [3, 1, 1, 1, 1, 1, 6, 1, 3, 5]
def baseStart_6127482 : Nat := 118140960795 + 6127482 * 2 ^ 59
def prefixEnd_6127482 : Nat := 4983230072969 + 3 ^ 40 * 6127482 * 2
def baseEnd_6127482 : Nat := 1048781155924366810731743

theorem tailTrace_6127482 : CollatzResearch.WordTrace tailWord_6127482 prefixEnd_6127482 1048781155924366810731743 := by
  unfold tailWord_6127482
  simp only [CollatzResearch.WordTrace]
  refine ⟨55871907196796669863834175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148991752524791119636891133 55871907196796669863834175)
  ·
    refine ⟨83807860795195004795751263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55871907196796669863834175 83807860795195004795751263)
    ·
      refine ⟨125711791192792507193626895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83807860795195004795751263 125711791192792507193626895)
      ·
        refine ⟨188567686789188760790440343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125711791192792507193626895 188567686789188760790440343)
        ·
          refine ⟨282851530183783141185660515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188567686789188760790440343 282851530183783141185660515)
          ·
            refine ⟨424277295275674711778490773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282851530183783141185660515 424277295275674711778490773)
            ·
              refine ⟨19887998216047252114616755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 424277295275674711778490773 19887998216047252114616755)
              ·
                refine ⟨29831997324070878171925133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19887998216047252114616755 29831997324070878171925133)
                ·
                  refine ⟨11186998996526579314471925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29831997324070878171925133 11186998996526579314471925)
                  ·
                    refine ⟨1048781155924366810731743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11186998996526579314471925 1048781155924366810731743)
                    ·
                      rfl

theorem cell23_6127482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 3, 5].length) (baseStart_6127482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6127482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6127482 prefixEnd_6127482 := by exact prefixLift 6127482
  have htrace : WordTrace (prefixWord ++ tailWord_6127482) baseStart_6127482 baseEnd_6127482 := by
    simpa [prefixWord, tailWord_6127482, baseEnd_6127482] using wordTrace_append hprefix tailTrace_6127482
  have hstable : (prefixWord ++ tailWord_6127482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6127482).length < 2 ^ (prefixWord ++ tailWord_6127482).sum := by decide
  have hdescent : baseEnd_6127482 < baseStart_6127482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6127482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
