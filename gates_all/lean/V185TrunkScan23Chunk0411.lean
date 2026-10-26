import V185TrunkScan23Chunk0410

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2430231 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 4, 2, 3]
def baseStart_2430231 : Nat := 118140960795 + 2430231 * 2 ^ 59
def prefixEnd_2430231 : Nat := 4983230072969 + 3 ^ 40 * 2430231 * 2
def baseEnd_2430231 : Nat := 1247876604456786443736077

theorem tailTrace_2430231 : CollatzResearch.WordTrace tailWord_2430231 prefixEnd_2430231 1247876604456786443736077 := by
  unfold tailWord_2430231
  simp only [CollatzResearch.WordTrace]
  refine ⟨88637806458695612256058547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59091870972463741504039031 88637806458695612256058547)
  ·
    refine ⟨132956709688043418384087821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88637806458695612256058547 132956709688043418384087821)
    ·
      refine ⟨49858766133016281894032933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132956709688043418384087821 49858766133016281894032933)
      ·
        refine ⟨9348518649940552855131175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49858766133016281894032933 9348518649940552855131175)
        ·
          refine ⟨14022777974910829282696763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9348518649940552855131175 14022777974910829282696763)
          ·
            refine ⟨21034166962366243924045145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14022777974910829282696763 21034166962366243924045145)
            ·
              refine ⟨15775625221774682943033859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21034166962366243924045145 15775625221774682943033859)
              ·
                refine ⟨23663437832662024414550789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15775625221774682943033859 23663437832662024414550789)
                ·
                  refine ⟨4436894593624129577728273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23663437832662024414550789 4436894593624129577728273)
                  ·
                    refine ⟨3327670945218097183296205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4436894593624129577728273 3327670945218097183296205)
                    ·
                      refine ⟨1247876604456786443736077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3327670945218097183296205 1247876604456786443736077)
                      ·
                        rfl

theorem cell23_2430231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_2430231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430231 prefixEnd_2430231 := by exact prefixLift 2430231
  have htrace : WordTrace (prefixWord ++ tailWord_2430231) baseStart_2430231 baseEnd_2430231 := by
    simpa [prefixWord, tailWord_2430231, baseEnd_2430231] using wordTrace_append hprefix tailTrace_2430231
  have hstable : (prefixWord ++ tailWord_2430231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430231).length < 2 ^ (prefixWord ++ tailWord_2430231).sum := by decide
  have hdescent : baseEnd_2430231 < baseStart_2430231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430281 : List Nat := [1, 2, 1, 1, 2, 3, 4, 3, 1, 5]
def baseStart_2430281 : Nat := 118140960795 + 2430281 * 2 ^ 59
def prefixEnd_2430281 : Nat := 4983230072969 + 3 ^ 40 * 2430281 * 2
def baseEnd_2430281 : Nat := 415967426163170416036949

theorem tailTrace_2430281 : CollatzResearch.WordTrace tailWord_2430281 prefixEnd_2430281 415967426163170416036949 := by
  unfold tailWord_2430281
  simp only [CollatzResearch.WordTrace]
  refine ⟨88639630108514470795378697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59093086739009647196919131 88639630108514470795378697)
  ·
    refine ⟨66479722581385853096534023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88639630108514470795378697 66479722581385853096534023)
    ·
      refine ⟨99719583872078779644801035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66479722581385853096534023 99719583872078779644801035)
      ·
        refine ⟨149579375808118169467201553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99719583872078779644801035 149579375808118169467201553)
        ·
          refine ⟨112184531856088627100401165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149579375808118169467201553 112184531856088627100401165)
          ·
            refine ⟨42069199446033235162650437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112184531856088627100401165 42069199446033235162650437)
            ·
              refine ⟨7887974896131231592996957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42069199446033235162650437 7887974896131231592996957)
              ·
                refine ⟨2957990586049211847373859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7887974896131231592996957 2957990586049211847373859)
                ·
                  refine ⟨4436985879073817771060789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2957990586049211847373859 4436985879073817771060789)
                  ·
                    refine ⟨415967426163170416036949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4436985879073817771060789 415967426163170416036949)
                    ·
                      rfl

theorem cell23_2430281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 5].length) (baseStart_2430281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430281 prefixEnd_2430281 := by exact prefixLift 2430281
  have htrace : WordTrace (prefixWord ++ tailWord_2430281) baseStart_2430281 baseEnd_2430281 := by
    simpa [prefixWord, tailWord_2430281, baseEnd_2430281] using wordTrace_append hprefix tailTrace_2430281
  have hstable : (prefixWord ++ tailWord_2430281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430281).length < 2 ^ (prefixWord ++ tailWord_2430281).sum := by decide
  have hdescent : baseEnd_2430281 < baseStart_2430281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430288 : List Nat := [2, 1, 1, 1, 1, 5, 3, 2, 2, 3, 2]
def baseStart_2430288 : Nat := 118140960795 + 2430288 * 2 ^ 59
def prefixEnd_2430288 : Nat := 4983230072969 + 3 ^ 40 * 2430288 * 2
def baseEnd_2430288 : Nat := 1247905872854092720723315

theorem tailTrace_2430288 : CollatzResearch.WordTrace tailWord_2430288 prefixEnd_2430288 1247905872854092720723315 := by
  unfold tailWord_2430288
  simp only [CollatzResearch.WordTrace]
  refine ⟨44319942709744555495441759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59093256946326073993922345 44319942709744555495441759)
  ·
    refine ⟨66479914064616833243162639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44319942709744555495441759 66479914064616833243162639)
    ·
      refine ⟨99719871096925249864743959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66479914064616833243162639 99719871096925249864743959)
      ·
        refine ⟨149579806645387874797115939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99719871096925249864743959 149579806645387874797115939)
        ·
          refine ⟨224369709968081812195673909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149579806645387874797115939 224369709968081812195673909)
          ·
            refine ⟨21034660309507669893344429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 224369709968081812195673909 21034660309507669893344429)
            ·
              refine ⟨7887997616065376210004161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21034660309507669893344429 7887997616065376210004161)
              ·
                refine ⟨5915998212049032157503121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7887997616065376210004161 5915998212049032157503121)
                ·
                  refine ⟨4436998659036774118127341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5915998212049032157503121 4436998659036774118127341)
                  ·
                    refine ⟨1663874497138790294297753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4436998659036774118127341 1663874497138790294297753)
                    ·
                      refine ⟨1247905872854092720723315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1663874497138790294297753 1247905872854092720723315)
                      ·
                        rfl

theorem cell23_2430288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 2, 3, 2].length) (baseStart_2430288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430288 prefixEnd_2430288 := by exact prefixLift 2430288
  have htrace : WordTrace (prefixWord ++ tailWord_2430288) baseStart_2430288 baseEnd_2430288 := by
    simpa [prefixWord, tailWord_2430288, baseEnd_2430288] using wordTrace_append hprefix tailTrace_2430288
  have hstable : (prefixWord ++ tailWord_2430288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430288).length < 2 ^ (prefixWord ++ tailWord_2430288).sum := by decide
  have hdescent : baseEnd_2430288 < baseStart_2430288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430295 : List Nat := [1, 1, 3, 2, 3, 4, 1, 1, 3, 1, 3]
def baseStart_2430295 : Nat := 118140960795 + 2430295 * 2 ^ 59
def prefixEnd_2430295 : Nat := 4983230072969 + 3 ^ 40 * 2430295 * 2
def baseEnd_2430295 : Nat := 1247909467218674193335783

theorem tailTrace_2430295 : CollatzResearch.WordTrace tailWord_2430295 prefixEnd_2430295 1247909467218674193335783 := by
  unfold tailWord_2430295
  simp only [CollatzResearch.WordTrace]
  refine ⟨88640140730463751186388339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59093427153642500790925559 88640140730463751186388339)
  ·
    refine ⟨132960211095695626779582509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88640140730463751186388339 132960211095695626779582509)
    ·
      refine ⟨49860079160885860042343441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132960211095695626779582509 49860079160885860042343441)
      ·
        refine ⟨37395059370664395031757581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49860079160885860042343441 37395059370664395031757581)
        ·
          refine ⟨14023147263999148136909093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37395059370664395031757581 14023147263999148136909093)
          ·
            refine ⟨2629340111999840275670455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14023147263999148136909093 2629340111999840275670455)
            ·
              refine ⟨3944010167999760413505683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2629340111999840275670455 3944010167999760413505683)
              ·
                refine ⟨5916015251999640620258525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3944010167999760413505683 5916015251999640620258525)
                ·
                  refine ⟨2218505719499865232596947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5916015251999640620258525 2218505719499865232596947)
                  ·
                    refine ⟨3327758579249797848895421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2218505719499865232596947 3327758579249797848895421)
                    ·
                      refine ⟨1247909467218674193335783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3327758579249797848895421 1247909467218674193335783)
                      ·
                        rfl

theorem cell23_2430295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_2430295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430295 prefixEnd_2430295 := by exact prefixLift 2430295
  have htrace : WordTrace (prefixWord ++ tailWord_2430295) baseStart_2430295 baseEnd_2430295 := by
    simpa [prefixWord, tailWord_2430295, baseEnd_2430295] using wordTrace_append hprefix tailTrace_2430295
  have hstable : (prefixWord ++ tailWord_2430295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430295).length < 2 ^ (prefixWord ++ tailWord_2430295).sum := by decide
  have hdescent : baseEnd_2430295 < baseStart_2430295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430331 : List Nat := [1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 4]
def baseStart_2430331 : Nat := 118140960795 + 2430331 * 2 ^ 59
def prefixEnd_2430331 : Nat := 4983230072969 + 3 ^ 40 * 2430331 * 2
def baseEnd_2430331 : Nat := 1247927952522236052485617

theorem tailTrace_2430331 : CollatzResearch.WordTrace tailWord_2430331 prefixEnd_2430331 1247927952522236052485617 := by
  unfold tailWord_2430331
  simp only [CollatzResearch.WordTrace]
  refine ⟨88641453758333329334698847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59094302505555552889799231 88641453758333329334698847)
  ·
    refine ⟨132962180637499994002048271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88641453758333329334698847 132962180637499994002048271)
    ·
      refine ⟨199443270956249991003072407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132962180637499994002048271 199443270956249991003072407)
      ·
        refine ⟨299164906434374986504608611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199443270956249991003072407 299164906434374986504608611)
        ·
          refine ⟨448747359651562479756912917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299164906434374986504608611 448747359651562479756912917)
          ·
            refine ⟨21035032483666991238605293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 448747359651562479756912917 21035032483666991238605293)
            ·
              refine ⟨7888137181375121714476985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21035032483666991238605293 7888137181375121714476985)
              ·
                refine ⟨5916102886031341285857739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7888137181375121714476985 5916102886031341285857739)
                ·
                  refine ⟨8874154329047011928786609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5916102886031341285857739 8874154329047011928786609)
                  ·
                    refine ⟨6655615746785258946589957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8874154329047011928786609 6655615746785258946589957)
                    ·
                      refine ⟨1247927952522236052485617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6655615746785258946589957 1247927952522236052485617)
                      ·
                        rfl

theorem cell23_2430331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 4].length) (baseStart_2430331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430331 prefixEnd_2430331 := by exact prefixLift 2430331
  have htrace : WordTrace (prefixWord ++ tailWord_2430331) baseStart_2430331 baseEnd_2430331 := by
    simpa [prefixWord, tailWord_2430331, baseEnd_2430331] using wordTrace_append hprefix tailTrace_2430331
  have hstable : (prefixWord ++ tailWord_2430331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430331).length < 2 ^ (prefixWord ++ tailWord_2430331).sum := by decide
  have hdescent : baseEnd_2430331 < baseStart_2430331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430345 : List Nat := [1, 2, 1, 1, 7, 1, 2, 2, 2, 4]
def baseStart_2430345 : Nat := 118140960795 + 2430345 * 2 ^ 59
def prefixEnd_2430345 : Nat := 4983230072969 + 3 ^ 40 * 2430345 * 2
def baseEnd_2430345 : Nat := 415978380417132999236851

theorem tailTrace_2430345 : CollatzResearch.WordTrace tailWord_2430345 prefixEnd_2430345 415978380417132999236851 := by
  unfold tailWord_2430345
  simp only [CollatzResearch.WordTrace]
  refine ⟨88641964380282609725708489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59094642920188406483805659 88641964380282609725708489)
  ·
    refine ⟨66481473285211957294281367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88641964380282609725708489 66481473285211957294281367)
    ·
      refine ⟨99722209927817935941422051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66481473285211957294281367 99722209927817935941422051)
      ·
        refine ⟨149583314891726903912133077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99722209927817935941422051 149583314891726903912133077)
        ·
          refine ⟨3505858942774849310440619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 149583314891726903912133077 3505858942774849310440619)
          ·
            refine ⟨5258788414162273965660929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3505858942774849310440619 5258788414162273965660929)
            ·
              refine ⟨3944091310621705474245697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5258788414162273965660929 3944091310621705474245697)
              ·
                refine ⟨2958068482966279105684273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3944091310621705474245697 2958068482966279105684273)
                ·
                  refine ⟨2218551362224709329263205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2958068482966279105684273 2218551362224709329263205)
                  ·
                    refine ⟨415978380417132999236851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2218551362224709329263205 415978380417132999236851)
                    ·
                      rfl

theorem cell23_2430345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2, 4].length) (baseStart_2430345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430345 prefixEnd_2430345 := by exact prefixLift 2430345
  have htrace : WordTrace (prefixWord ++ tailWord_2430345) baseStart_2430345 baseEnd_2430345 := by
    simpa [prefixWord, tailWord_2430345, baseEnd_2430345] using wordTrace_append hprefix tailTrace_2430345
  have hstable : (prefixWord ++ tailWord_2430345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430345).length < 2 ^ (prefixWord ++ tailWord_2430345).sum := by decide
  have hdescent : baseEnd_2430345 < baseStart_2430345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430368 : List Nat := [2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 3]
def baseStart_2430368 : Nat := 118140960795 + 2430368 * 2 ^ 59
def prefixEnd_2430368 : Nat := 4983230072969 + 3 ^ 40 * 2430368 * 2
def baseEnd_2430368 : Nat := 1247946951306452407722947

theorem tailTrace_2430368 : CollatzResearch.WordTrace tailWord_2430368 prefixEnd_2430368 1247946951306452407722947 := by
  unfold tailWord_2430368
  simp only [CollatzResearch.WordTrace]
  refine ⟨44321401629599642326897879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59095202172799523102530505 44321401629599642326897879)
  ·
    refine ⟨66482102444399463490346819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44321401629599642326897879 66482102444399463490346819)
    ·
      refine ⟨99723153666599195235520229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66482102444399463490346819 99723153666599195235520229)
      ·
        refine ⟨18698091312487349106660043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99723153666599195235520229 18698091312487349106660043)
        ·
          refine ⟨28047136968731023659990065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18698091312487349106660043 28047136968731023659990065)
          ·
            refine ⟨21035352726548267744992549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28047136968731023659990065 21035352726548267744992549)
            ·
              refine ⟨3944128636227800202186103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21035352726548267744992549 3944128636227800202186103)
              ·
                refine ⟨5916192954341700303279155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3944128636227800202186103 5916192954341700303279155)
                ·
                  refine ⟨8874289431512550454918733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5916192954341700303279155 8874289431512550454918733)
                  ·
                    refine ⟨3327858536817206420594525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8874289431512550454918733 3327858536817206420594525)
                    ·
                      refine ⟨1247946951306452407722947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3327858536817206420594525 1247946951306452407722947)
                      ·
                        rfl

theorem cell23_2430368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_2430368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430368 prefixEnd_2430368 := by exact prefixLift 2430368
  have htrace : WordTrace (prefixWord ++ tailWord_2430368) baseStart_2430368 baseEnd_2430368 := by
    simpa [prefixWord, tailWord_2430368, baseEnd_2430368] using wordTrace_append hprefix tailTrace_2430368
  have hstable : (prefixWord ++ tailWord_2430368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430368).length < 2 ^ (prefixWord ++ tailWord_2430368).sum := by decide
  have hdescent : baseEnd_2430368 < baseStart_2430368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430411 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 1, 6, 3]
def baseStart_2430411 : Nat := 118140960795 + 2430411 * 2 ^ 59
def prefixEnd_2430411 : Nat := 4983230072969 + 3 ^ 40 * 2430411 * 2
def baseEnd_2430411 : Nat := 1247969030974595739485249

theorem tailTrace_2430411 : CollatzResearch.WordTrace tailWord_2430411 prefixEnd_2430411 1247969030974595739485249 := by
  unfold tailWord_2430411
  simp only [CollatzResearch.WordTrace]
  refine ⟨88644371598043502997611087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59096247732029001998407391 88644371598043502997611087)
  ·
    refine ⟨132966557397065254496416631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88644371598043502997611087 132966557397065254496416631)
    ·
      refine ⟨199449836095597881744624947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132966557397065254496416631 199449836095597881744624947)
      ·
        refine ⟨299174754143396822616937421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199449836095597881744624947 299174754143396822616937421)
        ·
          refine ⟨112190532803773808481351533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 299174754143396822616937421 112190532803773808481351533)
          ·
            refine ⟨42071449801415178180506825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112190532803773808481351533 42071449801415178180506825)
            ·
              refine ⟨31553587351061383635380119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42071449801415178180506825 31553587351061383635380119)
              ·
                refine ⟨47330381026592075453070179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31553587351061383635380119 47330381026592075453070179)
                ·
                  refine ⟨70995571539888113179605269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47330381026592075453070179 70995571539888113179605269)
                  ·
                    refine ⟨3327917415932255305293997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70995571539888113179605269 3327917415932255305293997)
                    ·
                      refine ⟨1247969030974595739485249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3327917415932255305293997 1247969030974595739485249)
                      ·
                        rfl

theorem cell23_2430411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6, 3].length) (baseStart_2430411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430411 prefixEnd_2430411 := by exact prefixLift 2430411
  have htrace : WordTrace (prefixWord ++ tailWord_2430411) baseStart_2430411 baseEnd_2430411 := by
    simpa [prefixWord, tailWord_2430411, baseEnd_2430411] using wordTrace_append hprefix tailTrace_2430411
  have hstable : (prefixWord ++ tailWord_2430411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430411).length < 2 ^ (prefixWord ++ tailWord_2430411).sum := by decide
  have hdescent : baseEnd_2430411 < baseStart_2430411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430425 : List Nat := [1, 2, 1, 2, 4, 2, 3, 1, 1, 4, 2]
def baseStart_2430425 : Nat := 118140960795 + 2430425 * 2 ^ 59
def prefixEnd_2430425 : Nat := 4983230072969 + 3 ^ 40 * 2430425 * 2
def baseEnd_2430425 : Nat := 1247976219703758684710185

theorem tailTrace_2430425 : CollatzResearch.WordTrace tailWord_2430425 prefixEnd_2430425 1247976219703758684710185 := by
  unfold tailWord_2430425
  simp only [CollatzResearch.WordTrace]
  refine ⟨88644882219992783388620729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59096588146661855592413819 88644882219992783388620729)
  ·
    refine ⟨66483661664994587541465547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88644882219992783388620729 66483661664994587541465547)
    ·
      refine ⟨99725492497491881312198321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66483661664994587541465547 99725492497491881312198321)
      ·
        refine ⟨74794119373118910984148741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99725492497491881312198321 74794119373118910984148741)
        ·
          refine ⟨14023897382459795809527889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74794119373118910984148741 14023897382459795809527889)
          ·
            refine ⟨10517923036844846857145917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14023897382459795809527889 10517923036844846857145917)
            ·
              refine ⟨3944221138816817571429719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10517923036844846857145917 3944221138816817571429719)
              ·
                refine ⟨5916331708225226357144579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3944221138816817571429719 5916331708225226357144579)
                ·
                  refine ⟨8874497562337839535716869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5916331708225226357144579 8874497562337839535716869)
                  ·
                    refine ⟨1663968292938344912946913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8874497562337839535716869 1663968292938344912946913)
                    ·
                      refine ⟨1247976219703758684710185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1663968292938344912946913 1247976219703758684710185)
                      ·
                        rfl

theorem cell23_2430425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 4, 2].length) (baseStart_2430425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430425 prefixEnd_2430425 := by exact prefixLift 2430425
  have htrace : WordTrace (prefixWord ++ tailWord_2430425) baseStart_2430425 baseEnd_2430425 := by
    simpa [prefixWord, tailWord_2430425, baseEnd_2430425] using wordTrace_append hprefix tailTrace_2430425
  have hstable : (prefixWord ++ tailWord_2430425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430425).length < 2 ^ (prefixWord ++ tailWord_2430425).sum := by decide
  have hdescent : baseEnd_2430425 < baseStart_2430425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430431 : List Nat := [1, 1, 2, 3, 3, 1, 1, 4, 7]
def baseStart_2430431 : Nat := 118140960795 + 2430431 * 2 ^ 59
def prefixEnd_2430431 : Nat := 4983230072969 + 3 ^ 40 * 2430431 * 2
def baseEnd_2430431 : Nat := 138664366731965073470573

theorem tailTrace_2430431 : CollatzResearch.WordTrace tailWord_2430431 prefixEnd_2430431 138664366731965073470573 := by
  unfold tailWord_2430431
  simp only [CollatzResearch.WordTrace]
  refine ⟨88645101057971046413339147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59096734038647364275559431 88645101057971046413339147)
  ·
    refine ⟨132967651586956569620008721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88645101057971046413339147 132967651586956569620008721)
    ·
      refine ⟨99725738690217427215006541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132967651586956569620008721 99725738690217427215006541)
      ·
        refine ⟨37397152008831535205627453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99725738690217427215006541 37397152008831535205627453)
        ·
          refine ⟨14023932003311825702110295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37397152008831535205627453 14023932003311825702110295)
          ·
            refine ⟨21035898004967738553165443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14023932003311825702110295 21035898004967738553165443)
            ·
              refine ⟨31553847007451607829748165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21035898004967738553165443 31553847007451607829748165)
              ·
                refine ⟨5916346313897176468077781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31553847007451607829748165 5916346313897176468077781)
                ·
                  refine ⟨138664366731965073470573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5916346313897176468077781 138664366731965073470573)
                  ·
                    rfl

theorem cell23_2430431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 7].length) (baseStart_2430431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430431 prefixEnd_2430431 := by exact prefixLift 2430431
  have htrace : WordTrace (prefixWord ++ tailWord_2430431) baseStart_2430431 baseEnd_2430431 := by
    simpa [prefixWord, tailWord_2430431, baseEnd_2430431] using wordTrace_append hprefix tailTrace_2430431
  have hstable : (prefixWord ++ tailWord_2430431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430431).length < 2 ^ (prefixWord ++ tailWord_2430431).sum := by decide
  have hdescent : baseEnd_2430431 < baseStart_2430431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430445 : List Nat := [1, 5, 1, 3, 2, 1, 1, 1, 2, 1, 5]
def baseStart_2430445 : Nat := 118140960795 + 2430445 * 2 ^ 59
def prefixEnd_2430445 : Nat := 4983230072969 + 3 ^ 40 * 2430445 * 2
def baseEnd_2430445 : Nat := 1247986489316848606460093

theorem tailTrace_2430445 : CollatzResearch.WordTrace tailWord_2430445 prefixEnd_2430445 1247986489316848606460093 := by
  unfold tailWord_2430445
  simp only [CollatzResearch.WordTrace]
  refine ⟨88645611679920326804348789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59097074453280217869565859 88645611679920326804348789)
  ·
    refine ⟨8310526094992530637907699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88645611679920326804348789 8310526094992530637907699)
    ·
      refine ⟨12465789142488795956861549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8310526094992530637907699 12465789142488795956861549)
      ·
        refine ⟨4674670928433298483823081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12465789142488795956861549 4674670928433298483823081)
        ·
          refine ⟨3506003196324973862867311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4674670928433298483823081 3506003196324973862867311)
          ·
            refine ⟨5259004794487460794300967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3506003196324973862867311 5259004794487460794300967)
            ·
              refine ⟨7888507191731191191451451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5259004794487460794300967 7888507191731191191451451)
              ·
                refine ⟨11832760787596786787177177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7888507191731191191451451 11832760787596786787177177)
                ·
                  refine ⟨8874570590697590090382883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11832760787596786787177177 8874570590697590090382883)
                  ·
                    refine ⟨13311855886046385135574325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8874570590697590090382883 13311855886046385135574325)
                    ·
                      refine ⟨1247986489316848606460093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13311855886046385135574325 1247986489316848606460093)
                      ·
                        rfl

theorem cell23_2430445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_2430445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430445 prefixEnd_2430445 := by exact prefixLift 2430445
  have htrace : WordTrace (prefixWord ++ tailWord_2430445) baseStart_2430445 baseEnd_2430445 := by
    simpa [prefixWord, tailWord_2430445, baseEnd_2430445] using wordTrace_append hprefix tailTrace_2430445
  have hstable : (prefixWord ++ tailWord_2430445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430445).length < 2 ^ (prefixWord ++ tailWord_2430445).sum := by decide
  have hdescent : baseEnd_2430445 < baseStart_2430445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430465 : List Nat := [1, 2, 4, 1, 4, 2, 1, 1, 7]
def baseStart_2430465 : Nat := 118140960795 + 2430465 * 2 ^ 59
def prefixEnd_2430465 : Nat := 4983230072969 + 3 ^ 40 * 2430465 * 2
def baseEnd_2430465 : Nat := 138666306547770947578889

theorem tailTrace_2430465 : CollatzResearch.WordTrace tailWord_2430465 prefixEnd_2430465 138666306547770947578889 := by
  unfold tailWord_2430465
  simp only [CollatzResearch.WordTrace]
  refine ⟨88646341139847870220076849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59097560759898580146717899 88646341139847870220076849)
  ·
    refine ⟨66484755854885902665057637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88646341139847870220076849 66484755854885902665057637)
    ·
      refine ⟨12465891722791106749698307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66484755854885902665057637 12465891722791106749698307)
      ·
        refine ⟨18698837584186660124547461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12465891722791106749698307 18698837584186660124547461)
        ·
          refine ⟨3506032047034998773352649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18698837584186660124547461 3506032047034998773352649)
          ·
            refine ⟨2629524035276249080014487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3506032047034998773352649 2629524035276249080014487)
            ·
              refine ⟨3944286052914373620021731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2629524035276249080014487 3944286052914373620021731)
              ·
                refine ⟨5916429079371560430032597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3944286052914373620021731 5916429079371560430032597)
                ·
                  refine ⟨138666306547770947578889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5916429079371560430032597 138666306547770947578889)
                  ·
                    rfl

theorem cell23_2430465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 7].length) (baseStart_2430465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430465 prefixEnd_2430465 := by exact prefixLift 2430465
  have htrace : WordTrace (prefixWord ++ tailWord_2430465) baseStart_2430465 baseEnd_2430465 := by
    simpa [prefixWord, tailWord_2430465, baseEnd_2430465] using wordTrace_append hprefix tailTrace_2430465
  have hstable : (prefixWord ++ tailWord_2430465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430465).length < 2 ^ (prefixWord ++ tailWord_2430465).sum := by decide
  have hdescent : baseEnd_2430465 < baseStart_2430465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430470 : List Nat := [6, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3]
def baseStart_2430470 : Nat := 118140960795 + 2430470 * 2 ^ 59
def prefixEnd_2430470 : Nat := 4983230072969 + 3 ^ 40 * 2430470 * 2
def baseEnd_2430470 : Nat := 1247999326333211008647479

theorem tailTrace_2430470 : CollatzResearch.WordTrace tailWord_2430470 prefixEnd_2430470 1247999326333211008647479 := by
  unfold tailWord_2430470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2770203859525929877312777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59097682336553170716005909 2770203859525929877312777)
  ·
    refine ⟨2077652894644447407984583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2770203859525929877312777 2077652894644447407984583)
    ·
      refine ⟨3116479341966671111976875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2077652894644447407984583 3116479341966671111976875)
      ·
        refine ⟨4674719012950006667965313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3116479341966671111976875 4674719012950006667965313)
        ·
          refine ⟨3506039259712505000973985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4674719012950006667965313 3506039259712505000973985)
          ·
            refine ⟨2629529444784378750730489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3506039259712505000973985 2629529444784378750730489)
            ·
              refine ⟨1972147083588284063047867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2629529444784378750730489 1972147083588284063047867)
              ·
                refine ⟨2958220625382426094571801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1972147083588284063047867 2958220625382426094571801)
                ·
                  refine ⟨2218665469036819570928851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2958220625382426094571801 2218665469036819570928851)
                  ·
                    refine ⟨3327998203555229356393277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2218665469036819570928851 3327998203555229356393277)
                    ·
                      refine ⟨1247999326333211008647479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3327998203555229356393277 1247999326333211008647479)
                      ·
                        rfl

theorem cell23_2430470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_2430470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430470 prefixEnd_2430470 := by exact prefixLift 2430470
  have htrace : WordTrace (prefixWord ++ tailWord_2430470) baseStart_2430470 baseEnd_2430470 := by
    simpa [prefixWord, tailWord_2430470, baseEnd_2430470] using wordTrace_append hprefix tailTrace_2430470
  have hstable : (prefixWord ++ tailWord_2430470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430470).length < 2 ^ (prefixWord ++ tailWord_2430470).sum := by decide
  have hdescent : baseEnd_2430470 < baseStart_2430470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430476 : List Nat := [2, 2, 1, 2, 5, 2, 2, 1, 2, 2, 2]
def baseStart_2430476 : Nat := 118140960795 + 2430476 * 2 ^ 59
def prefixEnd_2430476 : Nat := 4983230072969 + 3 ^ 40 * 2430476 * 2
def baseEnd_2430476 : Nat := 1248002407217137985172451

theorem tailTrace_2430476 : CollatzResearch.WordTrace tailWord_2430476 prefixEnd_2430476 1248002407217137985172451 := by
  unfold tailWord_2430476
  simp only [CollatzResearch.WordTrace]
  refine ⟨44323371171404009549363641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59097828228538679399151521 44323371171404009549363641)
  ·
    refine ⟨33242528378553007162022731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44323371171404009549363641 33242528378553007162022731)
    ·
      refine ⟨49863792567829510743034097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33242528378553007162022731 49863792567829510743034097)
      ·
        refine ⟨37397844425872133057275573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49863792567829510743034097 37397844425872133057275573)
        ·
          refine ⟨3506047914925512474119585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37397844425872133057275573 3506047914925512474119585)
          ·
            refine ⟨2629535936194134355589689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3506047914925512474119585 2629535936194134355589689)
            ·
              refine ⟨1972151952145600766692267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2629535936194134355589689 1972151952145600766692267)
              ·
                refine ⟨2958227928218401150038401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1972151952145600766692267 2958227928218401150038401)
                ·
                  refine ⟨2218670946163800862528801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2958227928218401150038401 2218670946163800862528801)
                  ·
                    refine ⟨1664003209622850646896601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2218670946163800862528801 1664003209622850646896601)
                    ·
                      refine ⟨1248002407217137985172451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1664003209622850646896601 1248002407217137985172451)
                      ·
                        rfl

theorem cell23_2430476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 2, 2, 2].length) (baseStart_2430476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430476 prefixEnd_2430476 := by exact prefixLift 2430476
  have htrace : WordTrace (prefixWord ++ tailWord_2430476) baseStart_2430476 baseEnd_2430476 := by
    simpa [prefixWord, tailWord_2430476, baseEnd_2430476] using wordTrace_append hprefix tailTrace_2430476
  have hstable : (prefixWord ++ tailWord_2430476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430476).length < 2 ^ (prefixWord ++ tailWord_2430476).sum := by decide
  have hdescent : baseEnd_2430476 < baseStart_2430476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430498 : List Nat := [3, 3, 1, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_2430498 : Nat := 118140960795 + 2430498 * 2 ^ 59
def prefixEnd_2430498 : Nat := 4983230072969 + 3 ^ 40 * 2430498 * 2
def baseEnd_2430498 : Nat := 1248013703791536899097349

theorem tailTrace_2430498 : CollatzResearch.WordTrace tailWord_2430498 prefixEnd_2430498 1248013703791536899097349 := by
  unfold tailWord_2430498
  simp only [CollatzResearch.WordTrace]
  refine ⟨22161886187182079214007037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59098363165818877904018765 22161886187182079214007037)
  ·
    refine ⟨8310707320193279705252639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22161886187182079214007037 8310707320193279705252639)
    ·
      refine ⟨12466060980289919557878959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8310707320193279705252639 12466060980289919557878959)
      ·
        refine ⟨18699091470434879336818439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12466060980289919557878959 18699091470434879336818439)
        ·
          refine ⟨28048637205652319005227659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18699091470434879336818439 28048637205652319005227659)
          ·
            refine ⟨42072955808478478507841489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28048637205652319005227659 42072955808478478507841489)
            ·
              refine ⟨31554716856358858880881117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42072955808478478507841489 31554716856358858880881117)
              ·
                refine ⟨11833018821134572080330419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31554716856358858880881117 11833018821134572080330419)
                ·
                  refine ⟨17749528231701858120495629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11833018821134572080330419 17749528231701858120495629)
                  ·
                    refine ⟨6656073086888196795185861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17749528231701858120495629 6656073086888196795185861)
                    ·
                      refine ⟨1248013703791536899097349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6656073086888196795185861 1248013703791536899097349)
                      ·
                        rfl

theorem cell23_2430498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_2430498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430498 prefixEnd_2430498 := by exact prefixLift 2430498
  have htrace : WordTrace (prefixWord ++ tailWord_2430498) baseStart_2430498 baseEnd_2430498 := by
    simpa [prefixWord, tailWord_2430498, baseEnd_2430498] using wordTrace_append hprefix tailTrace_2430498
  have hstable : (prefixWord ++ tailWord_2430498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430498).length < 2 ^ (prefixWord ++ tailWord_2430498).sum := by decide
  have hdescent : baseEnd_2430498 < baseStart_2430498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430538 : List Nat := [3, 1, 2, 1, 1, 3, 1, 5, 6]
def baseStart_2430538 : Nat := 118140960795 + 2430538 * 2 ^ 59
def prefixEnd_2430538 : Nat := 4983230072969 + 3 ^ 40 * 2430538 * 2
def baseEnd_2430538 : Nat := 138670471446412971399685

theorem tailTrace_2430538 : CollatzResearch.WordTrace tailWord_2430538 prefixEnd_2430538 138670471446412971399685 := by
  unfold tailWord_2430538
  simp only [CollatzResearch.WordTrace]
  refine ⟨22162250917145850921871067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59099335779055602458322845 22162250917145850921871067)
  ·
    refine ⟨33243376375718776382806601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22162250917145850921871067 33243376375718776382806601)
    ·
      refine ⟨24932532281789082287104951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33243376375718776382806601 24932532281789082287104951)
      ·
        refine ⟨37398798422683623430657427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24932532281789082287104951 37398798422683623430657427)
        ·
          refine ⟨56098197634025435145986141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37398798422683623430657427 56098197634025435145986141)
          ·
            refine ⟨21036824112759538179744803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56098197634025435145986141 21036824112759538179744803)
            ·
              refine ⟨31555236169139307269617205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21036824112759538179744803 31555236169139307269617205)
              ·
                refine ⟨2958303390856810056526613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31555236169139307269617205 2958303390856810056526613)
                ·
                  refine ⟨138670471446412971399685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2958303390856810056526613 138670471446412971399685)
                  ·
                    rfl

theorem cell23_2430538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 6].length) (baseStart_2430538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430538 prefixEnd_2430538 := by exact prefixLift 2430538
  have htrace : WordTrace (prefixWord ++ tailWord_2430538) baseStart_2430538 baseEnd_2430538 := by
    simpa [prefixWord, tailWord_2430538, baseEnd_2430538] using wordTrace_append hprefix tailTrace_2430538
  have hstable : (prefixWord ++ tailWord_2430538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430538).length < 2 ^ (prefixWord ++ tailWord_2430538).sum := by decide
  have hdescent : baseEnd_2430538 < baseStart_2430538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430575 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 4, 3, 2]
def baseStart_2430575 : Nat := 118140960795 + 2430575 * 2 ^ 59
def prefixEnd_2430575 : Nat := 4983230072969 + 3 ^ 40 * 2430575 * 2
def baseEnd_2430575 : Nat := 1248053241801933097834495

theorem tailTrace_2430575 : CollatzResearch.WordTrace tailWord_2430575 prefixEnd_2430575 1248053241801933097834495 := by
  unfold tailWord_2430575
  simp only [CollatzResearch.WordTrace]
  refine ⟨88650353169449359006581179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59100235446299572671054119 88650353169449359006581179)
  ·
    refine ⟨132975529754174038509871769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88650353169449359006581179 132975529754174038509871769)
    ·
      refine ⟨99731647315630528882403827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132975529754174038509871769 99731647315630528882403827)
      ·
        refine ⟨149597470973445793323605741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99731647315630528882403827 149597470973445793323605741)
        ·
          refine ⟨56099051615042172496352153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149597470973445793323605741 56099051615042172496352153)
          ·
            refine ⟨42074288711281629372264115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56099051615042172496352153 42074288711281629372264115)
            ·
              refine ⟨63111433066922444058396173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42074288711281629372264115 63111433066922444058396173)
              ·
                refine ⟨23666787400095916521898565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63111433066922444058396173 23666787400095916521898565)
                ·
                  refine ⟨4437522637517984347855981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23666787400095916521898565 4437522637517984347855981)
                  ·
                    refine ⟨1664070989069244130445993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4437522637517984347855981 1664070989069244130445993)
                    ·
                      refine ⟨1248053241801933097834495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1664070989069244130445993 1248053241801933097834495)
                      ·
                        rfl

theorem cell23_2430575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 3, 2].length) (baseStart_2430575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430575 prefixEnd_2430575 := by exact prefixLift 2430575
  have htrace : WordTrace (prefixWord ++ tailWord_2430575) baseStart_2430575 baseEnd_2430575 := by
    simpa [prefixWord, tailWord_2430575, baseEnd_2430575] using wordTrace_append hprefix tailTrace_2430575
  have hstable : (prefixWord ++ tailWord_2430575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430575).length < 2 ^ (prefixWord ++ tailWord_2430575).sum := by decide
  have hdescent : baseEnd_2430575 < baseStart_2430575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430602 : List Nat := [3, 1, 2, 3, 2, 2, 2, 2, 1, 5]
def baseStart_2430602 : Nat := 118140960795 + 2430602 * 2 ^ 59
def prefixEnd_2430602 : Nat := 4983230072969 + 3 ^ 40 * 2430602 * 2
def baseEnd_2430602 : Nat := 416022368593201497398957

theorem tailTrace_2430602 : CollatzResearch.WordTrace tailWord_2430602 prefixEnd_2430602 416022368593201497398957 := by
  unfold tailWord_2430602
  simp only [CollatzResearch.WordTrace]
  refine ⟨22162834485087885654453515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59100891960234361745209373 22162834485087885654453515)
  ·
    refine ⟨33244251727631828481680273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22162834485087885654453515 33244251727631828481680273)
    ·
      refine ⟨24933188795723871361260205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33244251727631828481680273 24933188795723871361260205)
      ·
        refine ⟨9349945798396451760472577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24933188795723871361260205 9349945798396451760472577)
        ·
          refine ⟨7012459348797338820354433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9349945798396451760472577 7012459348797338820354433)
          ·
            refine ⟨5259344511598004115265825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7012459348797338820354433 5259344511598004115265825)
            ·
              refine ⟨3944508383698503086449369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5259344511598004115265825 3944508383698503086449369)
              ·
                refine ⟨2958381287773877314837027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3944508383698503086449369 2958381287773877314837027)
                ·
                  refine ⟨4437571931660815972255541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2958381287773877314837027 4437571931660815972255541)
                  ·
                    refine ⟨416022368593201497398957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4437571931660815972255541 416022368593201497398957)
                    ·
                      rfl

theorem cell23_2430602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_2430602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430602 prefixEnd_2430602 := by exact prefixLift 2430602
  have htrace : WordTrace (prefixWord ++ tailWord_2430602) baseStart_2430602 baseEnd_2430602 := by
    simpa [prefixWord, tailWord_2430602, baseEnd_2430602] using wordTrace_append hprefix tailTrace_2430602
  have hstable : (prefixWord ++ tailWord_2430602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430602).length < 2 ^ (prefixWord ++ tailWord_2430602).sum := by decide
  have hdescent : baseEnd_2430602 < baseStart_2430602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430608 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 3]
def baseStart_2430608 : Nat := 118140960795 + 2430608 * 2 ^ 59
def prefixEnd_2430608 : Nat := 4983230072969 + 3 ^ 40 * 2430608 * 2
def baseEnd_2430608 : Nat := 1248070186663531468721843

theorem tailTrace_2430608 : CollatzResearch.WordTrace tailWord_2430608 prefixEnd_2430608 1248070186663531468721843 := by
  unfold tailWord_2430608
  simp only [CollatzResearch.WordTrace]
  refine ⟨44325778389164902821266239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59101037852219870428354985 44325778389164902821266239)
  ·
    refine ⟨66488667583747354231899359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44325778389164902821266239 66488667583747354231899359)
    ·
      refine ⟨99733001375621031347849039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66488667583747354231899359 99733001375621031347849039)
      ·
        refine ⟨149599502063431547021773559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99733001375621031347849039 149599502063431547021773559)
        ·
          refine ⟨224399253095147320532660339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149599502063431547021773559 224399253095147320532660339)
          ·
            refine ⟨336598879642720980798990509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224399253095147320532660339 336598879642720980798990509)
            ·
              refine ⟨126224579866020367799621441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 336598879642720980798990509 126224579866020367799621441)
              ·
                refine ⟨94668434899515275849716081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126224579866020367799621441 94668434899515275849716081)
                ·
                  refine ⟨71001326174636456887287061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94668434899515275849716081 71001326174636456887287061)
                  ·
                    refine ⟨3328187164436083916591581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71001326174636456887287061 3328187164436083916591581)
                    ·
                      refine ⟨1248070186663531468721843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3328187164436083916591581 1248070186663531468721843)
                      ·
                        rfl

theorem cell23_2430608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 3].length) (baseStart_2430608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430608 prefixEnd_2430608 := by exact prefixLift 2430608
  have htrace : WordTrace (prefixWord ++ tailWord_2430608) baseStart_2430608 baseEnd_2430608 := by
    simpa [prefixWord, tailWord_2430608, baseEnd_2430608] using wordTrace_append hprefix tailTrace_2430608
  have hstable : (prefixWord ++ tailWord_2430608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430608).length < 2 ^ (prefixWord ++ tailWord_2430608).sum := by decide
  have hdescent : baseEnd_2430608 < baseStart_2430608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430615 : List Nat := [1, 1, 3, 3, 2, 2, 1, 2, 4, 4]
def baseStart_2430615 : Nat := 118140960795 + 2430615 * 2 ^ 59
def prefixEnd_2430615 : Nat := 4983230072969 + 3 ^ 40 * 2430615 * 2
def baseEnd_2430615 : Nat := 416024593676037647111437

theorem tailTrace_2430615 : CollatzResearch.WordTrace tailWord_2430615 prefixEnd_2430615 416024593676037647111437 := by
  unfold tailWord_2430615
  simp only [CollatzResearch.WordTrace]
  refine ⟨88651812089304445838037299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59101208059536297225358199 88651812089304445838037299)
  ·
    refine ⟨132977718133956668757055949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88651812089304445838037299 132977718133956668757055949)
    ·
      refine ⟨49866644300233750783895981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132977718133956668757055949 49866644300233750783895981)
      ·
        refine ⟨18699991612587656543960993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49866644300233750783895981 18699991612587656543960993)
        ·
          refine ⟨14024993709440742407970745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18699991612587656543960993 14024993709440742407970745)
          ·
            refine ⟨10518745282080556805978059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14024993709440742407970745 10518745282080556805978059)
            ·
              refine ⟨15778117923120835208967089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10518745282080556805978059 15778117923120835208967089)
              ·
                refine ⟨11833588442340626406725317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15778117923120835208967089 11833588442340626406725317)
                ·
                  refine ⟨2218797832938867451260997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11833588442340626406725317 2218797832938867451260997)
                  ·
                    refine ⟨416024593676037647111437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2218797832938867451260997 416024593676037647111437)
                    ·
                      rfl

theorem cell23_2430615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4, 4].length) (baseStart_2430615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430615 prefixEnd_2430615 := by exact prefixLift 2430615
  have htrace : WordTrace (prefixWord ++ tailWord_2430615) baseStart_2430615 baseEnd_2430615 := by
    simpa [prefixWord, tailWord_2430615, baseEnd_2430615] using wordTrace_append hprefix tailTrace_2430615
  have hstable : (prefixWord ++ tailWord_2430615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430615).length < 2 ^ (prefixWord ++ tailWord_2430615).sum := by decide
  have hdescent : baseEnd_2430615 < baseStart_2430615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430616 : List Nat := [2, 1, 2, 4, 1, 4, 1, 3, 1, 1, 3]
def baseStart_2430616 : Nat := 118140960795 + 2430616 * 2 ^ 59
def prefixEnd_2430616 : Nat := 4983230072969 + 3 ^ 40 * 2430616 * 2
def baseEnd_2430616 : Nat := 1248074294508767437421807

theorem tailTrace_2430616 : CollatzResearch.WordTrace tailWord_2430616 prefixEnd_2430616 1248074294508767437421807 := by
  unfold tailWord_2430616
  simp only [CollatzResearch.WordTrace]
  refine ⟨44325924281150411504411851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59101232374867215339215801 44325924281150411504411851)
  ·
    refine ⟨66488886421725617256617777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44325924281150411504411851 66488886421725617256617777)
    ·
      refine ⟨49866664816294212942463333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66488886421725617256617777 49866664816294212942463333)
      ·
        refine ⟨9349999653055164926711875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49866664816294212942463333 9349999653055164926711875)
        ·
          refine ⟨14024999479582747390067813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9349999653055164926711875 14024999479582747390067813)
          ·
            refine ⟨2629687402421765135637715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14024999479582747390067813 2629687402421765135637715)
            ·
              refine ⟨3944531103632647703456573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2629687402421765135637715 3944531103632647703456573)
              ·
                refine ⟨1479199163862242888796215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3944531103632647703456573 1479199163862242888796215)
                ·
                  refine ⟨2218798745793364333194323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1479199163862242888796215 2218798745793364333194323)
                  ·
                    refine ⟨3328198118690046499791485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2218798745793364333194323 3328198118690046499791485)
                    ·
                      refine ⟨1248074294508767437421807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3328198118690046499791485 1248074294508767437421807)
                      ·
                        rfl

theorem cell23_2430616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_2430616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430616 prefixEnd_2430616 := by exact prefixLift 2430616
  have htrace : WordTrace (prefixWord ++ tailWord_2430616) baseStart_2430616 baseEnd_2430616 := by
    simpa [prefixWord, tailWord_2430616, baseEnd_2430616] using wordTrace_append hprefix tailTrace_2430616
  have hstable : (prefixWord ++ tailWord_2430616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430616).length < 2 ^ (prefixWord ++ tailWord_2430616).sum := by decide
  have hdescent : baseEnd_2430616 < baseStart_2430616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430625 : List Nat := [1, 2, 3, 3, 2, 1, 1, 3, 1, 1, 5]
def baseStart_2430625 : Nat := 118140960795 + 2430625 * 2 ^ 59
def prefixEnd_2430625 : Nat := 4983230072969 + 3 ^ 40 * 2430625 * 2
def baseEnd_2430625 : Nat := 1248078915834657902209265

theorem tailTrace_2430625 : CollatzResearch.WordTrace tailWord_2430625 prefixEnd_2430625 1248078915834657902209265 := by
  unfold tailWord_2430625
  simp only [CollatzResearch.WordTrace]
  refine ⟨88652176819268217545901329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59101451212845478363934219 88652176819268217545901329)
  ·
    refine ⟨66489132614451163159425997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88652176819268217545901329 66489132614451163159425997)
    ·
      refine ⟨24933424730419186184784749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66489132614451163159425997 24933424730419186184784749)
      ·
        refine ⟨9350034273907194819294281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24933424730419186184784749 9350034273907194819294281)
        ·
          refine ⟨7012525705430396114470711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9350034273907194819294281 7012525705430396114470711)
          ·
            refine ⟨10518788558145594171706067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7012525705430396114470711 10518788558145594171706067)
            ·
              refine ⟨15778182837218391257559101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10518788558145594171706067 15778182837218391257559101)
              ·
                refine ⟨5916818563956896721584663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15778182837218391257559101 5916818563956896721584663)
                ·
                  refine ⟨8875227845935345082376995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5916818563956896721584663 8875227845935345082376995)
                  ·
                    refine ⟨13312841768903017623565493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8875227845935345082376995 13312841768903017623565493)
                    ·
                      refine ⟨1248078915834657902209265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13312841768903017623565493 1248078915834657902209265)
                      ·
                        rfl

theorem cell23_2430625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_2430625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430625 prefixEnd_2430625 := by exact prefixLift 2430625
  have htrace : WordTrace (prefixWord ++ tailWord_2430625) baseStart_2430625 baseEnd_2430625 := by
    simpa [prefixWord, tailWord_2430625, baseEnd_2430625] using wordTrace_append hprefix tailTrace_2430625
  have hstable : (prefixWord ++ tailWord_2430625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430625).length < 2 ^ (prefixWord ++ tailWord_2430625).sum := by decide
  have hdescent : baseEnd_2430625 < baseStart_2430625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430626 : List Nat := [3, 3, 1, 4, 1, 1, 1, 2, 2, 3, 2]
def baseStart_2430626 : Nat := 118140960795 + 2430626 * 2 ^ 59
def prefixEnd_2430626 : Nat := 4983230072969 + 3 ^ 40 * 2430626 * 2
def baseEnd_2430626 : Nat := 1248079429315312398296761

theorem tailTrace_2430626 : CollatzResearch.WordTrace tailWord_2430626 prefixEnd_2430626 1248079429315312398296761 := by
  unfold tailWord_2430626
  simp only [CollatzResearch.WordTrace]
  refine ⟨22163053323066148679171933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59101475528176396477791821 22163053323066148679171933)
  ·
    refine ⟨8311144996149805754689475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22163053323066148679171933 8311144996149805754689475)
    ·
      refine ⟨12466717494224708632034213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8311144996149805754689475 12466717494224708632034213)
      ·
        refine ⟨2337509530167132868506415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12466717494224708632034213 2337509530167132868506415)
        ·
          refine ⟨3506264295250699302759623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2337509530167132868506415 3506264295250699302759623)
          ·
            refine ⟨5259396442876048954139435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3506264295250699302759623 5259396442876048954139435)
            ·
              refine ⟨7889094664314073431209153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5259396442876048954139435 7889094664314073431209153)
              ·
                refine ⟨5916820998235555073406865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7889094664314073431209153 5916820998235555073406865)
                ·
                  refine ⟨4437615748676666305055149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5916820998235555073406865 4437615748676666305055149)
                  ·
                    refine ⟨1664105905753749864395681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4437615748676666305055149 1664105905753749864395681)
                    ·
                      refine ⟨1248079429315312398296761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1664105905753749864395681 1248079429315312398296761)
                      ·
                        rfl

theorem cell23_2430626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_2430626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430626 prefixEnd_2430626 := by exact prefixLift 2430626
  have htrace : WordTrace (prefixWord ++ tailWord_2430626) baseStart_2430626 baseEnd_2430626 := by
    simpa [prefixWord, tailWord_2430626, baseEnd_2430626] using wordTrace_append hprefix tailTrace_2430626
  have hstable : (prefixWord ++ tailWord_2430626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430626).length < 2 ^ (prefixWord ++ tailWord_2430626).sum := by decide
  have hdescent : baseEnd_2430626 < baseStart_2430626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430628 : List Nat := [2, 3, 1, 2, 2, 2, 11]
def baseStart_2430628 : Nat := 118140960795 + 2430628 * 2 ^ 59
def prefixEnd_2430628 : Nat := 4983230072969 + 3 ^ 40 * 2430628 * 2
def baseEnd_2430628 : Nat := 15408400694773103586071

theorem tailTrace_2430628 : CollatzResearch.WordTrace tailWord_2430628 prefixEnd_2430628 15408400694773103586071 := by
  unfold tailWord_2430628
  simp only [CollatzResearch.WordTrace]
  refine ⟨44326143119128674529130269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59101524158838232705507025 44326143119128674529130269)
  ·
    refine ⟨16622303669673252948423851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44326143119128674529130269 16622303669673252948423851)
    ·
      refine ⟨24933455504509879422635777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16622303669673252948423851 24933455504509879422635777)
      ·
        refine ⟨18700091628382409566976833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24933455504509879422635777 18700091628382409566976833)
        ·
          refine ⟨14025068721286807175232625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18700091628382409566976833 14025068721286807175232625)
          ·
            refine ⟨10518801540965105381424469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14025068721286807175232625 10518801540965105381424469)
            ·
              refine ⟨15408400694773103586071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 10518801540965105381424469 15408400694773103586071)
              ·
                rfl

theorem cell23_2430628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 11].length) (baseStart_2430628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430628 prefixEnd_2430628 := by exact prefixLift 2430628
  have htrace : WordTrace (prefixWord ++ tailWord_2430628) baseStart_2430628 baseEnd_2430628 := by
    simpa [prefixWord, tailWord_2430628, baseEnd_2430628] using wordTrace_append hprefix tailTrace_2430628
  have hstable : (prefixWord ++ tailWord_2430628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430628).length < 2 ^ (prefixWord ++ tailWord_2430628).sum := by decide
  have hdescent : baseEnd_2430628 < baseStart_2430628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430655 : List Nat := [1, 1, 2, 2, 2, 3, 2, 3, 1, 3, 3]
def baseStart_2430655 : Nat := 118140960795 + 2430655 * 2 ^ 59
def prefixEnd_2430655 : Nat := 4983230072969 + 3 ^ 40 * 2430655 * 2
def baseEnd_2430655 : Nat := 1248094320254292784834127

theorem tailTrace_2430655 : CollatzResearch.WordTrace tailWord_2430655 prefixEnd_2430655 1248094320254292784834127 := by
  unfold tailWord_2430655
  simp only [CollatzResearch.WordTrace]
  refine ⟨88653271009159532669493419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59102180672773021779662279 88653271009159532669493419)
  ·
    refine ⟨132979906513739299004240129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88653271009159532669493419 132979906513739299004240129)
    ·
      refine ⟨99734929885304474253180097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132979906513739299004240129 99734929885304474253180097)
      ·
        refine ⟨74801197413978355689885073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99734929885304474253180097 74801197413978355689885073)
        ·
          refine ⟨56100898060483766767413805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74801197413978355689885073 56100898060483766767413805)
          ·
            refine ⟨21037836772681412537780177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56100898060483766767413805 21037836772681412537780177)
            ·
              refine ⟨15778377579511059403335133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21037836772681412537780177 15778377579511059403335133)
              ·
                refine ⟨5916891592316647276250675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15778377579511059403335133 5916891592316647276250675)
                ·
                  refine ⟨8875337388474970914376013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5916891592316647276250675 8875337388474970914376013)
                  ·
                    refine ⟨3328251520678114092891005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8875337388474970914376013 3328251520678114092891005)
                    ·
                      refine ⟨1248094320254292784834127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3328251520678114092891005 1248094320254292784834127)
                      ·
                        rfl

theorem cell23_2430655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3, 3].length) (baseStart_2430655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430655 prefixEnd_2430655 := by exact prefixLift 2430655
  have htrace : WordTrace (prefixWord ++ tailWord_2430655) baseStart_2430655 baseEnd_2430655 := by
    simpa [prefixWord, tailWord_2430655, baseEnd_2430655] using wordTrace_append hprefix tailTrace_2430655
  have hstable : (prefixWord ++ tailWord_2430655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430655).length < 2 ^ (prefixWord ++ tailWord_2430655).sum := by decide
  have hdescent : baseEnd_2430655 < baseStart_2430655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430669 : List Nat := [1, 6, 2, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_2430669 : Nat := 118140960795 + 2430669 * 2 ^ 59
def prefixEnd_2430669 : Nat := 4983230072969 + 3 ^ 40 * 2430669 * 2
def baseEnd_2430669 : Nat := 1248101508983455730059063

theorem tailTrace_2430669 : CollatzResearch.WordTrace tailWord_2430669 prefixEnd_2430669 1248101508983455730059063 := by
  unfold tailWord_2430669
  simp only [CollatzResearch.WordTrace]
  refine ⟨88653781631108813060503061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59102521087405875373668707 88653781631108813060503061)
  ·
    refine ⟨4155646013958225612211081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 88653781631108813060503061 4155646013958225612211081)
    ·
      refine ⟨3116734510468669209158311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4155646013958225612211081 3116734510468669209158311)
      ·
        refine ⟨4675101765703003813737467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3116734510468669209158311 4675101765703003813737467)
        ·
          refine ⟨7012652648554505720606201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4675101765703003813737467 7012652648554505720606201)
          ·
            refine ⟨5259489486415879290454651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7012652648554505720606201 5259489486415879290454651)
            ·
              refine ⟨7889234229623818935681977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5259489486415879290454651 7889234229623818935681977)
              ·
                refine ⟨5916925672217864201761483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7889234229623818935681977 5916925672217864201761483)
                ·
                  refine ⟨8875388508326796302642225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5916925672217864201761483 8875388508326796302642225)
                  ·
                    refine ⟨6656541381245097226981669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8875388508326796302642225 6656541381245097226981669)
                    ·
                      refine ⟨1248101508983455730059063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6656541381245097226981669 1248101508983455730059063)
                      ·
                        rfl

theorem cell23_2430669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_2430669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430669 prefixEnd_2430669 := by exact prefixLift 2430669
  have htrace : WordTrace (prefixWord ++ tailWord_2430669) baseStart_2430669 baseEnd_2430669 := by
    simpa [prefixWord, tailWord_2430669, baseEnd_2430669] using wordTrace_append hprefix tailTrace_2430669
  have hstable : (prefixWord ++ tailWord_2430669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430669).length < 2 ^ (prefixWord ++ tailWord_2430669).sum := by decide
  have hdescent : baseEnd_2430669 < baseStart_2430669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430676 : List Nat := [2, 4, 1, 3, 1, 2, 3, 1, 1, 2, 3]
def baseStart_2430676 : Nat := 118140960795 + 2430676 * 2 ^ 59
def prefixEnd_2430676 : Nat := 4983230072969 + 3 ^ 40 * 2430676 * 2
def baseEnd_2430676 : Nat := 1248105103348037202671531

theorem tailTrace_2430676 : CollatzResearch.WordTrace tailWord_2430676 prefixEnd_2430676 1248105103348037202671531 := by
  unfold tailWord_2430676
  simp only [CollatzResearch.WordTrace]
  refine ⟨44327018471041726628003941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59102691294722302170671921 44327018471041726628003941)
  ·
    refine ⟨8311315963320323742750739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44327018471041726628003941 8311315963320323742750739)
    ·
      refine ⟨12466973944980485614126109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8311315963320323742750739 12466973944980485614126109)
      ·
        refine ⟨4675115229367682105297291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12466973944980485614126109 4675115229367682105297291)
        ·
          refine ⟨7012672844051523157945937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4675115229367682105297291 7012672844051523157945937)
          ·
            refine ⟨5259504633038642368459453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7012672844051523157945937 5259504633038642368459453)
            ·
              refine ⟨1972314237389490888172295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5259504633038642368459453 1972314237389490888172295)
              ·
                refine ⟨2958471356084236332258443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1972314237389490888172295 2958471356084236332258443)
                ·
                  refine ⟨4437707034126354498387665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2958471356084236332258443 4437707034126354498387665)
                  ·
                    refine ⟨3328280275594765873790749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4437707034126354498387665 3328280275594765873790749)
                    ·
                      refine ⟨1248105103348037202671531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3328280275594765873790749 1248105103348037202671531)
                      ·
                        rfl

theorem cell23_2430676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_2430676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430676 prefixEnd_2430676 := by exact prefixLift 2430676
  have htrace : WordTrace (prefixWord ++ tailWord_2430676) baseStart_2430676 baseEnd_2430676 := by
    simpa [prefixWord, tailWord_2430676, baseEnd_2430676] using wordTrace_append hprefix tailTrace_2430676
  have hstable : (prefixWord ++ tailWord_2430676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430676).length < 2 ^ (prefixWord ++ tailWord_2430676).sum := by decide
  have hdescent : baseEnd_2430676 < baseStart_2430676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430705 : List Nat := [1, 2, 2, 2, 2, 4, 1, 1, 2, 6]
def baseStart_2430705 : Nat := 118140960795 + 2430705 * 2 ^ 59
def prefixEnd_2430705 : Nat := 4983230072969 + 3 ^ 40 * 2430705 * 2
def baseEnd_2430705 : Nat := 416039998095672529736299

theorem tailTrace_2430705 : CollatzResearch.WordTrace tailWord_2430705 prefixEnd_2430705 416039998095672529736299 := by
  unfold tailWord_2430705
  simp only [CollatzResearch.WordTrace]
  refine ⟨88655094658978391208813569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59103396439318927472542379 88655094658978391208813569)
  ·
    refine ⟨66491320994233793406610177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88655094658978391208813569 66491320994233793406610177)
    ·
      refine ⟨49868490745675345054957633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66491320994233793406610177 49868490745675345054957633)
      ·
        refine ⟨37401368059256508791218225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49868490745675345054957633 37401368059256508791218225)
        ·
          refine ⟨28051026044442381593413669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37401368059256508791218225 28051026044442381593413669)
          ·
            refine ⟨5259567383332946548765063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28051026044442381593413669 5259567383332946548765063)
            ·
              refine ⟨7889351074999419823147595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5259567383332946548765063 7889351074999419823147595)
              ·
                refine ⟨11834026612499129734721393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7889351074999419823147595 11834026612499129734721393)
                ·
                  refine ⟨8875519959374347301041045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11834026612499129734721393 8875519959374347301041045)
                  ·
                    refine ⟨416039998095672529736299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8875519959374347301041045 416039998095672529736299)
                    ·
                      rfl

theorem cell23_2430705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 6].length) (baseStart_2430705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430705 prefixEnd_2430705 := by exact prefixLift 2430705
  have htrace : WordTrace (prefixWord ++ tailWord_2430705) baseStart_2430705 baseEnd_2430705 := by
    simpa [prefixWord, tailWord_2430705, baseEnd_2430705] using wordTrace_append hprefix tailTrace_2430705
  have hstable : (prefixWord ++ tailWord_2430705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430705).length < 2 ^ (prefixWord ++ tailWord_2430705).sum := by decide
  have hdescent : baseEnd_2430705 < baseStart_2430705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430746 : List Nat := [3, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2]
def baseStart_2430746 : Nat := 118140960795 + 2430746 * 2 ^ 59
def prefixEnd_2430746 : Nat := 4983230072969 + 3 ^ 40 * 2430746 * 2
def baseEnd_2430746 : Nat := 1248141046993851928796209

theorem tailTrace_2430746 : CollatzResearch.WordTrace tailWord_2430746 prefixEnd_2430746 1248141046993851928796209 := by
  unfold tailWord_2430746
  simp only [CollatzResearch.WordTrace]
  refine ⟨22164147512957463802764023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59104393367886570140704061 22164147512957463802764023)
  ·
    refine ⟨33246221269436195704146035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22164147512957463802764023 33246221269436195704146035)
    ·
      refine ⟨49869331904154293556219053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33246221269436195704146035 49869331904154293556219053)
      ·
        refine ⟨18700999464057860083582145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49869331904154293556219053 18700999464057860083582145)
        ·
          refine ⟨14025749598043395062686609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18700999464057860083582145 14025749598043395062686609)
          ·
            refine ⟨10519312198532546297014957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14025749598043395062686609 10519312198532546297014957)
            ·
              refine ⟨3944742074449704861380609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10519312198532546297014957 3944742074449704861380609)
              ·
                refine ⟨2958556555837278646035457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3944742074449704861380609 2958556555837278646035457)
                ·
                  refine ⟨2218917416877958984526593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2958556555837278646035457 2218917416877958984526593)
                  ·
                    refine ⟨1664188062658469238394945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2218917416877958984526593 1664188062658469238394945)
                    ·
                      refine ⟨1248141046993851928796209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1664188062658469238394945 1248141046993851928796209)
                      ·
                        rfl

theorem cell23_2430746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_2430746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430746 prefixEnd_2430746 := by exact prefixLift 2430746
  have htrace : WordTrace (prefixWord ++ tailWord_2430746) baseStart_2430746 baseEnd_2430746 := by
    simpa [prefixWord, tailWord_2430746, baseEnd_2430746] using wordTrace_append hprefix tailTrace_2430746
  have hstable : (prefixWord ++ tailWord_2430746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430746).length < 2 ^ (prefixWord ++ tailWord_2430746).sum := by decide
  have hdescent : baseEnd_2430746 < baseStart_2430746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430752 : List Nat := [2, 1, 1, 5, 1, 1, 1, 6, 5]
def baseStart_2430752 : Nat := 118140960795 + 2430752 * 2 ^ 59
def prefixEnd_2430752 : Nat := 4983230072969 + 3 ^ 40 * 2430752 * 2
def baseEnd_2430752 : Nat := 138682680875308767257909

theorem tailTrace_2430752 : CollatzResearch.WordTrace tailWord_2430752 prefixEnd_2430752 138682680875308767257909 := by
  unfold tailWord_2430752
  simp only [CollatzResearch.WordTrace]
  refine ⟨44328404444904059117887255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59104539259872078823849673 44328404444904059117887255)
  ·
    refine ⟨66492606667356088676830883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44328404444904059117887255 66492606667356088676830883)
    ·
      refine ⟨99738910001034133015246325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66492606667356088676830883 99738910001034133015246325)
      ·
        refine ⟨9350522812596949970179343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99738910001034133015246325 9350522812596949970179343)
        ·
          refine ⟨14025784218895424955269015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9350522812596949970179343 14025784218895424955269015)
          ·
            refine ⟨21038676328343137432903523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14025784218895424955269015 21038676328343137432903523)
            ·
              refine ⟨31558014492514706149355285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21038676328343137432903523 31558014492514706149355285)
              ·
                refine ⟨1479281929336626850751029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31558014492514706149355285 1479281929336626850751029)
                ·
                  refine ⟨138682680875308767257909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1479281929336626850751029 138682680875308767257909)
                  ·
                    rfl

theorem cell23_2430752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6, 5].length) (baseStart_2430752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430752 prefixEnd_2430752 := by exact prefixLift 2430752
  have htrace : WordTrace (prefixWord ++ tailWord_2430752) baseStart_2430752 baseEnd_2430752 := by
    simpa [prefixWord, tailWord_2430752, baseEnd_2430752] using wordTrace_append hprefix tailTrace_2430752
  have hstable : (prefixWord ++ tailWord_2430752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430752).length < 2 ^ (prefixWord ++ tailWord_2430752).sum := by decide
  have hdescent : baseEnd_2430752 < baseStart_2430752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430782 : List Nat := [4, 2, 1, 2, 2, 1, 2, 1, 1, 7]
def baseStart_2430782 : Nat := 118140960795 + 2430782 * 2 ^ 59
def prefixEnd_2430782 : Nat := 4983230072969 + 3 ^ 40 * 2430782 * 2
def baseEnd_2430782 : Nat := 416053177432471262648681

theorem tailTrace_2430782 : CollatzResearch.WordTrace tailWord_2430782 prefixEnd_2430782 416053177432471262648681 := by
  unfold tailWord_2430782
  simp only [CollatzResearch.WordTrace]
  refine ⟨11082237884962429169920825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59105268719799622239577733 11082237884962429169920825)
  ·
    refine ⟨8311678413721821877440619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11082237884962429169920825 8311678413721821877440619)
    ·
      refine ⟨12467517620582732816160929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8311678413721821877440619 12467517620582732816160929)
      ·
        refine ⟨9350638215437049612120697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12467517620582732816160929 9350638215437049612120697)
        ·
          refine ⟨7012978661577787209090523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9350638215437049612120697 7012978661577787209090523)
          ·
            refine ⟨10519467992366680813635785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7012978661577787209090523 10519467992366680813635785)
            ·
              refine ⟨7889600994275010610226839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10519467992366680813635785 7889600994275010610226839)
              ·
                refine ⟨11834401491412515915340259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7889600994275010610226839 11834401491412515915340259)
                ·
                  refine ⟨17751602237118773873010389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11834401491412515915340259 17751602237118773873010389)
                  ·
                    refine ⟨416053177432471262648681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17751602237118773873010389 416053177432471262648681)
                    ·
                      rfl

theorem cell23_2430782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_2430782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430782 prefixEnd_2430782 := by exact prefixLift 2430782
  have htrace : WordTrace (prefixWord ++ tailWord_2430782) baseStart_2430782 baseEnd_2430782 := by
    simpa [prefixWord, tailWord_2430782, baseEnd_2430782] using wordTrace_append hprefix tailTrace_2430782
  have hstable : (prefixWord ++ tailWord_2430782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430782).length < 2 ^ (prefixWord ++ tailWord_2430782).sum := by decide
  have hdescent : baseEnd_2430782 < baseStart_2430782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430802 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4]
def baseStart_2430802 : Nat := 118140960795 + 2430802 * 2 ^ 59
def prefixEnd_2430802 : Nat := 4983230072969 + 3 ^ 40 * 2430802 * 2
def baseEnd_2430802 : Nat := 1248169801910503709695951

theorem tailTrace_2430802 : CollatzResearch.WordTrace tailWord_2430802 prefixEnd_2430802 1248169801910503709695951 := by
  unfold tailWord_2430802
  simp only [CollatzResearch.WordTrace]
  refine ⟨22164658134906744193773665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59105755026417984516729773 22164658134906744193773665)
  ·
    refine ⟨16623493601180058145330249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22164658134906744193773665 16623493601180058145330249)
    ·
      refine ⟨12467620200885043608997687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16623493601180058145330249 12467620200885043608997687)
      ·
        refine ⟨18701430301327565413496531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12467620200885043608997687 18701430301327565413496531)
        ·
          refine ⟨28052145451991348120244797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18701430301327565413496531 28052145451991348120244797)
          ·
            refine ⟨10519554544496755545091799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28052145451991348120244797 10519554544496755545091799)
            ·
              refine ⟨15779331816745133317637699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10519554544496755545091799 15779331816745133317637699)
              ·
                refine ⟨23668997725117699976456549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15779331816745133317637699 23668997725117699976456549)
                ·
                  refine ⟨4437937073459568745585603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23668997725117699976456549 4437937073459568745585603)
                  ·
                    refine ⟨6656905610189353118378405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4437937073459568745585603 6656905610189353118378405)
                    ·
                      refine ⟨1248169801910503709695951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6656905610189353118378405 1248169801910503709695951)
                      ·
                        rfl

theorem cell23_2430802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_2430802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430802 prefixEnd_2430802 := by exact prefixLift 2430802
  have htrace : WordTrace (prefixWord ++ tailWord_2430802) baseStart_2430802 baseEnd_2430802 := by
    simpa [prefixWord, tailWord_2430802, baseEnd_2430802] using wordTrace_append hprefix tailTrace_2430802
  have hstable : (prefixWord ++ tailWord_2430802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430802).length < 2 ^ (prefixWord ++ tailWord_2430802).sum := by decide
  have hdescent : baseEnd_2430802 < baseStart_2430802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430845 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 1, 1, 8]
def baseStart_2430845 : Nat := 118140960795 + 2430845 * 2 ^ 59
def prefixEnd_2430845 : Nat := 4983230072969 + 3 ^ 40 * 2430845 * 2
def baseEnd_2430845 : Nat := 1248191881578647041458253

theorem tailTrace_2430845 : CollatzResearch.WordTrace tailWord_2430845 prefixEnd_2430845 1248191881578647041458253 := by
  unfold tailWord_2430845
  simp only [CollatzResearch.WordTrace]
  refine ⟨88660200878471195118909989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59106800585647463412606659 88660200878471195118909989)
  ·
    refine ⟨16623787664713349084795623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88660200878471195118909989 16623787664713349084795623)
    ·
      refine ⟨24935681497070023627193435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16623787664713349084795623 24935681497070023627193435)
      ·
        refine ⟨37403522245605035440790153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24935681497070023627193435 37403522245605035440790153)
        ·
          refine ⟨28052641684203776580592615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37403522245605035440790153 28052641684203776580592615)
          ·
            refine ⟨42078962526305664870888923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28052641684203776580592615 42078962526305664870888923)
            ·
              refine ⟨63118443789458497306333385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42078962526305664870888923 63118443789458497306333385)
              ·
                refine ⟨47338832842093872979750039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63118443789458497306333385 47338832842093872979750039)
                ·
                  refine ⟨71008249263140809469625059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47338832842093872979750039 71008249263140809469625059)
                  ·
                    refine ⟨106512373894711214204437589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71008249263140809469625059 106512373894711214204437589)
                    ·
                      refine ⟨1248191881578647041458253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 106512373894711214204437589 1248191881578647041458253)
                      ·
                        rfl

theorem cell23_2430845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_2430845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430845 prefixEnd_2430845 := by exact prefixLift 2430845
  have htrace : WordTrace (prefixWord ++ tailWord_2430845) baseStart_2430845 baseEnd_2430845 := by
    simpa [prefixWord, tailWord_2430845, baseEnd_2430845] using wordTrace_append hprefix tailTrace_2430845
  have hstable : (prefixWord ++ tailWord_2430845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430845).length < 2 ^ (prefixWord ++ tailWord_2430845).sum := by decide
  have hdescent : baseEnd_2430845 < baseStart_2430845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430869 : List Nat := [1, 3, 2, 1, 1, 3, 2, 3, 3, 1, 3]
def baseStart_2430869 : Nat := 118140960795 + 2430869 * 2 ^ 59
def prefixEnd_2430869 : Nat := 4983230072969 + 3 ^ 40 * 2430869 * 2
def baseEnd_2430869 : Nat := 1248204205114354947558143

theorem tailTrace_2430869 : CollatzResearch.WordTrace tailWord_2430869 prefixEnd_2430869 1248204205114354947558143 := by
  unfold tailWord_2430869
  simp only [CollatzResearch.WordTrace]
  refine ⟨88661076230384247217783661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59107384153589498145189107 88661076230384247217783661)
  ·
    refine ⟨33247903586394092706668873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88661076230384247217783661 33247903586394092706668873)
    ·
      refine ⟨24935927689795569530001655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33247903586394092706668873 24935927689795569530001655)
      ·
        refine ⟨37403891534693354295002483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24935927689795569530001655 37403891534693354295002483)
        ·
          refine ⟨56105837302040031442503725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37403891534693354295002483 56105837302040031442503725)
          ·
            refine ⟨21039688988265011790938897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56105837302040031442503725 21039688988265011790938897)
            ·
              refine ⟨15779766741198758843204173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21039688988265011790938897 15779766741198758843204173)
              ·
                refine ⟨5917412527949534566201565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15779766741198758843204173 5917412527949534566201565)
                ·
                  refine ⟨2219029697981075462325587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5917412527949534566201565 2219029697981075462325587)
                  ·
                    refine ⟨3328544546971613193488381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2219029697981075462325587 3328544546971613193488381)
                    ·
                      refine ⟨1248204205114354947558143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3328544546971613193488381 1248204205114354947558143)
                      ·
                        rfl

theorem cell23_2430869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_2430869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430869 prefixEnd_2430869 := by exact prefixLift 2430869
  have htrace : WordTrace (prefixWord ++ tailWord_2430869) baseStart_2430869 baseEnd_2430869 := by
    simpa [prefixWord, tailWord_2430869, baseEnd_2430869] using wordTrace_append hprefix tailTrace_2430869
  have hstable : (prefixWord ++ tailWord_2430869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430869).length < 2 ^ (prefixWord ++ tailWord_2430869).sum := by decide
  have hdescent : baseEnd_2430869 < baseStart_2430869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430870 : List Nat := [5, 3, 1, 1, 2, 1, 1, 1, 2, 4, 2]
def baseStart_2430870 : Nat := 118140960795 + 2430870 * 2 ^ 59
def prefixEnd_2430870 : Nat := 4983230072969 + 3 ^ 40 * 2430870 * 2
def baseEnd_2430870 : Nat := 1248204718595009443645639

theorem tailTrace_2430870 : CollatzResearch.WordTrace tailWord_2430870 prefixEnd_2430870 1248204718595009443645639 := by
  unfold tailWord_2430870
  simp only [CollatzResearch.WordTrace]
  refine ⟨5541319543961289024285629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59107408468920416259046709 5541319543961289024285629)
  ·
    refine ⟨2077994828985483384107111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5541319543961289024285629 2077994828985483384107111)
    ·
      refine ⟨3116992243478225076160667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2077994828985483384107111 3116992243478225076160667)
      ·
        refine ⟨4675488365217337614241001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3116992243478225076160667 4675488365217337614241001)
        ·
          refine ⟨3506616273913003210680751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4675488365217337614241001 3506616273913003210680751)
          ·
            refine ⟨5259924410869504816021127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3506616273913003210680751 5259924410869504816021127)
            ·
              refine ⟨7889886616304257224031691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5259924410869504816021127 7889886616304257224031691)
              ·
                refine ⟨11834829924456385836047537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7889886616304257224031691 11834829924456385836047537)
                ·
                  refine ⟨8876122443342289377035653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11834829924456385836047537 8876122443342289377035653)
                  ·
                    refine ⟨1664272958126679258194185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8876122443342289377035653 1664272958126679258194185)
                    ·
                      refine ⟨1248204718595009443645639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1664272958126679258194185 1248204718595009443645639)
                      ·
                        rfl

theorem cell23_2430870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_2430870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430870 prefixEnd_2430870 := by exact prefixLift 2430870
  have htrace : WordTrace (prefixWord ++ tailWord_2430870) baseStart_2430870 baseEnd_2430870 := by
    simpa [prefixWord, tailWord_2430870, baseEnd_2430870] using wordTrace_append hprefix tailTrace_2430870
  have hstable : (prefixWord ++ tailWord_2430870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430870).length < 2 ^ (prefixWord ++ tailWord_2430870).sum := by decide
  have hdescent : baseEnd_2430870 < baseStart_2430870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430912 : List Nat := [2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 5]
def baseStart_2430912 : Nat := 118140960795 + 2430912 * 2 ^ 59
def prefixEnd_2430912 : Nat := 4983230072969 + 3 ^ 40 * 2430912 * 2
def baseEnd_2430912 : Nat := 1248226284782498279320445

theorem tailTrace_2430912 : CollatzResearch.WordTrace tailWord_2430912 prefixEnd_2430912 1248226284782498279320445 := by
  unfold tailWord_2430912
  simp only [CollatzResearch.WordTrace]
  refine ⟨44331322284614232780799495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59108429712818977041065993 44331322284614232780799495)
  ·
    refine ⟨66496983426921349171199243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44331322284614232780799495 66496983426921349171199243)
    ·
      refine ⟨99745475140382023756798865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66496983426921349171199243 99745475140382023756798865)
      ·
        refine ⟨74809106355286517817599149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99745475140382023756798865 74809106355286517817599149)
        ·
          refine ⟨28053414883232444181599681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74809106355286517817599149 28053414883232444181599681)
          ·
            refine ⟨21040061162424333136199761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28053414883232444181599681 21040061162424333136199761)
            ·
              refine ⟨15780045871818249852149821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21040061162424333136199761 15780045871818249852149821)
              ·
                refine ⟨5917517201931843694556183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15780045871818249852149821 5917517201931843694556183)
                ·
                  refine ⟨8876275802897765541834275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5917517201931843694556183 8876275802897765541834275)
                  ·
                    refine ⟨13314413704346648312751413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8876275802897765541834275 13314413704346648312751413)
                    ·
                      refine ⟨1248226284782498279320445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13314413704346648312751413 1248226284782498279320445)
                      ·
                        rfl

theorem cell23_2430912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_2430912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430912 prefixEnd_2430912 := by exact prefixLift 2430912
  have htrace : WordTrace (prefixWord ++ tailWord_2430912) baseStart_2430912 baseEnd_2430912 := by
    simpa [prefixWord, tailWord_2430912, baseEnd_2430912] using wordTrace_append hprefix tailTrace_2430912
  have hstable : (prefixWord ++ tailWord_2430912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430912).length < 2 ^ (prefixWord ++ tailWord_2430912).sum := by decide
  have hdescent : baseEnd_2430912 < baseStart_2430912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430922 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 3, 2, 4]
def baseStart_2430922 : Nat := 118140960795 + 2430922 * 2 ^ 59
def prefixEnd_2430922 : Nat := 4983230072969 + 3 ^ 40 * 2430922 * 2
def baseEnd_2430922 : Nat := 1248231419589043240195399

theorem tailTrace_2430922 : CollatzResearch.WordTrace tailWord_2430922 prefixEnd_2430922 1248231419589043240195399 := by
  unfold tailWord_2430922
  simp only [CollatzResearch.WordTrace]
  refine ⟨22165752324798059317365755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59108672866128158179642013 22165752324798059317365755)
  ·
    refine ⟨33248628487197088976048633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22165752324798059317365755 33248628487197088976048633)
    ·
      refine ⟨24936471365397816732036475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33248628487197088976048633 24936471365397816732036475)
      ·
        refine ⟨37404707048096725098054713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24936471365397816732036475 37404707048096725098054713)
        ·
          refine ⟨28053530286072543823541035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37404707048096725098054713 28053530286072543823541035)
          ·
            refine ⟨42080295429108815735311553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28053530286072543823541035 42080295429108815735311553)
            ·
              refine ⟨31560221571831611801483665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42080295429108815735311553 31560221571831611801483665)
              ·
                refine ⟨23670166178873708851112749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31560221571831611801483665 23670166178873708851112749)
                ·
                  refine ⟨8876312317077640819167281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23670166178873708851112749 8876312317077640819167281)
                  ·
                    refine ⟨6657234237808230614375461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8876312317077640819167281 6657234237808230614375461)
                    ·
                      refine ⟨1248231419589043240195399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6657234237808230614375461 1248231419589043240195399)
                      ·
                        rfl

theorem cell23_2430922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_2430922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430922 prefixEnd_2430922 := by exact prefixLift 2430922
  have htrace : WordTrace (prefixWord ++ tailWord_2430922) baseStart_2430922 baseEnd_2430922 := by
    simpa [prefixWord, tailWord_2430922, baseEnd_2430922] using wordTrace_append hprefix tailTrace_2430922
  have hstable : (prefixWord ++ tailWord_2430922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430922).length < 2 ^ (prefixWord ++ tailWord_2430922).sum := by decide
  have hdescent : baseEnd_2430922 < baseStart_2430922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430932 : List Nat := [2, 4, 1, 2, 1, 1, 2, 10]
def baseStart_2430932 : Nat := 118140960795 + 2430932 * 2 ^ 59
def prefixEnd_2430932 : Nat := 4983230072969 + 3 ^ 40 * 2430932 * 2
def baseEnd_2430932 : Nat := 46230983496132896335939

theorem tailTrace_2430932 : CollatzResearch.WordTrace tailWord_2430932 prefixEnd_2430932 46230983496132896335939 := by
  unfold tailWord_2430932
  simp only [CollatzResearch.WordTrace]
  refine ⟨44331687014578004488663525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59108916019437339318218033 44331687014578004488663525)
  ·
    refine ⟨8312191315233375841624411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44331687014578004488663525 8312191315233375841624411)
    ·
      refine ⟨12468286972850063762436617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8312191315233375841624411 12468286972850063762436617)
      ·
        refine ⟨9351215229637547821827463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12468286972850063762436617 9351215229637547821827463)
        ·
          refine ⟨14026822844456321732741195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9351215229637547821827463 14026822844456321732741195)
          ·
            refine ⟨21040234266684482599111793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14026822844456321732741195 21040234266684482599111793)
            ·
              refine ⟨15780175700013361949333845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21040234266684482599111793 15780175700013361949333845)
              ·
                refine ⟨46230983496132896335939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 15780175700013361949333845 46230983496132896335939)
                ·
                  rfl

theorem cell23_2430932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 10].length) (baseStart_2430932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430932 prefixEnd_2430932 := by exact prefixLift 2430932
  have htrace : WordTrace (prefixWord ++ tailWord_2430932) baseStart_2430932 baseEnd_2430932 := by
    simpa [prefixWord, tailWord_2430932, baseEnd_2430932] using wordTrace_append hprefix tailTrace_2430932
  have hstable : (prefixWord ++ tailWord_2430932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430932).length < 2 ^ (prefixWord ++ tailWord_2430932).sum := by decide
  have hdescent : baseEnd_2430932 < baseStart_2430932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430936 : List Nat := [2, 1, 2, 2, 2, 2, 5, 1, 2, 4]
def baseStart_2430936 : Nat := 118140960795 + 2430936 * 2 ^ 59
def prefixEnd_2430936 : Nat := 4983230072969 + 3 ^ 40 * 2430936 * 2
def baseEnd_2430936 : Nat := 416079536106068728473445

theorem tailTrace_2430936 : CollatzResearch.WordTrace tailWord_2430936 prefixEnd_2430936 416079536106068728473445 := by
  unfold tailWord_2430936
  simp only [CollatzResearch.WordTrace]
  refine ⟨44331759960570758830236331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59109013280761011773648441 44331759960570758830236331)
  ·
    refine ⟨66497639940856138245354497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44331759960570758830236331 66497639940856138245354497)
    ·
      refine ⟨49873229955642103684015873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66497639940856138245354497 49873229955642103684015873)
      ·
        refine ⟨37404922466731577763011905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49873229955642103684015873 37404922466731577763011905)
        ·
          refine ⟨28053691850048683322258929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37404922466731577763011905 28053691850048683322258929)
          ·
            refine ⟨21040268887536512491694197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28053691850048683322258929 21040268887536512491694197)
            ·
              refine ⟨1972525208206548046096331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21040268887536512491694197 1972525208206548046096331)
              ·
                refine ⟨2958787812309822069144497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1972525208206548046096331 2958787812309822069144497)
                ·
                  refine ⟨2219090859232366551858373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2958787812309822069144497 2219090859232366551858373)
                  ·
                    refine ⟨416079536106068728473445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2219090859232366551858373 416079536106068728473445)
                    ·
                      rfl

theorem cell23_2430936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 2, 4].length) (baseStart_2430936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430936 prefixEnd_2430936 := by exact prefixLift 2430936
  have htrace : WordTrace (prefixWord ++ tailWord_2430936) baseStart_2430936 baseEnd_2430936 := by
    simpa [prefixWord, tailWord_2430936, baseEnd_2430936] using wordTrace_append hprefix tailTrace_2430936
  have hstable : (prefixWord ++ tailWord_2430936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430936).length < 2 ^ (prefixWord ++ tailWord_2430936).sum := by decide
  have hdescent : baseEnd_2430936 < baseStart_2430936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430940 : List Nat := [2, 2, 6, 1, 1, 1, 2, 2, 1, 5]
def baseStart_2430940 : Nat := 118140960795 + 2430940 * 2 ^ 59
def prefixEnd_2430940 : Nat := 4983230072969 + 3 ^ 40 * 2430940 * 2
def baseEnd_2430940 : Nat := 416080220746941389923439

theorem tailTrace_2430940 : CollatzResearch.WordTrace tailWord_2430940 prefixEnd_2430940 416080220746941389923439 := by
  unfold tailWord_2430940
  simp only [CollatzResearch.WordTrace]
  refine ⟨44331832906563513171809137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59109110542084684229078849 44331832906563513171809137)
  ·
    refine ⟨33248874679922634878856853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44331832906563513171809137 33248874679922634878856853)
    ·
      refine ⟨1558541000621373509946415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33248874679922634878856853 1558541000621373509946415)
      ·
        refine ⟨2337811500932060264919623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1558541000621373509946415 2337811500932060264919623)
        ·
          refine ⟨3506717251398090397379435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2337811500932060264919623 3506717251398090397379435)
          ·
            refine ⟨5260075877097135596069153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3506717251398090397379435 5260075877097135596069153)
            ·
              refine ⟨3945056907822851697051865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5260075877097135596069153 3945056907822851697051865)
              ·
                refine ⟨2958792680867138772788899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3945056907822851697051865 2958792680867138772788899)
                ·
                  refine ⟨4438189021300708159183349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2958792680867138772788899 4438189021300708159183349)
                  ·
                    refine ⟨416080220746941389923439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4438189021300708159183349 416080220746941389923439)
                    ·
                      rfl

theorem cell23_2430940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_2430940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430940 prefixEnd_2430940 := by exact prefixLift 2430940
  have htrace : WordTrace (prefixWord ++ tailWord_2430940) baseStart_2430940 baseEnd_2430940 := by
    simpa [prefixWord, tailWord_2430940, baseEnd_2430940] using wordTrace_append hprefix tailTrace_2430940
  have hstable : (prefixWord ++ tailWord_2430940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430940).length < 2 ^ (prefixWord ++ tailWord_2430940).sum := by decide
  have hdescent : baseEnd_2430940 < baseStart_2430940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430959 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 6, 1, 3]
def baseStart_2430959 : Nat := 118140960795 + 2430959 * 2 ^ 59
def prefixEnd_2430959 : Nat := 4983230072969 + 3 ^ 40 * 2430959 * 2
def baseEnd_2430959 : Nat := 1248250418373259595432729

theorem tailTrace_2430959 : CollatzResearch.WordTrace tailWord_2430959 prefixEnd_2430959 1248250418373259595432729 := by
  unfold tailWord_2430959
  simp only [CollatzResearch.WordTrace]
  refine ⟨88664358800058192588559931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59109572533372128392373287 88664358800058192588559931)
  ·
    refine ⟨132996538200087288882839897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88664358800058192588559931 132996538200087288882839897)
    ·
      refine ⟨99747403650065466662129923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132996538200087288882839897 99747403650065466662129923)
      ·
        refine ⟨149621105475098199993194885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99747403650065466662129923 149621105475098199993194885)
        ·
          refine ⟨28053957276580912498724041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149621105475098199993194885 28053957276580912498724041)
          ·
            refine ⟨21040467957435684374043031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28053957276580912498724041 21040467957435684374043031)
            ·
              refine ⟨31560701936153526561064547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21040467957435684374043031 31560701936153526561064547)
              ·
                refine ⟨47341052904230289841596821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31560701936153526561064547 47341052904230289841596821)
                ·
                  refine ⟨2219111854885794836324851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47341052904230289841596821 2219111854885794836324851)
                  ·
                    refine ⟨3328667782328692254487277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2219111854885794836324851 3328667782328692254487277)
                    ·
                      refine ⟨1248250418373259595432729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3328667782328692254487277 1248250418373259595432729)
                      ·
                        rfl

theorem cell23_2430959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6, 1, 3].length) (baseStart_2430959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430959 prefixEnd_2430959 := by exact prefixLift 2430959
  have htrace : WordTrace (prefixWord ++ tailWord_2430959) baseStart_2430959 baseEnd_2430959 := by
    simpa [prefixWord, tailWord_2430959, baseEnd_2430959] using wordTrace_append hprefix tailTrace_2430959
  have hstable : (prefixWord ++ tailWord_2430959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430959).length < 2 ^ (prefixWord ++ tailWord_2430959).sum := by decide
  have hdescent : baseEnd_2430959 < baseStart_2430959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430966 : List Nat := [5, 1, 1, 1, 5, 1, 9]
def baseStart_2430966 : Nat := 118140960795 + 2430966 * 2 ^ 59
def prefixEnd_2430966 : Nat := 4983230072969 + 3 ^ 40 * 2430966 * 2
def baseEnd_2430966 : Nat := 15410543367133840346237

theorem tailTrace_2430966 : CollatzResearch.WordTrace tailWord_2430966 prefixEnd_2430966 15410543367133840346237 := by
  unfold tailWord_2430966
  simp only [CollatzResearch.WordTrace]
  refine ⟨5541538381939552049004047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59109742740688555189376501 5541538381939552049004047)
  ·
    refine ⟨8312307572909328073506071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5541538381939552049004047 8312307572909328073506071)
    ·
      refine ⟨12468461359363992110259107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8312307572909328073506071 12468461359363992110259107)
      ·
        refine ⟨18702692039045988165388661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12468461359363992110259107 18702692039045988165388661)
        ·
          refine ⟨1753377378660561390505187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18702692039045988165388661 1753377378660561390505187)
          ·
            refine ⟨2630066067990842085757781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1753377378660561390505187 2630066067990842085757781)
            ·
              refine ⟨15410543367133840346237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2630066067990842085757781 15410543367133840346237)
              ·
                rfl

theorem cell23_2430966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 9].length) (baseStart_2430966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430966 prefixEnd_2430966 := by exact prefixLift 2430966
  have htrace : WordTrace (prefixWord ++ tailWord_2430966) baseStart_2430966 baseEnd_2430966 := by
    simpa [prefixWord, tailWord_2430966, baseEnd_2430966] using wordTrace_append hprefix tailTrace_2430966
  have hstable : (prefixWord ++ tailWord_2430966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430966).length < 2 ^ (prefixWord ++ tailWord_2430966).sum := by decide
  have hdescent : baseEnd_2430966 < baseStart_2430966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2430972 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 5]
def baseStart_2430972 : Nat := 118140960795 + 2430972 * 2 ^ 59
def prefixEnd_2430972 : Nat := 4983230072969 + 3 ^ 40 * 2430972 * 2
def baseEnd_2430972 : Nat := 1248257093621768044570169

theorem tailTrace_2430972 : CollatzResearch.WordTrace tailWord_2430972 prefixEnd_2430972 1248257093621768044570169 := by
  unfold tailWord_2430972
  simp only [CollatzResearch.WordTrace]
  refine ⟨44332416474505547904391585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59109888632674063872522113 44332416474505547904391585)
  ·
    refine ⟨33249312355879160928293689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44332416474505547904391585 33249312355879160928293689)
    ·
      refine ⟨24936984266909370696220267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33249312355879160928293689 24936984266909370696220267)
      ·
        refine ⟨37405476400364056044330401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24936984266909370696220267 37405476400364056044330401)
        ·
          refine ⟨28054107300273042033247801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37405476400364056044330401 28054107300273042033247801)
          ·
            refine ⟨21040580475204781524935851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28054107300273042033247801 21040580475204781524935851)
            ·
              refine ⟨31560870712807172287403777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21040580475204781524935851 31560870712807172287403777)
              ·
                refine ⟨23670653034605379215552833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31560870712807172287403777 23670653034605379215552833)
                ·
                  refine ⟨17752989775954034411664625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23670653034605379215552833 17752989775954034411664625)
                  ·
                    refine ⟨13314742331965525808748469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17752989775954034411664625 13314742331965525808748469)
                    ·
                      refine ⟨1248257093621768044570169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13314742331965525808748469 1248257093621768044570169)
                      ·
                        rfl

theorem cell23_2430972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_2430972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2430972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2430972 prefixEnd_2430972 := by exact prefixLift 2430972
  have htrace : WordTrace (prefixWord ++ tailWord_2430972) baseStart_2430972 baseEnd_2430972 := by
    simpa [prefixWord, tailWord_2430972, baseEnd_2430972] using wordTrace_append hprefix tailTrace_2430972
  have hstable : (prefixWord ++ tailWord_2430972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2430972).length < 2 ^ (prefixWord ++ tailWord_2430972).sum := by decide
  have hdescent : baseEnd_2430972 < baseStart_2430972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2430972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431049 : List Nat := [1, 2, 1, 1, 2, 2, 5, 1, 2, 3, 3]
def baseStart_2431049 : Nat := 118140960795 + 2431049 * 2 ^ 59
def prefixEnd_2431049 : Nat := 4983230072969 + 3 ^ 40 * 2431049 * 2
def baseEnd_2431049 : Nat := 1248296631632164243307315

theorem tailTrace_2431049 : CollatzResearch.WordTrace tailWord_2431049 prefixEnd_2431049 1248296631632164243307315 := by
  unfold tailWord_2431049
  simp only [CollatzResearch.WordTrace]
  refine ⟨88667641369732137959336201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59111760913154758639557467 88667641369732137959336201)
  ·
    refine ⟨66500731027299103469502151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88667641369732137959336201 66500731027299103469502151)
    ·
      refine ⟨99751096540948655204253227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66500731027299103469502151 99751096540948655204253227)
      ·
        refine ⟨149626644811422982806379841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99751096540948655204253227 149626644811422982806379841)
        ·
          refine ⟨112219983608567237104784881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149626644811422982806379841 112219983608567237104784881)
          ·
            refine ⟨84164987706425427828588661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112219983608567237104784881 84164987706425427828588661)
            ·
              refine ⟨7890467597477383858930187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84164987706425427828588661 7890467597477383858930187)
              ·
                refine ⟨11835701396216075788395281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7890467597477383858930187 11835701396216075788395281)
                ·
                  refine ⟨8876776047162056841296461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11835701396216075788395281 8876776047162056841296461)
                  ·
                    refine ⟨3328791017685771315486173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8876776047162056841296461 3328791017685771315486173)
                    ·
                      refine ⟨1248296631632164243307315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3328791017685771315486173 1248296631632164243307315)
                      ·
                        rfl

theorem cell23_2431049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 3, 3].length) (baseStart_2431049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431049 prefixEnd_2431049 := by exact prefixLift 2431049
  have htrace : WordTrace (prefixWord ++ tailWord_2431049) baseStart_2431049 baseEnd_2431049 := by
    simpa [prefixWord, tailWord_2431049, baseEnd_2431049] using wordTrace_append hprefix tailTrace_2431049
  have hstable : (prefixWord ++ tailWord_2431049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431049).length < 2 ^ (prefixWord ++ tailWord_2431049).sum := by decide
  have hdescent : baseEnd_2431049 < baseStart_2431049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431059 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 3, 7, 2]
def baseStart_2431059 : Nat := 118140960795 + 2431059 * 2 ^ 59
def prefixEnd_2431059 : Nat := 4983230072969 + 3 ^ 40 * 2431059 * 2
def baseEnd_2431059 : Nat := 1248301766438709204182269

theorem tailTrace_2431059 : CollatzResearch.WordTrace tailWord_2431059 prefixEnd_2431059 1248301766438709204182269 := by
  unfold tailWord_2431059
  simp only [CollatzResearch.WordTrace]
  refine ⟨88668006099695909667200231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59112004066463939778133487 88668006099695909667200231)
  ·
    refine ⟨133002009149543864500800347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88668006099695909667200231 133002009149543864500800347)
    ·
      refine ⟨199503013724315796751200521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133002009149543864500800347 199503013724315796751200521)
      ·
        refine ⟨149627260293236847563400391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199503013724315796751200521 149627260293236847563400391)
        ·
          refine ⟨224440890439855271345100587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149627260293236847563400391 224440890439855271345100587)
          ·
            refine ⟨336661335659782907017650881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224440890439855271345100587 336661335659782907017650881)
            ·
              refine ⟨252496001744837180263238161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 336661335659782907017650881 252496001744837180263238161)
              ·
                refine ⟨189372001308627885197428621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252496001744837180263238161 189372001308627885197428621)
                ·
                  refine ⟨71014500490735456949035733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189372001308627885197428621 71014500490735456949035733)
                  ·
                    refine ⟨1664402355251612272243025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 71014500490735456949035733 1664402355251612272243025)
                    ·
                      refine ⟨1248301766438709204182269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1664402355251612272243025 1248301766438709204182269)
                      ·
                        rfl

theorem cell23_2431059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 7, 2].length) (baseStart_2431059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431059 prefixEnd_2431059 := by exact prefixLift 2431059
  have htrace : WordTrace (prefixWord ++ tailWord_2431059) baseStart_2431059 baseEnd_2431059 := by
    simpa [prefixWord, tailWord_2431059, baseEnd_2431059] using wordTrace_append hprefix tailTrace_2431059
  have hstable : (prefixWord ++ tailWord_2431059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431059).length < 2 ^ (prefixWord ++ tailWord_2431059).sum := by decide
  have hdescent : baseEnd_2431059 < baseStart_2431059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431089 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 4, 1, 4]
def baseStart_2431089 : Nat := 118140960795 + 2431089 * 2 ^ 59
def prefixEnd_2431089 : Nat := 4983230072969 + 3 ^ 40 * 2431089 * 2
def baseEnd_2431089 : Nat := 1248317170858344086807131

theorem tailTrace_2431089 : CollatzResearch.WordTrace tailWord_2431089 prefixEnd_2431089 1248317170858344086807131 := by
  unfold tailWord_2431089
  simp only [CollatzResearch.WordTrace]
  refine ⟨88669100289587224790792321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59112733526391483193861547 88669100289587224790792321)
  ·
    refine ⟨66501825217190418593094241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88669100289587224790792321 66501825217190418593094241)
    ·
      refine ⟨49876368912892813944820681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66501825217190418593094241 49876368912892813944820681)
      ·
        refine ⟨37407276684669610458615511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49876368912892813944820681 37407276684669610458615511)
        ·
          refine ⟨56110915027004415687923267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37407276684669610458615511 56110915027004415687923267)
          ·
            refine ⟨84166372540506623531884901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56110915027004415687923267 84166372540506623531884901)
            ·
              refine ⟨15781194851344991912228419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84166372540506623531884901 15781194851344991912228419)
              ·
                refine ⟨23671792277017487868342629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15781194851344991912228419 23671792277017487868342629)
                ·
                  refine ⟨4438461051940778975314243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23671792277017487868342629 4438461051940778975314243)
                  ·
                    refine ⟨6657691577911168462971365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4438461051940778975314243 6657691577911168462971365)
                    ·
                      refine ⟨1248317170858344086807131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6657691577911168462971365 1248317170858344086807131)
                      ·
                        rfl

theorem cell23_2431089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_2431089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431089 prefixEnd_2431089 := by exact prefixLift 2431089
  have htrace : WordTrace (prefixWord ++ tailWord_2431089) baseStart_2431089 baseEnd_2431089 := by
    simpa [prefixWord, tailWord_2431089, baseEnd_2431089] using wordTrace_append hprefix tailTrace_2431089
  have hstable : (prefixWord ++ tailWord_2431089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431089).length < 2 ^ (prefixWord ++ tailWord_2431089).sum := by decide
  have hdescent : baseEnd_2431089 < baseStart_2431089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431183 : List Nat := [1, 1, 2, 1, 1, 3, 6, 1, 2, 3, 2]
def baseStart_2431183 : Nat := 118140960795 + 2431183 * 2 ^ 59
def prefixEnd_2431183 : Nat := 4983230072969 + 3 ^ 40 * 2431183 * 2
def baseEnd_2431183 : Nat := 1248365438039866719031699

theorem tailTrace_2431183 : CollatzResearch.WordTrace tailWord_2431183 prefixEnd_2431183 1248365438039866719031699 := by
  unfold tailWord_2431183
  simp only [CollatzResearch.WordTrace]
  refine ⟨88672528751246678844714203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59115019167497785896476135 88672528751246678844714203)
  ·
    refine ⟨133008793126870018267071305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88672528751246678844714203 133008793126870018267071305)
    ·
      refine ⟨99756594845152513700303479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133008793126870018267071305 99756594845152513700303479)
      ·
        refine ⟨149634892267728770550455219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99756594845152513700303479 149634892267728770550455219)
        ·
          refine ⟨224452338401593155825682829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149634892267728770550455219 224452338401593155825682829)
          ·
            refine ⟨84169626900597433434631061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 224452338401593155825682829 84169626900597433434631061)
            ·
              refine ⟨3945451260965504692248331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 84169626900597433434631061 3945451260965504692248331)
              ·
                refine ⟨5918176891448257038372497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3945451260965504692248331 5918176891448257038372497)
                ·
                  refine ⟨4438632668586192778779373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5918176891448257038372497 4438632668586192778779373)
                  ·
                    refine ⟨1664487250719822292042265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4438632668586192778779373 1664487250719822292042265)
                    ·
                      refine ⟨1248365438039866719031699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1664487250719822292042265 1248365438039866719031699)
                      ·
                        rfl

theorem cell23_2431183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 3, 2].length) (baseStart_2431183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431183 prefixEnd_2431183 := by exact prefixLift 2431183
  have htrace : WordTrace (prefixWord ++ tailWord_2431183) baseStart_2431183 baseEnd_2431183 := by
    simpa [prefixWord, tailWord_2431183, baseEnd_2431183] using wordTrace_append hprefix tailTrace_2431183
  have hstable : (prefixWord ++ tailWord_2431183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431183).length < 2 ^ (prefixWord ++ tailWord_2431183).sum := by decide
  have hdescent : baseEnd_2431183 < baseStart_2431183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431207 : List Nat := [1, 1, 5, 3, 1, 2, 1, 4, 1, 1, 3]
def baseStart_2431207 : Nat := 118140960795 + 2431207 * 2 ^ 59
def prefixEnd_2431207 : Nat := 4983230072969 + 3 ^ 40 * 2431207 * 2
def baseEnd_2431207 : Nat := 1248377761575574625131589

theorem tailTrace_2431207 : CollatzResearch.WordTrace tailWord_2431207 prefixEnd_2431207 1248377761575574625131589 := by
  unfold tailWord_2431207
  simp only [CollatzResearch.WordTrace]
  refine ⟨88673404103159730943587875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59115602735439820629058583 88673404103159730943587875)
  ·
    refine ⟨133010106154739596415381813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88673404103159730943587875 133010106154739596415381813)
    ·
      refine ⟨12469697452006837163942045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133010106154739596415381813 12469697452006837163942045)
      ·
        refine ⟨4676136544502563936478267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12469697452006837163942045 4676136544502563936478267)
        ·
          refine ⟨7014204816753845904717401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4676136544502563936478267 7014204816753845904717401)
          ·
            refine ⟨5260653612565384428538051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7014204816753845904717401 5260653612565384428538051)
            ·
              refine ⟨7890980418848076642807077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5260653612565384428538051 7890980418848076642807077)
              ·
                refine ⟨1479558828534014370526327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7890980418848076642807077 1479558828534014370526327)
                ·
                  refine ⟨2219338242801021555789491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1479558828534014370526327 2219338242801021555789491)
                  ·
                    refine ⟨3329007364201532333684237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2219338242801021555789491 3329007364201532333684237)
                    ·
                      refine ⟨1248377761575574625131589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3329007364201532333684237 1248377761575574625131589)
                      ·
                        rfl

theorem cell23_2431207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_2431207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431207 prefixEnd_2431207 := by exact prefixLift 2431207
  have htrace : WordTrace (prefixWord ++ tailWord_2431207) baseStart_2431207 baseEnd_2431207 := by
    simpa [prefixWord, tailWord_2431207, baseEnd_2431207] using wordTrace_append hprefix tailTrace_2431207
  have hstable : (prefixWord ++ tailWord_2431207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431207).length < 2 ^ (prefixWord ++ tailWord_2431207).sum := by decide
  have hdescent : baseEnd_2431207 < baseStart_2431207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431226 : List Nat := [3, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4]
def baseStart_2431226 : Nat := 118140960795 + 2431226 * 2 ^ 59
def prefixEnd_2431226 : Nat := 4983230072969 + 3 ^ 40 * 2431226 * 2
def baseEnd_2431226 : Nat := 1248387517708010050794001

theorem tailTrace_2431226 : CollatzResearch.WordTrace tailWord_2431226 prefixEnd_2431226 1248387517708010050794001 := by
  unfold tailWord_2431226
  simp only [CollatzResearch.WordTrace]
  refine ⟨22168524272522724297132383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59116064726727264792353021 22168524272522724297132383)
  ·
    refine ⟨33252786408784086445698575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22168524272522724297132383 33252786408784086445698575)
    ·
      refine ⟨49879179613176129668547863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33252786408784086445698575 49879179613176129668547863)
      ·
        refine ⟨74818769419764194502821795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49879179613176129668547863 74818769419764194502821795)
        ·
          refine ⟨112228154129646291754232693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74818769419764194502821795 112228154129646291754232693)
          ·
            refine ⟨10521389449654339851959315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 112228154129646291754232693 10521389449654339851959315)
            ·
              refine ⟨15782084174481509777938973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10521389449654339851959315 15782084174481509777938973)
              ·
                refine ⟨5918281565430566166727115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15782084174481509777938973 5918281565430566166727115)
                ·
                  refine ⟨8877422348145849250090673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5918281565430566166727115 8877422348145849250090673)
                  ·
                    refine ⟨6658066761109386937568005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8877422348145849250090673 6658066761109386937568005)
                    ·
                      refine ⟨1248387517708010050794001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6658066761109386937568005 1248387517708010050794001)
                      ·
                        rfl

theorem cell23_2431226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_2431226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431226 prefixEnd_2431226 := by exact prefixLift 2431226
  have htrace : WordTrace (prefixWord ++ tailWord_2431226) baseStart_2431226 baseEnd_2431226 := by
    simpa [prefixWord, tailWord_2431226, baseEnd_2431226] using wordTrace_append hprefix tailTrace_2431226
  have hstable : (prefixWord ++ tailWord_2431226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431226).length < 2 ^ (prefixWord ++ tailWord_2431226).sum := by decide
  have hdescent : baseEnd_2431226 < baseStart_2431226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431229 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 2, 2, 7]
def baseStart_2431229 : Nat := 118140960795 + 2431229 * 2 ^ 59
def prefixEnd_2431229 : Nat := 4983230072969 + 3 ^ 40 * 2431229 * 2
def baseEnd_2431229 : Nat := 1248389058149973539056487

theorem tailTrace_2431229 : CollatzResearch.WordTrace tailWord_2431229 prefixEnd_2431229 1248389058149973539056487 := by
  unfold tailWord_2431229
  simp only [CollatzResearch.WordTrace]
  refine ⟨88674206509080028700888741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59116137672720019133925827 88674206509080028700888741)
  ·
    refine ⟨16626413720452505381416639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88674206509080028700888741 16626413720452505381416639)
    ·
      refine ⟨24939620580678758072124959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16626413720452505381416639 24939620580678758072124959)
      ·
        refine ⟨37409430871018137108187439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24939620580678758072124959 37409430871018137108187439)
        ·
          refine ⟨56114146306527205662281159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37409430871018137108187439 56114146306527205662281159)
          ·
            refine ⟨84171219459790808493421739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56114146306527205662281159 84171219459790808493421739)
            ·
              refine ⟨126256829189686212740132609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84171219459790808493421739 126256829189686212740132609)
              ·
                refine ⟨94692621892264659555099457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126256829189686212740132609 94692621892264659555099457)
                ·
                  refine ⟨71019466419198494666324593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94692621892264659555099457 71019466419198494666324593)
                  ·
                    refine ⟨53264599814398870999743445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71019466419198494666324593 53264599814398870999743445)
                    ·
                      refine ⟨1248389058149973539056487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53264599814398870999743445 1248389058149973539056487)
                      ·
                        rfl

theorem cell23_2431229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_2431229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431229 prefixEnd_2431229 := by exact prefixLift 2431229
  have htrace : WordTrace (prefixWord ++ tailWord_2431229) baseStart_2431229 baseEnd_2431229 := by
    simpa [prefixWord, tailWord_2431229, baseEnd_2431229] using wordTrace_append hprefix tailTrace_2431229
  have hstable : (prefixWord ++ tailWord_2431229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431229).length < 2 ^ (prefixWord ++ tailWord_2431229).sum := by decide
  have hdescent : baseEnd_2431229 < baseStart_2431229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431233 : List Nat := [1, 2, 4, 1, 1, 2, 2, 4, 1, 2, 3]
def baseStart_2431233 : Nat := 118140960795 + 2431233 * 2 ^ 59
def prefixEnd_2431233 : Nat := 4983230072969 + 3 ^ 40 * 2431233 * 2
def baseEnd_2431233 : Nat := 1248391112072591523406469

theorem tailTrace_2431233 : CollatzResearch.WordTrace tailWord_2431233 prefixEnd_2431233 1248391112072591523406469 := by
  unfold tailWord_2431233
  simp only [CollatzResearch.WordTrace]
  refine ⟨88674352401065537384034353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59116234934043691589356235 88674352401065537384034353)
  ·
    refine ⟨66505764300799153038025765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88674352401065537384034353 66505764300799153038025765)
    ·
      refine ⟨12469830806399841194629831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66505764300799153038025765 12469830806399841194629831)
      ·
        refine ⟨18704746209599761791944747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12469830806399841194629831 18704746209599761791944747)
        ·
          refine ⟨28057119314399642687917121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18704746209599761791944747 28057119314399642687917121)
          ·
            refine ⟨21042839485799732015937841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28057119314399642687917121 21042839485799732015937841)
            ·
              refine ⟨15782129614349799011953381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21042839485799732015937841 15782129614349799011953381)
              ·
                refine ⟨2959149302690587314741259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15782129614349799011953381 2959149302690587314741259)
                ·
                  refine ⟨4438723954035880972111889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2959149302690587314741259 4438723954035880972111889)
                  ·
                    refine ⟨3329042965526910729083917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4438723954035880972111889 3329042965526910729083917)
                    ·
                      refine ⟨1248391112072591523406469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3329042965526910729083917 1248391112072591523406469)
                      ·
                        rfl

theorem cell23_2431233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_2431233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431233 prefixEnd_2431233 := by exact prefixLift 2431233
  have htrace : WordTrace (prefixWord ++ tailWord_2431233) baseStart_2431233 baseEnd_2431233 := by
    simpa [prefixWord, tailWord_2431233, baseEnd_2431233] using wordTrace_append hprefix tailTrace_2431233
  have hstable : (prefixWord ++ tailWord_2431233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431233).length < 2 ^ (prefixWord ++ tailWord_2431233).sum := by decide
  have hdescent : baseEnd_2431233 < baseStart_2431233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431277 : List Nat := [1, 5, 3, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_2431277 : Nat := 118140960795 + 2431277 * 2 ^ 59
def prefixEnd_2431277 : Nat := 4983230072969 + 3 ^ 40 * 2431277 * 2
def baseEnd_2431277 : Nat := 1248413705221389351256267

theorem tailTrace_2431277 : CollatzResearch.WordTrace tailWord_2431277 prefixEnd_2431277 1248413705221389351256267 := by
  unfold tailWord_2431277
  simp only [CollatzResearch.WordTrace]
  refine ⟨88675957212906132898636085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59117304808604088599090723 88675957212906132898636085)
  ·
    refine ⟨8313370988709949959247133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88675957212906132898636085 8313370988709949959247133)
    ·
      refine ⟨3117514120766231234717675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8313370988709949959247133 3117514120766231234717675)
      ·
        refine ⟨4676271181149346852076513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3117514120766231234717675 4676271181149346852076513)
        ·
          refine ⟨3507203385862010139057385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4676271181149346852076513 3507203385862010139057385)
          ·
            refine ⟨2630402539396507604293039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3507203385862010139057385 2630402539396507604293039)
            ·
              refine ⟨3945603809094761406439559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2630402539396507604293039 3945603809094761406439559)
              ·
                refine ⟨5918405713642142109659339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3945603809094761406439559 5918405713642142109659339)
                ·
                  refine ⟨8877608570463213164489009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5918405713642142109659339 8877608570463213164489009)
                  ·
                    refine ⟨6658206427847409873366757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8877608570463213164489009 6658206427847409873366757)
                    ·
                      refine ⟨1248413705221389351256267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6658206427847409873366757 1248413705221389351256267)
                      ·
                        rfl

theorem cell23_2431277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_2431277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431277 prefixEnd_2431277 := by exact prefixLift 2431277
  have htrace : WordTrace (prefixWord ++ tailWord_2431277) baseStart_2431277 baseEnd_2431277 := by
    simpa [prefixWord, tailWord_2431277, baseEnd_2431277] using wordTrace_append hprefix tailTrace_2431277
  have hstable : (prefixWord ++ tailWord_2431277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431277).length < 2 ^ (prefixWord ++ tailWord_2431277).sum := by decide
  have hdescent : baseEnd_2431277 < baseStart_2431277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431290 : List Nat := [3, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2]
def baseStart_2431290 : Nat := 118140960795 + 2431290 * 2 ^ 59
def prefixEnd_2431290 : Nat := 4983230072969 + 3 ^ 40 * 2431290 * 2
def baseEnd_2431290 : Nat := 1248420380469897800393707

theorem tailTrace_2431290 : CollatzResearch.WordTrace tailWord_2431290 prefixEnd_2431290 1248420380469897800393707 := by
  unfold tailWord_2431290
  simp only [CollatzResearch.WordTrace]
  refine ⟨22169107840464759029714831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59117620907906024079239549 22169107840464759029714831)
  ·
    refine ⟨33253661760697138544572247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22169107840464759029714831 33253661760697138544572247)
    ·
      refine ⟨49880492641045707816858371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33253661760697138544572247 49880492641045707816858371)
      ·
        refine ⟨74820738961568561725287557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49880492641045707816858371 74820738961568561725287557)
        ·
          refine ⟨14028888555294105323491417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74820738961568561725287557 14028888555294105323491417)
          ·
            refine ⟨10521666416470578992618563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14028888555294105323491417 10521666416470578992618563)
            ·
              refine ⟨15782499624705868488927845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10521666416470578992618563 15782499624705868488927845)
              ·
                refine ⟨2959218679632350341673971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15782499624705868488927845 2959218679632350341673971)
                ·
                  refine ⟨4438828019448525512510957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2959218679632350341673971 4438828019448525512510957)
                  ·
                    refine ⟨1664560507293197067191609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4438828019448525512510957 1664560507293197067191609)
                    ·
                      refine ⟨1248420380469897800393707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1664560507293197067191609 1248420380469897800393707)
                      ·
                        rfl

theorem cell23_2431290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2].length) (baseStart_2431290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431290 prefixEnd_2431290 := by exact prefixLift 2431290
  have htrace : WordTrace (prefixWord ++ tailWord_2431290) baseStart_2431290 baseEnd_2431290 := by
    simpa [prefixWord, tailWord_2431290, baseEnd_2431290] using wordTrace_append hprefix tailTrace_2431290
  have hstable : (prefixWord ++ tailWord_2431290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431290).length < 2 ^ (prefixWord ++ tailWord_2431290).sum := by decide
  have hdescent : baseEnd_2431290 < baseStart_2431290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431303 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 3, 4, 2]
def baseStart_2431303 : Nat := 118140960795 + 2431303 * 2 ^ 59
def prefixEnd_2431303 : Nat := 4983230072969 + 3 ^ 40 * 2431303 * 2
def baseEnd_2431303 : Nat := 1248427055718406249531147

theorem tailTrace_2431303 : CollatzResearch.WordTrace tailWord_2431303 prefixEnd_2431303 1248427055718406249531147 := by
  unfold tailWord_2431303
  simp only [CollatzResearch.WordTrace]
  refine ⟨88676905510811939339082563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59117937007207959559388375 88676905510811939339082563)
  ·
    refine ⟨133015358266217909008623845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88676905510811939339082563 133015358266217909008623845)
    ·
      refine ⟨24940379674915857939116971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133015358266217909008623845 24940379674915857939116971)
      ·
        refine ⟨37410569512373786908675457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24940379674915857939116971 37410569512373786908675457)
        ·
          refine ⟨28057927134280340181506593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37410569512373786908675457 28057927134280340181506593)
          ·
            refine ⟨21043445350710255136129945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28057927134280340181506593 21043445350710255136129945)
            ·
              refine ⟨15782584013032691352097459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21043445350710255136129945 15782584013032691352097459)
              ·
                refine ⟨23673876019549037028146189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15782584013032691352097459 23673876019549037028146189)
                ·
                  refine ⟨8877703507330888885554821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23673876019549037028146189 8877703507330888885554821)
                  ·
                    refine ⟨1664569407624541666041529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8877703507330888885554821 1664569407624541666041529)
                    ·
                      refine ⟨1248427055718406249531147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1664569407624541666041529 1248427055718406249531147)
                      ·
                        rfl

theorem cell23_2431303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 4, 2].length) (baseStart_2431303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431303 prefixEnd_2431303 := by exact prefixLift 2431303
  have htrace : WordTrace (prefixWord ++ tailWord_2431303) baseStart_2431303 baseEnd_2431303 := by
    simpa [prefixWord, tailWord_2431303, baseEnd_2431303] using wordTrace_append hprefix tailTrace_2431303
  have hstable : (prefixWord ++ tailWord_2431303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431303).length < 2 ^ (prefixWord ++ tailWord_2431303).sum := by decide
  have hdescent : baseEnd_2431303 < baseStart_2431303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431306 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 3, 6, 3]
def baseStart_2431306 : Nat := 118140960795 + 2431306 * 2 ^ 59
def prefixEnd_2431306 : Nat := 4983230072969 + 3 ^ 40 * 2431306 * 2
def baseEnd_2431306 : Nat := 1248428596160369737793633

theorem tailTrace_2431306 : CollatzResearch.WordTrace tailWord_2431306 prefixEnd_2431306 1248428596160369737793633 := by
  unfold tailWord_2431306
  simp only [CollatzResearch.WordTrace]
  refine ⟨22169253732450267712860443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59118009953200713900961181 22169253732450267712860443)
  ·
    refine ⟨33253880598675401569290665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22169253732450267712860443 33253880598675401569290665)
    ·
      refine ⟨24940410449006551176967999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33253880598675401569290665 24940410449006551176967999)
      ·
        refine ⟨37410615673509826765451999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24940410449006551176967999 37410615673509826765451999)
        ·
          refine ⟨56115923510264740148177999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37410615673509826765451999 56115923510264740148177999)
          ·
            refine ⟨84173885265397110222266999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56115923510264740148177999 84173885265397110222266999)
            ·
              refine ⟨126260827898095665333400499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84173885265397110222266999 126260827898095665333400499)
              ·
                refine ⟨189391241847143498000100749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126260827898095665333400499 189391241847143498000100749)
                ·
                  refine ⟨71021715692678811750037781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189391241847143498000100749 71021715692678811750037781)
                  ·
                    refine ⟨3329142923094319300783021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71021715692678811750037781 3329142923094319300783021)
                    ·
                      refine ⟨1248428596160369737793633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3329142923094319300783021 1248428596160369737793633)
                      ·
                        rfl

theorem cell23_2431306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_2431306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431306 prefixEnd_2431306 := by exact prefixLift 2431306
  have htrace : WordTrace (prefixWord ++ tailWord_2431306) baseStart_2431306 baseEnd_2431306 := by
    simpa [prefixWord, tailWord_2431306, baseEnd_2431306] using wordTrace_append hprefix tailTrace_2431306
  have hstable : (prefixWord ++ tailWord_2431306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431306).length < 2 ^ (prefixWord ++ tailWord_2431306).sum := by decide
  have hdescent : baseEnd_2431306 < baseStart_2431306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431416 : List Nat := [2, 1, 2, 1, 2, 2, 1, 4, 8]
def baseStart_2431416 : Nat := 118140960795 + 2431416 * 2 ^ 59
def prefixEnd_2431416 : Nat := 4983230072969 + 3 ^ 40 * 2431416 * 2
def baseEnd_2431416 : Nat := 138720564336929367490903

theorem tailTrace_2431416 : CollatzResearch.WordTrace tailWord_2431416 prefixEnd_2431416 138720564336929367490903 := by
  unfold tailWord_2431416
  simp only [CollatzResearch.WordTrace]
  refine ⟨44340513479701279818973051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59120684639601706425297401 44340513479701279818973051)
  ·
    refine ⟨66510770219551919728459577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44340513479701279818973051 66510770219551919728459577)
    ·
      refine ⟨49883077664663939796344683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66510770219551919728459577 49883077664663939796344683)
      ·
        refine ⟨74824616496995909694517025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49883077664663939796344683 74824616496995909694517025)
        ·
          refine ⟨56118462372746932270887769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74824616496995909694517025 56118462372746932270887769)
          ·
            refine ⟨42088846779560199203165827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56118462372746932270887769 42088846779560199203165827)
            ·
              refine ⟨63133270169340298804748741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42088846779560199203165827 63133270169340298804748741)
              ·
                refine ⟨11837488156751306025890389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63133270169340298804748741 11837488156751306025890389)
                ·
                  refine ⟨138720564336929367490903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11837488156751306025890389 138720564336929367490903)
                  ·
                    rfl

theorem cell23_2431416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 8].length) (baseStart_2431416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431416 prefixEnd_2431416 := by exact prefixLift 2431416
  have htrace : WordTrace (prefixWord ++ tailWord_2431416) baseStart_2431416 baseEnd_2431416 := by
    simpa [prefixWord, tailWord_2431416, baseEnd_2431416] using wordTrace_append hprefix tailTrace_2431416
  have hstable : (prefixWord ++ tailWord_2431416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431416).length < 2 ^ (prefixWord ++ tailWord_2431416).sum := by decide
  have hdescent : baseEnd_2431416 < baseStart_2431416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431433 : List Nat := [1, 2, 1, 1, 2, 1, 7, 2, 6]
def baseStart_2431433 : Nat := 118140960795 + 2431433 * 2 ^ 59
def prefixEnd_2431433 : Nat := 4983230072969 + 3 ^ 40 * 2431433 * 2
def baseEnd_2431433 : Nat := 138721534244832304545061

theorem tailTrace_2431433 : CollatzResearch.WordTrace tailWord_2431433 prefixEnd_2431433 138721534244832304545061 := by
  unfold tailWord_2431433
  simp only [CollatzResearch.WordTrace]
  refine ⟨88681647000340971541314953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59121098000227314360876635 88681647000340971541314953)
  ·
    refine ⟨66511235250255728655986215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88681647000340971541314953 66511235250255728655986215)
    ·
      refine ⟨99766852875383592983979323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66511235250255728655986215 99766852875383592983979323)
      ·
        refine ⟨149650279313075389475968985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99766852875383592983979323 149650279313075389475968985)
        ·
          refine ⟨112237709484806542106976739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149650279313075389475968985 112237709484806542106976739)
          ·
            refine ⟨168356564227209813160465109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112237709484806542106976739 168356564227209813160465109)
            ·
              refine ⟨3945856974075229995948401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 168356564227209813160465109 3945856974075229995948401)
              ·
                refine ⟨2959392730556422496961301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3945856974075229995948401 2959392730556422496961301)
                ·
                  refine ⟨138721534244832304545061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2959392730556422496961301 138721534244832304545061)
                  ·
                    rfl

theorem cell23_2431433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 6].length) (baseStart_2431433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431433 prefixEnd_2431433 := by exact prefixLift 2431433
  have htrace : WordTrace (prefixWord ++ tailWord_2431433) baseStart_2431433 baseEnd_2431433 := by
    simpa [prefixWord, tailWord_2431433, baseEnd_2431433] using wordTrace_append hprefix tailTrace_2431433
  have hstable : (prefixWord ++ tailWord_2431433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431433).length < 2 ^ (prefixWord ++ tailWord_2431433).sum := by decide
  have hdescent : baseEnd_2431433 < baseStart_2431433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431450 : List Nat := [3, 1, 1, 2, 3, 1, 5, 1, 6]
def baseStart_2431450 : Nat := 118140960795 + 2431450 * 2 ^ 59
def prefixEnd_2431450 : Nat := 4983230072969 + 3 ^ 40 * 2431450 * 2
def baseEnd_2431450 : Nat := 138722504152735241599219

theorem tailTrace_2431450 : CollatzResearch.WordTrace tailWord_2431450 prefixEnd_2431450 138722504152735241599219 := by
  unfold tailWord_2431450
  simp only [CollatzResearch.WordTrace]
  refine ⟨22170566760319845861170951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59121511360852922296455869 22170566760319845861170951)
  ·
    refine ⟨33255850140479768791756427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22170566760319845861170951 33255850140479768791756427)
    ·
      refine ⟨49883775210719653187634641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33255850140479768791756427 49883775210719653187634641)
      ·
        refine ⟨37412831408039739890725981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49883775210719653187634641 37412831408039739890725981)
        ·
          refine ⟨14029811778014902459022243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37412831408039739890725981 14029811778014902459022243)
          ·
            refine ⟨21044717667022353688533365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14029811778014902459022243 21044717667022353688533365)
            ·
              refine ⟨1972942281283345658300003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21044717667022353688533365 1972942281283345658300003)
              ·
                refine ⟨2959413421925018487450005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1972942281283345658300003 2959413421925018487450005)
                ·
                  refine ⟨138722504152735241599219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2959413421925018487450005 138722504152735241599219)
                  ·
                    rfl

theorem cell23_2431450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 6].length) (baseStart_2431450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431450 prefixEnd_2431450 := by exact prefixLift 2431450
  have htrace : WordTrace (prefixWord ++ tailWord_2431450) baseStart_2431450 baseEnd_2431450 := by
    simpa [prefixWord, tailWord_2431450, baseEnd_2431450] using wordTrace_append hprefix tailTrace_2431450
  have hstable : (prefixWord ++ tailWord_2431450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431450).length < 2 ^ (prefixWord ++ tailWord_2431450).sum := by decide
  have hdescent : baseEnd_2431450 < baseStart_2431450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431453 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_2431453 : Nat := 118140960795 + 2431453 * 2 ^ 59
def prefixEnd_2431453 : Nat := 4983230072969 + 3 ^ 40 * 2431453 * 2
def baseEnd_2431453 : Nat := 1248504077816580662655457

theorem tailTrace_2431453 : CollatzResearch.WordTrace tailWord_2431453 prefixEnd_2431453 1248504077816580662655457 := by
  unfold tailWord_2431453
  simp only [CollatzResearch.WordTrace]
  refine ⟨88682376460268514957043013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59121584306845676638028675 88682376460268514957043013)
  ·
    refine ⟨16627945586300346554445565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88682376460268514957043013 16627945586300346554445565)
    ·
      refine ⟨6235479594862629957917087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16627945586300346554445565 6235479594862629957917087)
      ·
        refine ⟨9353219392293944936875631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6235479594862629957917087 9353219392293944936875631)
        ·
          refine ⟨14029829088440917405313447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9353219392293944936875631 14029829088440917405313447)
          ·
            refine ⟨21044743632661376107970171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14029829088440917405313447 21044743632661376107970171)
            ·
              refine ⟨31567115448992064161955257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21044743632661376107970171 31567115448992064161955257)
              ·
                refine ⟨23675336586744048121466443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31567115448992064161955257 23675336586744048121466443)
                ·
                  refine ⟨35513004880116072182199665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23675336586744048121466443 35513004880116072182199665)
                  ·
                    refine ⟨26634753660087054136649749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35513004880116072182199665 26634753660087054136649749)
                    ·
                      refine ⟨1248504077816580662655457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26634753660087054136649749 1248504077816580662655457)
                      ·
                        rfl

theorem cell23_2431453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_2431453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431453 prefixEnd_2431453 := by exact prefixLift 2431453
  have htrace : WordTrace (prefixWord ++ tailWord_2431453) baseStart_2431453 baseEnd_2431453 := by
    simpa [prefixWord, tailWord_2431453, baseEnd_2431453] using wordTrace_append hprefix tailTrace_2431453
  have hstable : (prefixWord ++ tailWord_2431453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431453).length < 2 ^ (prefixWord ++ tailWord_2431453).sum := by decide
  have hdescent : baseEnd_2431453 < baseStart_2431453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431501 : List Nat := [1, 7, 1, 1, 1, 3, 2, 1, 6]
def baseStart_2431501 : Nat := 118140960795 + 2431501 * 2 ^ 59
def prefixEnd_2431501 : Nat := 4983230072969 + 3 ^ 40 * 2431501 * 2
def baseEnd_2431501 : Nat := 138725413876444052761693

theorem tailTrace_2431501 : CollatzResearch.WordTrace tailWord_2431501 prefixEnd_2431501 138725413876444052761693 := by
  unfold tailWord_2431501
  simp only [CollatzResearch.WordTrace]
  refine ⟨88684127164094619154790357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59122751442729746103193571 88684127164094619154790357)
  ·
    refine ⟨2078534230408467636440399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 88684127164094619154790357 2078534230408467636440399)
    ·
      refine ⟨3117801345612701454660599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2078534230408467636440399 3117801345612701454660599)
      ·
        refine ⟨4676702018419052181990899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3117801345612701454660599 4676702018419052181990899)
        ·
          refine ⟨7015053027628578272986349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4676702018419052181990899 7015053027628578272986349)
          ·
            refine ⟨2630644885360716852369881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7015053027628578272986349 2630644885360716852369881)
            ·
              refine ⟨1972983664020537639277411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2630644885360716852369881 1972983664020537639277411)
              ·
                refine ⟨2959475496030806458916117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1972983664020537639277411 2959475496030806458916117)
                ·
                  refine ⟨138725413876444052761693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2959475496030806458916117 138725413876444052761693)
                  ·
                    rfl

theorem cell23_2431501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_2431501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431501 prefixEnd_2431501 := by exact prefixLift 2431501
  have htrace : WordTrace (prefixWord ++ tailWord_2431501) baseStart_2431501 baseEnd_2431501 := by
    simpa [prefixWord, tailWord_2431501, baseEnd_2431501] using wordTrace_append hprefix tailTrace_2431501
  have hstable : (prefixWord ++ tailWord_2431501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431501).length < 2 ^ (prefixWord ++ tailWord_2431501).sum := by decide
  have hdescent : baseEnd_2431501 < baseStart_2431501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431517 : List Nat := [1, 4, 2, 2, 1, 2, 3, 2, 1, 1, 4]
def baseStart_2431517 : Nat := 118140960795 + 2431517 * 2 ^ 59
def prefixEnd_2431517 : Nat := 4983230072969 + 3 ^ 40 * 2431517 * 2
def baseEnd_2431517 : Nat := 1248536940578468412255163

theorem tailTrace_2431517 : CollatzResearch.WordTrace tailWord_2431517 prefixEnd_2431517 1248536940578468412255163 := by
  unfold tailWord_2431517
  simp only [CollatzResearch.WordTrace]
  refine ⟨88684710732036653887372805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59123140488024435924915203 88684710732036653887372805)
  ·
    refine ⟨16628383262256872603882401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88684710732036653887372805 16628383262256872603882401)
    ·
      refine ⟨12471287446692654452911801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16628383262256872603882401 12471287446692654452911801)
      ·
        refine ⟨9353465585019490839683851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12471287446692654452911801 9353465585019490839683851)
        ·
          refine ⟨14030198377529236259525777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9353465585019490839683851 14030198377529236259525777)
          ·
            refine ⟨10522648783146927194644333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14030198377529236259525777 10522648783146927194644333)
            ·
              refine ⟨3945993293680097697991625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10522648783146927194644333 3945993293680097697991625)
              ·
                refine ⟨2959494970260073273493719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3945993293680097697991625 2959494970260073273493719)
                ·
                  refine ⟨4439242455390109910240579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2959494970260073273493719 4439242455390109910240579)
                  ·
                    refine ⟨6658863683085164865360869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4439242455390109910240579 6658863683085164865360869)
                    ·
                      refine ⟨1248536940578468412255163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6658863683085164865360869 1248536940578468412255163)
                      ·
                        rfl

theorem cell23_2431517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_2431517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431517 prefixEnd_2431517 := by exact prefixLift 2431517
  have htrace : WordTrace (prefixWord ++ tailWord_2431517) baseStart_2431517 baseEnd_2431517 := by
    simpa [prefixWord, tailWord_2431517, baseEnd_2431517] using wordTrace_append hprefix tailTrace_2431517
  have hstable : (prefixWord ++ tailWord_2431517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431517).length < 2 ^ (prefixWord ++ tailWord_2431517).sum := by decide
  have hdescent : baseEnd_2431517 < baseStart_2431517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431523 : List Nat := [1, 1, 1, 4, 4, 1, 2, 9]
def baseStart_2431523 : Nat := 118140960795 + 2431523 * 2 ^ 59
def prefixEnd_2431523 : Nat := 4983230072969 + 3 ^ 40 * 2431523 * 2
def baseEnd_2431523 : Nat := 46242223017125755140005

theorem tailTrace_2431523 : CollatzResearch.WordTrace tailWord_2431523 prefixEnd_2431523 46242223017125755140005 := by
  unfold tailWord_2431523
  simp only [CollatzResearch.WordTrace]
  refine ⟨88684929570014916912091223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59123286380009944608060815 88684929570014916912091223)
  ·
    refine ⟨133027394355022375368136835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88684929570014916912091223 133027394355022375368136835)
    ·
      refine ⟨199541091532533563052205253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133027394355022375368136835 199541091532533563052205253)
      ·
        refine ⟨37413954662350043072288485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 199541091532533563052205253 37413954662350043072288485)
        ·
          refine ⟨7015116499190633076054091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37413954662350043072288485 7015116499190633076054091)
          ·
            refine ⟨10522674748785949614081137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7015116499190633076054091 10522674748785949614081137)
            ·
              refine ⟨7892006061589462210560853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10522674748785949614081137 7892006061589462210560853)
              ·
                refine ⟨46242223017125755140005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7892006061589462210560853 46242223017125755140005)
                ·
                  rfl

theorem cell23_2431523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 9].length) (baseStart_2431523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431523 prefixEnd_2431523 := by exact prefixLift 2431523
  have htrace : WordTrace (prefixWord ++ tailWord_2431523) baseStart_2431523 baseEnd_2431523 := by
    simpa [prefixWord, tailWord_2431523, baseEnd_2431523] using wordTrace_append hprefix tailTrace_2431523
  have hstable : (prefixWord ++ tailWord_2431523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431523).length < 2 ^ (prefixWord ++ tailWord_2431523).sum := by decide
  have hdescent : baseEnd_2431523 < baseStart_2431523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431530 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_2431530 : Nat := 118140960795 + 2431530 * 2 ^ 59
def prefixEnd_2431530 : Nat := 4983230072969 + 3 ^ 40 * 2431530 * 2
def baseEnd_2431530 : Nat := 1248543615826976861392603

theorem tailTrace_2431530 : CollatzResearch.WordTrace tailWord_2431530 prefixEnd_2431530 1248543615826976861392603 := by
  unfold tailWord_2431530
  simp only [CollatzResearch.WordTrace]
  refine ⟨22171296220247389276899011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59123456587326371405064029 22171296220247389276899011)
  ·
    refine ⟨33256944330371083915348517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22171296220247389276899011 33256944330371083915348517)
    ·
      refine ⟨6235677061944578234127847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33256944330371083915348517 6235677061944578234127847)
      ·
        refine ⟨9353515592916867351191771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6235677061944578234127847 9353515592916867351191771)
        ·
          refine ⟨14030273389375301026787657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9353515592916867351191771 14030273389375301026787657)
          ·
            refine ⟨10522705042031475770090743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14030273389375301026787657 10522705042031475770090743)
            ·
              refine ⟨15784057563047213655136115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10522705042031475770090743 15784057563047213655136115)
              ·
                refine ⟨23676086344570820482704173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15784057563047213655136115 23676086344570820482704173)
                ·
                  refine ⟨8878532379214057681014065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23676086344570820482704173 8878532379214057681014065)
                  ·
                    refine ⟨6658899284410543260760549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8878532379214057681014065 6658899284410543260760549)
                    ·
                      refine ⟨1248543615826976861392603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6658899284410543260760549 1248543615826976861392603)
                      ·
                        rfl

theorem cell23_2431530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_2431530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431530 prefixEnd_2431530 := by exact prefixLift 2431530
  have htrace : WordTrace (prefixWord ++ tailWord_2431530) baseStart_2431530 baseEnd_2431530 := by
    simpa [prefixWord, tailWord_2431530, baseEnd_2431530] using wordTrace_append hprefix tailTrace_2431530
  have hstable : (prefixWord ++ tailWord_2431530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431530).length < 2 ^ (prefixWord ++ tailWord_2431530).sum := by decide
  have hdescent : baseEnd_2431530 < baseStart_2431530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431540 : List Nat := [2, 5, 1, 3, 12]
def baseStart_2431540 : Nat := 118140960795 + 2431540 * 2 ^ 59
def prefixEnd_2431540 : Nat := 4983230072969 + 3 ^ 40 * 2431540 * 2
def baseEnd_2431540 : Nat := 1712686900731854351533

theorem tailTrace_2431540 : CollatzResearch.WordTrace tailWord_2431540 prefixEnd_2431540 1712686900731854351533 := by
  unfold tailWord_2431540
  simp only [CollatzResearch.WordTrace]
  refine ⟨44342774805476664407730037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59123699740635552543640049 44342774805476664407730037)
  ·
    refine ⟨4157135138013437288224691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44342774805476664407730037 4157135138013437288224691)
    ·
      refine ⟨6235702707020155932337037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4157135138013437288224691 6235702707020155932337037)
      ·
        refine ⟨2338388515132558474626389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6235702707020155932337037 2338388515132558474626389)
        ·
          refine ⟨1712686900731854351533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2338388515132558474626389 1712686900731854351533)
          ·
            rfl

theorem cell23_2431540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 12].length) (baseStart_2431540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431540 prefixEnd_2431540 := by exact prefixLift 2431540
  have htrace : WordTrace (prefixWord ++ tailWord_2431540) baseStart_2431540 baseEnd_2431540 := by
    simpa [prefixWord, tailWord_2431540, baseEnd_2431540] using wordTrace_append hprefix tailTrace_2431540
  have hstable : (prefixWord ++ tailWord_2431540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431540).length < 2 ^ (prefixWord ++ tailWord_2431540).sum := by decide
  have hdescent : baseEnd_2431540 < baseStart_2431540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431567 : List Nat := [1, 1, 2, 1, 1, 2, 6, 3, 2, 1, 3]
def baseStart_2431567 : Nat := 118140960795 + 2431567 * 2 ^ 59
def prefixEnd_2431567 : Nat := 4983230072969 + 3 ^ 40 * 2431567 * 2
def baseEnd_2431567 : Nat := 1248562614611193216629933

theorem tailTrace_2431567 : CollatzResearch.WordTrace tailWord_2431567 prefixEnd_2431567 1248562614611193216629933 := by
  unfold tailWord_2431567
  simp only [CollatzResearch.WordTrace]
  refine ⟨88686534381855512426692955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59124356254570341617795303 88686534381855512426692955)
  ·
    refine ⟨133029801572783268640039433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88686534381855512426692955 133029801572783268640039433)
    ·
      refine ⟨99772351179587451480029575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133029801572783268640039433 99772351179587451480029575)
      ·
        refine ⟨149658526769381177220044363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99772351179587451480029575 149658526769381177220044363)
        ·
          refine ⟨224487790154071765830066545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149658526769381177220044363 224487790154071765830066545)
          ·
            refine ⟨168365842615553824372549909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224487790154071765830066545 168365842615553824372549909)
            ·
              refine ⟨7892148872604085517463277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 168365842615553824372549909 7892148872604085517463277)
              ·
                refine ⟨2959555827226532069048729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7892148872604085517463277 2959555827226532069048729)
                ·
                  refine ⟨2219666870419899051786547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2959555827226532069048729 2219666870419899051786547)
                  ·
                    refine ⟨3329500305629848577679821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2219666870419899051786547 3329500305629848577679821)
                    ·
                      refine ⟨1248562614611193216629933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3329500305629848577679821 1248562614611193216629933)
                      ·
                        rfl

theorem cell23_2431567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2, 1, 3].length) (baseStart_2431567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431567 prefixEnd_2431567 := by exact prefixLift 2431567
  have htrace : WordTrace (prefixWord ++ tailWord_2431567) baseStart_2431567 baseEnd_2431567 := by
    simpa [prefixWord, tailWord_2431567, baseEnd_2431567] using wordTrace_append hprefix tailTrace_2431567
  have hstable : (prefixWord ++ tailWord_2431567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431567).length < 2 ^ (prefixWord ++ tailWord_2431567).sum := by decide
  have hdescent : baseEnd_2431567 < baseStart_2431567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431593 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 1, 3, 5]
def baseStart_2431593 : Nat := 118140960795 + 2431593 * 2 ^ 59
def prefixEnd_2431593 : Nat := 4983230072969 + 3 ^ 40 * 2431593 * 2
def baseEnd_2431593 : Nat := 1248575965108210114904813

theorem tailTrace_2431593 : CollatzResearch.WordTrace tailWord_2431593 prefixEnd_2431593 1248575965108210114904813 := by
  unfold tailWord_2431593
  simp only [CollatzResearch.WordTrace]
  refine ⟨88687482679761318867139433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59124988453174212578092955 88687482679761318867139433)
  ·
    refine ⟨66515612009820989150354575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88687482679761318867139433 66515612009820989150354575)
    ·
      refine ⟨99773418014731483725531863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66515612009820989150354575 99773418014731483725531863)
      ·
        refine ⟨149660127022097225588297795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99773418014731483725531863 149660127022097225588297795)
        ·
          refine ⟨224490190533145838382446693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149660127022097225588297795 224490190533145838382446693)
          ·
            refine ⟨42091910724964844696708755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 224490190533145838382446693 42091910724964844696708755)
            ·
              refine ⟨63137866087447267045063133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42091910724964844696708755 63137866087447267045063133)
              ·
                refine ⟨23676699782792725141898675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63137866087447267045063133 23676699782792725141898675)
                ·
                  refine ⟨35515049674189087712848013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23676699782792725141898675 35515049674189087712848013)
                  ·
                    refine ⟨13318143627820907892318005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35515049674189087712848013 13318143627820907892318005)
                    ·
                      refine ⟨1248575965108210114904813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13318143627820907892318005 1248575965108210114904813)
                      ·
                        rfl

theorem cell23_2431593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 3, 5].length) (baseStart_2431593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431593 prefixEnd_2431593 := by exact prefixLift 2431593
  have htrace : WordTrace (prefixWord ++ tailWord_2431593) baseStart_2431593 baseEnd_2431593 := by
    simpa [prefixWord, tailWord_2431593, baseEnd_2431593] using wordTrace_append hprefix tailTrace_2431593
  have hstable : (prefixWord ++ tailWord_2431593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431593).length < 2 ^ (prefixWord ++ tailWord_2431593).sum := by decide
  have hdescent : baseEnd_2431593 < baseStart_2431593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431594 : List Nat := [3, 1, 3, 2, 1, 1, 3, 3, 1, 3, 2]
def baseStart_2431594 : Nat := 118140960795 + 2431594 * 2 ^ 59
def prefixEnd_2431594 : Nat := 4983230072969 + 3 ^ 40 * 2431594 * 2
def baseEnd_2431594 : Nat := 1248576478588864610992309

theorem tailTrace_2431594 : CollatzResearch.WordTrace tailWord_2431594 prefixEnd_2431594 1248576478588864610992309 := by
  unfold tailWord_2431594
  simp only [CollatzResearch.WordTrace]
  refine ⟨22171879788189424009481459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59125012768505130691950557 22171879788189424009481459)
  ·
    refine ⟨33257819682284136014222189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22171879788189424009481459 33257819682284136014222189)
    ·
      refine ⟨12471682380856551005333321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33257819682284136014222189 12471682380856551005333321)
      ·
        refine ⟨9353761785642413253999991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12471682380856551005333321 9353761785642413253999991)
        ·
          refine ⟨14030642678463619880999987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9353761785642413253999991 14030642678463619880999987)
          ·
            refine ⟨21045964017695429821499981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14030642678463619880999987 21045964017695429821499981)
            ·
              refine ⟨7892236506635786183062493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21045964017695429821499981 7892236506635786183062493)
              ·
                refine ⟨2959588689988419818648435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7892236506635786183062493 2959588689988419818648435)
                ·
                  refine ⟨4439383034982629727972653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2959588689988419818648435 4439383034982629727972653)
                  ·
                    refine ⟨1664768638118486147989745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4439383034982629727972653 1664768638118486147989745)
                    ·
                      refine ⟨1248576478588864610992309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1664768638118486147989745 1248576478588864610992309)
                      ·
                        rfl

theorem cell23_2431594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_2431594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431594 prefixEnd_2431594 := by exact prefixLift 2431594
  have htrace : WordTrace (prefixWord ++ tailWord_2431594) baseStart_2431594 baseEnd_2431594 := by
    simpa [prefixWord, tailWord_2431594, baseEnd_2431594] using wordTrace_append hprefix tailTrace_2431594
  have hstable : (prefixWord ++ tailWord_2431594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431594).length < 2 ^ (prefixWord ++ tailWord_2431594).sum := by decide
  have hdescent : baseEnd_2431594 < baseStart_2431594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431630 : List Nat := [4, 1, 1, 3, 1, 1, 1, 4, 7]
def baseStart_2431630 : Nat := 118140960795 + 2431630 * 2 ^ 59
def prefixEnd_2431630 : Nat := 4983230072969 + 3 ^ 40 * 2431630 * 2
def baseEnd_2431630 : Nat := 138732773765825163349127

theorem tailTrace_2431630 : CollatzResearch.WordTrace tailWord_2431630 prefixEnd_2431630 138732773765825163349127 := by
  unfold tailWord_2431630
  simp only [CollatzResearch.WordTrace]
  refine ⟨11086104022578409273279543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59125888120418182790824229 11086104022578409273279543)
  ·
    refine ⟨16629156033867613909919315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11086104022578409273279543 16629156033867613909919315)
    ·
      refine ⟨24943734050801420864878973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16629156033867613909919315 24943734050801420864878973)
      ·
        refine ⟨9353900269050532824329615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24943734050801420864878973 9353900269050532824329615)
        ·
          refine ⟨14030850403575799236494423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9353900269050532824329615 14030850403575799236494423)
          ·
            refine ⟨21046275605363698854741635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14030850403575799236494423 21046275605363698854741635)
            ·
              refine ⟨31569413408045548282112453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21046275605363698854741635 31569413408045548282112453)
              ·
                refine ⟨5919265014008540302896085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31569413408045548282112453 5919265014008540302896085)
                ·
                  refine ⟨138732773765825163349127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5919265014008540302896085 138732773765825163349127)
                  ·
                    rfl

theorem cell23_2431630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 7].length) (baseStart_2431630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431630 prefixEnd_2431630 := by exact prefixLift 2431630
  have htrace : WordTrace (prefixWord ++ tailWord_2431630) baseStart_2431630 baseEnd_2431630 := by
    simpa [prefixWord, tailWord_2431630, baseEnd_2431630] using wordTrace_append hprefix tailTrace_2431630
  have hstable : (prefixWord ++ tailWord_2431630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431630).length < 2 ^ (prefixWord ++ tailWord_2431630).sum := by decide
  have hdescent : baseEnd_2431630 < baseStart_2431630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431633 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 6]
def baseStart_2431633 : Nat := 118140960795 + 2431633 * 2 ^ 59
def prefixEnd_2431633 : Nat := 4983230072969 + 3 ^ 40 * 2431633 * 2
def baseEnd_2431633 : Nat := 1248596504334389958404629

theorem tailTrace_2431633 : CollatzResearch.WordTrace tailWord_2431633 prefixEnd_2431633 1248596504334389958404629 := by
  unfold tailWord_2431633
  simp only [CollatzResearch.WordTrace]
  refine ⟨88688941599616405698595553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59125961066410937132397035 88688941599616405698595553)
  ·
    refine ⟨66516706199712304273946665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88688941599616405698595553 66516706199712304273946665)
    ·
      refine ⟨49887529649784228205459999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66516706199712304273946665 49887529649784228205459999)
      ·
        refine ⟨74831294474676342308189999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49887529649784228205459999 74831294474676342308189999)
        ·
          refine ⟨112246941712014513462284999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74831294474676342308189999 112246941712014513462284999)
          ·
            refine ⟨168370412568021770193427499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112246941712014513462284999 168370412568021770193427499)
            ·
              refine ⟨252555618852032655290141249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168370412568021770193427499 252555618852032655290141249)
              ·
                refine ⟨189416714139024491467605937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252555618852032655290141249 189416714139024491467605937)
                ·
                  refine ⟨142062535604268368600704453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189416714139024491467605937 142062535604268368600704453)
                  ·
                    refine ⟨26636725425800319112632085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 142062535604268368600704453 26636725425800319112632085)
                    ·
                      refine ⟨1248596504334389958404629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26636725425800319112632085 1248596504334389958404629)
                      ·
                        rfl

theorem cell23_2431633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_2431633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431633 prefixEnd_2431633 := by exact prefixLift 2431633
  have htrace : WordTrace (prefixWord ++ tailWord_2431633) baseStart_2431633 baseEnd_2431633 := by
    simpa [prefixWord, tailWord_2431633, baseEnd_2431633] using wordTrace_append hprefix tailTrace_2431633
  have hstable : (prefixWord ++ tailWord_2431633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431633).length < 2 ^ (prefixWord ++ tailWord_2431633).sum := by decide
  have hdescent : baseEnd_2431633 < baseStart_2431633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431697 : List Nat := [1, 2, 2, 1, 2, 3, 4, 1, 2, 1, 4]
def baseStart_2431697 : Nat := 118140960795 + 2431697 * 2 ^ 59
def prefixEnd_2431697 : Nat := 4983230072969 + 3 ^ 40 * 2431697 * 2
def baseEnd_2431697 : Nat := 1248629367096277708004335

theorem tailTrace_2431697 : CollatzResearch.WordTrace tailWord_2431697 prefixEnd_2431697 1248629367096277708004335 := by
  unfold tailWord_2431697
  simp only [CollatzResearch.WordTrace]
  refine ⟨88691275871384544628925345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59127517247589696419283563 88691275871384544628925345)
  ·
    refine ⟨66518456903538408471694009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88691275871384544628925345 66518456903538408471694009)
    ·
      refine ⟨49888842677653806353770507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66518456903538408471694009 49888842677653806353770507)
      ·
        refine ⟨74833264016480709530655761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49888842677653806353770507 74833264016480709530655761)
        ·
          refine ⟨56124948012360532147991821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74833264016480709530655761 56124948012360532147991821)
          ·
            refine ⟨21046855504635199555496933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56124948012360532147991821 21046855504635199555496933)
            ·
              refine ⟨3946285407119099916655675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21046855504635199555496933 3946285407119099916655675)
              ·
                refine ⟨5919428110678649874983513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3946285407119099916655675 5919428110678649874983513)
                ·
                  refine ⟨4439571083008987406237635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5919428110678649874983513 4439571083008987406237635)
                  ·
                    refine ⟨6659356624513481109356453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4439571083008987406237635 6659356624513481109356453)
                    ·
                      refine ⟨1248629367096277708004335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6659356624513481109356453 1248629367096277708004335)
                      ·
                        rfl

theorem cell23_2431697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 1, 4].length) (baseStart_2431697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431697 prefixEnd_2431697 := by exact prefixLift 2431697
  have htrace : WordTrace (prefixWord ++ tailWord_2431697) baseStart_2431697 baseEnd_2431697 := by
    simpa [prefixWord, tailWord_2431697, baseEnd_2431697] using wordTrace_append hprefix tailTrace_2431697
  have hstable : (prefixWord ++ tailWord_2431697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431697).length < 2 ^ (prefixWord ++ tailWord_2431697).sum := by decide
  have hdescent : baseEnd_2431697 < baseStart_2431697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431751 : List Nat := [1, 1, 4, 4, 1, 3, 1, 1, 2, 2, 3]
def baseStart_2431751 : Nat := 118140960795 + 2431751 * 2 ^ 59
def prefixEnd_2431751 : Nat := 4983230072969 + 3 ^ 40 * 2431751 * 2
def baseEnd_2431751 : Nat := 1248657095051620496729087

theorem tailTrace_2431751 : CollatzResearch.WordTrace tailWord_2431751 prefixEnd_2431751 1248657095051620496729087 := by
  unfold tailWord_2431751
  simp only [CollatzResearch.WordTrace]
  refine ⟨88693245413188911851391107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59128830275459274567594071 88693245413188911851391107)
  ·
    refine ⟨133039868119783367777086661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88693245413188911851391107 133039868119783367777086661)
    ·
      refine ⟨24944975272459381458203749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133039868119783367777086661 24944975272459381458203749)
      ·
        refine ⟨4677182863586134023413203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24944975272459381458203749 4677182863586134023413203)
        ·
          refine ⟨7015774295379201035119805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4677182863586134023413203 7015774295379201035119805)
          ·
            refine ⟨2630915360767200388169927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7015774295379201035119805 2630915360767200388169927)
            ·
              refine ⟨3946373041150800582254891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2630915360767200388169927 3946373041150800582254891)
              ·
                refine ⟨5919559561726200873382337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3946373041150800582254891 5919559561726200873382337)
                ·
                  refine ⟨4439669671294650655036753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5919559561726200873382337 4439669671294650655036753)
                  ·
                    refine ⟨3329752253470987991277565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4439669671294650655036753 3329752253470987991277565)
                    ·
                      refine ⟨1248657095051620496729087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3329752253470987991277565 1248657095051620496729087)
                      ·
                        rfl

theorem cell23_2431751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_2431751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431751 prefixEnd_2431751 := by exact prefixLift 2431751
  have htrace : WordTrace (prefixWord ++ tailWord_2431751) baseStart_2431751 baseEnd_2431751 := by
    simpa [prefixWord, tailWord_2431751, baseEnd_2431751] using wordTrace_append hprefix tailTrace_2431751
  have hstable : (prefixWord ++ tailWord_2431751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431751).length < 2 ^ (prefixWord ++ tailWord_2431751).sum := by decide
  have hdescent : baseEnd_2431751 < baseStart_2431751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431781 : List Nat := [1, 3, 1, 2, 3, 1, 1, 6, 1, 1, 3]
def baseStart_2431781 : Nat := 118140960795 + 2431781 * 2 ^ 59
def prefixEnd_2431781 : Nat := 4983230072969 + 3 ^ 40 * 2431781 * 2
def baseEnd_2431781 : Nat := 1248672499471255379353949

theorem tailTrace_2431781 : CollatzResearch.WordTrace tailWord_2431781 prefixEnd_2431781 1248672499471255379353949 := by
  unfold tailWord_2431781
  simp only [CollatzResearch.WordTrace]
  refine ⟨88694339603080226974983197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59129559735386817983322131 88694339603080226974983197)
  ·
    refine ⟨33260377351155085115618699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88694339603080226974983197 33260377351155085115618699)
    ·
      refine ⟨49890566026732627673428049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33260377351155085115618699 49890566026732627673428049)
      ·
        refine ⟨37417924520049470755071037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49890566026732627673428049 37417924520049470755071037)
        ·
          refine ⟨14031721695018551533151639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37417924520049470755071037 14031721695018551533151639)
          ·
            refine ⟨21047582542527827299727459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14031721695018551533151639 21047582542527827299727459)
            ·
              refine ⟨31571373813791740949591189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21047582542527827299727459 31571373813791740949591189)
              ·
                refine ⟨1479908147521487857012087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31571373813791740949591189 1479908147521487857012087)
                ·
                  refine ⟨2219862221282231785518131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1479908147521487857012087 2219862221282231785518131)
                  ·
                    refine ⟨3329793331923347678277197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2219862221282231785518131 3329793331923347678277197)
                    ·
                      refine ⟨1248672499471255379353949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3329793331923347678277197 1248672499471255379353949)
                      ·
                        rfl

theorem cell23_2431781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6, 1, 1, 3].length) (baseStart_2431781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431781 prefixEnd_2431781 := by exact prefixLift 2431781
  have htrace : WordTrace (prefixWord ++ tailWord_2431781) baseStart_2431781 baseEnd_2431781 := by
    simpa [prefixWord, tailWord_2431781, baseEnd_2431781] using wordTrace_append hprefix tailTrace_2431781
  have hstable : (prefixWord ++ tailWord_2431781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431781).length < 2 ^ (prefixWord ++ tailWord_2431781).sum := by decide
  have hdescent : baseEnd_2431781 < baseStart_2431781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431787 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 2, 6, 2]
def baseStart_2431787 : Nat := 118140960795 + 2431787 * 2 ^ 59
def prefixEnd_2431787 : Nat := 4983230072969 + 3 ^ 40 * 2431787 * 2
def baseEnd_2431787 : Nat := 1248675580355182355878921

theorem tailTrace_2431787 : CollatzResearch.WordTrace tailWord_2431787 prefixEnd_2431787 1248675580355182355878921 := by
  unfold tailWord_2431787
  simp only [CollatzResearch.WordTrace]
  refine ⟨88694558441058489999701615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59129705627372326666467743 88694558441058489999701615)
  ·
    refine ⟨133041837661587734999552423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88694558441058489999701615 133041837661587734999552423)
    ·
      refine ⟨199562756492381602499328635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133041837661587734999552423 199562756492381602499328635)
      ·
        refine ⟨299344134738572403748992953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199562756492381602499328635 299344134738572403748992953)
        ·
          refine ⟨224508101053929302811744715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 299344134738572403748992953 224508101053929302811744715)
          ·
            refine ⟨336762151580893954217617073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224508101053929302811744715 336762151580893954217617073)
            ·
              refine ⟨252571613685670465663212805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 336762151580893954217617073 252571613685670465663212805)
              ·
                refine ⟨47357177566063212311852401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 252571613685670465663212805 47357177566063212311852401)
                ·
                  refine ⟨35517883174547409233889301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47357177566063212311852401 35517883174547409233889301)
                  ·
                    refine ⟨1664900773806909807838561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35517883174547409233889301 1664900773806909807838561)
                    ·
                      refine ⟨1248675580355182355878921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1664900773806909807838561 1248675580355182355878921)
                      ·
                        rfl

theorem cell23_2431787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 6, 2].length) (baseStart_2431787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431787 prefixEnd_2431787 := by exact prefixLift 2431787
  have htrace : WordTrace (prefixWord ++ tailWord_2431787) baseStart_2431787 baseEnd_2431787 := by
    simpa [prefixWord, tailWord_2431787, baseEnd_2431787] using wordTrace_append hprefix tailTrace_2431787
  have hstable : (prefixWord ++ tailWord_2431787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431787).length < 2 ^ (prefixWord ++ tailWord_2431787).sum := by decide
  have hdescent : baseEnd_2431787 < baseStart_2431787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431824 : List Nat := [2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 3]
def baseStart_2431824 : Nat := 118140960795 + 2431824 * 2 ^ 59
def prefixEnd_2431824 : Nat := 4983230072969 + 3 ^ 40 * 2431824 * 2
def baseEnd_2431824 : Nat := 1248694579139398711116251

theorem tailTrace_2431824 : CollatzResearch.WordTrace tailWord_2431824 prefixEnd_2431824 1248694579139398711116251 := by
  unfold tailWord_2431824
  simp only [CollatzResearch.WordTrace]
  refine ⟨44347953970962222659399263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59130605294616296879199017 44347953970962222659399263)
  ·
    refine ⟨66521930956443333989098895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44347953970962222659399263 66521930956443333989098895)
    ·
      refine ⟨99782896434665000983648343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66521930956443333989098895 99782896434665000983648343)
      ·
        refine ⟨149674344651997501475472515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99782896434665000983648343 149674344651997501475472515)
        ·
          refine ⟨224511516977996252213208773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149674344651997501475472515 224511516977996252213208773)
          ·
            refine ⟨42095909433374297289976645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 224511516977996252213208773 42095909433374297289976645)
            ·
              refine ⟨7892983018757680741870621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42095909433374297289976645 7892983018757680741870621)
              ·
                refine ⟨2959868632034130278201483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7892983018757680741870621 2959868632034130278201483)
                ·
                  refine ⟨4439802948051195417302225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2959868632034130278201483 4439802948051195417302225)
                  ·
                    refine ⟨3329852211038396562976669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4439802948051195417302225 3329852211038396562976669)
                    ·
                      refine ⟨1248694579139398711116251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3329852211038396562976669 1248694579139398711116251)
                      ·
                        rfl

theorem cell23_2431824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 3].length) (baseStart_2431824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431824 prefixEnd_2431824 := by exact prefixLift 2431824
  have htrace : WordTrace (prefixWord ++ tailWord_2431824) baseStart_2431824 baseEnd_2431824 := by
    simpa [prefixWord, tailWord_2431824, baseEnd_2431824] using wordTrace_append hprefix tailTrace_2431824
  have hstable : (prefixWord ++ tailWord_2431824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431824).length < 2 ^ (prefixWord ++ tailWord_2431824).sum := by decide
  have hdescent : baseEnd_2431824 < baseStart_2431824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431848 : List Nat := [2, 1, 4, 2, 1, 4, 2, 1, 2, 4]
def baseStart_2431848 : Nat := 118140960795 + 2431848 * 2 ^ 59
def prefixEnd_2431848 : Nat := 4983230072969 + 3 ^ 40 * 2431848 * 2
def baseEnd_2431848 : Nat := 416235634225035539072047

theorem tailTrace_2431848 : CollatzResearch.WordTrace tailWord_2431848 prefixEnd_2431848 416235634225035539072047 := by
  unfold tailWord_2431848
  simp only [CollatzResearch.WordTrace]
  refine ⟨44348391646918748708836099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59131188862558331611781465 44348391646918748708836099)
  ·
    refine ⟨66522587470378123063254149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44348391646918748708836099 66522587470378123063254149)
    ·
      refine ⟨12472985150695898074360153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66522587470378123063254149 12472985150695898074360153)
      ·
        refine ⟨9354738863021923555770115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12472985150695898074360153 9354738863021923555770115)
        ·
          refine ⟨14032108294532885333655173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9354738863021923555770115 14032108294532885333655173)
          ·
            refine ⟨2631020305224916000060345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14032108294532885333655173 2631020305224916000060345)
            ·
              refine ⟨1973265228918687000045259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2631020305224916000060345 1973265228918687000045259)
              ·
                refine ⟨2959897843378030500067889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1973265228918687000045259 2959897843378030500067889)
                ·
                  refine ⟨2219923382533522875050917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2959897843378030500067889 2219923382533522875050917)
                  ·
                    refine ⟨416235634225035539072047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2219923382533522875050917 416235634225035539072047)
                    ·
                      rfl

theorem cell23_2431848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_2431848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431848 prefixEnd_2431848 := by exact prefixLift 2431848
  have htrace : WordTrace (prefixWord ++ tailWord_2431848) baseStart_2431848 baseEnd_2431848 := by
    simpa [prefixWord, tailWord_2431848, baseEnd_2431848] using wordTrace_append hprefix tailTrace_2431848
  have hstable : (prefixWord ++ tailWord_2431848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431848).length < 2 ^ (prefixWord ++ tailWord_2431848).sum := by decide
  have hdescent : baseEnd_2431848 < baseStart_2431848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431907 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 4]
def baseStart_2431907 : Nat := 118140960795 + 2431907 * 2 ^ 59
def prefixEnd_2431907 : Nat := 4983230072969 + 3 ^ 40 * 2431907 * 2
def baseEnd_2431907 : Nat := 1248737198033721886378369

theorem tailTrace_2431907 : CollatzResearch.WordTrace tailWord_2431907 prefixEnd_2431907 1248737198033721886378369 := by
  unfold tailWord_2431907
  simp only [CollatzResearch.WordTrace]
  refine ⟨88698935200623750494069975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59132623467082500329379983 88698935200623750494069975)
  ·
    refine ⟨133048402800935625741104963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88698935200623750494069975 133048402800935625741104963)
    ·
      refine ⟨199572604201403438611657445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133048402800935625741104963 199572604201403438611657445)
      ·
        refine ⟨37419863287763144739685771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 199572604201403438611657445 37419863287763144739685771)
        ·
          refine ⟨56129794931644717109528657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37419863287763144739685771 56129794931644717109528657)
          ·
            refine ⟨42097346198733537832146493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56129794931644717109528657 42097346198733537832146493)
            ·
              refine ⟨15786504824525076687054935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42097346198733537832146493 15786504824525076687054935)
              ·
                refine ⟨23679757236787615030582403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15786504824525076687054935 23679757236787615030582403)
                ·
                  refine ⟨35519635855181422545873605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23679757236787615030582403 35519635855181422545873605)
                  ·
                    refine ⟨6659931722846516727351301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35519635855181422545873605 6659931722846516727351301)
                    ·
                      refine ⟨1248737198033721886378369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6659931722846516727351301 1248737198033721886378369)
                      ·
                        rfl

theorem cell23_2431907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_2431907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431907 prefixEnd_2431907 := by exact prefixLift 2431907
  have htrace : WordTrace (prefixWord ++ tailWord_2431907) baseStart_2431907 baseEnd_2431907 := by
    simpa [prefixWord, tailWord_2431907, baseEnd_2431907] using wordTrace_append hprefix tailTrace_2431907
  have hstable : (prefixWord ++ tailWord_2431907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431907).length < 2 ^ (prefixWord ++ tailWord_2431907).sum := by decide
  have hdescent : baseEnd_2431907 < baseStart_2431907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431926 : List Nat := [5, 1, 4, 1, 2, 1, 2, 1, 1, 2, 3]
def baseStart_2431926 : Nat := 118140960795 + 2431926 * 2 ^ 59
def prefixEnd_2431926 : Nat := 4983230072969 + 3 ^ 40 * 2431926 * 2
def baseEnd_2431926 : Nat := 1248746954166157312040783

theorem tailTrace_2431926 : CollatzResearch.WordTrace tailWord_2431926 prefixEnd_2431926 1248746954166157312040783 := by
  unfold tailWord_2431926
  simp only [CollatzResearch.WordTrace]
  refine ⟨5543726761722182296188227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59133085458369944492674421 5543726761722182296188227)
  ·
    refine ⟨8315590142583273444282341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5543726761722182296188227 8315590142583273444282341)
    ·
      refine ⟨1559173151734363770802939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8315590142583273444282341 1559173151734363770802939)
      ·
        refine ⟨2338759727601545656204409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1559173151734363770802939 2338759727601545656204409)
        ·
          refine ⟨1754069795701159242153307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2338759727601545656204409 1754069795701159242153307)
          ·
            refine ⟨2631104693551738863229961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1754069795701159242153307 2631104693551738863229961)
            ·
              refine ⟨1973328520163804147422471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2631104693551738863229961 1973328520163804147422471)
              ·
                refine ⟨2959992780245706221133707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1973328520163804147422471 2959992780245706221133707)
                ·
                  refine ⟨4439989170368559331700561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2959992780245706221133707 4439989170368559331700561)
                  ·
                    refine ⟨3329991877776419498775421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4439989170368559331700561 3329991877776419498775421)
                    ·
                      refine ⟨1248746954166157312040783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3329991877776419498775421 1248746954166157312040783)
                      ·
                        rfl

theorem cell23_2431926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_2431926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431926 prefixEnd_2431926 := by exact prefixLift 2431926
  have htrace : WordTrace (prefixWord ++ tailWord_2431926) baseStart_2431926 baseEnd_2431926 := by
    simpa [prefixWord, tailWord_2431926, baseEnd_2431926] using wordTrace_append hprefix tailTrace_2431926
  have hstable : (prefixWord ++ tailWord_2431926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431926).length < 2 ^ (prefixWord ++ tailWord_2431926).sum := by decide
  have hdescent : baseEnd_2431926 < baseStart_2431926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431984 : List Nat := [2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 4]
def baseStart_2431984 : Nat := 118140960795 + 2431984 * 2 ^ 59
def prefixEnd_2431984 : Nat := 4983230072969 + 3 ^ 40 * 2431984 * 2
def baseEnd_2431984 : Nat := 1248776736044118085115515

theorem tailTrace_2431984 : CollatzResearch.WordTrace tailWord_2431984 prefixEnd_2431984 1248776736044118085115515 := by
  unfold tailWord_2431984
  simp only [CollatzResearch.WordTrace]
  refine ⟨44350871810672396322311503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59134495747563195096415337 44350871810672396322311503)
  ·
    refine ⟨66526307716008594483467255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44350871810672396322311503 66526307716008594483467255)
    ·
      refine ⟨99789461574012891725200883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66526307716008594483467255 99789461574012891725200883)
      ·
        refine ⟨149684192361019337587801325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99789461574012891725200883 149684192361019337587801325)
        ·
          refine ⟨56131572135382251595425497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149684192361019337587801325 56131572135382251595425497)
          ·
            refine ⟨42098679101536688696569123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56131572135382251595425497 42098679101536688696569123)
            ·
              refine ⟨63148018652305033044853685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42098679101536688696569123 63148018652305033044853685)
              ·
                refine ⟨5920126748653596847955033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63148018652305033044853685 5920126748653596847955033)
                ·
                  refine ⟨4440095061490197635966275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5920126748653596847955033 4440095061490197635966275)
                  ·
                    refine ⟨6660142592235296453949413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4440095061490197635966275 6660142592235296453949413)
                    ·
                      refine ⟨1248776736044118085115515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6660142592235296453949413 1248776736044118085115515)
                      ·
                        rfl

theorem cell23_2431984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 4].length) (baseStart_2431984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431984 prefixEnd_2431984 := by exact prefixLift 2431984
  have htrace : WordTrace (prefixWord ++ tailWord_2431984) baseStart_2431984 baseEnd_2431984 := by
    simpa [prefixWord, tailWord_2431984, baseEnd_2431984] using wordTrace_append hprefix tailTrace_2431984
  have hstable : (prefixWord ++ tailWord_2431984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431984).length < 2 ^ (prefixWord ++ tailWord_2431984).sum := by decide
  have hdescent : baseEnd_2431984 < baseStart_2431984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431987 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 5]
def baseStart_2431987 : Nat := 118140960795 + 2431987 * 2 ^ 59
def prefixEnd_2431987 : Nat := 4983230072969 + 3 ^ 40 * 2431987 * 2
def baseEnd_2431987 : Nat := 1248778276486081573378001

theorem tailTrace_2431987 : CollatzResearch.WordTrace tailWord_2431987 prefixEnd_2431987 1248778276486081573378001 := by
  unfold tailWord_2431987
  simp only [CollatzResearch.WordTrace]
  refine ⟨88701853040333924156982215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59134568693555949437988143 88701853040333924156982215)
  ·
    refine ⟨133052779560500886235473323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88701853040333924156982215 133052779560500886235473323)
    ·
      refine ⟨199579169340751329353209985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133052779560500886235473323 199579169340751329353209985)
      ·
        refine ⟨149684377005563497014907489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199579169340751329353209985 149684377005563497014907489)
        ·
          refine ⟨112263282754172622761180617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149684377005563497014907489 112263282754172622761180617)
          ·
            refine ⟨84197462065629467070885463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112263282754172622761180617 84197462065629467070885463)
            ·
              refine ⟨126296193098444200606328195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84197462065629467070885463 126296193098444200606328195)
              ·
                refine ⟨189444289647666300909492293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126296193098444200606328195 189444289647666300909492293)
                ·
                  refine ⟨35520804308937431420529805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 189444289647666300909492293 35520804308937431420529805)
                  ·
                    refine ⟨13320301615851536782698677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35520804308937431420529805 13320301615851536782698677)
                    ·
                      refine ⟨1248778276486081573378001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13320301615851536782698677 1248778276486081573378001)
                      ·
                        rfl

theorem cell23_2431987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 5].length) (baseStart_2431987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431987 prefixEnd_2431987 := by exact prefixLift 2431987
  have htrace : WordTrace (prefixWord ++ tailWord_2431987) baseStart_2431987 baseEnd_2431987 := by
    simpa [prefixWord, tailWord_2431987, baseEnd_2431987] using wordTrace_append hprefix tailTrace_2431987
  have hstable : (prefixWord ++ tailWord_2431987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431987).length < 2 ^ (prefixWord ++ tailWord_2431987).sum := by decide
  have hdescent : baseEnd_2431987 < baseStart_2431987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431994 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 5, 4]
def baseStart_2431994 : Nat := 118140960795 + 2431994 * 2 ^ 59
def prefixEnd_2431994 : Nat := 4983230072969 + 3 ^ 40 * 2431994 * 2
def baseEnd_2431994 : Nat := 416260623616887681996823

theorem tailTrace_2431994 : CollatzResearch.WordTrace tailWord_2431994 prefixEnd_2431994 416260623616887681996823 := by
  unfold tailWord_2431994
  simp only [CollatzResearch.WordTrace]
  refine ⟨22175527087827141088121759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59134738900872376234991357 22175527087827141088121759)
  ·
    refine ⟨33263290631740711632182639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22175527087827141088121759 33263290631740711632182639)
    ·
      refine ⟨49894935947611067448273959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33263290631740711632182639 49894935947611067448273959)
      ·
        refine ⟨74842403921416601172410939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49894935947611067448273959 74842403921416601172410939)
        ·
          refine ⟨112263605882124901758616409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74842403921416601172410939 112263605882124901758616409)
          ·
            refine ⟨84197704411593676318962307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112263605882124901758616409 84197704411593676318962307)
            ·
              refine ⟨126296556617390514478443461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84197704411593676318962307 126296556617390514478443461)
              ·
                refine ⟨23680604365760721464708149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126296556617390514478443461 23680604365760721464708149)
                ·
                  refine ⟨2220056659290067637316389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23680604365760721464708149 2220056659290067637316389)
                  ·
                    refine ⟨416260623616887681996823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2220056659290067637316389 416260623616887681996823)
                    ·
                      rfl

theorem cell23_2431994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 5, 4].length) (baseStart_2431994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431994 prefixEnd_2431994 := by exact prefixLift 2431994
  have htrace : WordTrace (prefixWord ++ tailWord_2431994) baseStart_2431994 baseEnd_2431994 := by
    simpa [prefixWord, tailWord_2431994, baseEnd_2431994] using wordTrace_append hprefix tailTrace_2431994
  have hstable : (prefixWord ++ tailWord_2431994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431994).length < 2 ^ (prefixWord ++ tailWord_2431994).sum := by decide
  have hdescent : baseEnd_2431994 < baseStart_2431994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2431998 : List Nat := [4, 2, 2, 2, 2, 1, 1, 2, 2, 5]
def baseStart_2431998 : Nat := 118140960795 + 2431998 * 2 ^ 59
def prefixEnd_2431998 : Nat := 4983230072969 + 3 ^ 40 * 2431998 * 2
def baseEnd_2431998 : Nat := 416261308257760343446817

theorem tailTrace_2431998 : CollatzResearch.WordTrace tailWord_2431998 prefixEnd_2431998 416261308257760343446817 := by
  unfold tailWord_2431998
  simp only [CollatzResearch.WordTrace]
  refine ⟨11087781780411759129454081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59134836162196048690421765 11087781780411759129454081)
  ·
    refine ⟨8315836335308819347090561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11087781780411759129454081 8315836335308819347090561)
    ·
      refine ⟨6236877251481614510317921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8315836335308819347090561 6236877251481614510317921)
      ·
        refine ⟨4677657938611210882738441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6236877251481614510317921 4677657938611210882738441)
        ·
          refine ⟨3508243453958408162053831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4677657938611210882738441 3508243453958408162053831)
          ·
            refine ⟨5262365180937612243080747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3508243453958408162053831 5262365180937612243080747)
            ·
              refine ⟨7893547771406418364621121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5262365180937612243080747 7893547771406418364621121)
              ·
                refine ⟨5920160828554813773465841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7893547771406418364621121 5920160828554813773465841)
                ·
                  refine ⟨4440120621416110330099381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5920160828554813773465841 4440120621416110330099381)
                  ·
                    refine ⟨416261308257760343446817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4440120621416110330099381 416261308257760343446817)
                    ·
                      rfl

theorem cell23_2431998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_2431998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2431998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2431998 prefixEnd_2431998 := by exact prefixLift 2431998
  have htrace : WordTrace (prefixWord ++ tailWord_2431998) baseStart_2431998 baseEnd_2431998 := by
    simpa [prefixWord, tailWord_2431998, baseEnd_2431998] using wordTrace_append hprefix tailTrace_2431998
  have hstable : (prefixWord ++ tailWord_2431998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2431998).length < 2 ^ (prefixWord ++ tailWord_2431998).sum := by decide
  have hdescent : baseEnd_2431998 < baseStart_2431998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2431998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432001 : List Nat := [1, 2, 4, 1, 2, 3, 1, 2, 2, 1, 4]
def baseStart_2432001 : Nat := 118140960795 + 2432001 * 2 ^ 59
def prefixEnd_2432001 : Nat := 4983230072969 + 3 ^ 40 * 2432001 * 2
def baseEnd_2432001 : Nat := 1248785465215244518602937

theorem tailTrace_2432001 : CollatzResearch.WordTrace tailWord_2432001 prefixEnd_2432001 1248785465215244518602937 := by
  unfold tailWord_2432001
  simp only [CollatzResearch.WordTrace]
  refine ⟨88702363662283204547991857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59134909108188803031994571 88702363662283204547991857)
  ·
    refine ⟨66526772746712403410993893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88702363662283204547991857 66526772746712403410993893)
    ·
      refine ⟨12473769890008575639561355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66526772746712403410993893 12473769890008575639561355)
      ·
        refine ⟨18710654835012863459342033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12473769890008575639561355 18710654835012863459342033)
        ·
          refine ⟨14032991126259647594506525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18710654835012863459342033 14032991126259647594506525)
          ·
            refine ⟨5262371672347367847939947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14032991126259647594506525 5262371672347367847939947)
            ·
              refine ⟨7893557508521051771909921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5262371672347367847939947 7893557508521051771909921)
              ·
                refine ⟨5920168131390788828932441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7893557508521051771909921 5920168131390788828932441)
                ·
                  refine ⟨4440126098543091621699331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5920168131390788828932441 4440126098543091621699331)
                  ·
                    refine ⟨6660189147814637432548997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4440126098543091621699331 6660189147814637432548997)
                    ·
                      refine ⟨1248785465215244518602937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6660189147814637432548997 1248785465215244518602937)
                      ·
                        rfl

theorem cell23_2432001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_2432001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432001 prefixEnd_2432001 := by exact prefixLift 2432001
  have htrace : WordTrace (prefixWord ++ tailWord_2432001) baseStart_2432001 baseEnd_2432001 := by
    simpa [prefixWord, tailWord_2432001, baseEnd_2432001] using wordTrace_append hprefix tailTrace_2432001
  have hstable : (prefixWord ++ tailWord_2432001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432001).length < 2 ^ (prefixWord ++ tailWord_2432001).sum := by decide
  have hdescent : baseEnd_2432001 < baseStart_2432001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432002 : List Nat := [3, 4, 1, 3, 1, 1, 3, 2, 5]
def baseStart_2432002 : Nat := 118140960795 + 2432002 * 2 ^ 59
def prefixEnd_2432002 : Nat := 4983230072969 + 3 ^ 40 * 2432002 * 2
def baseEnd_2432002 : Nat := 138753997632877668298937

theorem tailTrace_2432002 : CollatzResearch.WordTrace tailWord_2432002 prefixEnd_2432002 138753997632877668298937 := by
  unfold tailWord_2432002
  simp only [CollatzResearch.WordTrace]
  refine ⟨22175600033819895429694565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59134933423519721145852173 22175600033819895429694565)
  ·
    refine ⟨4157925006341230393067731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22175600033819895429694565 4157925006341230393067731)
    ·
      refine ⟨6236887509511845589601597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4157925006341230393067731 6236887509511845589601597)
      ·
        refine ⟨2338832816066942096100599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6236887509511845589601597 2338832816066942096100599)
        ·
          refine ⟨3508249224100413144150899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2338832816066942096100599 3508249224100413144150899)
          ·
            refine ⟨5262373836150619716226349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3508249224100413144150899 5262373836150619716226349)
            ·
              refine ⟨1973390188556482393584881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5262373836150619716226349 1973390188556482393584881)
              ·
                refine ⟨1480042641417361795188661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1973390188556482393584881 1480042641417361795188661)
                ·
                  refine ⟨138753997632877668298937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1480042641417361795188661 138753997632877668298937)
                  ·
                    rfl

theorem cell23_2432002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_2432002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432002 prefixEnd_2432002 := by exact prefixLift 2432002
  have htrace : WordTrace (prefixWord ++ tailWord_2432002) baseStart_2432002 baseEnd_2432002 := by
    simpa [prefixWord, tailWord_2432002, baseEnd_2432002] using wordTrace_append hprefix tailTrace_2432002
  have hstable : (prefixWord ++ tailWord_2432002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432002).length < 2 ^ (prefixWord ++ tailWord_2432002).sum := by decide
  have hdescent : baseEnd_2432002 < baseStart_2432002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432011 : List Nat := [1, 1, 1, 1, 6, 2, 3, 1, 3, 4]
def baseStart_2432011 : Nat := 118140960795 + 2432011 * 2 ^ 59
def prefixEnd_2432011 : Nat := 4983230072969 + 3 ^ 40 * 2432011 * 2
def baseEnd_2432011 : Nat := 416263533340596493159297

theorem tailTrace_2432011 : CollatzResearch.WordTrace tailWord_2432011 prefixEnd_2432011 416263533340596493159297 := by
  unfold tailWord_2432011
  simp only [CollatzResearch.WordTrace]
  refine ⟨88702728392246976255855887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59135152261497984170570591 88702728392246976255855887)
  ·
    refine ⟨133054092588370464383783831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88702728392246976255855887 133054092588370464383783831)
    ·
      refine ⟨199581138882555696575675747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133054092588370464383783831 199581138882555696575675747)
      ·
        refine ⟨299371708323833544863513621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199581138882555696575675747 299371708323833544863513621)
        ·
          refine ⟨14033048827679697415477201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 299371708323833544863513621 14033048827679697415477201)
          ·
            refine ⟨10524786620759773061607901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14033048827679697415477201 10524786620759773061607901)
            ·
              refine ⟨3946794982784914898102963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10524786620759773061607901 3946794982784914898102963)
              ·
                refine ⟨5920192474177372347154445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3946794982784914898102963 5920192474177372347154445)
                ·
                  refine ⟨2220072177816514630182917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5920192474177372347154445 2220072177816514630182917)
                  ·
                    refine ⟨416263533340596493159297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2220072177816514630182917 416263533340596493159297)
                    ·
                      rfl

theorem cell23_2432011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3, 4].length) (baseStart_2432011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432011 prefixEnd_2432011 := by exact prefixLift 2432011
  have htrace : WordTrace (prefixWord ++ tailWord_2432011) baseStart_2432011 baseEnd_2432011 := by
    simpa [prefixWord, tailWord_2432011, baseEnd_2432011] using wordTrace_append hprefix tailTrace_2432011
  have hstable : (prefixWord ++ tailWord_2432011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432011).length < 2 ^ (prefixWord ++ tailWord_2432011).sum := by decide
  have hdescent : baseEnd_2432011 < baseStart_2432011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432027 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 8]
def baseStart_2432027 : Nat := 118140960795 + 2432027 * 2 ^ 59
def prefixEnd_2432027 : Nat := 4983230072969 + 3 ^ 40 * 2432027 * 2
def baseEnd_2432027 : Nat := 1248798815712261416877817

theorem tailTrace_2432027 : CollatzResearch.WordTrace tailWord_2432027 prefixEnd_2432027 1248798815712261416877817 := by
  unfold tailWord_2432027
  simp only [CollatzResearch.WordTrace]
  refine ⟨88703311960189010988438335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59135541306792673992292223 88703311960189010988438335)
  ·
    refine ⟨133054967940283516482657503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88703311960189010988438335 133054967940283516482657503)
    ·
      refine ⟨199582451910425274723986255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133054967940283516482657503 199582451910425274723986255)
      ·
        refine ⟨299373677865637912085979383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199582451910425274723986255 299373677865637912085979383)
        ·
          refine ⟨449060516798456868128969075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299373677865637912085979383 449060516798456868128969075)
          ·
            refine ⟨673590775197685302193453613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449060516798456868128969075 673590775197685302193453613)
            ·
              refine ⟨252596540699131988322545105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 673590775197685302193453613 252596540699131988322545105)
              ·
                refine ⟨189447405524348991241908829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252596540699131988322545105 189447405524348991241908829)
                ·
                  refine ⟨71042777071630871715715811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189447405524348991241908829 71042777071630871715715811)
                  ·
                    refine ⟨106564165607446307573573717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71042777071630871715715811 106564165607446307573573717)
                    ·
                      refine ⟨1248798815712261416877817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 106564165607446307573573717 1248798815712261416877817)
                      ·
                        rfl

theorem cell23_2432027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 8].length) (baseStart_2432027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432027 prefixEnd_2432027 := by exact prefixLift 2432027
  have htrace : WordTrace (prefixWord ++ tailWord_2432027) baseStart_2432027 baseEnd_2432027 := by
    simpa [prefixWord, tailWord_2432027, baseEnd_2432027] using wordTrace_append hprefix tailTrace_2432027
  have hstable : (prefixWord ++ tailWord_2432027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432027).length < 2 ^ (prefixWord ++ tailWord_2432027).sum := by decide
  have hdescent : baseEnd_2432027 < baseStart_2432027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432062 : List Nat := [4, 2, 1, 3, 1, 1, 4, 2, 1, 4]
def baseStart_2432062 : Nat := 118140960795 + 2432062 * 2 ^ 59
def prefixEnd_2432062 : Nat := 4983230072969 + 3 ^ 40 * 2432062 * 2
def baseEnd_2432062 : Nat := 416272262511722926646719

theorem tailTrace_2432062 : CollatzResearch.WordTrace tailWord_2432062 prefixEnd_2432062 416272262511722926646719 := by
  unfold tailWord_2432062
  simp only [CollatzResearch.WordTrace]
  refine ⟨11088073564382776495745305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59136392343374807977308293 11088073564382776495745305)
  ·
    refine ⟨8316055173287082371808979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11088073564382776495745305 8316055173287082371808979)
    ·
      refine ⟨12474082759930623557713469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8316055173287082371808979 12474082759930623557713469)
      ·
        refine ⟨4677781034973983834142551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12474082759930623557713469 4677781034973983834142551)
        ·
          refine ⟨7016671552460975751213827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4677781034973983834142551 7016671552460975751213827)
          ·
            refine ⟨10525007328691463626820741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7016671552460975751213827 10525007328691463626820741)
            ·
              refine ⟨1973438874129649430028889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10525007328691463626820741 1973438874129649430028889)
              ·
                refine ⟨1480079155597237072521667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1973438874129649430028889 1480079155597237072521667)
                ·
                  refine ⟨2220118733395855608782501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1480079155597237072521667 2220118733395855608782501)
                  ·
                    refine ⟨416272262511722926646719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2220118733395855608782501 416272262511722926646719)
                    ·
                      rfl

theorem cell23_2432062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_2432062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432062 prefixEnd_2432062 := by exact prefixLift 2432062
  have htrace : WordTrace (prefixWord ++ tailWord_2432062) baseStart_2432062 baseEnd_2432062 := by
    simpa [prefixWord, tailWord_2432062, baseEnd_2432062] using wordTrace_append hprefix tailTrace_2432062
  have hstable : (prefixWord ++ tailWord_2432062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432062).length < 2 ^ (prefixWord ++ tailWord_2432062).sum := by decide
  have hdescent : baseEnd_2432062 < baseStart_2432062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432101 : List Nat := [1, 3, 1, 3, 2, 1, 2, 2, 4, 4]
def baseStart_2432101 : Nat := 118140960795 + 2432101 * 2 ^ 59
def prefixEnd_2432101 : Nat := 4983230072969 + 3 ^ 40 * 2432101 * 2
def baseEnd_2432101 : Nat := 416278937760231375784159

theorem tailTrace_2432101 : CollatzResearch.WordTrace tailWord_2432101 prefixEnd_2432101 416278937760231375784159 := by
  unfold tailWord_2432101
  simp only [CollatzResearch.WordTrace]
  refine ⟨88706010961920921626632157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59137340641280614417754771 88706010961920921626632157)
  ·
    refine ⟨33264754110720345609987059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88706010961920921626632157 33264754110720345609987059)
    ·
      refine ⟨49897131166080518414980589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33264754110720345609987059 49897131166080518414980589)
      ·
        refine ⟨18711424187280194405617721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49897131166080518414980589 18711424187280194405617721)
        ·
          refine ⟨14033568140460145804213291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18711424187280194405617721 14033568140460145804213291)
          ·
            refine ⟨21050352210690218706319937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14033568140460145804213291 21050352210690218706319937)
            ·
              refine ⟨15787764158017664029739953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21050352210690218706319937 15787764158017664029739953)
              ·
                refine ⟨11840823118513248022304965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15787764158017664029739953 11840823118513248022304965)
                ·
                  refine ⟨2220154334721234004182181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11840823118513248022304965 2220154334721234004182181)
                  ·
                    refine ⟨416278937760231375784159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2220154334721234004182181 416278937760231375784159)
                    ·
                      rfl

theorem cell23_2432101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4, 4].length) (baseStart_2432101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432101 prefixEnd_2432101 := by exact prefixLift 2432101
  have htrace : WordTrace (prefixWord ++ tailWord_2432101) baseStart_2432101 baseEnd_2432101 := by
    simpa [prefixWord, tailWord_2432101, baseEnd_2432101] using wordTrace_append hprefix tailTrace_2432101
  have hstable : (prefixWord ++ tailWord_2432101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432101).length < 2 ^ (prefixWord ++ tailWord_2432101).sum := by decide
  have hdescent : baseEnd_2432101 < baseStart_2432101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432108 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 5, 2, 2]
def baseStart_2432108 : Nat := 118140960795 + 2432108 * 2 ^ 59
def prefixEnd_2432108 : Nat := 4983230072969 + 3 ^ 40 * 2432108 * 2
def baseEnd_2432108 : Nat := 1248840407645275599964945

theorem tailTrace_2432108 : CollatzResearch.WordTrace tailWord_2432108 prefixEnd_2432108 1248840407645275599964945 := by
  unfold tailWord_2432108
  simp only [CollatzResearch.WordTrace]
  refine ⟨44353133136447780911068489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59137510848597041214757985 44353133136447780911068489)
  ·
    refine ⟨33264849852335835683301367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44353133136447780911068489 33264849852335835683301367)
    ·
      refine ⟨49897274778503753524952051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33264849852335835683301367 49897274778503753524952051)
      ·
        refine ⟨74845912167755630287428077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49897274778503753524952051 74845912167755630287428077)
        ·
          refine ⟨28067217062908361357785529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74845912167755630287428077 28067217062908361357785529)
          ·
            refine ⟨21050412797181271018339147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28067217062908361357785529 21050412797181271018339147)
            ·
              refine ⟨31575619195771906527508721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21050412797181271018339147 31575619195771906527508721)
              ·
                refine ⟨23681714396828929895631541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31575619195771906527508721 23681714396828929895631541)
                ·
                  refine ⟨2220160724702712177715457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23681714396828929895631541 2220160724702712177715457)
                  ·
                    refine ⟨1665120543527034133286593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2220160724702712177715457 1665120543527034133286593)
                    ·
                      refine ⟨1248840407645275599964945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1665120543527034133286593 1248840407645275599964945)
                      ·
                        rfl

theorem cell23_2432108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 2, 2].length) (baseStart_2432108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432108 prefixEnd_2432108 := by exact prefixLift 2432108
  have htrace : WordTrace (prefixWord ++ tailWord_2432108) baseStart_2432108 baseEnd_2432108 := by
    simpa [prefixWord, tailWord_2432108, baseEnd_2432108] using wordTrace_append hprefix tailTrace_2432108
  have hstable : (prefixWord ++ tailWord_2432108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432108).length < 2 ^ (prefixWord ++ tailWord_2432108).sum := by decide
  have hdescent : baseEnd_2432108 < baseStart_2432108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432114 : List Nat := [3, 2, 1, 2, 2, 1, 12]
def baseStart_2432114 : Nat := 118140960795 + 2432114 * 2 ^ 59
def prefixEnd_2432114 : Nat := 4983230072969 + 3 ^ 40 * 2432114 * 2
def baseEnd_2432114 : Nat := 15417820846039537981357

theorem tailTrace_2432114 : CollatzResearch.WordTrace tailWord_2432114 prefixEnd_2432114 15417820846039537981357 := by
  unfold tailWord_2432114
  simp only [CollatzResearch.WordTrace]
  refine ⟨22176621277718456211713849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59137656740582549897903597 22176621277718456211713849)
  ·
    refine ⟨16632465958288842158785387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22176621277718456211713849 16632465958288842158785387)
    ·
      refine ⟨24948698937433263238178081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16632465958288842158785387 24948698937433263238178081)
      ·
        refine ⟨18711524203074947428633561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24948698937433263238178081 18711524203074947428633561)
        ·
          refine ⟨14033643152306210571475171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18711524203074947428633561 14033643152306210571475171)
          ·
            refine ⟨21050464728459315857212757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14033643152306210571475171 21050464728459315857212757)
            ·
              refine ⟨15417820846039537981357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 21050464728459315857212757 15417820846039537981357)
              ·
                rfl

theorem cell23_2432114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 12].length) (baseStart_2432114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432114 prefixEnd_2432114 := by exact prefixLift 2432114
  have htrace : WordTrace (prefixWord ++ tailWord_2432114) baseStart_2432114 baseEnd_2432114 := by
    simpa [prefixWord, tailWord_2432114, baseEnd_2432114] using wordTrace_append hprefix tailTrace_2432114
  have hstable : (prefixWord ++ tailWord_2432114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432114).length < 2 ^ (prefixWord ++ tailWord_2432114).sum := by decide
  have hdescent : baseEnd_2432114 < baseStart_2432114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432118 : List Nat := [5, 1, 1, 2, 1, 1, 3, 1, 4, 4]
def baseStart_2432118 : Nat := 118140960795 + 2432118 * 2 ^ 59
def prefixEnd_2432118 : Nat := 4983230072969 + 3 ^ 40 * 2432118 * 2
def baseEnd_2432118 : Nat := 416281847483940186946633

theorem tailTrace_2432118 : CollatzResearch.WordTrace tailWord_2432118 prefixEnd_2432118 416281847483940186946633 := by
  unfold tailWord_2432118
  simp only [CollatzResearch.WordTrace]
  refine ⟨5544164437678708345625063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59137754001906222353334005 5544164437678708345625063)
  ·
    refine ⟨8316246656518062518437595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5544164437678708345625063 8316246656518062518437595)
    ·
      refine ⟨12474369984777093777656393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8316246656518062518437595 12474369984777093777656393)
      ·
        refine ⟨9355777488582820333242295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12474369984777093777656393 9355777488582820333242295)
        ·
          refine ⟨14033666232874230499863443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9355777488582820333242295 14033666232874230499863443)
          ·
            refine ⟨21050499349311345749795165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14033666232874230499863443 21050499349311345749795165)
            ·
              refine ⟨7893937255991754656173187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21050499349311345749795165 7893937255991754656173187)
              ·
                refine ⟨11840905883987631984259781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7893937255991754656173187 11840905883987631984259781)
                ·
                  refine ⟨2220169853247680997048709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11840905883987631984259781 2220169853247680997048709)
                  ·
                    refine ⟨416281847483940186946633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2220169853247680997048709 416281847483940186946633)
                    ·
                      rfl

theorem cell23_2432118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_2432118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432118 prefixEnd_2432118 := by exact prefixLift 2432118
  have htrace : WordTrace (prefixWord ++ tailWord_2432118) baseStart_2432118 baseEnd_2432118 := by
    simpa [prefixWord, tailWord_2432118, baseEnd_2432118] using wordTrace_append hprefix tailTrace_2432118
  have hstable : (prefixWord ++ tailWord_2432118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432118).length < 2 ^ (prefixWord ++ tailWord_2432118).sum := by decide
  have hdescent : baseEnd_2432118 < baseStart_2432118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432125 : List Nat := [1, 4, 1, 1, 3, 1, 4, 1, 3, 2, 2]
def baseStart_2432125 : Nat := 118140960795 + 2432125 * 2 ^ 59
def prefixEnd_2432125 : Nat := 4983230072969 + 3 ^ 40 * 2432125 * 2
def baseEnd_2432125 : Nat := 1248849136816402033452367

theorem tailTrace_2432125 : CollatzResearch.WordTrace tailWord_2432125 prefixEnd_2432125 1248849136816402033452367 := by
  unfold tailWord_2432125
  simp only [CollatzResearch.WordTrace]
  refine ⟨88706886313833973725505829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59137924209222649150337219 88706886313833973725505829)
  ·
    refine ⟨16632541183843870073532343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88706886313833973725505829 16632541183843870073532343)
    ·
      refine ⟨24948811775765805110298515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16632541183843870073532343 24948811775765805110298515)
      ·
        refine ⟨37423217663648707665447773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24948811775765805110298515 37423217663648707665447773)
        ·
          refine ⟨14033706623868265374542915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37423217663648707665447773 14033706623868265374542915)
          ·
            refine ⟨21050559935802398061814373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14033706623868265374542915 21050559935802398061814373)
            ·
              refine ⟨3946979987962949636590195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21050559935802398061814373 3946979987962949636590195)
              ·
                refine ⟨5920469981944424454885293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3946979987962949636590195 5920469981944424454885293)
                ·
                  refine ⟨2220176243229159170581985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5920469981944424454885293 2220176243229159170581985)
                  ·
                    refine ⟨1665132182421869377936489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2220176243229159170581985 1665132182421869377936489)
                    ·
                      refine ⟨1248849136816402033452367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1665132182421869377936489 1248849136816402033452367)
                      ·
                        rfl

theorem cell23_2432125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3, 2, 2].length) (baseStart_2432125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432125 prefixEnd_2432125 := by exact prefixLift 2432125
  have htrace : WordTrace (prefixWord ++ tailWord_2432125) baseStart_2432125 baseEnd_2432125 := by
    simpa [prefixWord, tailWord_2432125, baseEnd_2432125] using wordTrace_append hprefix tailTrace_2432125
  have hstable : (prefixWord ++ tailWord_2432125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432125).length < 2 ^ (prefixWord ++ tailWord_2432125).sum := by decide
  have hdescent : baseEnd_2432125 < baseStart_2432125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432202 : List Nat := [3, 1, 2, 1, 3, 4, 1, 2, 1, 3, 2]
def baseStart_2432202 : Nat := 118140960795 + 2432202 * 2 ^ 59
def prefixEnd_2432202 : Nat := 4983230072969 + 3 ^ 40 * 2432202 * 2
def baseEnd_2432202 : Nat := 1248888674826798232189513

theorem tailTrace_2432202 : CollatzResearch.WordTrace tailWord_2432202 prefixEnd_2432202 1248888674826798232189513 := by
  unfold tailWord_2432202
  simp only [CollatzResearch.WordTrace]
  refine ⟨22177423683638753969014715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59139796489703343917372573 22177423683638753969014715)
  ·
    refine ⟨33266135525458130953522073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22177423683638753969014715 33266135525458130953522073)
    ·
      refine ⟨24949601644093598215141555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33266135525458130953522073 24949601644093598215141555)
      ·
        refine ⟨37424402466140397322712333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24949601644093598215141555 37424402466140397322712333)
        ·
          refine ⟨14034150924802648996017125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37424402466140397322712333 14034150924802648996017125)
          ·
            refine ⟨2631403298400496686753211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14034150924802648996017125 2631403298400496686753211)
            ·
              refine ⟨3947104947600745030129817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2631403298400496686753211 3947104947600745030129817)
              ·
                refine ⟨2960328710700558772597363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3947104947600745030129817 2960328710700558772597363)
                ·
                  refine ⟨4440493066050838158896045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2960328710700558772597363 4440493066050838158896045)
                  ·
                    refine ⟨1665184899769064309586017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4440493066050838158896045 1665184899769064309586017)
                    ·
                      refine ⟨1248888674826798232189513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1665184899769064309586017 1248888674826798232189513)
                      ·
                        rfl

theorem cell23_2432202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 1, 3, 2].length) (baseStart_2432202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432202 prefixEnd_2432202 := by exact prefixLift 2432202
  have htrace : WordTrace (prefixWord ++ tailWord_2432202) baseStart_2432202 baseEnd_2432202 := by
    simpa [prefixWord, tailWord_2432202, baseEnd_2432202] using wordTrace_append hprefix tailTrace_2432202
  have hstable : (prefixWord ++ tailWord_2432202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432202).length < 2 ^ (prefixWord ++ tailWord_2432202).sum := by decide
  have hdescent : baseEnd_2432202 < baseStart_2432202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432232 : List Nat := [2, 1, 4, 1, 2, 1, 4, 2, 2, 2, 2]
def baseStart_2432232 : Nat := 118140960795 + 2432232 * 2 ^ 59
def prefixEnd_2432232 : Nat := 4983230072969 + 3 ^ 40 * 2432232 * 2
def baseEnd_2432232 : Nat := 1248904079246433114814375

theorem tailTrace_2432232 : CollatzResearch.WordTrace tailWord_2432232 prefixEnd_2432232 1248904079246433114814375 := by
  unfold tailWord_2432232
  simp only [CollatzResearch.WordTrace]
  refine ⟨44355394462223165499825475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59140525949630887333100633 44355394462223165499825475)
  ·
    refine ⟨66533091693334748249738213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44355394462223165499825475 66533091693334748249738213)
    ·
      refine ⟨12474954692500265296825915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66533091693334748249738213 12474954692500265296825915)
      ·
        refine ⟨18712432038750397945238873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12474954692500265296825915 18712432038750397945238873)
        ·
          refine ⟨14034324029062798458929155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18712432038750397945238873 14034324029062798458929155)
          ·
            refine ⟨21051486043594197688393733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14034324029062798458929155 21051486043594197688393733)
            ·
              refine ⟨3947153633173912066573825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21051486043594197688393733 3947153633173912066573825)
              ·
                refine ⟨2960365224880434049930369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3947153633173912066573825 2960365224880434049930369)
                ·
                  refine ⟨2220273918660325537447777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2960365224880434049930369 2220273918660325537447777)
                  ·
                    refine ⟨1665205438995244153085833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2220273918660325537447777 1665205438995244153085833)
                    ·
                      refine ⟨1248904079246433114814375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1665205438995244153085833 1248904079246433114814375)
                      ·
                        rfl

theorem cell23_2432232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_2432232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432232 prefixEnd_2432232 := by exact prefixLift 2432232
  have htrace : WordTrace (prefixWord ++ tailWord_2432232) baseStart_2432232 baseEnd_2432232 := by
    simpa [prefixWord, tailWord_2432232, baseEnd_2432232] using wordTrace_append hprefix tailTrace_2432232
  have hstable : (prefixWord ++ tailWord_2432232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432232).length < 2 ^ (prefixWord ++ tailWord_2432232).sum := by decide
  have hdescent : baseEnd_2432232 < baseStart_2432232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432268 : List Nat := [2, 2, 1, 2, 2, 3, 3, 1, 2, 5]
def baseStart_2432268 : Nat := 118140960795 + 2432268 * 2 ^ 59
def prefixEnd_2432268 : Nat := 4983230072969 + 3 ^ 40 * 2432268 * 2
def baseEnd_2432268 : Nat := 416307521516664991321403

theorem tailTrace_2432268 : CollatzResearch.WordTrace tailWord_2432268 prefixEnd_2432268 416307521516664991321403 := by
  unfold tailWord_2432268
  simp only [CollatzResearch.WordTrace]
  refine ⟨44356050976157954573980729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59141401301543939431974305 44356050976157954573980729)
  ·
    refine ⟨33267038232118465930485547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44356050976157954573980729 33267038232118465930485547)
    ·
      refine ⟨49900557348177698895728321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33267038232118465930485547 49900557348177698895728321)
      ·
        refine ⟨37425418011133274171796241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49900557348177698895728321 37425418011133274171796241)
        ·
          refine ⟨28069063508349955628847181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37425418011133274171796241 28069063508349955628847181)
          ·
            refine ⟨10525898815631233360817693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28069063508349955628847181 10525898815631233360817693)
            ·
              refine ⟨3947212055861712510306635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10525898815631233360817693 3947212055861712510306635)
              ·
                refine ⟨5920818083792568765459953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3947212055861712510306635 5920818083792568765459953)
                ·
                  refine ⟨4440613562844426574094965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5920818083792568765459953 4440613562844426574094965)
                  ·
                    refine ⟨416307521516664991321403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4440613562844426574094965 416307521516664991321403)
                    ·
                      rfl

theorem cell23_2432268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 2, 5].length) (baseStart_2432268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432268 prefixEnd_2432268 := by exact prefixLift 2432268
  have htrace : WordTrace (prefixWord ++ tailWord_2432268) baseStart_2432268 baseEnd_2432268 := by
    simpa [prefixWord, tailWord_2432268, baseEnd_2432268] using wordTrace_append hprefix tailTrace_2432268
  have hstable : (prefixWord ++ tailWord_2432268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432268).length < 2 ^ (prefixWord ++ tailWord_2432268).sum := by decide
  have hdescent : baseEnd_2432268 < baseStart_2432268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432305 : List Nat := [1, 2, 2, 3, 3, 1, 2, 1, 2, 4, 2]
def baseStart_2432305 : Nat := 118140960795 + 2432305 * 2 ^ 59
def prefixEnd_2432305 : Nat := 4983230072969 + 3 ^ 40 * 2432305 * 2
def baseEnd_2432305 : Nat := 1248941563334211329201539

theorem tailTrace_2432305 : CollatzResearch.WordTrace tailWord_2432305 prefixEnd_2432305 1248941563334211329201539 := by
  unfold tailWord_2432305
  simp only [CollatzResearch.WordTrace]
  refine ⟨88713451453181864467058369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59142300968787909644705579 88713451453181864467058369)
  ·
    refine ⟨66535088589886398350293777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88713451453181864467058369 66535088589886398350293777)
    ·
      refine ⟨49901316442414798762720333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66535088589886398350293777 49901316442414798762720333)
      ·
        refine ⟨18712993665905549536020125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49901316442414798762720333 18712993665905549536020125)
        ·
          refine ⟨7017372624714581076007547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18712993665905549536020125 7017372624714581076007547)
          ·
            refine ⟨10526058937071871614011321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7017372624714581076007547 10526058937071871614011321)
            ·
              refine ⟨7894544202803903710508491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10526058937071871614011321 7894544202803903710508491)
              ·
                refine ⟨11841816304205855565762737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7894544202803903710508491 11841816304205855565762737)
                ·
                  refine ⟨8881362228154391674322053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11841816304205855565762737 8881362228154391674322053)
                  ·
                    refine ⟨1665255417778948438935385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8881362228154391674322053 1665255417778948438935385)
                    ·
                      refine ⟨1248941563334211329201539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1665255417778948438935385 1248941563334211329201539)
                      ·
                        rfl

theorem cell23_2432305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_2432305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432305 prefixEnd_2432305 := by exact prefixLift 2432305
  have htrace : WordTrace (prefixWord ++ tailWord_2432305) baseStart_2432305 baseEnd_2432305 := by
    simpa [prefixWord, tailWord_2432305, baseEnd_2432305] using wordTrace_append hprefix tailTrace_2432305
  have hstable : (prefixWord ++ tailWord_2432305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432305).length < 2 ^ (prefixWord ++ tailWord_2432305).sum := by decide
  have hdescent : baseEnd_2432305 < baseStart_2432305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432318 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_2432318 : Nat := 118140960795 + 2432318 * 2 ^ 59
def prefixEnd_2432318 : Nat := 4983230072969 + 3 ^ 40 * 2432318 * 2
def baseEnd_2432318 : Nat := 1248948238582719778338979

theorem tailTrace_2432318 : CollatzResearch.WordTrace tailWord_2432318 prefixEnd_2432318 1248948238582719778338979 := by
  unfold tailWord_2432318
  simp only [CollatzResearch.WordTrace]
  refine ⟨11089240700266845960910201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59142617068089845124854405 11089240700266845960910201)
  ·
    refine ⟨8316930525200134470682651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11089240700266845960910201 8316930525200134470682651)
    ·
      refine ⟨12475395787800201706023977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8316930525200134470682651 12475395787800201706023977)
      ·
        refine ⟨9356546840850151279517983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12475395787800201706023977 9356546840850151279517983)
        ·
          refine ⟨14034820261275226919276975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9356546840850151279517983 14034820261275226919276975)
          ·
            refine ⟨21052230391912840378915463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14034820261275226919276975 21052230391912840378915463)
            ·
              refine ⟨31578345587869260568373195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21052230391912840378915463 31578345587869260568373195)
              ·
                refine ⟨47367518381803890852559793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31578345587869260568373195 47367518381803890852559793)
                ·
                  refine ⟨35525638786352918139419845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47367518381803890852559793 35525638786352918139419845)
                  ·
                    refine ⟨6661057272441172151141221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35525638786352918139419845 6661057272441172151141221)
                    ·
                      refine ⟨1248948238582719778338979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6661057272441172151141221 1248948238582719778338979)
                      ·
                        rfl

theorem cell23_2432318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_2432318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432318 prefixEnd_2432318 := by exact prefixLift 2432318
  have htrace : WordTrace (prefixWord ++ tailWord_2432318) baseStart_2432318 baseEnd_2432318 := by
    simpa [prefixWord, tailWord_2432318, baseEnd_2432318] using wordTrace_append hprefix tailTrace_2432318
  have hstable : (prefixWord ++ tailWord_2432318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432318).length < 2 ^ (prefixWord ++ tailWord_2432318).sum := by decide
  have hdescent : baseEnd_2432318 < baseStart_2432318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432332 : List Nat := [2, 2, 1, 3, 2, 2, 3, 3, 1, 4]
def baseStart_2432332 : Nat := 118140960795 + 2432332 * 2 ^ 59
def prefixEnd_2432332 : Nat := 4983230072969 + 3 ^ 40 * 2432332 * 2
def baseEnd_2432332 : Nat := 416318475770627574521305

theorem tailTrace_2432332 : CollatzResearch.WordTrace tailWord_2432332 prefixEnd_2432332 416318475770627574521305 := by
  unfold tailWord_2432332
  simp only [CollatzResearch.WordTrace]
  refine ⟨44357218112042024039145625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59142957482722698718860833 44357218112042024039145625)
  ·
    refine ⟨33267913584031518029359219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44357218112042024039145625 33267913584031518029359219)
    ·
      refine ⟨49901870376047277044038829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33267913584031518029359219 49901870376047277044038829)
      ·
        refine ⟨18713201391017728891514561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49901870376047277044038829 18713201391017728891514561)
        ·
          refine ⟨14034901043263296668635921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18713201391017728891514561 14034901043263296668635921)
          ·
            refine ⟨10526175782447472501476941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14034901043263296668635921 10526175782447472501476941)
            ·
              refine ⟨3947315918417802188053853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10526175782447472501476941 3947315918417802188053853)
              ·
                refine ⟨1480243469406675820520195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3947315918417802188053853 1480243469406675820520195)
                ·
                  refine ⟨2220365204110013730780293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1480243469406675820520195 2220365204110013730780293)
                  ·
                    refine ⟨416318475770627574521305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2220365204110013730780293 416318475770627574521305)
                    ·
                      rfl

theorem cell23_2432332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3, 1, 4].length) (baseStart_2432332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432332 prefixEnd_2432332 := by exact prefixLift 2432332
  have htrace : WordTrace (prefixWord ++ tailWord_2432332) baseStart_2432332 baseEnd_2432332 := by
    simpa [prefixWord, tailWord_2432332, baseEnd_2432332] using wordTrace_append hprefix tailTrace_2432332
  have hstable : (prefixWord ++ tailWord_2432332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432332).length < 2 ^ (prefixWord ++ tailWord_2432332).sum := by decide
  have hdescent : baseEnd_2432332 < baseStart_2432332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432351 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 7]
def baseStart_2432351 : Nat := 118140960795 + 2432351 * 2 ^ 59
def prefixEnd_2432351 : Nat := 4983230072969 + 3 ^ 40 * 2432351 * 2
def baseEnd_2432351 : Nat := 1248965183444318149226327

theorem tailTrace_2432351 : CollatzResearch.WordTrace tailWord_2432351 prefixEnd_2432351 1248965183444318149226327 := by
  unfold tailWord_2432351
  simp only [CollatzResearch.WordTrace]
  refine ⟨88715129211015214323232907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59143419474010142882155271 88715129211015214323232907)
  ·
    refine ⟨133072693816522821484849361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88715129211015214323232907 133072693816522821484849361)
    ·
      refine ⟨99804520362392116113637021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133072693816522821484849361 99804520362392116113637021)
      ·
        refine ⟨37426695135897043542613883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99804520362392116113637021 37426695135897043542613883)
        ·
          refine ⟨56140042703845565313920825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37426695135897043542613883 56140042703845565313920825)
          ·
            refine ⟨42105032027884173985440619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56140042703845565313920825 42105032027884173985440619)
            ·
              refine ⟨63157548041826260978160929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42105032027884173985440619 63157548041826260978160929)
              ·
                refine ⟨47368161031369695733620697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63157548041826260978160929 47368161031369695733620697)
                ·
                  refine ⟨35526120773527271800215523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47368161031369695733620697 35526120773527271800215523)
                  ·
                    refine ⟨53289181160290907700323285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35526120773527271800215523 53289181160290907700323285)
                    ·
                      refine ⟨1248965183444318149226327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53289181160290907700323285 1248965183444318149226327)
                      ·
                        rfl

theorem cell23_2432351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_2432351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432351 prefixEnd_2432351 := by exact prefixLift 2432351
  have htrace : WordTrace (prefixWord ++ tailWord_2432351) baseStart_2432351 baseEnd_2432351 := by
    simpa [prefixWord, tailWord_2432351, baseEnd_2432351] using wordTrace_append hprefix tailTrace_2432351
  have hstable : (prefixWord ++ tailWord_2432351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432351).length < 2 ^ (prefixWord ++ tailWord_2432351).sum := by decide
  have hdescent : baseEnd_2432351 < baseStart_2432351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432378 : List Nat := [3, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4]
def baseStart_2432378 : Nat := 118140960795 + 2432378 * 2 ^ 59
def prefixEnd_2432378 : Nat := 4983230072969 + 3 ^ 40 * 2432378 * 2
def baseEnd_2432378 : Nat := 1248979047421989543588703

theorem tailTrace_2432378 : CollatzResearch.WordTrace tailWord_2432378 prefixEnd_2432378 1248979047421989543588703 := by
  unfold tailWord_2432378
  simp only [CollatzResearch.WordTrace]
  refine ⟨22179028495479349483616447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59144075987944931956310525 22179028495479349483616447)
  ·
    refine ⟨33268542743219024225424671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22179028495479349483616447 33268542743219024225424671)
    ·
      refine ⟨49902814114828536338137007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33268542743219024225424671 49902814114828536338137007)
      ·
        refine ⟨74854221172242804507205511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49902814114828536338137007 74854221172242804507205511)
        ·
          refine ⟨112281331758364206760808267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74854221172242804507205511 112281331758364206760808267)
          ·
            refine ⟨168421997637546310141212401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112281331758364206760808267 168421997637546310141212401)
            ·
              refine ⟨126316498228159732605909301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168421997637546310141212401 126316498228159732605909301)
              ·
                refine ⟨11842171708889974931803997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126316498228159732605909301 11842171708889974931803997)
                ·
                  refine ⟨4440814390833740599426499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11842171708889974931803997 4440814390833740599426499)
                  ·
                    refine ⟨6661221586250610899139749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4440814390833740599426499 6661221586250610899139749)
                    ·
                      refine ⟨1248979047421989543588703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6661221586250610899139749 1248979047421989543588703)
                      ·
                        rfl

theorem cell23_2432378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_2432378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432378 prefixEnd_2432378 := by exact prefixLift 2432378
  have htrace : WordTrace (prefixWord ++ tailWord_2432378) baseStart_2432378 baseEnd_2432378 := by
    simpa [prefixWord, tailWord_2432378, baseEnd_2432378] using wordTrace_append hprefix tailTrace_2432378
  have hstable : (prefixWord ++ tailWord_2432378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432378).length < 2 ^ (prefixWord ++ tailWord_2432378).sum := by decide
  have hdescent : baseEnd_2432378 < baseStart_2432378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432388 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 3, 6]
def baseStart_2432388 : Nat := 118140960795 + 2432388 * 2 ^ 59
def prefixEnd_2432388 : Nat := 4983230072969 + 3 ^ 40 * 2432388 * 2
def baseEnd_2432388 : Nat := 416328060742844834821219

theorem tailTrace_2432388 : CollatzResearch.WordTrace tailWord_2432388 prefixEnd_2432388 416328060742844834821219 := by
  unfold tailWord_2432388
  simp only [CollatzResearch.WordTrace]
  refine ⟨44358239355940584821164909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59144319141254113094886545 44358239355940584821164909)
  ·
    refine ⟨16634339758477719307936841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44358239355940584821164909 16634339758477719307936841)
    ·
      refine ⟨12475754818858289480952631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16634339758477719307936841 12475754818858289480952631)
      ·
        refine ⟨18713632228287434221428947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12475754818858289480952631 18713632228287434221428947)
        ·
          refine ⟨28070448342431151332143421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18713632228287434221428947 28070448342431151332143421)
          ·
            refine ⟨10526418128411681749553783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28070448342431151332143421 10526418128411681749553783)
            ·
              refine ⟨15789627192617522624330675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10526418128411681749553783 15789627192617522624330675)
              ·
                refine ⟨23684440788926283936496013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15789627192617522624330675 23684440788926283936496013)
                ·
                  refine ⟨8881665295847356476186005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23684440788926283936496013 8881665295847356476186005)
                  ·
                    refine ⟨416328060742844834821219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8881665295847356476186005 416328060742844834821219)
                    ·
                      rfl

theorem cell23_2432388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_2432388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432388 prefixEnd_2432388 := by exact prefixLift 2432388
  have htrace : WordTrace (prefixWord ++ tailWord_2432388) baseStart_2432388 baseEnd_2432388 := by
    simpa [prefixWord, tailWord_2432388, baseEnd_2432388] using wordTrace_append hprefix tailTrace_2432388
  have hstable : (prefixWord ++ tailWord_2432388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432388).length < 2 ^ (prefixWord ++ tailWord_2432388).sum := by decide
  have hdescent : baseEnd_2432388 < baseStart_2432388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432392 : List Nat := [2, 1, 3, 3, 1, 3, 3, 1, 1, 5]
def baseStart_2432392 : Nat := 118140960795 + 2432392 * 2 ^ 59
def prefixEnd_2432392 : Nat := 4983230072969 + 3 ^ 40 * 2432392 * 2
def baseEnd_2432392 : Nat := 416328745383717496271213

theorem tailTrace_2432392 : CollatzResearch.WordTrace tailWord_2432392 prefixEnd_2432392 416328745383717496271213 := by
  unfold tailWord_2432392
  simp only [CollatzResearch.WordTrace]
  refine ⟨44358312301933339162737715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59144416402577785550316953 44358312301933339162737715)
  ·
    refine ⟨66537468452900008744106573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44358312301933339162737715 66537468452900008744106573)
    ·
      refine ⟨24951550669837503279039965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66537468452900008744106573 24951550669837503279039965)
      ·
        refine ⟨9356831501189063729639987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24951550669837503279039965 9356831501189063729639987)
        ·
          refine ⟨14035247251783595594459981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9356831501189063729639987 14035247251783595594459981)
          ·
            refine ⟨5263217719418848347922493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14035247251783595594459981 5263217719418848347922493)
            ·
              refine ⟨1973706644782068130470935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5263217719418848347922493 1973706644782068130470935)
              ·
                refine ⟨2960559967173102195706403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1973706644782068130470935 2960559967173102195706403)
                ·
                  refine ⟨4440839950759653293559605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2960559967173102195706403 4440839950759653293559605)
                  ·
                    refine ⟨416328745383717496271213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4440839950759653293559605 416328745383717496271213)
                    ·
                      rfl

theorem cell23_2432392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_2432392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432392 prefixEnd_2432392 := by exact prefixLift 2432392
  have htrace : WordTrace (prefixWord ++ tailWord_2432392) baseStart_2432392 baseEnd_2432392 := by
    simpa [prefixWord, tailWord_2432392, baseEnd_2432392] using wordTrace_append hprefix tailTrace_2432392
  have hstable : (prefixWord ++ tailWord_2432392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432392).length < 2 ^ (prefixWord ++ tailWord_2432392).sum := by decide
  have hdescent : baseEnd_2432392 < baseStart_2432392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432405 : List Nat := [1, 3, 2, 1, 1, 2, 3, 4, 2, 4]
def baseStart_2432405 : Nat := 118140960795 + 2432405 * 2 ^ 59
def prefixEnd_2432405 : Nat := 4983230072969 + 3 ^ 40 * 2432405 * 2
def baseEnd_2432405 : Nat := 416330970466553645983693

theorem tailTrace_2432405 : CollatzResearch.WordTrace tailWord_2432405 prefixEnd_2432405 416330970466553645983693 := by
  unfold tailWord_2432405
  simp only [CollatzResearch.WordTrace]
  refine ⟨88717098752819581545698669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59144732501879721030465779 88717098752819581545698669)
  ·
    refine ⟨33268912032307343079637001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88717098752819581545698669 33268912032307343079637001)
    ·
      refine ⟨24951684024230507309727751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33268912032307343079637001 24951684024230507309727751)
      ·
        refine ⟨37427526036345760964591627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24951684024230507309727751 37427526036345760964591627)
        ·
          refine ⟨56141289054518641446887441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37427526036345760964591627 56141289054518641446887441)
          ·
            refine ⟨42105966790888981085165581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56141289054518641446887441 42105966790888981085165581)
            ·
              refine ⟨15789737546583367906937093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42105966790888981085165581 15789737546583367906937093)
              ·
                refine ⟨2960575789984381482550705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15789737546583367906937093 2960575789984381482550705)
                ·
                  refine ⟨2220431842488286111913029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2960575789984381482550705 2220431842488286111913029)
                  ·
                    refine ⟨416330970466553645983693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2220431842488286111913029 416330970466553645983693)
                    ·
                      rfl

theorem cell23_2432405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_2432405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432405 prefixEnd_2432405 := by exact prefixLift 2432405
  have htrace : WordTrace (prefixWord ++ tailWord_2432405) baseStart_2432405 baseEnd_2432405 := by
    simpa [prefixWord, tailWord_2432405, baseEnd_2432405] using wordTrace_append hprefix tailTrace_2432405
  have hstable : (prefixWord ++ tailWord_2432405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432405).length < 2 ^ (prefixWord ++ tailWord_2432405).sum := by decide
  have hdescent : baseEnd_2432405 < baseStart_2432405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432415 : List Nat := [1, 1, 2, 5, 1, 2, 1, 2, 3, 2, 3]
def baseStart_2432415 : Nat := 118140960795 + 2432415 * 2 ^ 59
def prefixEnd_2432415 : Nat := 4983230072969 + 3 ^ 40 * 2432415 * 2
def baseEnd_2432415 : Nat := 1248998046206205898826033

theorem tailTrace_2432415 : CollatzResearch.WordTrace tailWord_2432415 prefixEnd_2432415 1248998046206205898826033 := by
  unfold tailWord_2432415
  simp only [CollatzResearch.WordTrace]
  refine ⟨88717463482783353253562699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59144975655188902169041799 88717463482783353253562699)
  ·
    refine ⟨133076195224175029880344049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88717463482783353253562699 133076195224175029880344049)
    ·
      refine ⟨99807146418131272410258037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133076195224175029880344049 99807146418131272410258037)
      ·
        refine ⟨9356919976699806788461691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99807146418131272410258037 9356919976699806788461691)
        ·
          refine ⟨14035379965049710182692537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9356919976699806788461691 14035379965049710182692537)
          ·
            refine ⟨10526534973787282637019403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14035379965049710182692537 10526534973787282637019403)
            ·
              refine ⟨15789802460680923955529105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10526534973787282637019403 15789802460680923955529105)
              ·
                refine ⟨11842351845510692966646829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15789802460680923955529105 11842351845510692966646829)
                ·
                  refine ⟨4440881942066509862492561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11842351845510692966646829 4440881942066509862492561)
                  ·
                    refine ⟨3330661456549882396869421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4440881942066509862492561 3330661456549882396869421)
                    ·
                      refine ⟨1248998046206205898826033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3330661456549882396869421 1248998046206205898826033)
                      ·
                        rfl

theorem cell23_2432415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_2432415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432415 prefixEnd_2432415 := by exact prefixLift 2432415
  have htrace : WordTrace (prefixWord ++ tailWord_2432415) baseStart_2432415 baseEnd_2432415 := by
    simpa [prefixWord, tailWord_2432415, baseEnd_2432415] using wordTrace_append hprefix tailTrace_2432415
  have hstable : (prefixWord ++ tailWord_2432415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432415).length < 2 ^ (prefixWord ++ tailWord_2432415).sum := by decide
  have hdescent : baseEnd_2432415 < baseStart_2432415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432429 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 5, 2, 2]
def baseStart_2432429 : Nat := 118140960795 + 2432429 * 2 ^ 59
def prefixEnd_2432429 : Nat := 4983230072969 + 3 ^ 40 * 2432429 * 2
def baseEnd_2432429 : Nat := 1249005234935368844050969

theorem tailTrace_2432429 : CollatzResearch.WordTrace tailWord_2432429 prefixEnd_2432429 1249005234935368844050969 := by
  unfold tailWord_2432429
  simp only [CollatzResearch.WordTrace]
  refine ⟨88717974104732633644572341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59145316069821755763048227 88717974104732633644572341)
  ·
    refine ⟨8317310072318684404178657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88717974104732633644572341 8317310072318684404178657)
    ·
      refine ⟨6237982554239013303133993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8317310072318684404178657 6237982554239013303133993)
      ·
        refine ⟨4678486915679259977350495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6237982554239013303133993 4678486915679259977350495)
        ·
          refine ⟨7017730373518889966025743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4678486915679259977350495 7017730373518889966025743)
          ·
            refine ⟨10526595560278334949038615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7017730373518889966025743 10526595560278334949038615)
            ·
              refine ⟨15789893340417502423557923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10526595560278334949038615 15789893340417502423557923)
              ·
                refine ⟨23684840010626253635336885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15789893340417502423557923 23684840010626253635336885)
                ·
                  refine ⟨2220453750996211278312833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23684840010626253635336885 2220453750996211278312833)
                  ·
                    refine ⟨1665340313247158458734625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2220453750996211278312833 1665340313247158458734625)
                    ·
                      refine ⟨1249005234935368844050969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1665340313247158458734625 1249005234935368844050969)
                      ·
                        rfl

theorem cell23_2432429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_2432429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432429 prefixEnd_2432429 := by exact prefixLift 2432429
  have htrace : WordTrace (prefixWord ++ tailWord_2432429) baseStart_2432429 baseEnd_2432429 := by
    simpa [prefixWord, tailWord_2432429, baseEnd_2432429] using wordTrace_append hprefix tailTrace_2432429
  have hstable : (prefixWord ++ tailWord_2432429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432429).length < 2 ^ (prefixWord ++ tailWord_2432429).sum := by decide
  have hdescent : baseEnd_2432429 < baseStart_2432429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432445 : List Nat := [1, 4, 1, 2, 2, 1, 1, 4, 1, 3, 3]
def baseStart_2432445 : Nat := 118140960795 + 2432445 * 2 ^ 59
def prefixEnd_2432445 : Nat := 4983230072969 + 3 ^ 40 * 2432445 * 2
def baseEnd_2432445 : Nat := 1249013450625840781450895

theorem tailTrace_2432445 : CollatzResearch.WordTrace tailWord_2432445 prefixEnd_2432445 1249013450625840781450895 := by
  unfold tailWord_2432445
  simp only [CollatzResearch.WordTrace]
  refine ⟨88718557672674668377154789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59145705115116445584769859 88718557672674668377154789)
  ·
    refine ⟨16634729563626500320716523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88718557672674668377154789 16634729563626500320716523)
    ·
      refine ⟨24952094345439750481074785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16634729563626500320716523 24952094345439750481074785)
      ·
        refine ⟨18714070759079812860806089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24952094345439750481074785 18714070759079812860806089)
        ·
          refine ⟨14035553069309859645604567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18714070759079812860806089 14035553069309859645604567)
          ·
            refine ⟨21053329603964789468406851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14035553069309859645604567 21053329603964789468406851)
            ·
              refine ⟨31579994405947184202610277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21053329603964789468406851 31579994405947184202610277)
              ·
                refine ⟨5921248951115097037989427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31579994405947184202610277 5921248951115097037989427)
                ·
                  refine ⟨8881873426672645556984141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5921248951115097037989427 8881873426672645556984141)
                  ·
                    refine ⟨3330702535002242083869053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8881873426672645556984141 3330702535002242083869053)
                    ·
                      refine ⟨1249013450625840781450895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3330702535002242083869053 1249013450625840781450895)
                      ·
                        rfl

theorem cell23_2432445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_2432445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432445 prefixEnd_2432445 := by exact prefixLift 2432445
  have htrace : WordTrace (prefixWord ++ tailWord_2432445) baseStart_2432445 baseEnd_2432445 := by
    simpa [prefixWord, tailWord_2432445, baseEnd_2432445] using wordTrace_append hprefix tailTrace_2432445
  have hstable : (prefixWord ++ tailWord_2432445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432445).length < 2 ^ (prefixWord ++ tailWord_2432445).sum := by decide
  have hdescent : baseEnd_2432445 < baseStart_2432445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432479 : List Nat := [1, 1, 2, 3, 3, 1, 5, 1, 2, 1, 3]
def baseStart_2432479 : Nat := 118140960795 + 2432479 * 2 ^ 59
def prefixEnd_2432479 : Nat := 4983230072969 + 3 ^ 40 * 2432479 * 2
def baseEnd_2432479 : Nat := 1249030908968093648425739

theorem tailTrace_2432479 : CollatzResearch.WordTrace tailWord_2432479 prefixEnd_2432479 1249030908968093648425739 := by
  unfold tailWord_2432479
  simp only [CollatzResearch.WordTrace]
  refine ⟨88719797754551492183892491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59146531836367661455928327 88719797754551492183892491)
  ·
    refine ⟨133079696631827238275838737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88719797754551492183892491 133079696631827238275838737)
    ·
      refine ⟨99809772473870428706879053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133079696631827238275838737 99809772473870428706879053)
      ·
        refine ⟨37428664677701410765079645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99809772473870428706879053 37428664677701410765079645)
        ·
          refine ⟨14035749254138029036904867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37428664677701410765079645 14035749254138029036904867)
          ·
            refine ⟨21053623881207043555357301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14035749254138029036904867 21053623881207043555357301)
            ·
              refine ⟨1973777238863160333314747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21053623881207043555357301 1973777238863160333314747)
              ·
                refine ⟨2960665858294740499972121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1973777238863160333314747 2960665858294740499972121)
                ·
                  refine ⟨2220499393721055374979091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2960665858294740499972121 2220499393721055374979091)
                  ·
                    refine ⟨3330749090581583062468637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2220499393721055374979091 3330749090581583062468637)
                    ·
                      refine ⟨1249030908968093648425739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3330749090581583062468637 1249030908968093648425739)
                      ·
                        rfl

theorem cell23_2432479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 2, 1, 3].length) (baseStart_2432479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432479 prefixEnd_2432479 := by exact prefixLift 2432479
  have htrace : WordTrace (prefixWord ++ tailWord_2432479) baseStart_2432479 baseEnd_2432479 := by
    simpa [prefixWord, tailWord_2432479, baseEnd_2432479] using wordTrace_append hprefix tailTrace_2432479
  have hstable : (prefixWord ++ tailWord_2432479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432479).length < 2 ^ (prefixWord ++ tailWord_2432479).sum := by decide
  have hdescent : baseEnd_2432479 < baseStart_2432479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432508 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 9]
def baseStart_2432508 : Nat := 118140960795 + 2432508 * 2 ^ 59
def prefixEnd_2432508 : Nat := 4983230072969 + 3 ^ 40 * 2432508 * 2
def baseEnd_2432508 : Nat := 138782866656341559440345

theorem tailTrace_2432508 : CollatzResearch.WordTrace tailWord_2432508 prefixEnd_2432508 138782866656341559440345 := by
  unfold tailWord_2432508
  simp only [CollatzResearch.WordTrace]
  refine ⟨44360427735723215068349089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59147236980964286757798785 44360427735723215068349089)
  ·
    refine ⟨33270320801792411301261817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44360427735723215068349089 33270320801792411301261817)
    ·
      refine ⟨24952740601344308475946363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33270320801792411301261817 24952740601344308475946363)
      ·
        refine ⟨37429110902016462713919545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24952740601344308475946363 37429110902016462713919545)
        ·
          refine ⟨28071833176512347035439659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37429110902016462713919545 28071833176512347035439659)
          ·
            refine ⟨42107749764768520553159489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28071833176512347035439659 42107749764768520553159489)
            ·
              refine ⟨31580812323576390414869617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42107749764768520553159489 31580812323576390414869617)
              ·
                refine ⟨23685609242682292811152213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31580812323576390414869617 23685609242682292811152213)
                ·
                  refine ⟨138782866656341559440345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23685609242682292811152213 138782866656341559440345)
                  ·
                    rfl

theorem cell23_2432508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 9].length) (baseStart_2432508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432508 prefixEnd_2432508 := by exact prefixLift 2432508
  have htrace : WordTrace (prefixWord ++ tailWord_2432508) baseStart_2432508 baseEnd_2432508 := by
    simpa [prefixWord, tailWord_2432508, baseEnd_2432508] using wordTrace_append hprefix tailTrace_2432508
  have hstable : (prefixWord ++ tailWord_2432508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432508).length < 2 ^ (prefixWord ++ tailWord_2432508).sum := by decide
  have hdescent : baseEnd_2432508 < baseStart_2432508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432519 : List Nat := [1, 1, 4, 3, 2, 1, 2, 1, 4, 2, 2]
def baseStart_2432519 : Nat := 118140960795 + 2432519 * 2 ^ 59
def prefixEnd_2432519 : Nat := 4983230072969 + 3 ^ 40 * 2432519 * 2
def baseEnd_2432519 : Nat := 1249051448194273491925555

theorem tailTrace_2432519 : CollatzResearch.WordTrace tailWord_2432519 prefixEnd_2432519 1249051448194273491925555 := by
  unfold tailWord_2432519
  simp only [CollatzResearch.WordTrace]
  refine ⟨88721256674406579015348611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59147504449604386010232407 88721256674406579015348611)
  ·
    refine ⟨133081885011609868523022917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88721256674406579015348611 133081885011609868523022917)
    ·
      refine ⟨24952853439676850348066797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133081885011609868523022917 24952853439676850348066797)
      ·
        refine ⟨9357320039878818880525049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24952853439676850348066797 9357320039878818880525049)
        ·
          refine ⟨7017990029909114160393787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9357320039878818880525049 7017990029909114160393787)
          ·
            refine ⟨10526985044863671240590681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7017990029909114160393787 10526985044863671240590681)
            ·
              refine ⟨7895238783647753430443011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10526985044863671240590681 7895238783647753430443011)
              ·
                refine ⟨11842858175471630145664517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7895238783647753430443011 11842858175471630145664517)
                ·
                  refine ⟨2220535907900930652312097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11842858175471630145664517 2220535907900930652312097)
                  ·
                    refine ⟨1665401930925697989234073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2220535907900930652312097 1665401930925697989234073)
                    ·
                      refine ⟨1249051448194273491925555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1665401930925697989234073 1249051448194273491925555)
                      ·
                        rfl

theorem cell23_2432519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_2432519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432519 prefixEnd_2432519 := by exact prefixLift 2432519
  have htrace : WordTrace (prefixWord ++ tailWord_2432519) baseStart_2432519 baseEnd_2432519 := by
    simpa [prefixWord, tailWord_2432519, baseEnd_2432519] using wordTrace_append hprefix tailTrace_2432519
  have hstable : (prefixWord ++ tailWord_2432519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432519).length < 2 ^ (prefixWord ++ tailWord_2432519).sum := by decide
  have hdescent : baseEnd_2432519 < baseStart_2432519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432536 : List Nat := [2, 1, 2, 3, 4, 1, 1, 3, 2, 2, 2]
def baseStart_2432536 : Nat := 118140960795 + 2432536 * 2 ^ 59
def prefixEnd_2432536 : Nat := 4983230072969 + 3 ^ 40 * 2432536 * 2
def baseEnd_2432536 : Nat := 1249060177365399925412977

theorem tailTrace_2432536 : CollatzResearch.WordTrace tailWord_2432536 prefixEnd_2432536 1249060177365399925412977 := by
  unfold tailWord_2432536
  simp only [CollatzResearch.WordTrace]
  refine ⟨44360938357672495459358731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59147917810229993945811641 44360938357672495459358731)
  ·
    refine ⟨66541407536508743189038097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44360938357672495459358731 66541407536508743189038097)
    ·
      refine ⟨49906055652381557391778573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66541407536508743189038097 49906055652381557391778573)
      ·
        refine ⟨18714770869643084021916965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49906055652381557391778573 18714770869643084021916965)
        ·
          refine ⟨3509019538058078254109431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18714770869643084021916965 3509019538058078254109431)
          ·
            refine ⟨5263529307087117381164147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3509019538058078254109431 5263529307087117381164147)
            ·
              refine ⟨7895293960630676071746221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5263529307087117381164147 7895293960630676071746221)
              ·
                refine ⟨2960735235236503526904833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7895293960630676071746221 2960735235236503526904833)
                ·
                  refine ⟨2220551426427377645178625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2960735235236503526904833 2220551426427377645178625)
                  ·
                    refine ⟨1665413569820533233883969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2220551426427377645178625 1665413569820533233883969)
                    ·
                      refine ⟨1249060177365399925412977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1665413569820533233883969 1249060177365399925412977)
                      ·
                        rfl

theorem cell23_2432536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_2432536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432536 prefixEnd_2432536 := by exact prefixLift 2432536
  have htrace : WordTrace (prefixWord ++ tailWord_2432536) baseStart_2432536 baseEnd_2432536 := by
    simpa [prefixWord, tailWord_2432536, baseEnd_2432536] using wordTrace_append hprefix tailTrace_2432536
  have hstable : (prefixWord ++ tailWord_2432536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432536).length < 2 ^ (prefixWord ++ tailWord_2432536).sum := by decide
  have hdescent : baseEnd_2432536 < baseStart_2432536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432565 : List Nat := [1, 3, 3, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_2432565 : Nat := 118140960795 + 2432565 * 2 ^ 59
def prefixEnd_2432565 : Nat := 4983230072969 + 3 ^ 40 * 2432565 * 2
def baseEnd_2432565 : Nat := 1249075068304380311950343

theorem tailTrace_2432565 : CollatzResearch.WordTrace tailWord_2432565 prefixEnd_2432565 1249075068304380311950343 := by
  unfold tailWord_2432565
  simp only [CollatzResearch.WordTrace]
  refine ⟨88722934432239928871523149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59148622954826619247682099 88722934432239928871523149)
  ·
    refine ⟨33271100412089973326821181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88722934432239928871523149 33271100412089973326821181)
    ·
      refine ⟨12476662654533739997557943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33271100412089973326821181 12476662654533739997557943)
      ·
        refine ⟨18714993981800609996336915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12476662654533739997557943 18714993981800609996336915)
        ·
          refine ⟨28072490972700914994505373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18714993981800609996336915 28072490972700914994505373)
          ·
            refine ⟨10527184114762843122939515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28072490972700914994505373 10527184114762843122939515)
            ·
              refine ⟨15790776172144264684409273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10527184114762843122939515 15790776172144264684409273)
              ·
                refine ⟨11843082129108198513306955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15790776172144264684409273 11843082129108198513306955)
                ·
                  refine ⟨17764623193662297769960433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11843082129108198513306955 17764623193662297769960433)
                  ·
                    refine ⟨13323467395246723327470325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17764623193662297769960433 13323467395246723327470325)
                    ·
                      refine ⟨1249075068304380311950343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13323467395246723327470325 1249075068304380311950343)
                      ·
                        rfl

theorem cell23_2432565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_2432565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432565 prefixEnd_2432565 := by exact prefixLift 2432565
  have htrace : WordTrace (prefixWord ++ tailWord_2432565) baseStart_2432565 baseEnd_2432565 := by
    simpa [prefixWord, tailWord_2432565, baseEnd_2432565] using wordTrace_append hprefix tailTrace_2432565
  have hstable : (prefixWord ++ tailWord_2432565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432565).length < 2 ^ (prefixWord ++ tailWord_2432565).sum := by decide
  have hdescent : baseEnd_2432565 < baseStart_2432565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432585 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 7, 4]
def baseStart_2432585 : Nat := 118140960795 + 2432585 * 2 ^ 59
def prefixEnd_2432585 : Nat := 4983230072969 + 3 ^ 40 * 2432585 * 2
def baseEnd_2432585 : Nat := 416361779305823411233417

theorem tailTrace_2432585 : CollatzResearch.WordTrace tailWord_2432585 prefixEnd_2432585 416361779305823411233417 := by
  unfold tailWord_2432585
  simp only [CollatzResearch.WordTrace]
  refine ⟨88723663892167472287251209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59149109261444981524834139 88723663892167472287251209)
  ·
    refine ⟨66542747919125604215438407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88723663892167472287251209 66542747919125604215438407)
    ·
      refine ⟨99814121878688406323157611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66542747919125604215438407 99814121878688406323157611)
      ·
        refine ⟨149721182818032609484736417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99814121878688406323157611 149721182818032609484736417)
        ·
          refine ⟨112290887113524457113552313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149721182818032609484736417 112290887113524457113552313)
          ·
            refine ⟨84218165335143342835164235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112290887113524457113552313 84218165335143342835164235)
            ·
              refine ⟨126327248002715014252746353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84218165335143342835164235 126327248002715014252746353)
              ·
                refine ⟨94745436002036260689559765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126327248002715014252746353 94745436002036260689559765)
                ·
                  refine ⟨2220596156297724859911557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 94745436002036260689559765 2220596156297724859911557)
                  ·
                    refine ⟨416361779305823411233417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2220596156297724859911557 416361779305823411233417)
                    ·
                      rfl

theorem cell23_2432585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7, 4].length) (baseStart_2432585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432585 prefixEnd_2432585 := by exact prefixLift 2432585
  have htrace : WordTrace (prefixWord ++ tailWord_2432585) baseStart_2432585 baseEnd_2432585 := by
    simpa [prefixWord, tailWord_2432585, baseEnd_2432585] using wordTrace_append hprefix tailTrace_2432585
  have hstable : (prefixWord ++ tailWord_2432585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432585).length < 2 ^ (prefixWord ++ tailWord_2432585).sum := by decide
  have hdescent : baseEnd_2432585 < baseStart_2432585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432592 : List Nat := [2, 1, 1, 1, 1, 3, 5, 1, 2, 4, 2]
def baseStart_2432592 : Nat := 118140960795 + 2432592 * 2 ^ 59
def prefixEnd_2432592 : Nat := 4983230072969 + 3 ^ 40 * 2432592 * 2
def baseEnd_2432592 : Nat := 1249088932282051706312719

theorem tailTrace_2432592 : CollatzResearch.WordTrace tailWord_2432592 prefixEnd_2432592 1249088932282051706312719 := by
  unfold tailWord_2432592
  simp only [CollatzResearch.WordTrace]
  refine ⟨44361959601571056241378015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59149279468761408321837353 44361959601571056241378015)
  ·
    refine ⟨66542939402356584362067023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44361959601571056241378015 66542939402356584362067023)
    ·
      refine ⟨99814409103534876543100535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66542939402356584362067023 99814409103534876543100535)
      ·
        refine ⟨149721613655302314814650803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99814409103534876543100535 149721613655302314814650803)
        ·
          refine ⟨224582420482953472221976205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149721613655302314814650803 224582420482953472221976205)
          ·
            refine ⟨84218407681107552083241077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 224582420482953472221976205 84218407681107552083241077)
            ·
              refine ⟨7895475720103833007803851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84218407681107552083241077 7895475720103833007803851)
              ·
                refine ⟨11843213580155749511705777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7895475720103833007803851 11843213580155749511705777)
                ·
                  refine ⟨8882410185116812133779333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11843213580155749511705777 8882410185116812133779333)
                  ·
                    refine ⟨1665451909709402275083625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8882410185116812133779333 1665451909709402275083625)
                    ·
                      refine ⟨1249088932282051706312719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1665451909709402275083625 1249088932282051706312719)
                      ·
                        rfl

theorem cell23_2432592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 2, 4, 2].length) (baseStart_2432592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432592 prefixEnd_2432592 := by exact prefixLift 2432592
  have htrace : WordTrace (prefixWord ++ tailWord_2432592) baseStart_2432592 baseEnd_2432592 := by
    simpa [prefixWord, tailWord_2432592, baseEnd_2432592] using wordTrace_append hprefix tailTrace_2432592
  have hstable : (prefixWord ++ tailWord_2432592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432592).length < 2 ^ (prefixWord ++ tailWord_2432592).sum := by decide
  have hdescent : baseEnd_2432592 < baseStart_2432592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432612 : List Nat := [2, 3, 1, 1, 2, 4, 1, 1, 1, 4, 3]
def baseStart_2432612 : Nat := 118140960795 + 2432612 * 2 ^ 59
def prefixEnd_2432612 : Nat := 4983230072969 + 3 ^ 40 * 2432612 * 2
def baseEnd_2432612 : Nat := 1249099201895141628062627

theorem tailTrace_2432612 : CollatzResearch.WordTrace tailWord_2432612 prefixEnd_2432612 1249099201895141628062627 := by
  unfold tailWord_2432612
  simp only [CollatzResearch.WordTrace]
  refine ⟨44362324331534827949242045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59149765775379770598989393 44362324331534827949242045)
  ·
    refine ⟨16635871624325560480965767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44362324331534827949242045 16635871624325560480965767)
    ·
      refine ⟨24953807436488340721448651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16635871624325560480965767 24953807436488340721448651)
      ·
        refine ⟨37430711154732511082172977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24953807436488340721448651 37430711154732511082172977)
        ·
          refine ⟨28073033366049383311629733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37430711154732511082172977 28073033366049383311629733)
          ·
            refine ⟨5263693756134259370930575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28073033366049383311629733 5263693756134259370930575)
            ·
              refine ⟨7895540634201389056395863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5263693756134259370930575 7895540634201389056395863)
              ·
                refine ⟨11843310951302083584593795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7895540634201389056395863 11843310951302083584593795)
                ·
                  refine ⟨17764966426953125376890693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11843310951302083584593795 17764966426953125376890693)
                  ·
                    refine ⟨3330931205053711008167005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17764966426953125376890693 3330931205053711008167005)
                    ·
                      refine ⟨1249099201895141628062627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3330931205053711008167005 1249099201895141628062627)
                      ·
                        rfl

theorem cell23_2432612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_2432612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432612 prefixEnd_2432612 := by exact prefixLift 2432612
  have htrace : WordTrace (prefixWord ++ tailWord_2432612) baseStart_2432612 baseEnd_2432612 := by
    simpa [prefixWord, tailWord_2432612, baseEnd_2432612] using wordTrace_append hprefix tailTrace_2432612
  have hstable : (prefixWord ++ tailWord_2432612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432612).length < 2 ^ (prefixWord ++ tailWord_2432612).sum := by decide
  have hdescent : baseEnd_2432612 < baseStart_2432612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432625 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 1, 7, 3]
def baseStart_2432625 : Nat := 118140960795 + 2432625 * 2 ^ 59
def prefixEnd_2432625 : Nat := 4983230072969 + 3 ^ 40 * 2432625 * 2
def baseEnd_2432625 : Nat := 1249105877143650077200067

theorem tailTrace_2432625 : CollatzResearch.WordTrace tailWord_2432625 prefixEnd_2432625 1249105877143650077200067 := by
  unfold tailWord_2432625
  simp only [CollatzResearch.WordTrace]
  refine ⟨88725122812022559118707329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59150081874681706079138219 88725122812022559118707329)
  ·
    refine ⟨66543842109016919339030497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88725122812022559118707329 66543842109016919339030497)
    ·
      refine ⟨49907881581762689504272873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66543842109016919339030497 49907881581762689504272873)
      ·
        refine ⟨37430911186322017128204655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49907881581762689504272873 37430911186322017128204655)
        ·
          refine ⟨56146366779483025692306983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37430911186322017128204655 56146366779483025692306983)
          ·
            refine ⟨84219550169224538538460475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56146366779483025692306983 84219550169224538538460475)
            ·
              refine ⟨126329325253836807807690713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84219550169224538538460475 126329325253836807807690713)
              ·
                refine ⟨94746993940377605855768035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126329325253836807807690713 94746993940377605855768035)
                ·
                  refine ⟨142120490910566408783652053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94746993940377605855768035 142120490910566408783652053)
                  ·
                    refine ⟨3330949005716400205866845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 142120490910566408783652053 3330949005716400205866845)
                    ·
                      refine ⟨1249105877143650077200067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3330949005716400205866845 1249105877143650077200067)
                      ·
                        rfl

theorem cell23_2432625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_2432625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432625 prefixEnd_2432625 := by exact prefixLift 2432625
  have htrace : WordTrace (prefixWord ++ tailWord_2432625) baseStart_2432625 baseEnd_2432625 := by
    simpa [prefixWord, tailWord_2432625, baseEnd_2432625] using wordTrace_append hprefix tailTrace_2432625
  have hstable : (prefixWord ++ tailWord_2432625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432625).length < 2 ^ (prefixWord ++ tailWord_2432625).sum := by decide
  have hdescent : baseEnd_2432625 < baseStart_2432625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432652 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 3, 5, 2]
def baseStart_2432652 : Nat := 118140960795 + 2432652 * 2 ^ 59
def prefixEnd_2432652 : Nat := 4983230072969 + 3 ^ 40 * 2432652 * 2
def baseEnd_2432652 : Nat := 1249119741121321471562443

theorem tailTrace_2432652 : CollatzResearch.WordTrace tailWord_2432652 prefixEnd_2432652 1249119741121321471562443 := by
  unfold tailWord_2432652
  simp only [CollatzResearch.WordTrace]
  refine ⟨44363053791462371364970105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59150738388616495153293473 44363053791462371364970105)
  ·
    refine ⟨33272290343596778523727579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44363053791462371364970105 33272290343596778523727579)
    ·
      refine ⟨49908435515395167785591369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33272290343596778523727579 49908435515395167785591369)
      ·
        refine ⟨37431326636546375839193527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49908435515395167785591369 37431326636546375839193527)
        ·
          refine ⟨56146989954819563758790291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37431326636546375839193527 56146989954819563758790291)
          ·
            refine ⟨84220484932229345638185437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56146989954819563758790291 84220484932229345638185437)
            ·
              refine ⟨31582681849586004614319539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84220484932229345638185437 31582681849586004614319539)
              ·
                refine ⟨47374022774379006921479309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31582681849586004614319539 47374022774379006921479309)
                ·
                  refine ⟨17765258540392127595554741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47374022774379006921479309 17765258540392127595554741)
                  ·
                    refine ⟨1665492988161761962083257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17765258540392127595554741 1665492988161761962083257)
                    ·
                      refine ⟨1249119741121321471562443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1665492988161761962083257 1249119741121321471562443)
                      ·
                        rfl

theorem cell23_2432652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 5, 2].length) (baseStart_2432652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432652 prefixEnd_2432652 := by exact prefixLift 2432652
  have htrace : WordTrace (prefixWord ++ tailWord_2432652) baseStart_2432652 baseEnd_2432652 := by
    simpa [prefixWord, tailWord_2432652, baseEnd_2432652] using wordTrace_append hprefix tailTrace_2432652
  have hstable : (prefixWord ++ tailWord_2432652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432652).length < 2 ^ (prefixWord ++ tailWord_2432652).sum := by decide
  have hdescent : baseEnd_2432652 < baseStart_2432652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432669 : List Nat := [1, 4, 2, 1, 1, 1, 1, 5, 2, 3, 2]
def baseStart_2432669 : Nat := 118140960795 + 2432669 * 2 ^ 59
def prefixEnd_2432669 : Nat := 4983230072969 + 3 ^ 40 * 2432669 * 2
def baseEnd_2432669 : Nat := 1249128470292447905049865

theorem tailTrace_2432669 : CollatzResearch.WordTrace tailWord_2432669 prefixEnd_2432669 1249128470292447905049865 := by
  unfold tailWord_2432669
  simp only [CollatzResearch.WordTrace]
  refine ⟨88726727623863154633309061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59151151749242103088872707 88726727623863154633309061)
  ·
    refine ⟨16636261429474341493745449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88726727623863154633309061 16636261429474341493745449)
    ·
      refine ⟨12477196072105756120309087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16636261429474341493745449 12477196072105756120309087)
      ·
        refine ⟨18715794108158634180463631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12477196072105756120309087 18715794108158634180463631)
        ·
          refine ⟨28073691162237951270695447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18715794108158634180463631 28073691162237951270695447)
          ·
            refine ⟨42110536743356926906043171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28073691162237951270695447 42110536743356926906043171)
            ·
              refine ⟨63165805115035390359064757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42110536743356926906043171 63165805115035390359064757)
              ·
                refine ⟨5921794229534567846162321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63165805115035390359064757 5921794229534567846162321)
                ·
                  refine ⟨4441345672150925884621741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5921794229534567846162321 4441345672150925884621741)
                  ·
                    refine ⟨1665504627056597206733153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4441345672150925884621741 1665504627056597206733153)
                    ·
                      refine ⟨1249128470292447905049865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1665504627056597206733153 1249128470292447905049865)
                      ·
                        rfl

theorem cell23_2432669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_2432669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432669 prefixEnd_2432669 := by exact prefixLift 2432669
  have htrace : WordTrace (prefixWord ++ tailWord_2432669) baseStart_2432669 baseEnd_2432669 := by
    simpa [prefixWord, tailWord_2432669, baseEnd_2432669] using wordTrace_append hprefix tailTrace_2432669
  have hstable : (prefixWord ++ tailWord_2432669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432669).length < 2 ^ (prefixWord ++ tailWord_2432669).sum := by decide
  have hdescent : baseEnd_2432669 < baseStart_2432669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432675 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 3, 6]
def baseStart_2432675 : Nat := 118140960795 + 2432675 * 2 ^ 59
def prefixEnd_2432675 : Nat := 4983230072969 + 3 ^ 40 * 2432675 * 2
def baseEnd_2432675 : Nat := 416377183725458293858279

theorem tailTrace_2432675 : CollatzResearch.WordTrace tailWord_2432675 prefixEnd_2432675 416377183725458293858279 := by
  unfold tailWord_2432675
  simp only [CollatzResearch.WordTrace]
  refine ⟨88726946461841417658027479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59151297641227611772018319 88726946461841417658027479)
  ·
    refine ⟨133090419692762126487041219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88726946461841417658027479 133090419692762126487041219)
    ·
      refine ⟨199635629539143189730561829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133090419692762126487041219 199635629539143189730561829)
      ·
        refine ⟨37431680538589348074480343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 199635629539143189730561829 37431680538589348074480343)
        ·
          refine ⟨56147520807884022111720515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37431680538589348074480343 56147520807884022111720515)
          ·
            refine ⟨84221281211826033167580773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56147520807884022111720515 84221281211826033167580773)
            ·
              refine ⟨15791490227217381218921395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84221281211826033167580773 15791490227217381218921395)
              ·
                refine ⟨23687235340826071828382093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15791490227217381218921395 23687235340826071828382093)
                ·
                  refine ⟨8882713252809776935643285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23687235340826071828382093 8882713252809776935643285)
                  ·
                    refine ⟨416377183725458293858279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8882713252809776935643285 416377183725458293858279)
                    ·
                      rfl

theorem cell23_2432675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 6].length) (baseStart_2432675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432675 prefixEnd_2432675 := by exact prefixLift 2432675
  have htrace : WordTrace (prefixWord ++ tailWord_2432675) baseStart_2432675 baseEnd_2432675 := by
    simpa [prefixWord, tailWord_2432675, baseEnd_2432675] using wordTrace_append hprefix tailTrace_2432675
  have hstable : (prefixWord ++ tailWord_2432675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432675).length < 2 ^ (prefixWord ++ tailWord_2432675).sum := by decide
  have hdescent : baseEnd_2432675 < baseStart_2432675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432693 : List Nat := [1, 3, 3, 3, 2, 2, 1, 1, 3, 1, 3]
def baseStart_2432693 : Nat := 118140960795 + 2432693 * 2 ^ 59
def prefixEnd_2432693 : Nat := 4983230072969 + 3 ^ 40 * 2432693 * 2
def baseEnd_2432693 : Nat := 1249140793828155811149755

theorem tailTrace_2432693 : CollatzResearch.WordTrace tailWord_2432693 prefixEnd_2432693 1249140793828155811149755 := by
  unfold tailWord_2432693
  simp only [CollatzResearch.WordTrace]
  refine ⟨88727602975776206732182733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59151735317184137821455155 88727602975776206732182733)
  ·
    refine ⟨33272851115916077524568525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88727602975776206732182733 33272851115916077524568525)
    ·
      refine ⟨12477319168468529071713197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33272851115916077524568525 12477319168468529071713197)
      ·
        refine ⟨4678994688175698401892449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12477319168468529071713197 4678994688175698401892449)
        ·
          refine ⟨3509246016131773801419337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4678994688175698401892449 3509246016131773801419337)
          ·
            refine ⟨2631934512098830351064503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3509246016131773801419337 2631934512098830351064503)
            ·
              refine ⟨3947901768148245526596755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2631934512098830351064503 3947901768148245526596755)
              ·
                refine ⟨5921852652222368289895133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3947901768148245526596755 5921852652222368289895133)
                ·
                  refine ⟨2220694744583388108710675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5921852652222368289895133 2220694744583388108710675)
                  ·
                    refine ⟨3331042116875082163066013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2220694744583388108710675 3331042116875082163066013)
                    ·
                      refine ⟨1249140793828155811149755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3331042116875082163066013 1249140793828155811149755)
                      ·
                        rfl

theorem cell23_2432693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_2432693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432693 prefixEnd_2432693 := by exact prefixLift 2432693
  have htrace : WordTrace (prefixWord ++ tailWord_2432693) baseStart_2432693 baseEnd_2432693 := by
    simpa [prefixWord, tailWord_2432693, baseEnd_2432693] using wordTrace_append hprefix tailTrace_2432693
  have hstable : (prefixWord ++ tailWord_2432693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432693).length < 2 ^ (prefixWord ++ tailWord_2432693).sum := by decide
  have hdescent : baseEnd_2432693 < baseStart_2432693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432712 : List Nat := [2, 1, 3, 1, 2, 2, 2, 3, 1, 2, 4]
def baseStart_2432712 : Nat := 118140960795 + 2432712 * 2 ^ 59
def prefixEnd_2432712 : Nat := 4983230072969 + 3 ^ 40 * 2432712 * 2
def baseEnd_2432712 : Nat := 1249150549960591236812167

theorem tailTrace_2432712 : CollatzResearch.WordTrace tailWord_2432712 prefixEnd_2432712 1249150549960591236812167 := by
  unfold tailWord_2432712
  simp only [CollatzResearch.WordTrace]
  refine ⟨44364147981353686488562195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59152197308471581984749593 44364147981353686488562195)
  ·
    refine ⟨66546221972030529732843293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44364147981353686488562195 66546221972030529732843293)
    ·
      refine ⟨24954833239511448649816235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66546221972030529732843293 24954833239511448649816235)
      ·
        refine ⟨37432249859267172974724353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24954833239511448649816235 37432249859267172974724353)
        ·
          refine ⟨28074187394450379731043265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37432249859267172974724353 28074187394450379731043265)
          ·
            refine ⟨21055640545837784798282449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28074187394450379731043265 21055640545837784798282449)
            ·
              refine ⟨15791730409378338598711837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21055640545837784798282449 15791730409378338598711837)
              ·
                refine ⟨5921898903516876974516939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15791730409378338598711837 5921898903516876974516939)
                ·
                  refine ⟨8882848355275315461775409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5921898903516876974516939 8882848355275315461775409)
                  ·
                    refine ⟨6662136266456486596331557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8882848355275315461775409 6662136266456486596331557)
                    ·
                      refine ⟨1249150549960591236812167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6662136266456486596331557 1249150549960591236812167)
                      ·
                        rfl

theorem cell23_2432712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_2432712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432712 prefixEnd_2432712 := by exact prefixLift 2432712
  have htrace : WordTrace (prefixWord ++ tailWord_2432712) baseStart_2432712 baseEnd_2432712 := by
    simpa [prefixWord, tailWord_2432712, baseEnd_2432712] using wordTrace_append hprefix tailTrace_2432712
  have hstable : (prefixWord ++ tailWord_2432712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432712).length < 2 ^ (prefixWord ++ tailWord_2432712).sum := by decide
  have hdescent : baseEnd_2432712 < baseStart_2432712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432722 : List Nat := [3, 2, 2, 2, 2, 1, 2, 9]
def baseStart_2432722 : Nat := 118140960795 + 2432722 * 2 ^ 59
def prefixEnd_2432722 : Nat := 4983230072969 + 3 ^ 40 * 2432722 * 2
def baseEnd_2432722 : Nat := 46265025361745785099523

theorem tailTrace_2432722 : CollatzResearch.WordTrace tailWord_2432722 prefixEnd_2432722 46265025361745785099523 := by
  unfold tailWord_2432722
  simp only [CollatzResearch.WordTrace]
  refine ⟨22182165173167786171247105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59152440461780763123325613 22182165173167786171247105)
  ·
    refine ⟨16636623879875839628435329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22182165173167786171247105 16636623879875839628435329)
    ·
      refine ⟨12477467909906879721326497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16636623879875839628435329 12477467909906879721326497)
      ·
        refine ⟨9358100932430159790994873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12477467909906879721326497 9358100932430159790994873)
        ·
          refine ⟨7018575699322619843246155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9358100932430159790994873 7018575699322619843246155)
          ·
            refine ⟨10527863548983929764869233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7018575699322619843246155 10527863548983929764869233)
            ·
              refine ⟨7895897661737947323651925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10527863548983929764869233 7895897661737947323651925)
              ·
                refine ⟨46265025361745785099523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7895897661737947323651925 46265025361745785099523)
                ·
                  rfl

theorem cell23_2432722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 9].length) (baseStart_2432722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432722 prefixEnd_2432722 := by exact prefixLift 2432722
  have htrace : WordTrace (prefixWord ++ tailWord_2432722) baseStart_2432722 baseEnd_2432722 := by
    simpa [prefixWord, tailWord_2432722, baseEnd_2432722] using wordTrace_append hprefix tailTrace_2432722
  have hstable : (prefixWord ++ tailWord_2432722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432722).length < 2 ^ (prefixWord ++ tailWord_2432722).sum := by decide
  have hdescent : baseEnd_2432722 < baseStart_2432722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432743 : List Nat := [1, 1, 5, 4, 1, 1, 2, 2, 2, 4]
def baseStart_2432743 : Nat := 118140960795 + 2432743 * 2 ^ 59
def prefixEnd_2432743 : Nat := 4983230072969 + 3 ^ 40 * 2432743 * 2
def baseEnd_2432743 : Nat := 416388822620293538508175

theorem tailTrace_2432743 : CollatzResearch.WordTrace tailWord_2432743 prefixEnd_2432743 416388822620293538508175 := by
  unfold tailWord_2432743
  simp only [CollatzResearch.WordTrace]
  refine ⟨88729426625595065271502883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59152951083730043514335255 88729426625595065271502883)
  ·
    refine ⟨133094139938392597907254325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88729426625595065271502883 133094139938392597907254325)
    ·
      refine ⟨12477575619224306053805093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133094139938392597907254325 12477575619224306053805093)
      ·
        refine ⟨2339545428604557385088455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12477575619224306053805093 2339545428604557385088455)
        ·
          refine ⟨3509318142906836077632683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2339545428604557385088455 3509318142906836077632683)
          ·
            refine ⟨5263977214360254116449025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3509318142906836077632683 5263977214360254116449025)
            ·
              refine ⟨3947982910770190587336769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5263977214360254116449025 3947982910770190587336769)
              ·
                refine ⟨2960987183077642940502577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3947982910770190587336769 2960987183077642940502577)
                ·
                  refine ⟨2220740387308232205376933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2960987183077642940502577 2220740387308232205376933)
                  ·
                    refine ⟨416388822620293538508175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2220740387308232205376933 416388822620293538508175)
                    ·
                      rfl

theorem cell23_2432743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_2432743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432743 prefixEnd_2432743 := by exact prefixLift 2432743
  have htrace : WordTrace (prefixWord ++ tailWord_2432743) baseStart_2432743 baseEnd_2432743 := by
    simpa [prefixWord, tailWord_2432743, baseEnd_2432743] using wordTrace_append hprefix tailTrace_2432743
  have hstable : (prefixWord ++ tailWord_2432743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432743).length < 2 ^ (prefixWord ++ tailWord_2432743).sum := by decide
  have hdescent : baseEnd_2432743 < baseStart_2432743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432756 : List Nat := [2, 6, 1, 1, 1, 1, 3, 8]
def baseStart_2432756 : Nat := 118140960795 + 2432756 * 2 ^ 59
def prefixEnd_2432756 : Nat := 4983230072969 + 3 ^ 40 * 2432756 * 2
def baseEnd_2432756 : Nat := 46265671967014409802295

theorem tailTrace_2432756 : CollatzResearch.WordTrace tailWord_2432756 prefixEnd_2432756 46265671967014409802295 := by
  unfold tailWord_2432756
  simp only [CollatzResearch.WordTrace]
  refine ⟨44364950387273984245863061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59153267183031978994484081 44364950387273984245863061)
  ·
    refine ⟨2079607049403468011524831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 44364950387273984245863061 2079607049403468011524831)
    ·
      refine ⟨3119410574105202017287247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2079607049403468011524831 3119410574105202017287247)
      ·
        refine ⟨4679115861157803025930871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3119410574105202017287247 4679115861157803025930871)
        ·
          refine ⟨7018673791736704538896307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4679115861157803025930871 7018673791736704538896307)
          ·
            refine ⟨10528010687605056808344461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7018673791736704538896307 10528010687605056808344461)
            ·
              refine ⟨3948004007851896303129173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10528010687605056808344461 3948004007851896303129173)
              ·
                refine ⟨46265671967014409802295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3948004007851896303129173 46265671967014409802295)
                ·
                  rfl

theorem cell23_2432756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 8].length) (baseStart_2432756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432756 prefixEnd_2432756 := by exact prefixLift 2432756
  have htrace : WordTrace (prefixWord ++ tailWord_2432756) baseStart_2432756 baseEnd_2432756 := by
    simpa [prefixWord, tailWord_2432756, baseEnd_2432756] using wordTrace_append hprefix tailTrace_2432756
  have hstable : (prefixWord ++ tailWord_2432756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432756).length < 2 ^ (prefixWord ++ tailWord_2432756).sum := by decide
  have hdescent : baseEnd_2432756 < baseStart_2432756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432759 : List Nat := [1, 1, 3, 1, 1, 1, 5, 2, 3, 3, 2]
def baseStart_2432759 : Nat := 118140960795 + 2432759 * 2 ^ 59
def prefixEnd_2432759 : Nat := 4983230072969 + 3 ^ 40 * 2432759 * 2
def baseEnd_2432759 : Nat := 1249174683551352552924451

theorem tailTrace_2432759 : CollatzResearch.WordTrace tailWord_2432759 prefixEnd_2432759 1249174683551352552924451 := by
  unfold tailWord_2432759
  simp only [CollatzResearch.WordTrace]
  refine ⟨88730010193537100004085331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59153340129024733336056887 88730010193537100004085331)
  ·
    refine ⟨133095015290305650006127997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88730010193537100004085331 133095015290305650006127997)
    ·
      refine ⟨49910630733864618752297999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133095015290305650006127997 49910630733864618752297999)
      ·
        refine ⟨74865946100796928128446999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49910630733864618752297999 74865946100796928128446999)
        ·
          refine ⟨112298919151195392192670499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74865946100796928128446999 112298919151195392192670499)
          ·
            refine ⟨168448378726793088289005749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112298919151195392192670499 168448378726793088289005749)
            ·
              refine ⟨15792035505636852027094289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 168448378726793088289005749 15792035505636852027094289)
              ·
                refine ⟨11844026629227639020320717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15792035505636852027094289 11844026629227639020320717)
                ·
                  refine ⟨4441509985960364632620269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11844026629227639020320717 4441509985960364632620269)
                  ·
                    refine ⟨1665566244735136737232601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4441509985960364632620269 1665566244735136737232601)
                    ·
                      refine ⟨1249174683551352552924451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1665566244735136737232601 1249174683551352552924451)
                      ·
                        rfl

theorem cell23_2432759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 3, 2].length) (baseStart_2432759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432759 prefixEnd_2432759 := by exact prefixLift 2432759
  have htrace : WordTrace (prefixWord ++ tailWord_2432759) baseStart_2432759 baseEnd_2432759 := by
    simpa [prefixWord, tailWord_2432759, baseEnd_2432759] using wordTrace_append hprefix tailTrace_2432759
  have hstable : (prefixWord ++ tailWord_2432759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432759).length < 2 ^ (prefixWord ++ tailWord_2432759).sum := by decide
  have hdescent : baseEnd_2432759 < baseStart_2432759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432776 : List Nat := [2, 1, 3, 2, 2, 1, 2, 4, 1, 3, 2]
def baseStart_2432776 : Nat := 118140960795 + 2432776 * 2 ^ 59
def prefixEnd_2432776 : Nat := 4983230072969 + 3 ^ 40 * 2432776 * 2
def baseEnd_2432776 : Nat := 1249183412722478986411873

theorem tailTrace_2432776 : CollatzResearch.WordTrace tailWord_2432776 prefixEnd_2432776 1249183412722478986411873 := by
  unfold tailWord_2432776
  simp only [CollatzResearch.WordTrace]
  refine ⟨44365315117237755953727091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59153753489650341271636121 44365315117237755953727091)
  ·
    refine ⟨66547972675856633930590637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44365315117237755953727091 66547972675856633930590637)
    ·
      refine ⟨24955489753446237723971489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66547972675856633930590637 24955489753446237723971489)
      ·
        refine ⟨18716617315084678292978617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24955489753446237723971489 18716617315084678292978617)
        ·
          refine ⟨14037462986313508719733963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18716617315084678292978617 14037462986313508719733963)
          ·
            refine ⟨21056194479470263079600945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14037462986313508719733963 21056194479470263079600945)
            ·
              refine ⟨15792145859602697309700709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21056194479470263079600945 15792145859602697309700709)
              ·
                refine ⟨2961027348675505745568883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15792145859602697309700709 2961027348675505745568883)
                ·
                  refine ⟨4441541023013258618353325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2961027348675505745568883 4441541023013258618353325)
                  ·
                    refine ⟨1665577883629971981882497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4441541023013258618353325 1665577883629971981882497)
                    ·
                      refine ⟨1249183412722478986411873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1665577883629971981882497 1249183412722478986411873)
                      ·
                        rfl

theorem cell23_2432776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_2432776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432776 prefixEnd_2432776 := by exact prefixLift 2432776
  have htrace : WordTrace (prefixWord ++ tailWord_2432776) baseStart_2432776 baseEnd_2432776 := by
    simpa [prefixWord, tailWord_2432776, baseEnd_2432776] using wordTrace_append hprefix tailTrace_2432776
  have hstable : (prefixWord ++ tailWord_2432776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432776).length < 2 ^ (prefixWord ++ tailWord_2432776).sum := by decide
  have hdescent : baseEnd_2432776 < baseStart_2432776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432792 : List Nat := [2, 1, 2, 3, 1, 1, 2, 3, 2, 1, 5]
def baseStart_2432792 : Nat := 118140960795 + 2432792 * 2 ^ 59
def prefixEnd_2432792 : Nat := 4983230072969 + 3 ^ 40 * 2432792 * 2
def baseEnd_2432792 : Nat := 1249191628412950923811799

theorem tailTrace_2432792 : CollatzResearch.WordTrace tailWord_2432792 prefixEnd_2432792 1249191628412950923811799 := by
  unfold tailWord_2432792
  simp only [CollatzResearch.WordTrace]
  refine ⟨44365606901208773320018315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59154142534945031093357753 44365606901208773320018315)
  ·
    refine ⟨66548410351813159980027473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44365606901208773320018315 66548410351813159980027473)
    ·
      refine ⟨49911307763859869985020605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66548410351813159980027473 49911307763859869985020605)
      ·
        refine ⟨18716740411447451244382727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49911307763859869985020605 18716740411447451244382727)
        ·
          refine ⟨28075110617171176866574091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18716740411447451244382727 28075110617171176866574091)
          ·
            refine ⟨42112665925756765299861137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28075110617171176866574091 42112665925756765299861137)
            ·
              refine ⟨31584499444317573974895853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42112665925756765299861137 31584499444317573974895853)
              ·
                refine ⟨11844187291619090240585945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31584499444317573974895853 11844187291619090240585945)
                ·
                  refine ⟨8883140468714317680439459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11844187291619090240585945 8883140468714317680439459)
                  ·
                    refine ⟨13324710703071476520659189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8883140468714317680439459 13324710703071476520659189)
                    ·
                      refine ⟨1249191628412950923811799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13324710703071476520659189 1249191628412950923811799)
                      ·
                        rfl

theorem cell23_2432792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_2432792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432792 prefixEnd_2432792 := by exact prefixLift 2432792
  have htrace : WordTrace (prefixWord ++ tailWord_2432792) baseStart_2432792 baseEnd_2432792 := by
    simpa [prefixWord, tailWord_2432792, baseEnd_2432792] using wordTrace_append hprefix tailTrace_2432792
  have hstable : (prefixWord ++ tailWord_2432792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432792).length < 2 ^ (prefixWord ++ tailWord_2432792).sum := by decide
  have hdescent : baseEnd_2432792 < baseStart_2432792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432812 : List Nat := [2, 2, 1, 1, 1, 5, 1, 3, 7]
def baseStart_2432812 : Nat := 118140960795 + 2432812 * 2 ^ 59
def prefixEnd_2432812 : Nat := 4983230072969 + 3 ^ 40 * 2432812 * 2
def baseEnd_2432812 : Nat := 138800210891782316173523

theorem tailTrace_2432812 : CollatzResearch.WordTrace tailWord_2432812 prefixEnd_2432812 138800210891782316173523 := by
  unfold tailWord_2432812
  simp only [CollatzResearch.WordTrace]
  refine ⟨44365971631172545027882345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59154628841563393370509793 44365971631172545027882345)
  ·
    refine ⟨33274478723379408770911759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44365971631172545027882345 33274478723379408770911759)
    ·
      refine ⟨49911718085069113156367639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33274478723379408770911759 49911718085069113156367639)
      ·
        refine ⟨74867577127603669734551459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49911718085069113156367639 74867577127603669734551459)
        ·
          refine ⟨112301365691405504601827189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74867577127603669734551459 112301365691405504601827189)
          ·
            refine ⟨10528253033569266056421299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 112301365691405504601827189 10528253033569266056421299)
            ·
              refine ⟨15792379550353899084631949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10528253033569266056421299 15792379550353899084631949)
              ·
                refine ⟨5922142331382712156736981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15792379550353899084631949 5922142331382712156736981)
                ·
                  refine ⟨138800210891782316173523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5922142331382712156736981 138800210891782316173523)
                  ·
                    rfl

theorem cell23_2432812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 7].length) (baseStart_2432812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432812 prefixEnd_2432812 := by exact prefixLift 2432812
  have htrace : WordTrace (prefixWord ++ tailWord_2432812) baseStart_2432812 baseEnd_2432812 := by
    simpa [prefixWord, tailWord_2432812, baseEnd_2432812] using wordTrace_append hprefix tailTrace_2432812
  have hstable : (prefixWord ++ tailWord_2432812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432812).length < 2 ^ (prefixWord ++ tailWord_2432812).sum := by decide
  have hdescent : baseEnd_2432812 < baseStart_2432812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432829 : List Nat := [1, 4, 1, 4, 1, 1, 2, 2, 7]
def baseStart_2432829 : Nat := 118140960795 + 2432829 * 2 ^ 59
def prefixEnd_2432829 : Nat := 4983230072969 + 3 ^ 40 * 2432829 * 2
def baseEnd_2432829 : Nat := 138801180799685253227681

theorem tailTrace_2432829 : CollatzResearch.WordTrace tailWord_2432829 prefixEnd_2432829 138801180799685253227681 := by
  unfold tailWord_2432829
  simp only [CollatzResearch.WordTrace]
  refine ⟨88732563303283501959133541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59155042202189001306089027 88732563303283501959133541)
  ·
    refine ⟨16637355619365656617337539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88732563303283501959133541 16637355619365656617337539)
    ·
      refine ⟨24956033429048484926006309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16637355619365656617337539 24956033429048484926006309)
      ·
        refine ⟨4679256267946590923626183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24956033429048484926006309 4679256267946590923626183)
        ·
          refine ⟨7018884401919886385439275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4679256267946590923626183 7018884401919886385439275)
          ·
            refine ⟨10528326602879829578158913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7018884401919886385439275 10528326602879829578158913)
            ·
              refine ⟨7896244952159872183619185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10528326602879829578158913 7896244952159872183619185)
              ·
                refine ⟨5922183714119904137714389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7896244952159872183619185 5922183714119904137714389)
                ·
                  refine ⟨138801180799685253227681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5922183714119904137714389 138801180799685253227681)
                  ·
                    rfl

theorem cell23_2432829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 7].length) (baseStart_2432829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432829 prefixEnd_2432829 := by exact prefixLift 2432829
  have htrace : WordTrace (prefixWord ++ tailWord_2432829) baseStart_2432829 baseEnd_2432829 := by
    simpa [prefixWord, tailWord_2432829, baseEnd_2432829] using wordTrace_append hprefix tailTrace_2432829
  have hstable : (prefixWord ++ tailWord_2432829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432829).length < 2 ^ (prefixWord ++ tailWord_2432829).sum := by decide
  have hdescent : baseEnd_2432829 < baseStart_2432829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432842 : List Nat := [3, 1, 2, 1, 1, 1, 3, 3, 1, 7]
def baseStart_2432842 : Nat := 118140960795 + 2432842 * 2 ^ 59
def prefixEnd_2432842 : Nat := 4983230072969 + 3 ^ 40 * 2432842 * 2
def baseEnd_2432842 : Nat := 416405767481891909395523

theorem tailTrace_2432842 : CollatzResearch.WordTrace tailWord_2432842 prefixEnd_2432842 416405767481891909395523 := by
  unfold tailWord_2432842
  simp only [CollatzResearch.WordTrace]
  refine ⟨22183259363059101294839195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59155358301490936786237853 22183259363059101294839195)
  ·
    refine ⟨33274889044588651942258793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22183259363059101294839195 33274889044588651942258793)
    ·
      refine ⟨24956166783441488956694095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33274889044588651942258793 24956166783441488956694095)
      ·
        refine ⟨37434250175162233435041143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24956166783441488956694095 37434250175162233435041143)
        ·
          refine ⟨56151375262743350152561715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37434250175162233435041143 56151375262743350152561715)
          ·
            refine ⟨84227062894115025228842573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56151375262743350152561715 84227062894115025228842573)
            ·
              refine ⟨31585148585293134460815965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84227062894115025228842573 31585148585293134460815965)
              ·
                refine ⟨11844430719484925422805987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31585148585293134460815965 11844430719484925422805987)
                ·
                  refine ⟨17766646079227388134208981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11844430719484925422805987 17766646079227388134208981)
                  ·
                    refine ⟨416405767481891909395523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17766646079227388134208981 416405767481891909395523)
                    ·
                      rfl

theorem cell23_2432842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_2432842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432842 prefixEnd_2432842 := by exact prefixLift 2432842
  have htrace : WordTrace (prefixWord ++ tailWord_2432842) baseStart_2432842 baseEnd_2432842 := by
    simpa [prefixWord, tailWord_2432842, baseEnd_2432842] using wordTrace_append hprefix tailTrace_2432842
  have hstable : (prefixWord ++ tailWord_2432842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432842).length < 2 ^ (prefixWord ++ tailWord_2432842).sum := by decide
  have hdescent : baseEnd_2432842 < baseStart_2432842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432874 : List Nat := [3, 1, 3, 4, 1, 2, 2, 1, 2, 2, 2]
def baseStart_2432874 : Nat := 118140960795 + 2432874 * 2 ^ 59
def prefixEnd_2432874 : Nat := 4983230072969 + 3 ^ 40 * 2432874 * 2
def baseEnd_2432874 : Nat := 1249233733826619602986423

theorem tailTrace_2432874 : CollatzResearch.WordTrace tailWord_2432874 prefixEnd_2432874 1249233733826619602986423 := by
  unfold tailWord_2432874
  simp only [CollatzResearch.WordTrace]
  refine ⟨22183551147030118661130419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59156136392080316429681117 22183551147030118661130419)
  ·
    refine ⟨33275326720545177991695629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22183551147030118661130419 33275326720545177991695629)
    ·
      refine ⟨12478247520204441746885861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33275326720545177991695629 12478247520204441746885861)
      ·
        refine ⟨2339671410038332827541099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12478247520204441746885861 2339671410038332827541099)
        ·
          refine ⟨3509507115057499241311649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2339671410038332827541099 3509507115057499241311649)
          ·
            refine ⟨2632130336293124430983737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3509507115057499241311649 2632130336293124430983737)
            ·
              refine ⟨1974097752219843323237803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2632130336293124430983737 1974097752219843323237803)
              ·
                refine ⟨2961146628329764984856705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1974097752219843323237803 2961146628329764984856705)
                ·
                  refine ⟨2220859971247323738642529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2961146628329764984856705 2220859971247323738642529)
                  ·
                    refine ⟨1665644978435492803981897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2220859971247323738642529 1665644978435492803981897)
                    ·
                      refine ⟨1249233733826619602986423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1665644978435492803981897 1249233733826619602986423)
                      ·
                        rfl

theorem cell23_2432874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_2432874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432874 prefixEnd_2432874 := by exact prefixLift 2432874
  have htrace : WordTrace (prefixWord ++ tailWord_2432874) baseStart_2432874 baseEnd_2432874 := by
    simpa [prefixWord, tailWord_2432874, baseEnd_2432874] using wordTrace_append hprefix tailTrace_2432874
  have hstable : (prefixWord ++ tailWord_2432874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432874).length < 2 ^ (prefixWord ++ tailWord_2432874).sum := by decide
  have hdescent : baseEnd_2432874 < baseStart_2432874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432889 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 5, 4]
def baseStart_2432889 : Nat := 118140960795 + 2432889 * 2 ^ 59
def prefixEnd_2432889 : Nat := 4983230072969 + 3 ^ 40 * 2432889 * 2
def baseEnd_2432889 : Nat := 416413812012145681432951

theorem tailTrace_2432889 : CollatzResearch.WordTrace tailWord_2432889 prefixEnd_2432889 416413812012145681432951 := by
  unfold tailWord_2432889
  simp only [CollatzResearch.WordTrace]
  refine ⟨88734751683066132206317721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59156501122044088137545147 88734751683066132206317721)
  ·
    refine ⟨66551063762299599154738291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88734751683066132206317721 66551063762299599154738291)
    ·
      refine ⟨99826595643449398732107437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66551063762299599154738291 99826595643449398732107437)
      ·
        refine ⟨37434973366293524524540289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99826595643449398732107437 37434973366293524524540289)
        ·
          refine ⟨28076230024720143393405217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37434973366293524524540289 28076230024720143393405217)
          ·
            refine ⟨21057172518540107545053913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28076230024720143393405217 21057172518540107545053913)
            ·
              refine ⟨15792879388905080658790435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21057172518540107545053913 15792879388905080658790435)
              ·
                refine ⟨23689319083357620988185653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15792879388905080658790435 23689319083357620988185653)
                ·
                  refine ⟨2220873664064776967642405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23689319083357620988185653 2220873664064776967642405)
                  ·
                    refine ⟨416413812012145681432951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2220873664064776967642405 416413812012145681432951)
                    ·
                      rfl

theorem cell23_2432889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5, 4].length) (baseStart_2432889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432889 prefixEnd_2432889 := by exact prefixLift 2432889
  have htrace : WordTrace (prefixWord ++ tailWord_2432889) baseStart_2432889 baseEnd_2432889 := by
    simpa [prefixWord, tailWord_2432889, baseEnd_2432889] using wordTrace_append hprefix tailTrace_2432889
  have hstable : (prefixWord ++ tailWord_2432889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432889).length < 2 ^ (prefixWord ++ tailWord_2432889).sum := by decide
  have hdescent : baseEnd_2432889 < baseStart_2432889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432892 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 3, 3, 6]
def baseStart_2432892 : Nat := 118140960795 + 2432892 * 2 ^ 59
def prefixEnd_2432892 : Nat := 4983230072969 + 3 ^ 40 * 2432892 * 2
def baseEnd_2432892 : Nat := 1249242976478400532561339

theorem tailTrace_2432892 : CollatzResearch.WordTrace tailWord_2432892 prefixEnd_2432892 1249242976478400532561339 := by
  unfold tailWord_2432892
  simp only [CollatzResearch.WordTrace]
  refine ⟨44367430551027631859338465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59156574068036842479117953 44367430551027631859338465)
  ·
    refine ⟨33275572913270723894503849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44367430551027631859338465 33275572913270723894503849)
    ·
      refine ⟨24956679684953042920877887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33275572913270723894503849 24956679684953042920877887)
      ·
        refine ⟨37435019527429564381316831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24956679684953042920877887 37435019527429564381316831)
        ·
          refine ⟨56152529291144346571975247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37435019527429564381316831 56152529291144346571975247)
          ·
            refine ⟨84228793936716519857962871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56152529291144346571975247 84228793936716519857962871)
            ·
              refine ⟨126343190905074779786944307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84228793936716519857962871 126343190905074779786944307)
              ·
                refine ⟨189514786357612169680416461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126343190905074779786944307 189514786357612169680416461)
                ·
                  refine ⟨71068044884104563630156173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189514786357612169680416461 71068044884104563630156173)
                  ·
                    refine ⟨26650516831539211361308565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71068044884104563630156173 26650516831539211361308565)
                    ·
                      refine ⟨1249242976478400532561339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26650516831539211361308565 1249242976478400532561339)
                      ·
                        rfl

theorem cell23_2432892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_2432892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432892 prefixEnd_2432892 := by exact prefixLift 2432892
  have htrace : WordTrace (prefixWord ++ tailWord_2432892) baseStart_2432892 baseEnd_2432892 := by
    simpa [prefixWord, tailWord_2432892, baseEnd_2432892] using wordTrace_append hprefix tailTrace_2432892
  have hstable : (prefixWord ++ tailWord_2432892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432892).length < 2 ^ (prefixWord ++ tailWord_2432892).sum := by decide
  have hdescent : baseEnd_2432892 < baseStart_2432892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432919 : List Nat := [1, 1, 3, 3, 1, 3, 1, 4, 6]
def baseStart_2432919 : Nat := 118140960795 + 2432919 * 2 ^ 59
def prefixEnd_2432919 : Nat := 4983230072969 + 3 ^ 40 * 2432919 * 2
def baseEnd_2432919 : Nat := 138806315606230214102635

theorem tailTrace_2432919 : CollatzResearch.WordTrace tailWord_2432919 prefixEnd_2432919 138806315606230214102635 := by
  unfold tailWord_2432919
  simp only [CollatzResearch.WordTrace]
  refine ⟨88735845872957447329909811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59157230581971631553273207 88735845872957447329909811)
  ·
    refine ⟨133103768809436170994864717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88735845872957447329909811 133103768809436170994864717)
    ·
      refine ⟨49913913303538564123074269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133103768809436170994864717 49913913303538564123074269)
      ·
        refine ⟨18717717488826961546152851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49913913303538564123074269 18717717488826961546152851)
        ·
          refine ⟨28076576233240442319229277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18717717488826961546152851 28076576233240442319229277)
          ·
            refine ⟨10528716087465165869710979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28076576233240442319229277 10528716087465165869710979)
            ·
              refine ⟨15793074131197748804566469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10528716087465165869710979 15793074131197748804566469)
              ·
                refine ⟨2961201399599577900856213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15793074131197748804566469 2961201399599577900856213)
                ·
                  refine ⟨138806315606230214102635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2961201399599577900856213 138806315606230214102635)
                  ·
                    rfl

theorem cell23_2432919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 6].length) (baseStart_2432919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432919 prefixEnd_2432919 := by exact prefixLift 2432919
  have htrace : WordTrace (prefixWord ++ tailWord_2432919) baseStart_2432919 baseEnd_2432919 := by
    simpa [prefixWord, tailWord_2432919, baseEnd_2432919] using wordTrace_append hprefix tailTrace_2432919
  have hstable : (prefixWord ++ tailWord_2432919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432919).length < 2 ^ (prefixWord ++ tailWord_2432919).sum := by decide
  have hdescent : baseEnd_2432919 < baseStart_2432919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2432980 : List Nat := [2, 4, 1, 2, 1, 1, 1, 6, 1, 1, 3]
def baseStart_2432980 : Nat := 118140960795 + 2432980 * 2 ^ 59
def prefixEnd_2432980 : Nat := 4983230072969 + 3 ^ 40 * 2432980 * 2
def baseEnd_2432980 : Nat := 1249288162775996188260935

theorem tailTrace_2432980 : CollatzResearch.WordTrace tailWord_2432980 prefixEnd_2432980 1249288162775996188260935 := by
  unfold tailWord_2432980
  simp only [CollatzResearch.WordTrace]
  refine ⟨44369035362868227373940197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59158713817157636498586929 44369035362868227373940197)
  ·
    refine ⟨8319194130537792632613787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44369035362868227373940197 8319194130537792632613787)
    ·
      refine ⟨12478791195806688948920681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8319194130537792632613787 12478791195806688948920681)
      ·
        refine ⟨9359093396855016711690511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12478791195806688948920681 9359093396855016711690511)
        ·
          refine ⟨14038640095282525067535767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9359093396855016711690511 14038640095282525067535767)
          ·
            refine ⟨21057960142923787601303651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14038640095282525067535767 21057960142923787601303651)
            ·
              refine ⟨31586940214385681401955477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21057960142923787601303651 31586940214385681401955477)
              ·
                refine ⟨1480637822549328815716663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31586940214385681401955477 1480637822549328815716663)
                ·
                  refine ⟨2220956733823993223574995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1480637822549328815716663 2220956733823993223574995)
                  ·
                    refine ⟨3331435100735989835362493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2220956733823993223574995 3331435100735989835362493)
                    ·
                      refine ⟨1249288162775996188260935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3331435100735989835362493 1249288162775996188260935)
                      ·
                        rfl

theorem cell23_2432980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_2432980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2432980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2432980 prefixEnd_2432980 := by exact prefixLift 2432980
  have htrace : WordTrace (prefixWord ++ tailWord_2432980) baseStart_2432980 baseEnd_2432980 := by
    simpa [prefixWord, tailWord_2432980, baseEnd_2432980] using wordTrace_append hprefix tailTrace_2432980
  have hstable : (prefixWord ++ tailWord_2432980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2432980).length < 2 ^ (prefixWord ++ tailWord_2432980).sum := by decide
  have hdescent : baseEnd_2432980 < baseStart_2432980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2432980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433014 : List Nat := [5, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3]
def baseStart_2433014 : Nat := 118140960795 + 2433014 * 2 ^ 59
def prefixEnd_2433014 : Nat := 4983230072969 + 3 ^ 40 * 2433014 * 2
def baseEnd_2433014 : Nat := 1249305621118249055235779

theorem tailTrace_2433014 : CollatzResearch.WordTrace tailWord_2433014 prefixEnd_2433014 1249305621118249055235779 := by
  unfold tailWord_2433014
  simp only [CollatzResearch.WordTrace]
  refine ⟨5546206925475829909663631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59159540538408852369745397 5546206925475829909663631)
  ·
    refine ⟨8319310388213744864495447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5546206925475829909663631 8319310388213744864495447)
    ·
      refine ⟨12478965582320617296743171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8319310388213744864495447 12478965582320617296743171)
      ·
        refine ⟨18718448373480925945114757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12478965582320617296743171 18718448373480925945114757)
        ·
          refine ⟨3509709070027673614709017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18718448373480925945114757 3509709070027673614709017)
          ·
            refine ⟨2632281802520755211031763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3509709070027673614709017 2632281802520755211031763)
            ·
              refine ⟨3948422703781132816547645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2632281802520755211031763 3948422703781132816547645)
              ·
                refine ⟨1480658513917924806205367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3948422703781132816547645 1480658513917924806205367)
                ·
                  refine ⟨2220987770876887209308051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1480658513917924806205367 2220987770876887209308051)
                  ·
                    refine ⟨3331481656315330813962077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2220987770876887209308051 3331481656315330813962077)
                    ·
                      refine ⟨1249305621118249055235779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3331481656315330813962077 1249305621118249055235779)
                      ·
                        rfl

theorem cell23_2433014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_2433014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433014 prefixEnd_2433014 := by exact prefixLift 2433014
  have htrace : WordTrace (prefixWord ++ tailWord_2433014) baseStart_2433014 baseEnd_2433014 := by
    simpa [prefixWord, tailWord_2433014, baseEnd_2433014] using wordTrace_append hprefix tailTrace_2433014
  have hstable : (prefixWord ++ tailWord_2433014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433014).length < 2 ^ (prefixWord ++ tailWord_2433014).sum := by decide
  have hdescent : baseEnd_2433014 < baseStart_2433014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433047 : List Nat := [1, 1, 3, 5, 2, 2, 2, 1, 2, 4]
def baseStart_2433047 : Nat := 118140960795 + 2433047 * 2 ^ 59
def prefixEnd_2433047 : Nat := 4983230072969 + 3 ^ 40 * 2433047 * 2
def baseEnd_2433047 : Nat := 416440855326615808707709

theorem tailTrace_2433047 : CollatzResearch.WordTrace tailWord_2433047 prefixEnd_2433047 416440855326615808707709 := by
  unfold tailWord_2433047
  simp only [CollatzResearch.WordTrace]
  refine ⟨88740514416493725190569395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59160342944329150127046263 88740514416493725190569395)
  ·
    refine ⟨133110771624740587785854093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88740514416493725190569395 133110771624740587785854093)
    ·
      refine ⟨49916539359277720419695285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133110771624740587785854093 49916539359277720419695285)
      ·
        refine ⟨4679675564932286289346433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49916539359277720419695285 4679675564932286289346433)
        ·
          refine ⟨3509756673699214717009825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4679675564932286289346433 3509756673699214717009825)
          ·
            refine ⟨2632317505274411037757369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3509756673699214717009825 2632317505274411037757369)
            ·
              refine ⟨1974238128955808278318027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2632317505274411037757369 1974238128955808278318027)
              ·
                refine ⟨2961357193433712417477041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1974238128955808278318027 2961357193433712417477041)
                ·
                  refine ⟨2221017895075284313107781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2961357193433712417477041 2221017895075284313107781)
                  ·
                    refine ⟨416440855326615808707709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2221017895075284313107781 416440855326615808707709)
                    ·
                      rfl

theorem cell23_2433047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 2, 4].length) (baseStart_2433047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433047 prefixEnd_2433047 := by exact prefixLift 2433047
  have htrace : WordTrace (prefixWord ++ tailWord_2433047) baseStart_2433047 baseEnd_2433047 := by
    simpa [prefixWord, tailWord_2433047, baseEnd_2433047] using wordTrace_append hprefix tailTrace_2433047
  have hstable : (prefixWord ++ tailWord_2433047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433047).length < 2 ^ (prefixWord ++ tailWord_2433047).sum := by decide
  have hdescent : baseEnd_2433047 < baseStart_2433047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433057 : List Nat := [1, 2, 3, 2, 5, 1, 1, 2, 1, 2, 3]
def baseStart_2433057 : Nat := 118140960795 + 2433057 * 2 ^ 59
def prefixEnd_2433057 : Nat := 4983230072969 + 3 ^ 40 * 2433057 * 2
def baseEnd_2433057 : Nat := 1249327700786392386998081

theorem tailTrace_2433057 : CollatzResearch.WordTrace tailWord_2433057 prefixEnd_2433057 1249327700786392386998081 := by
  unfold tailWord_2433057
  simp only [CollatzResearch.WordTrace]
  refine ⟨88740879146457496898433425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59160586097638331265622283 88740879146457496898433425)
  ·
    refine ⟨66555659359843122673825069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88740879146457496898433425 66555659359843122673825069)
    ·
      refine ⟨24958372259941171002684401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66555659359843122673825069 24958372259941171002684401)
      ·
        refine ⟨18718779194955878252013301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24958372259941171002684401 18718779194955878252013301)
        ·
          refine ⟨1754885549527113586126247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18718779194955878252013301 1754885549527113586126247)
          ·
            refine ⟨2632328324290670379189371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1754885549527113586126247 2632328324290670379189371)
            ·
              refine ⟨3948492486436005568784057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2632328324290670379189371 3948492486436005568784057)
              ·
                refine ⟨2961369364827004176588043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3948492486436005568784057 2961369364827004176588043)
                ·
                  refine ⟨4442054047240506264882065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2961369364827004176588043 4442054047240506264882065)
                  ·
                    refine ⟨3331540535430379698661549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4442054047240506264882065 3331540535430379698661549)
                    ·
                      refine ⟨1249327700786392386998081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3331540535430379698661549 1249327700786392386998081)
                      ·
                        rfl

theorem cell23_2433057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_2433057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433057 prefixEnd_2433057 := by exact prefixLift 2433057
  have htrace : WordTrace (prefixWord ++ tailWord_2433057) baseStart_2433057 baseEnd_2433057 := by
    simpa [prefixWord, tailWord_2433057, baseEnd_2433057] using wordTrace_append hprefix tailTrace_2433057
  have hstable : (prefixWord ++ tailWord_2433057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433057).length < 2 ^ (prefixWord ++ tailWord_2433057).sum := by decide
  have hdescent : baseEnd_2433057 < baseStart_2433057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433116 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 9]
def baseStart_2433116 : Nat := 118140960795 + 2433116 * 2 ^ 59
def prefixEnd_2433116 : Nat := 4983230072969 + 3 ^ 40 * 2433116 * 2
def baseEnd_2433116 : Nat := 138817555127223072906701

theorem tailTrace_2433116 : CollatzResearch.WordTrace tailWord_2433116 prefixEnd_2433116 138817555127223072906701 := by
  unfold tailWord_2433116
  simp only [CollatzResearch.WordTrace]
  refine ⟨44371515526621874987415601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59162020702162499983220801 44371515526621874987415601)
  ·
    refine ⟨33278636644966406240561701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44371515526621874987415601 33278636644966406240561701)
    ·
      refine ⟨6239744370931201170105319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33278636644966406240561701 6239744370931201170105319)
      ·
        refine ⟨9359616556396801755157979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6239744370931201170105319 9359616556396801755157979)
        ·
          refine ⟨14039424834595202632736969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9359616556396801755157979 14039424834595202632736969)
          ·
            refine ⟨10529568625946401974552727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14039424834595202632736969 10529568625946401974552727)
            ·
              refine ⟨15794352938919602961829091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10529568625946401974552727 15794352938919602961829091)
              ·
                refine ⟨23691529408379404442743637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15794352938919602961829091 23691529408379404442743637)
                ·
                  refine ⟨138817555127223072906701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23691529408379404442743637 138817555127223072906701)
                  ·
                    rfl

theorem cell23_2433116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 9].length) (baseStart_2433116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433116 prefixEnd_2433116 := by exact prefixLift 2433116
  have htrace : WordTrace (prefixWord ++ tailWord_2433116) baseStart_2433116 baseEnd_2433116 := by
    simpa [prefixWord, tailWord_2433116, baseEnd_2433116] using wordTrace_append hprefix tailTrace_2433116
  have hstable : (prefixWord ++ tailWord_2433116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433116).length < 2 ^ (prefixWord ++ tailWord_2433116).sum := by decide
  have hdescent : baseEnd_2433116 < baseStart_2433116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433156 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_2433156 : Nat := 118140960795 + 2433156 * 2 ^ 59
def prefixEnd_2433156 : Nat := 4983230072969 + 3 ^ 40 * 2433156 * 2
def baseEnd_2433156 : Nat := 1249378535371187499660125

theorem tailTrace_2433156 : CollatzResearch.WordTrace tailWord_2433156 prefixEnd_2433156 1249378535371187499660125 := by
  unfold tailWord_2433156
  simp only [CollatzResearch.WordTrace]
  refine ⟨44372244986549418403143661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59162993315399224537524881 44372244986549418403143661)
  ·
    refine ⟨16639591869956031901178873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44372244986549418403143661 16639591869956031901178873)
    ·
      refine ⟨12479693902467023925884155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16639591869956031901178873 12479693902467023925884155)
      ·
        refine ⟨18719540853700535888826233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12479693902467023925884155 18719540853700535888826233)
        ·
          refine ⟨14039655640275401916619675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18719540853700535888826233 14039655640275401916619675)
          ·
            refine ⟨21059483460413102874929513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14039655640275401916619675 21059483460413102874929513)
            ·
              refine ⟨15794612595309827156197135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21059483460413102874929513 15794612595309827156197135)
              ·
                refine ⟨23691918892964740734295703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15794612595309827156197135 23691918892964740734295703)
                ·
                  refine ⟨35537878339447111101443555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23691918892964740734295703 35537878339447111101443555)
                  ·
                    refine ⟨53306817509170666652165333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35537878339447111101443555 53306817509170666652165333)
                    ·
                      refine ⟨1249378535371187499660125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53306817509170666652165333 1249378535371187499660125)
                      ·
                        rfl

theorem cell23_2433156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_2433156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433156 prefixEnd_2433156 := by exact prefixLift 2433156
  have htrace : WordTrace (prefixWord ++ tailWord_2433156) baseStart_2433156 baseEnd_2433156 := by
    simpa [prefixWord, tailWord_2433156, baseEnd_2433156] using wordTrace_append hprefix tailTrace_2433156
  have hstable : (prefixWord ++ tailWord_2433156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433156).length < 2 ^ (prefixWord ++ tailWord_2433156).sum := by decide
  have hdescent : baseEnd_2433156 < baseStart_2433156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433183 : List Nat := [1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 4]
def baseStart_2433183 : Nat := 118140960795 + 2433183 * 2 ^ 59
def prefixEnd_2433183 : Nat := 4983230072969 + 3 ^ 40 * 2433183 * 2
def baseEnd_2433183 : Nat := 1249392399348858894022501

theorem tailTrace_2433183 : CollatzResearch.WordTrace tailWord_2433183 prefixEnd_2433183 1249392399348858894022501 := by
  unfold tailWord_2433183
  simp only [CollatzResearch.WordTrace]
  refine ⟨88745474744001020417520203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59163649829334013611680135 88745474744001020417520203)
  ·
    refine ⟨133118212116001530626280305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88745474744001020417520203 133118212116001530626280305)
    ·
      refine ⟨99838659087001147969710229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133118212116001530626280305 99838659087001147969710229)
      ·
        refine ⟨4679937144703178811080167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 99838659087001147969710229 4679937144703178811080167)
        ·
          refine ⟨7019905717054768216620251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4679937144703178811080167 7019905717054768216620251)
          ·
            refine ⟨10529858575582152324930377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7019905717054768216620251 10529858575582152324930377)
            ·
              refine ⟨7897393931686614243697783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10529858575582152324930377 7897393931686614243697783)
              ·
                refine ⟨11846090897529921365546675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7897393931686614243697783 11846090897529921365546675)
                ·
                  refine ⟨17769136346294882048320013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11846090897529921365546675 17769136346294882048320013)
                  ·
                    refine ⟨6663426129860580768120005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17769136346294882048320013 6663426129860580768120005)
                    ·
                      refine ⟨1249392399348858894022501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6663426129860580768120005 1249392399348858894022501)
                      ·
                        rfl

theorem cell23_2433183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_2433183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433183 prefixEnd_2433183 := by exact prefixLift 2433183
  have htrace : WordTrace (prefixWord ++ tailWord_2433183) baseStart_2433183 baseEnd_2433183 := by
    simpa [prefixWord, tailWord_2433183, baseEnd_2433183] using wordTrace_append hprefix tailTrace_2433183
  have hstable : (prefixWord ++ tailWord_2433183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433183).length < 2 ^ (prefixWord ++ tailWord_2433183).sum := by decide
  have hdescent : baseEnd_2433183 < baseStart_2433183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433210 : List Nat := [3, 1, 1, 1, 2, 2, 2, 6, 1, 4]
def baseStart_2433210 : Nat := 118140960795 + 2433210 * 2 ^ 59
def prefixEnd_2433210 : Nat := 4983230072969 + 3 ^ 40 * 2433210 * 2
def baseEnd_2433210 : Nat := 416468754442176762794959

theorem tailTrace_2433210 : CollatzResearch.WordTrace tailWord_2433210 prefixEnd_2433210 416468754442176762794959 := by
  unfold tailWord_2433210
  simp only [CollatzResearch.WordTrace]
  refine ⟨22186614878725801007188271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59164306343268802685835389 22186614878725801007188271)
  ·
    refine ⟨33279922318088701510782407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22186614878725801007188271 33279922318088701510782407)
    ·
      refine ⟨49919883477133052266173611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33279922318088701510782407 49919883477133052266173611)
      ·
        refine ⟨74879825215699578399260417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49919883477133052266173611 74879825215699578399260417)
        ·
          refine ⟨56159868911774683799445313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74879825215699578399260417 56159868911774683799445313)
          ·
            refine ⟨42119901683831012849583985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56159868911774683799445313 42119901683831012849583985)
            ·
              refine ⟨31589926262873259637187989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42119901683831012849583985 31589926262873259637187989)
              ·
                refine ⟨1480777793572184045493187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31589926262873259637187989 1480777793572184045493187)
                ·
                  refine ⟨2221166690358276068239781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1480777793572184045493187 2221166690358276068239781)
                  ·
                    refine ⟨416468754442176762794959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2221166690358276068239781 416468754442176762794959)
                    ·
                      rfl

theorem cell23_2433210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6, 1, 4].length) (baseStart_2433210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433210 prefixEnd_2433210 := by exact prefixLift 2433210
  have htrace : WordTrace (prefixWord ++ tailWord_2433210) baseStart_2433210 baseEnd_2433210 := by
    simpa [prefixWord, tailWord_2433210, baseEnd_2433210] using wordTrace_append hprefix tailTrace_2433210
  have hstable : (prefixWord ++ tailWord_2433210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433210).length < 2 ^ (prefixWord ++ tailWord_2433210).sum := by decide
  have hdescent : baseEnd_2433210 < baseStart_2433210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433237 : List Nat := [1, 3, 2, 4, 2, 1, 2, 1, 2, 2, 3]
def baseStart_2433237 : Nat := 118140960795 + 2433237 * 2 ^ 59
def prefixEnd_2433237 : Nat := 4983230072969 + 3 ^ 40 * 2433237 * 2
def baseEnd_2433237 : Nat := 1249420127304201682747253

theorem tailTrace_2433237 : CollatzResearch.WordTrace tailWord_2433237 prefixEnd_2433237 1249420127304201682747253 := by
  unfold tailWord_2433237
  simp only [CollatzResearch.WordTrace]
  refine ⟨88747444285805387639985965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59164962857203591759990643 88747444285805387639985965)
  ·
    refine ⟨33280291607177020364994737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88747444285805387639985965 33280291607177020364994737)
    ·
      refine ⟨24960218705382765273746053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33280291607177020364994737 24960218705382765273746053)
      ·
        refine ⟨4680041007259268488827385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24960218705382765273746053 4680041007259268488827385)
        ·
          refine ⟨3510030755444451366620539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4680041007259268488827385 3510030755444451366620539)
          ·
            refine ⟨5265046133166677049930809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3510030755444451366620539 5265046133166677049930809)
            ·
              refine ⟨3948784599875007787448107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5265046133166677049930809 3948784599875007787448107)
              ·
                refine ⟨5923176899812511681172161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3948784599875007787448107 5923176899812511681172161)
                ·
                  refine ⟨4442382674859383760879121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5923176899812511681172161 4442382674859383760879121)
                  ·
                    refine ⟨3331787006144537820659341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4442382674859383760879121 3331787006144537820659341)
                    ·
                      refine ⟨1249420127304201682747253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3331787006144537820659341 1249420127304201682747253)
                      ·
                        rfl

theorem cell23_2433237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_2433237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433237 prefixEnd_2433237 := by exact prefixLift 2433237
  have htrace : WordTrace (prefixWord ++ tailWord_2433237) baseStart_2433237 baseEnd_2433237 := by
    simpa [prefixWord, tailWord_2433237, baseEnd_2433237] using wordTrace_append hprefix tailTrace_2433237
  have hstable : (prefixWord ++ tailWord_2433237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433237).length < 2 ^ (prefixWord ++ tailWord_2433237).sum := by decide
  have hdescent : baseEnd_2433237 < baseStart_2433237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433260 : List Nat := [2, 2, 1, 1, 2, 3, 1, 4, 2, 3, 2]
def baseStart_2433260 : Nat := 118140960795 + 2433260 * 2 ^ 59
def prefixEnd_2433260 : Nat := 4983230072969 + 3 ^ 40 * 2433260 * 2
def baseEnd_2433260 : Nat := 1249431937359255092759647

theorem tailTrace_2433260 : CollatzResearch.WordTrace tailWord_2433260 prefixEnd_2433260 1249431937359255092759647 := by
  unfold tailWord_2433260
  simp only [CollatzResearch.WordTrace]
  refine ⟨44374141582361031284036617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59165522109814708378715489 44374141582361031284036617)
  ·
    refine ⟨33280606186770773463027463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44374141582361031284036617 33280606186770773463027463)
    ·
      refine ⟨49920909280156160194541195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33280606186770773463027463 49920909280156160194541195)
      ·
        refine ⟨74881363920234240291811793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49920909280156160194541195 74881363920234240291811793)
        ·
          refine ⟨56161022940175680218858845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74881363920234240291811793 56161022940175680218858845)
          ·
            refine ⟨21060383602565880082072067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56161022940175680218858845 21060383602565880082072067)
            ·
              refine ⟨31590575403848820123108101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21060383602565880082072067 31590575403848820123108101)
              ·
                refine ⟨5923232888221653773082769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31590575403848820123108101 5923232888221653773082769)
                ·
                  refine ⟨4442424666166240329812077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5923232888221653773082769 4442424666166240329812077)
                  ·
                    refine ⟨1665909249812340123679529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4442424666166240329812077 1665909249812340123679529)
                    ·
                      refine ⟨1249431937359255092759647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1665909249812340123679529 1249431937359255092759647)
                      ·
                        rfl

theorem cell23_2433260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 3, 2].length) (baseStart_2433260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433260 prefixEnd_2433260 := by exact prefixLift 2433260
  have htrace : WordTrace (prefixWord ++ tailWord_2433260) baseStart_2433260 baseEnd_2433260 := by
    simpa [prefixWord, tailWord_2433260, baseEnd_2433260] using wordTrace_append hprefix tailTrace_2433260
  have hstable : (prefixWord ++ tailWord_2433260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433260).length < 2 ^ (prefixWord ++ tailWord_2433260).sum := by decide
  have hdescent : baseEnd_2433260 < baseStart_2433260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433261 : List Nat := [1, 5, 1, 2, 3, 2, 2, 2, 1, 4]
def baseStart_2433261 : Nat := 118140960795 + 2433261 * 2 ^ 59
def prefixEnd_2433261 : Nat := 4983230072969 + 3 ^ 40 * 2433261 * 2
def baseEnd_2433261 : Nat := 416477483613303196282381

theorem tailTrace_2433261 : CollatzResearch.WordTrace tailWord_2433261 prefixEnd_2433261 416477483613303196282381 := by
  unfold tailWord_2433261
  simp only [CollatzResearch.WordTrace]
  refine ⟨88748319637718439738859637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59165546425145626492573091 88748319637718439738859637)
  ·
    refine ⟨8320154966036103725518091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88748319637718439738859637 8320154966036103725518091)
    ·
      refine ⟨12480232449054155588277137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8320154966036103725518091 12480232449054155588277137)
      ·
        refine ⟨9360174336790616691207853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12480232449054155588277137 9360174336790616691207853)
        ·
          refine ⟨3510065376296481259202945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9360174336790616691207853 3510065376296481259202945)
          ·
            refine ⟨2632549032222360944402209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3510065376296481259202945 2632549032222360944402209)
            ·
              refine ⟨1974411774166770708301657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2632549032222360944402209 1974411774166770708301657)
              ·
                refine ⟨1480808830625078031226243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1974411774166770708301657 1480808830625078031226243)
                ·
                  refine ⟨2221213245937617046839365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1480808830625078031226243 2221213245937617046839365)
                  ·
                    refine ⟨416477483613303196282381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2221213245937617046839365 416477483613303196282381)
                    ·
                      rfl

theorem cell23_2433261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_2433261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433261 prefixEnd_2433261 := by exact prefixLift 2433261
  have htrace : WordTrace (prefixWord ++ tailWord_2433261) baseStart_2433261 baseEnd_2433261 := by
    simpa [prefixWord, tailWord_2433261, baseEnd_2433261] using wordTrace_append hprefix tailTrace_2433261
  have hstable : (prefixWord ++ tailWord_2433261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433261).length < 2 ^ (prefixWord ++ tailWord_2433261).sum := by decide
  have hdescent : baseEnd_2433261 < baseStart_2433261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433267 : List Nat := [1, 1, 1, 2, 2, 4, 3, 4, 1, 1, 3]
def baseStart_2433267 : Nat := 118140960795 + 2433267 * 2 ^ 59
def prefixEnd_2433267 : Nat := 4983230072969 + 3 ^ 40 * 2433267 * 2
def baseEnd_2433267 : Nat := 1249435531723836565372115

theorem tailTrace_2433267 : CollatzResearch.WordTrace tailWord_2433267 prefixEnd_2433267 1249435531723836565372115 := by
  unfold tailWord_2433267
  simp only [CollatzResearch.WordTrace]
  refine ⟨88748538475696702763578055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59165692317131135175718703 88748538475696702763578055)
  ·
    refine ⟨133122807713545054145367083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88748538475696702763578055 133122807713545054145367083)
    ·
      refine ⟨199684211570317581218050625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133122807713545054145367083 199684211570317581218050625)
      ·
        refine ⟨149763158677738185913537969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199684211570317581218050625 149763158677738185913537969)
        ·
          refine ⟨112322369008303639435153477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149763158677738185913537969 112322369008303639435153477)
          ·
            refine ⟨21060444189056932394091277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112322369008303639435153477 21060444189056932394091277)
            ·
              refine ⟨7897666570896349647784229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21060444189056932394091277 7897666570896349647784229)
              ·
                refine ⟨1480812482043065558959543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7897666570896349647784229 1480812482043065558959543)
                ·
                  refine ⟨2221218723064598338439315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1480812482043065558959543 2221218723064598338439315)
                  ·
                    refine ⟨3331828084596897507658973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2221218723064598338439315 3331828084596897507658973)
                    ·
                      refine ⟨1249435531723836565372115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3331828084596897507658973 1249435531723836565372115)
                      ·
                        rfl

theorem cell23_2433267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4, 1, 1, 3].length) (baseStart_2433267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433267 prefixEnd_2433267 := by exact prefixLift 2433267
  have htrace : WordTrace (prefixWord ++ tailWord_2433267) baseStart_2433267 baseEnd_2433267 := by
    simpa [prefixWord, tailWord_2433267, baseEnd_2433267] using wordTrace_append hprefix tailTrace_2433267
  have hstable : (prefixWord ++ tailWord_2433267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433267).length < 2 ^ (prefixWord ++ tailWord_2433267).sum := by decide
  have hdescent : baseEnd_2433267 < baseStart_2433267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433283 : List Nat := [1, 1, 1, 3, 2, 3, 4, 1, 1, 6]
def baseStart_2433283 : Nat := 118140960795 + 2433283 * 2 ^ 59
def prefixEnd_2433283 : Nat := 4983230072969 + 3 ^ 40 * 2433283 * 2
def baseEnd_2433283 : Nat := 416481249138102834257347

theorem tailTrace_2433283 : CollatzResearch.WordTrace tailWord_2433283 prefixEnd_2433283 416481249138102834257347 := by
  unfold tailWord_2433283
  simp only [CollatzResearch.WordTrace]
  refine ⟨88749122043638737496160503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59166081362425824997440335 88749122043638737496160503)
  ·
    refine ⟨133123683065458106244240755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88749122043638737496160503 133123683065458106244240755)
    ·
      refine ⟨199685524598187159366361133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133123683065458106244240755 199685524598187159366361133)
      ·
        refine ⟨74882071724320184762385425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199685524598187159366361133 74882071724320184762385425)
        ·
          refine ⟨56161553793240138571789069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74882071724320184762385425 56161553793240138571789069)
          ·
            refine ⟨21060582672465051964420901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56161553793240138571789069 21060582672465051964420901)
            ·
              refine ⟨3948859251087197243328919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21060582672465051964420901 3948859251087197243328919)
              ·
                refine ⟨5923288876630795864993379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3948859251087197243328919 5923288876630795864993379)
                ·
                  refine ⟨8884933314946193797490069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5923288876630795864993379 8884933314946193797490069)
                  ·
                    refine ⟨416481249138102834257347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8884933314946193797490069 416481249138102834257347)
                    ·
                      rfl

theorem cell23_2433283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 6].length) (baseStart_2433283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433283 prefixEnd_2433283 := by exact prefixLift 2433283
  have htrace : WordTrace (prefixWord ++ tailWord_2433283) baseStart_2433283 baseEnd_2433283 := by
    simpa [prefixWord, tailWord_2433283, baseEnd_2433283] using wordTrace_append hprefix tailTrace_2433283
  have hstable : (prefixWord ++ tailWord_2433283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433283).length < 2 ^ (prefixWord ++ tailWord_2433283).sum := by decide
  have hdescent : baseEnd_2433283 < baseStart_2433283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433324 : List Nat := [2, 2, 1, 1, 1, 3, 4, 4, 1, 2, 2]
def baseStart_2433324 : Nat := 118140960795 + 2433324 * 2 ^ 59
def prefixEnd_2433324 : Nat := 4983230072969 + 3 ^ 40 * 2433324 * 2
def baseEnd_2433324 : Nat := 1249464800121142842359353

theorem tailTrace_2433324 : CollatzResearch.WordTrace tailWord_2433324 prefixEnd_2433324 1249464800121142842359353 := by
  unfold tailWord_2433324
  simp only [CollatzResearch.WordTrace]
  refine ⟨44375308718245100749201513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59167078290993467665602017 44375308718245100749201513)
  ·
    refine ⟨33281481538683825561901135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44375308718245100749201513 33281481538683825561901135)
    ·
      refine ⟨49922222308025738342851703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33281481538683825561901135 49922222308025738342851703)
      ·
        refine ⟨74883333462038607514277555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49922222308025738342851703 74883333462038607514277555)
        ·
          refine ⟨112325000193057911271416333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74883333462038607514277555 112325000193057911271416333)
          ·
            refine ⟨42121875072396716726781125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112325000193057911271416333 42121875072396716726781125)
            ·
              refine ⟨7897851576074384386271461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42121875072396716726781125 7897851576074384386271461)
              ·
                refine ⟨1480847170513947072425899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7897851576074384386271461 1480847170513947072425899)
                ·
                  refine ⟨2221270755770920608638849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1480847170513947072425899 2221270755770920608638849)
                  ·
                    refine ⟨1665953066828190456479137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2221270755770920608638849 1665953066828190456479137)
                    ·
                      refine ⟨1249464800121142842359353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1665953066828190456479137 1249464800121142842359353)
                      ·
                        rfl

theorem cell23_2433324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4, 1, 2, 2].length) (baseStart_2433324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433324 prefixEnd_2433324 := by exact prefixLift 2433324
  have htrace : WordTrace (prefixWord ++ tailWord_2433324) baseStart_2433324 baseEnd_2433324 := by
    simpa [prefixWord, tailWord_2433324, baseEnd_2433324] using wordTrace_append hprefix tailTrace_2433324
  have hstable : (prefixWord ++ tailWord_2433324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433324).length < 2 ^ (prefixWord ++ tailWord_2433324).sum := by decide
  have hdescent : baseEnd_2433324 < baseStart_2433324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433337 : List Nat := [1, 2, 1, 6, 1, 3, 1, 1, 1, 2, 4]
def baseStart_2433337 : Nat := 118140960795 + 2433337 * 2 ^ 59
def prefixEnd_2433337 : Nat := 4983230072969 + 3 ^ 40 * 2433337 * 2
def baseEnd_2433337 : Nat := 1249471475369651291496793

theorem tailTrace_2433337 : CollatzResearch.WordTrace tailWord_2433337 prefixEnd_2433337 1249471475369651291496793 := by
  unfold tailWord_2433337
  simp only [CollatzResearch.WordTrace]
  refine ⟨88751091585443104718626265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59167394390295403145750843 88751091585443104718626265)
  ·
    refine ⟨66563318689082328538969699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88751091585443104718626265 66563318689082328538969699)
    ·
      refine ⟨99844978033623492808454549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66563318689082328538969699 99844978033623492808454549)
      ·
        refine ⟨4680233345326101225396307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 99844978033623492808454549 4680233345326101225396307)
        ·
          refine ⟨7020350017989151838094461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4680233345326101225396307 7020350017989151838094461)
          ·
            refine ⟨2632631256745931939285423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7020350017989151838094461 2632631256745931939285423)
            ·
              refine ⟨3948946885118897908928135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2632631256745931939285423 3948946885118897908928135)
              ·
                refine ⟨5923420327678346863392203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3948946885118897908928135 5923420327678346863392203)
                ·
                  refine ⟨8885130491517520295088305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5923420327678346863392203 8885130491517520295088305)
                  ·
                    refine ⟨6663847868638140221316229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8885130491517520295088305 6663847868638140221316229)
                    ·
                      refine ⟨1249471475369651291496793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6663847868638140221316229 1249471475369651291496793)
                      ·
                        rfl

theorem cell23_2433337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_2433337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433337 prefixEnd_2433337 := by exact prefixLift 2433337
  have htrace : WordTrace (prefixWord ++ tailWord_2433337) baseStart_2433337 baseEnd_2433337 := by
    simpa [prefixWord, tailWord_2433337, baseEnd_2433337] using wordTrace_append hprefix tailTrace_2433337
  have hstable : (prefixWord ++ tailWord_2433337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433337).length < 2 ^ (prefixWord ++ tailWord_2433337).sum := by decide
  have hdescent : baseEnd_2433337 < baseStart_2433337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433367 : List Nat := [1, 1, 3, 2, 3, 1, 1, 5, 1, 3, 2]
def baseStart_2433367 : Nat := 118140960795 + 2433367 * 2 ^ 59
def prefixEnd_2433367 : Nat := 4983230072969 + 3 ^ 40 * 2433367 * 2
def baseEnd_2433367 : Nat := 1249486879789286174121655

theorem tailTrace_2433367 : CollatzResearch.WordTrace tailWord_2433367 prefixEnd_2433367 1249486879789286174121655 := by
  unfold tailWord_2433367
  simp only [CollatzResearch.WordTrace]
  refine ⟨88752185775334419842218355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59168123850222946561478903 88752185775334419842218355)
  ·
    refine ⟨133128278663001629763327533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88752185775334419842218355 133128278663001629763327533)
    ·
      refine ⟨49923104498625611161247825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133128278663001629763327533 49923104498625611161247825)
      ·
        refine ⟨37442328373969208370935869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49923104498625611161247825 37442328373969208370935869)
        ·
          refine ⟨14040873140238453139100951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37442328373969208370935869 14040873140238453139100951)
          ·
            refine ⟨21061309710357679708651427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14040873140238453139100951 21061309710357679708651427)
            ·
              refine ⟨31591964565536519562977141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21061309710357679708651427 31591964565536519562977141)
              ·
                refine ⟨2961746678019048709029107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31591964565536519562977141 2961746678019048709029107)
                ·
                  refine ⟨4442620017028573063543661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2961746678019048709029107 4442620017028573063543661)
                  ·
                    refine ⟨1665982506385714898828873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4442620017028573063543661 1665982506385714898828873)
                    ·
                      refine ⟨1249486879789286174121655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1665982506385714898828873 1249486879789286174121655)
                      ·
                        rfl

theorem cell23_2433367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 3, 2].length) (baseStart_2433367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433367 prefixEnd_2433367 := by exact prefixLift 2433367
  have htrace : WordTrace (prefixWord ++ tailWord_2433367) baseStart_2433367 baseEnd_2433367 := by
    simpa [prefixWord, tailWord_2433367, baseEnd_2433367] using wordTrace_append hprefix tailTrace_2433367
  have hstable : (prefixWord ++ tailWord_2433367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433367).length < 2 ^ (prefixWord ++ tailWord_2433367).sum := by decide
  have hdescent : baseEnd_2433367 < baseStart_2433367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433393 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 1, 4, 4]
def baseStart_2433393 : Nat := 118140960795 + 2433393 * 2 ^ 59
def prefixEnd_2433393 : Nat := 4983230072969 + 3 ^ 40 * 2433393 * 2
def baseEnd_2433393 : Nat := 1249500230286303072396535

theorem tailTrace_2433393 : CollatzResearch.WordTrace tailWord_2433393 prefixEnd_2433393 1249500230286303072396535 := by
  unfold tailWord_2433393
  simp only [CollatzResearch.WordTrace]
  refine ⟨88753134073240226282664833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59168756048826817521776555 88753134073240226282664833)
  ·
    refine ⟨66564850554930169711998625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88753134073240226282664833 66564850554930169711998625)
    ·
      refine ⟨49923637916197627283998969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66564850554930169711998625 49923637916197627283998969)
      ·
        refine ⟨37442728437148220462999227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49923637916197627283998969 37442728437148220462999227)
        ·
          refine ⟨56164092655722330694498841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37442728437148220462999227 56164092655722330694498841)
          ·
            refine ⟨42123069491791748020874131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56164092655722330694498841 42123069491791748020874131)
            ·
              refine ⟨63184604237687622031311197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42123069491791748020874131 63184604237687622031311197)
              ·
                refine ⟨23694226589132858261741699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63184604237687622031311197 23694226589132858261741699)
                ·
                  refine ⟨35541339883699287392612549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23694226589132858261741699 35541339883699287392612549)
                  ·
                    refine ⟨6664001228193616386114853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35541339883699287392612549 6664001228193616386114853)
                    ·
                      refine ⟨1249500230286303072396535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6664001228193616386114853 1249500230286303072396535)
                      ·
                        rfl

theorem cell23_2433393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_2433393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433393 prefixEnd_2433393 := by exact prefixLift 2433393
  have htrace : WordTrace (prefixWord ++ tailWord_2433393) baseStart_2433393 baseEnd_2433393 := by
    simpa [prefixWord, tailWord_2433393, baseEnd_2433393] using wordTrace_append hprefix tailTrace_2433393
  have hstable : (prefixWord ++ tailWord_2433393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433393).length < 2 ^ (prefixWord ++ tailWord_2433393).sum := by decide
  have hdescent : baseEnd_2433393 < baseStart_2433393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433418 : List Nat := [3, 1, 2, 5, 1, 1, 3, 1, 1, 3, 2]
def baseStart_2433418 : Nat := 118140960795 + 2433418 * 2 ^ 59
def prefixEnd_2433418 : Nat := 4983230072969 + 3 ^ 40 * 2433418 * 2
def baseEnd_2433418 : Nat := 1249513067302665474583921

theorem tailTrace_2433418 : CollatzResearch.WordTrace tailWord_2433418 prefixEnd_2433418 1249513067302665474583921 := by
  unfold tailWord_2433418
  simp only [CollatzResearch.WordTrace]
  refine ⟨22188511474537413888081227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59169363932099770368216605 22188511474537413888081227)
  ·
    refine ⟨33282767211806120832121841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22188511474537413888081227 33282767211806120832121841)
    ·
      refine ⟨24962075408854590624091381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33282767211806120832121841 24962075408854590624091381)
      ·
        refine ⟨2340194569580117871008567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24962075408854590624091381 2340194569580117871008567)
        ·
          refine ⟨3510291854370176806512851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2340194569580117871008567 3510291854370176806512851)
          ·
            refine ⟨5265437781555265209769277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3510291854370176806512851 5265437781555265209769277)
            ·
              refine ⟨1974539168083224453663479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5265437781555265209769277 1974539168083224453663479)
              ·
                refine ⟨2961808752124836680495219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1974539168083224453663479 2961808752124836680495219)
                ·
                  refine ⟨4442713128187255020742829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2961808752124836680495219 4442713128187255020742829)
                  ·
                    refine ⟨1666017423070220632778561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4442713128187255020742829 1666017423070220632778561)
                    ·
                      refine ⟨1249513067302665474583921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1666017423070220632778561 1249513067302665474583921)
                      ·
                        rfl

theorem cell23_2433418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_2433418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433418 prefixEnd_2433418 := by exact prefixLift 2433418
  have htrace : WordTrace (prefixWord ++ tailWord_2433418) baseStart_2433418 baseEnd_2433418 := by
    simpa [prefixWord, tailWord_2433418, baseEnd_2433418] using wordTrace_append hprefix tailTrace_2433418
  have hstable : (prefixWord ++ tailWord_2433418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433418).length < 2 ^ (prefixWord ++ tailWord_2433418).sum := by decide
  have hdescent : baseEnd_2433418 < baseStart_2433418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433447 : List Nat := [1, 1, 6, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_2433447 : Nat := 118140960795 + 2433447 * 2 ^ 59
def prefixEnd_2433447 : Nat := 4983230072969 + 3 ^ 40 * 2433447 * 2
def baseEnd_2433447 : Nat := 1249527958241645861121287

theorem tailTrace_2433447 : CollatzResearch.WordTrace tailWord_2433447 prefixEnd_2433447 1249527958241645861121287 := by
  unfold tailWord_2433447
  simp only [CollatzResearch.WordTrace]
  refine ⟨88755103615044593505130595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59170069076696395670087063 88755103615044593505130595)
  ·
    refine ⟨133132655422566890257695893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88755103615044593505130595 133132655422566890257695893)
    ·
      refine ⟨6240593222932822980829495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 133132655422566890257695893 6240593222932822980829495)
      ·
        refine ⟨9360889834399234471244243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6240593222932822980829495 9360889834399234471244243)
        ·
          refine ⟨14041334751598851706866365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9360889834399234471244243 14041334751598851706866365)
          ·
            refine ⟨5265500531849569390074887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14041334751598851706866365 5265500531849569390074887)
            ·
              refine ⟨7898250797774354085112331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5265500531849569390074887 7898250797774354085112331)
              ·
                refine ⟨11847376196661531127668497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7898250797774354085112331 11847376196661531127668497)
                ·
                  refine ⟨8885532147496148345751373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11847376196661531127668497 8885532147496148345751373)
                  ·
                    refine ⟨3332074555311055629656765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8885532147496148345751373 3332074555311055629656765)
                    ·
                      refine ⟨1249527958241645861121287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3332074555311055629656765 1249527958241645861121287)
                      ·
                        rfl

theorem cell23_2433447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_2433447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433447 prefixEnd_2433447 := by exact prefixLift 2433447
  have htrace : WordTrace (prefixWord ++ tailWord_2433447) baseStart_2433447 baseEnd_2433447 := by
    simpa [prefixWord, tailWord_2433447, baseEnd_2433447] using wordTrace_append hprefix tailTrace_2433447
  have hstable : (prefixWord ++ tailWord_2433447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433447).length < 2 ^ (prefixWord ++ tailWord_2433447).sum := by decide
  have hdescent : baseEnd_2433447 < baseStart_2433447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433497 : List Nat := [1, 2, 1, 2, 4, 1, 4, 1, 3, 4]
def baseStart_2433497 : Nat := 118140960795 + 2433497 * 2 ^ 59
def prefixEnd_2433497 : Nat := 4983230072969 + 3 ^ 40 * 2433497 * 2
def baseEnd_2433497 : Nat := 416517877424790221832019

theorem tailTrace_2433497 : CollatzResearch.WordTrace tailWord_2433497 prefixEnd_2433497 416517877424790221832019 := by
  unfold tailWord_2433497
  simp only [CollatzResearch.WordTrace]
  refine ⟨88756927264863452044450745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59171284843242301362967163 88756927264863452044450745)
  ·
    refine ⟨66567695448647589033338059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88756927264863452044450745 66567695448647589033338059)
    ·
      refine ⟨99851543172971383550007089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66567695448647589033338059 99851543172971383550007089)
      ·
        refine ⟨74888657379728537662505317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99851543172971383550007089 74888657379728537662505317)
        ·
          refine ⟨14041623258699100811719747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74888657379728537662505317 14041623258699100811719747)
          ·
            refine ⟨21062434888048651217579621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14041623258699100811719747 21062434888048651217579621)
            ·
              refine ⟨3949206541509122103296179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21062434888048651217579621 3949206541509122103296179)
              ·
                refine ⟨5923809812263683154944269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3949206541509122103296179 5923809812263683154944269)
                ·
                  refine ⟨2221428679598881183104101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5923809812263683154944269 2221428679598881183104101)
                  ·
                    refine ⟨416517877424790221832019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2221428679598881183104101 416517877424790221832019)
                    ·
                      rfl

theorem cell23_2433497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3, 4].length) (baseStart_2433497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433497 prefixEnd_2433497 := by exact prefixLift 2433497
  have htrace : WordTrace (prefixWord ++ tailWord_2433497) baseStart_2433497 baseEnd_2433497 := by
    simpa [prefixWord, tailWord_2433497, baseEnd_2433497] using wordTrace_append hprefix tailTrace_2433497
  have hstable : (prefixWord ++ tailWord_2433497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433497).length < 2 ^ (prefixWord ++ tailWord_2433497).sum := by decide
  have hdescent : baseEnd_2433497 < baseStart_2433497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433520 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 3]
def baseStart_2433520 : Nat := 118140960795 + 2433520 * 2 ^ 59
def prefixEnd_2433520 : Nat := 4983230072969 + 3 ^ 40 * 2433520 * 2
def baseEnd_2433520 : Nat := 1249565442329424075508451

theorem tailTrace_2433520 : CollatzResearch.WordTrace tailWord_2433520 prefixEnd_2433520 1249565442329424075508451 := by
  unfold tailWord_2433520
  simp only [CollatzResearch.WordTrace]
  refine ⟨44378883071890063486269007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59171844095853417981692009 44378883071890063486269007)
  ·
    refine ⟨66568324607835095229403511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44378883071890063486269007 66568324607835095229403511)
    ·
      refine ⟨99852486911752642844105267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66568324607835095229403511 99852486911752642844105267)
      ·
        refine ⟨149778730367628964266157901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99852486911752642844105267 149778730367628964266157901)
        ·
          refine ⟨56167023887860861599809213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149778730367628964266157901 56167023887860861599809213)
          ·
            refine ⟨21062633957947823099928455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56167023887860861599809213 21062633957947823099928455)
            ·
              refine ⟨31593950936921734649892683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21062633957947823099928455 31593950936921734649892683)
              ·
                refine ⟨47390926405382601974839025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31593950936921734649892683 47390926405382601974839025)
                ·
                  refine ⟨35543194804036951481129269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47390926405382601974839025 35543194804036951481129269)
                  ·
                    refine ⟨3332174512878464201355869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35543194804036951481129269 3332174512878464201355869)
                    ·
                      refine ⟨1249565442329424075508451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3332174512878464201355869 1249565442329424075508451)
                      ·
                        rfl

theorem cell23_2433520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 3].length) (baseStart_2433520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433520 prefixEnd_2433520 := by exact prefixLift 2433520
  have htrace : WordTrace (prefixWord ++ tailWord_2433520) baseStart_2433520 baseEnd_2433520 := by
    simpa [prefixWord, tailWord_2433520, baseEnd_2433520] using wordTrace_append hprefix tailTrace_2433520
  have hstable : (prefixWord ++ tailWord_2433520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433520).length < 2 ^ (prefixWord ++ tailWord_2433520).sum := by decide
  have hdescent : baseEnd_2433520 < baseStart_2433520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433580 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 5]
def baseStart_2433580 : Nat := 118140960795 + 2433580 * 2 ^ 59
def prefixEnd_2433580 : Nat := 4983230072969 + 3 ^ 40 * 2433580 * 2
def baseEnd_2433580 : Nat := 1249596251168693840758175

theorem tailTrace_2433580 : CollatzResearch.WordTrace tailWord_2433580 prefixEnd_2433580 1249596251168693840758175 := by
  unfold tailWord_2433580
  simp only [CollatzResearch.WordTrace]
  refine ⟨44379977261781378609861097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59173303015708504813148129 44379977261781378609861097)
  ·
    refine ⟨33284982946336033957395823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44379977261781378609861097 33284982946336033957395823)
    ·
      refine ⟨49927474419504050936093735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33284982946336033957395823 49927474419504050936093735)
      ·
        refine ⟨74891211629256076404140603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49927474419504050936093735 74891211629256076404140603)
        ·
          refine ⟨112336817443884114606210905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74891211629256076404140603 112336817443884114606210905)
          ·
            refine ⟨84252613082913085954658179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112336817443884114606210905 84252613082913085954658179)
            ·
              refine ⟨126378919624369628931987269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84252613082913085954658179 126378919624369628931987269)
              ·
                refine ⟨23696047429569305424747613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126378919624369628931987269 23696047429569305424747613)
                ·
                  refine ⟨8886017786088489534280355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23696047429569305424747613 8886017786088489534280355)
                  ·
                    refine ⟨13329026679132734301420533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8886017786088489534280355 13329026679132734301420533)
                    ·
                      refine ⟨1249596251168693840758175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13329026679132734301420533 1249596251168693840758175)
                      ·
                        rfl

theorem cell23_2433580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_2433580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433580 prefixEnd_2433580 := by exact prefixLift 2433580
  have htrace : WordTrace (prefixWord ++ tailWord_2433580) baseStart_2433580 baseEnd_2433580 := by
    simpa [prefixWord, tailWord_2433580, baseEnd_2433580] using wordTrace_append hprefix tailTrace_2433580
  have hstable : (prefixWord ++ tailWord_2433580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433580).length < 2 ^ (prefixWord ++ tailWord_2433580).sum := by decide
  have hdescent : baseEnd_2433580 < baseStart_2433580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433617 : List Nat := [1, 2, 2, 1, 3, 5, 1, 8]
def baseStart_2433617 : Nat := 118140960795 + 2433617 * 2 ^ 59
def prefixEnd_2433617 : Nat := 4983230072969 + 3 ^ 40 * 2433617 * 2
def baseEnd_2433617 : Nat := 46282046294552229481315

theorem tailTrace_2433617 : CollatzResearch.WordTrace tailWord_2433617 prefixEnd_2433617 46282046294552229481315 := by
  unfold tailWord_2433617
  simp only [CollatzResearch.WordTrace]
  refine ⟨88761304024428712538819105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59174202682952475025879403 88761304024428712538819105)
  ·
    refine ⟨66570978018321534404114329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88761304024428712538819105 66570978018321534404114329)
    ·
      refine ⟨49928233513741150803085747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66570978018321534404114329 49928233513741150803085747)
      ·
        refine ⟨74892350270611726204628621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49928233513741150803085747 74892350270611726204628621)
        ·
          refine ⟨28084631351479397326735733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74892350270611726204628621 28084631351479397326735733)
          ·
            refine ⟨2632934189201193499381475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28084631351479397326735733 2632934189201193499381475)
            ·
              refine ⟨3949401283801790249072213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2632934189201193499381475 3949401283801790249072213)
              ·
                refine ⟨46282046294552229481315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3949401283801790249072213 46282046294552229481315)
                ·
                  rfl

theorem cell23_2433617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 8].length) (baseStart_2433617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433617 prefixEnd_2433617 := by exact prefixLift 2433617
  have htrace : WordTrace (prefixWord ++ tailWord_2433617) baseStart_2433617 baseEnd_2433617 := by
    simpa [prefixWord, tailWord_2433617, baseEnd_2433617] using wordTrace_append hprefix tailTrace_2433617
  have hstable : (prefixWord ++ tailWord_2433617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433617).length < 2 ^ (prefixWord ++ tailWord_2433617).sum := by decide
  have hdescent : baseEnd_2433617 < baseStart_2433617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433628 : List Nat := [2, 2, 4, 1, 3, 1, 1, 2, 3, 2, 2]
def baseStart_2433628 : Nat := 118140960795 + 2433628 * 2 ^ 59
def prefixEnd_2433628 : Nat := 4983230072969 + 3 ^ 40 * 2433628 * 2
def baseEnd_2433628 : Nat := 1249620898240109652957955

theorem tailTrace_2433628 : CollatzResearch.WordTrace tailWord_2433628 prefixEnd_2433628 1249620898240109652957955 := by
  unfold tailWord_2433628
  simp only [CollatzResearch.WordTrace]
  refine ⟨44380852613694430708734769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59174470151592574278313025 44380852613694430708734769)
  ·
    refine ⟨33285639460270823031551077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44380852613694430708734769 33285639460270823031551077)
    ·
      refine ⟨6241057398800779318415827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33285639460270823031551077 6241057398800779318415827)
      ·
        refine ⟨9361586098201168977623741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6241057398800779318415827 9361586098201168977623741)
        ·
          refine ⟨3510594786825438366608903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9361586098201168977623741 3510594786825438366608903)
          ·
            refine ⟨5265892180238157549913355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3510594786825438366608903 5265892180238157549913355)
            ·
              refine ⟨7898838270357236324870033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5265892180238157549913355 7898838270357236324870033)
              ·
                refine ⟨5924128702767927243652525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7898838270357236324870033 5924128702767927243652525)
                ·
                  refine ⟨2221548263537972716369697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5924128702767927243652525 2221548263537972716369697)
                  ·
                    refine ⟨1666161197653479537277273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2221548263537972716369697 1666161197653479537277273)
                    ·
                      refine ⟨1249620898240109652957955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1666161197653479537277273 1249620898240109652957955)
                      ·
                        rfl

theorem cell23_2433628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_2433628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433628 prefixEnd_2433628 := by exact prefixLift 2433628
  have htrace : WordTrace (prefixWord ++ tailWord_2433628) baseStart_2433628 baseEnd_2433628 := by
    simpa [prefixWord, tailWord_2433628, baseEnd_2433628] using wordTrace_append hprefix tailTrace_2433628
  have hstable : (prefixWord ++ tailWord_2433628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433628).length < 2 ^ (prefixWord ++ tailWord_2433628).sum := by decide
  have hdescent : baseEnd_2433628 < baseStart_2433628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433645 : List Nat := [1, 5, 1, 1, 3, 2, 2, 3, 1, 2, 2]
def baseStart_2433645 : Nat := 118140960795 + 2433645 * 2 ^ 59
def prefixEnd_2433645 : Nat := 4983230072969 + 3 ^ 40 * 2433645 * 2
def baseEnd_2433645 : Nat := 1249629627411236086445377

theorem tailTrace_2433645 : CollatzResearch.WordTrace tailWord_2433645 prefixEnd_2433645 1249629627411236086445377 := by
  unfold tailWord_2433645
  simp only [CollatzResearch.WordTrace]
  refine ⟨88762325268327273320838389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59174883512218182213892259 88762325268327273320838389)
  ·
    refine ⟨8321467993905681873828599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88762325268327273320838389 8321467993905681873828599)
    ·
      refine ⟨12482201990858522810742899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8321467993905681873828599 12482201990858522810742899)
      ·
        refine ⟨18723302986287784216114349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12482201990858522810742899 18723302986287784216114349)
        ·
          refine ⟨7021238619857919081042881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18723302986287784216114349 7021238619857919081042881)
          ·
            refine ⟨5265928964893439310782161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7021238619857919081042881 5265928964893439310782161)
            ·
              refine ⟨3949446723670079483086621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5265928964893439310782161 3949446723670079483086621)
              ·
                refine ⟨1481042521376279806157483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3949446723670079483086621 1481042521376279806157483)
                ·
                  refine ⟨2221563782064419709236225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1481042521376279806157483 2221563782064419709236225)
                  ·
                    refine ⟨1666172836548314781927169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2221563782064419709236225 1666172836548314781927169)
                    ·
                      refine ⟨1249629627411236086445377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1666172836548314781927169 1249629627411236086445377)
                      ·
                        rfl

theorem cell23_2433645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_2433645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433645 prefixEnd_2433645 := by exact prefixLift 2433645
  have htrace : WordTrace (prefixWord ++ tailWord_2433645) baseStart_2433645 baseEnd_2433645 := by
    simpa [prefixWord, tailWord_2433645, baseEnd_2433645] using wordTrace_append hprefix tailTrace_2433645
  have hstable : (prefixWord ++ tailWord_2433645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433645).length < 2 ^ (prefixWord ++ tailWord_2433645).sum := by decide
  have hdescent : baseEnd_2433645 < baseStart_2433645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433648 : List Nat := [2, 1, 1, 1, 7, 2, 2, 1, 1, 2, 3]
def baseStart_2433648 : Nat := 118140960795 + 2433648 * 2 ^ 59
def prefixEnd_2433648 : Nat := 4983230072969 + 3 ^ 40 * 2433648 * 2
def baseEnd_2433648 : Nat := 1249631167853199574707863

theorem tailTrace_2433648 : CollatzResearch.WordTrace tailWord_2433648 prefixEnd_2433648 1249631167853199574707863 := by
  unfold tailWord_2433648
  simp only [CollatzResearch.WordTrace]
  refine ⟨44381217343658202416598799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59174956458210936555465065 44381217343658202416598799)
  ·
    refine ⟨66571826015487303624898199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44381217343658202416598799 66571826015487303624898199)
    ·
      refine ⟨99857739023230955437347299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66571826015487303624898199 99857739023230955437347299)
      ·
        refine ⟨149786608534846433156020949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99857739023230955437347299 149786608534846433156020949)
        ·
          refine ⟨3510623637535463277094241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 149786608534846433156020949 3510623637535463277094241)
          ·
            refine ⟨2632967728151597457820681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3510623637535463277094241 2632967728151597457820681)
            ·
              refine ⟨1974725796113698093365511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2632967728151597457820681 1974725796113698093365511)
              ·
                refine ⟨2962088694170547140048267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1974725796113698093365511 2962088694170547140048267)
                ·
                  refine ⟨4443133041255820710072401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2962088694170547140048267 4443133041255820710072401)
                  ·
                    refine ⟨3332349780941865532554301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4443133041255820710072401 3332349780941865532554301)
                    ·
                      refine ⟨1249631167853199574707863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3332349780941865532554301 1249631167853199574707863)
                      ·
                        rfl

theorem cell23_2433648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 1, 2, 3].length) (baseStart_2433648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433648 prefixEnd_2433648 := by exact prefixLift 2433648
  have htrace : WordTrace (prefixWord ++ tailWord_2433648) baseStart_2433648 baseEnd_2433648 := by
    simpa [prefixWord, tailWord_2433648, baseEnd_2433648] using wordTrace_append hprefix tailTrace_2433648
  have hstable : (prefixWord ++ tailWord_2433648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433648).length < 2 ^ (prefixWord ++ tailWord_2433648).sum := by decide
  have hdescent : baseEnd_2433648 < baseStart_2433648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433661 : List Nat := [1, 4, 1, 1, 5, 1, 1, 1, 4, 1, 3]
def baseStart_2433661 : Nat := 118140960795 + 2433661 * 2 ^ 59
def prefixEnd_2433661 : Nat := 4983230072969 + 3 ^ 40 * 2433661 * 2
def baseEnd_2433661 : Nat := 1249637843101708023845303

theorem tailTrace_2433661 : CollatzResearch.WordTrace tailWord_2433661 prefixEnd_2433661 1249637843101708023845303 := by
  unfold tailWord_2433661
  simp only [CollatzResearch.WordTrace]
  refine ⟨88762908836269308053420837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59175272557512872035613891 88762908836269308053420837)
  ·
    refine ⟨16643045406800495260016407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88762908836269308053420837 16643045406800495260016407)
    ·
      refine ⟨24964568110200742890024611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16643045406800495260016407 24964568110200742890024611)
      ·
        refine ⟨37446852165301114335036917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24964568110200742890024611 37446852165301114335036917)
        ·
          refine ⟨3510642390496979468909711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37446852165301114335036917 3510642390496979468909711)
          ·
            refine ⟨5265963585745469203364567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3510642390496979468909711 5265963585745469203364567)
            ·
              refine ⟨7898945378618203805046851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5265963585745469203364567 7898945378618203805046851)
              ·
                refine ⟨11848418067927305707570277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7898945378618203805046851 11848418067927305707570277)
                ·
                  refine ⟨2221578387736369820169427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11848418067927305707570277 2221578387736369820169427)
                  ·
                    refine ⟨3332367581604554730254141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2221578387736369820169427 3332367581604554730254141)
                    ·
                      refine ⟨1249637843101708023845303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3332367581604554730254141 1249637843101708023845303)
                      ·
                        rfl

theorem cell23_2433661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_2433661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433661 prefixEnd_2433661 := by exact prefixLift 2433661
  have htrace : WordTrace (prefixWord ++ tailWord_2433661) baseStart_2433661 baseEnd_2433661 := by
    simpa [prefixWord, tailWord_2433661, baseEnd_2433661] using wordTrace_append hprefix tailTrace_2433661
  have hstable : (prefixWord ++ tailWord_2433661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433661).length < 2 ^ (prefixWord ++ tailWord_2433661).sum := by decide
  have hdescent : baseEnd_2433661 < baseStart_2433661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433678 : List Nat := [4, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3]
def baseStart_2433678 : Nat := 118140960795 + 2433678 * 2 ^ 59
def prefixEnd_2433678 : Nat := 4983230072969 + 3 ^ 40 * 2433678 * 2
def baseEnd_2433678 : Nat := 1249646572272834457332725

theorem tailTrace_2433678 : CollatzResearch.WordTrace tailWord_2433678 prefixEnd_2433678 1249646572272834457332725 := by
  unfold tailWord_2433678
  simp only [CollatzResearch.WordTrace]
  refine ⟨11095441109650964994598711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59175685918138479971193125 11095441109650964994598711)
  ·
    refine ⟨16643161664476447491898067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11095441109650964994598711 16643161664476447491898067)
    ·
      refine ⟨24964742496714671237847101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16643161664476447491898067 24964742496714671237847101)
      ·
        refine ⟨9361778436268001714192663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24964742496714671237847101 9361778436268001714192663)
        ·
          refine ⟨14042667654402002571288995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9361778436268001714192663 14042667654402002571288995)
          ·
            refine ⟨21064001481603003856933493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14042667654402002571288995 21064001481603003856933493)
            ·
              refine ⟨1974750138900281611587515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21064001481603003856933493 1974750138900281611587515)
              ·
                refine ⟨2962125208350422417381273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1974750138900281611587515 2962125208350422417381273)
                ·
                  refine ⟨2221593906262816813035955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2962125208350422417381273 2221593906262816813035955)
                  ·
                    refine ⟨3332390859394225219553933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2221593906262816813035955 3332390859394225219553933)
                    ·
                      refine ⟨1249646572272834457332725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3332390859394225219553933 1249646572272834457332725)
                      ·
                        rfl

theorem cell23_2433678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_2433678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433678 prefixEnd_2433678 := by exact prefixLift 2433678
  have htrace : WordTrace (prefixWord ++ tailWord_2433678) baseStart_2433678 baseEnd_2433678 := by
    simpa [prefixWord, tailWord_2433678, baseEnd_2433678] using wordTrace_append hprefix tailTrace_2433678
  have hstable : (prefixWord ++ tailWord_2433678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433678).length < 2 ^ (prefixWord ++ tailWord_2433678).sum := by decide
  have hdescent : baseEnd_2433678 < baseStart_2433678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433687 : List Nat := [1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 5]
def baseStart_2433687 : Nat := 118140960795 + 2433687 * 2 ^ 59
def prefixEnd_2433687 : Nat := 4983230072969 + 3 ^ 40 * 2433687 * 2
def baseEnd_2433687 : Nat := 1249651193598724922120183

theorem tailTrace_2433687 : CollatzResearch.WordTrace tailWord_2433687 prefixEnd_2433687 1249651193598724922120183 := by
  unfold tailWord_2433687
  simp only [CollatzResearch.WordTrace]
  refine ⟨88763857134175114493867315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59175904756116742995911543 88763857134175114493867315)
  ·
    refine ⟨133145785701262671740800973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88763857134175114493867315 133145785701262671740800973)
    ·
      refine ⟨49929669637973501902800365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133145785701262671740800973 49929669637973501902800365)
      ·
        refine ⟨18723626114240063213550137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49929669637973501902800365 18723626114240063213550137)
        ·
          refine ⟨14042719585680047410162603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18723626114240063213550137 14042719585680047410162603)
          ·
            refine ⟨21064079378520071115243905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14042719585680047410162603 21064079378520071115243905)
            ·
              refine ⟨15798059533890053336432929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21064079378520071115243905 15798059533890053336432929)
              ·
                refine ⟨11848544650417540002324697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15798059533890053336432929 11848544650417540002324697)
                ·
                  refine ⟨8886408487813155001743523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11848544650417540002324697 8886408487813155001743523)
                  ·
                    refine ⟨13329612731719732502615285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8886408487813155001743523 13329612731719732502615285)
                    ·
                      refine ⟨1249651193598724922120183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13329612731719732502615285 1249651193598724922120183)
                      ·
                        rfl

theorem cell23_2433687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_2433687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433687 prefixEnd_2433687 := by exact prefixLift 2433687
  have htrace : WordTrace (prefixWord ++ tailWord_2433687) baseStart_2433687 baseEnd_2433687 := by
    simpa [prefixWord, tailWord_2433687, baseEnd_2433687] using wordTrace_append hprefix tailTrace_2433687
  have hstable : (prefixWord ++ tailWord_2433687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433687).length < 2 ^ (prefixWord ++ tailWord_2433687).sum := by decide
  have hdescent : baseEnd_2433687 < baseStart_2433687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433729 : List Nat := [1, 2, 6, 2, 2, 1, 2, 1, 2, 1, 3]
def baseStart_2433729 : Nat := 118140960795 + 2433729 * 2 ^ 59
def prefixEnd_2433729 : Nat := 4983230072969 + 3 ^ 40 * 2433729 * 2
def baseEnd_2433729 : Nat := 1249672759786213757794991

theorem tailTrace_2433729 : CollatzResearch.WordTrace tailWord_2433729 prefixEnd_2433729 1249672759786213757794991 := by
  unfold tailWord_2433729
  simp only [CollatzResearch.WordTrace]
  refine ⟨88765389000022955666896241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59176926000015303777930827 88765389000022955666896241)
  ·
    refine ⟨66574041750017216750172181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88765389000022955666896241 66574041750017216750172181)
    ·
      refine ⟨3120658207032057035164321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 66574041750017216750172181 3120658207032057035164321)
      ·
        refine ⟨2340493655274042776373241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3120658207032057035164321 2340493655274042776373241)
        ·
          refine ⟨1755370241455532082279931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2340493655274042776373241 1755370241455532082279931)
          ·
            refine ⟨2633055362183298123419897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1755370241455532082279931 2633055362183298123419897)
            ·
              refine ⟨1974791521637473592564923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2633055362183298123419897 1974791521637473592564923)
              ·
                refine ⟨2962187282456210388847385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1974791521637473592564923 2962187282456210388847385)
                ·
                  refine ⟨2221640461842157791635539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2962187282456210388847385 2221640461842157791635539)
                  ·
                    refine ⟨3332460692763236687453309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2221640461842157791635539 3332460692763236687453309)
                    ·
                      refine ⟨1249672759786213757794991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3332460692763236687453309 1249672759786213757794991)
                      ·
                        rfl

theorem cell23_2433729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_2433729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433729 prefixEnd_2433729 := by exact prefixLift 2433729
  have htrace : WordTrace (prefixWord ++ tailWord_2433729) baseStart_2433729 baseEnd_2433729 := by
    simpa [prefixWord, tailWord_2433729, baseEnd_2433729] using wordTrace_append hprefix tailTrace_2433729
  have hstable : (prefixWord ++ tailWord_2433729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433729).length < 2 ^ (prefixWord ++ tailWord_2433729).sum := by decide
  have hdescent : baseEnd_2433729 < baseStart_2433729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433754 : List Nat := [3, 1, 1, 2, 2, 2, 4, 1, 2, 5]
def baseStart_2433754 : Nat := 118140960795 + 2433754 * 2 ^ 59
def prefixEnd_2433754 : Nat := 4983230072969 + 3 ^ 40 * 2433754 * 2
def baseEnd_2433754 : Nat := 416561865600858719994125

theorem tailTrace_2433754 : CollatzResearch.WordTrace tailWord_2433754 prefixEnd_2433754 416561865600858719994125 := by
  unfold tailWord_2433754
  simp only [CollatzResearch.WordTrace]
  refine ⟨22191575206233096234139079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59177533883288256624370877 22191575206233096234139079)
  ·
    refine ⟨33287362809349644351208619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22191575206233096234139079 33287362809349644351208619)
    ·
      refine ⟨49931044214024466526812929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33287362809349644351208619 49931044214024466526812929)
      ·
        refine ⟨37448283160518349895109697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49931044214024466526812929 37448283160518349895109697)
        ·
          refine ⟨28086212370388762421332273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37448283160518349895109697 28086212370388762421332273)
          ·
            refine ⟨21064659277791571815999205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28086212370388762421332273 21064659277791571815999205)
            ·
              refine ⟨3949623614585919715499851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21064659277791571815999205 3949623614585919715499851)
              ·
                refine ⟨5924435421878879573249777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3949623614585919715499851 5924435421878879573249777)
                ·
                  refine ⟨4443326566409159679937333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5924435421878879573249777 4443326566409159679937333)
                  ·
                    refine ⟨416561865600858719994125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4443326566409159679937333 416561865600858719994125)
                    ·
                      rfl

theorem cell23_2433754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 2, 5].length) (baseStart_2433754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433754 prefixEnd_2433754 := by exact prefixLift 2433754
  have htrace : WordTrace (prefixWord ++ tailWord_2433754) baseStart_2433754 baseEnd_2433754 := by
    simpa [prefixWord, tailWord_2433754, baseEnd_2433754] using wordTrace_append hprefix tailTrace_2433754
  have hstable : (prefixWord ++ tailWord_2433754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433754).length < 2 ^ (prefixWord ++ tailWord_2433754).sum := by decide
  have hdescent : baseEnd_2433754 < baseStart_2433754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433777 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 2, 3, 5]
def baseStart_2433777 : Nat := 118140960795 + 2433777 * 2 ^ 59
def prefixEnd_2433777 : Nat := 4983230072969 + 3 ^ 40 * 2433777 * 2
def baseEnd_2433777 : Nat := 1249697406857629569994769

theorem tailTrace_2433777 : CollatzResearch.WordTrace tailWord_2433777 prefixEnd_2433777 1249697406857629569994769 := by
  unfold tailWord_2433777
  simp only [CollatzResearch.WordTrace]
  refine ⟨88767139703849059864643585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59178093135899373243095723 88767139703849059864643585)
  ·
    refine ⟨66575354777886794898482689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88767139703849059864643585 66575354777886794898482689)
    ·
      refine ⟨49931516083415096173862017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66575354777886794898482689 49931516083415096173862017)
      ·
        refine ⟨37448637062561322130396513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49931516083415096173862017 37448637062561322130396513)
        ·
          refine ⟨28086477796920991597797385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37448637062561322130396513 28086477796920991597797385)
          ·
            refine ⟨21064858347690743698348039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28086477796920991597797385 21064858347690743698348039)
            ·
              refine ⟨31597287521536115547522059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21064858347690743698348039 31597287521536115547522059)
              ·
                refine ⟨47395931282304173321283089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31597287521536115547522059 47395931282304173321283089)
                ·
                  refine ⟨35546948461728129990962317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47395931282304173321283089 35546948461728129990962317)
                  ·
                    refine ⟨13330105673148048746610869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35546948461728129990962317 13330105673148048746610869)
                    ·
                      refine ⟨1249697406857629569994769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13330105673148048746610869 1249697406857629569994769)
                      ·
                        rfl

theorem cell23_2433777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_2433777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433777 prefixEnd_2433777 := by exact prefixLift 2433777
  have htrace : WordTrace (prefixWord ++ tailWord_2433777) baseStart_2433777 baseEnd_2433777 := by
    simpa [prefixWord, tailWord_2433777, baseEnd_2433777] using wordTrace_append hprefix tailTrace_2433777
  have hstable : (prefixWord ++ tailWord_2433777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433777).length < 2 ^ (prefixWord ++ tailWord_2433777).sum := by decide
  have hdescent : baseEnd_2433777 < baseStart_2433777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433784 : List Nat := [2, 1, 2, 1, 1, 2, 4, 3, 3, 4]
def baseStart_2433784 : Nat := 118140960795 + 2433784 * 2 ^ 59
def prefixEnd_2433784 : Nat := 4983230072969 + 3 ^ 40 * 2433784 * 2
def baseEnd_2433784 : Nat := 416567000407403680869079

theorem tailTrace_2433784 : CollatzResearch.WordTrace tailWord_2433784 prefixEnd_2433784 416567000407403680869079 := by
  unfold tailWord_2433784
  simp only [CollatzResearch.WordTrace]
  refine ⟨44383697507411850030074203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59178263343215800040098937 44383697507411850030074203)
  ·
    refine ⟨66575546261117775045111305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44383697507411850030074203 66575546261117775045111305)
    ·
      refine ⟨49931659695838331283833479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66575546261117775045111305 49931659695838331283833479)
      ·
        refine ⟨74897489543757496925750219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49931659695838331283833479 74897489543757496925750219)
        ·
          refine ⟨112346234315636245388625329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74897489543757496925750219 112346234315636245388625329)
          ·
            refine ⟨84259675736727184041468997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112346234315636245388625329 84259675736727184041468997)
            ·
              refine ⟨15798689200636347007775437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84259675736727184041468997 15798689200636347007775437)
              ·
                refine ⟨5924508450238630127915789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15798689200636347007775437 5924508450238630127915789)
                ·
                  refine ⟨2221690668839486297968421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5924508450238630127915789 2221690668839486297968421)
                  ·
                    refine ⟨416567000407403680869079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2221690668839486297968421 416567000407403680869079)
                    ·
                      rfl

theorem cell23_2433784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 3, 4].length) (baseStart_2433784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433784 prefixEnd_2433784 := by exact prefixLift 2433784
  have htrace : WordTrace (prefixWord ++ tailWord_2433784) baseStart_2433784 baseEnd_2433784 := by
    simpa [prefixWord, tailWord_2433784, baseEnd_2433784] using wordTrace_append hprefix tailTrace_2433784
  have hstable : (prefixWord ++ tailWord_2433784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433784).length < 2 ^ (prefixWord ++ tailWord_2433784).sum := by decide
  have hdescent : baseEnd_2433784 < baseStart_2433784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433818 : List Nat := [3, 1, 1, 3, 2, 1, 4, 3, 1, 4]
def baseStart_2433818 : Nat := 118140960795 + 2433818 * 2 ^ 59
def prefixEnd_2433818 : Nat := 4983230072969 + 3 ^ 40 * 2433818 * 2
def baseEnd_2433818 : Nat := 416572819854821303194027

theorem tailTrace_2433818 : CollatzResearch.WordTrace tailWord_2433818 prefixEnd_2433818 416572819854821303194027 := by
  unfold tailWord_2433818
  simp only [CollatzResearch.WordTrace]
  refine ⟨22192158774175130966721527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59179090064467015911257405 22192158774175130966721527)
  ·
    refine ⟨33288238161262696450082291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22192158774175130966721527 33288238161262696450082291)
    ·
      refine ⟨49932357241894044675123437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33288238161262696450082291 49932357241894044675123437)
      ·
        refine ⟨18724633965710266753171289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49932357241894044675123437 18724633965710266753171289)
        ·
          refine ⟨14043475474282700064878467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18724633965710266753171289 14043475474282700064878467)
          ·
            refine ⟨21065213211424050097317701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14043475474282700064878467 21065213211424050097317701)
            ·
              refine ⟨3949727477142009393247069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21065213211424050097317701 3949727477142009393247069)
              ·
                refine ⟨1481147803928253522467651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3949727477142009393247069 1481147803928253522467651)
                ·
                  refine ⟨2221721705892380283701477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1481147803928253522467651 2221721705892380283701477)
                  ·
                    refine ⟨416572819854821303194027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2221721705892380283701477 416572819854821303194027)
                    ·
                      rfl

theorem cell23_2433818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3, 1, 4].length) (baseStart_2433818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433818 prefixEnd_2433818 := by exact prefixLift 2433818
  have htrace : WordTrace (prefixWord ++ tailWord_2433818) baseStart_2433818 baseEnd_2433818 := by
    simpa [prefixWord, tailWord_2433818, baseEnd_2433818] using wordTrace_append hprefix tailTrace_2433818
  have hstable : (prefixWord ++ tailWord_2433818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433818).length < 2 ^ (prefixWord ++ tailWord_2433818).sum := by decide
  have hdescent : baseEnd_2433818 < baseStart_2433818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433869 : List Nat := [1, 6, 1, 2, 3, 1, 1, 3, 1, 4]
def baseStart_2433869 : Nat := 118140960795 + 2433869 * 2 ^ 59
def prefixEnd_2433869 : Nat := 4983230072969 + 3 ^ 40 * 2433869 * 2
def baseEnd_2433869 : Nat := 416581549025947736681449

theorem tailTrace_2433869 : CollatzResearch.WordTrace tailWord_2433869 prefixEnd_2433869 416581549025947736681449 := by
  unfold tailWord_2433869
  simp only [CollatzResearch.WordTrace]
  refine ⟨88770495219515759576992661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59180330146343839717995107 88770495219515759576992661)
  ·
    refine ⟨4161116963414801230171531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 88770495219515759576992661 4161116963414801230171531)
    ·
      refine ⟨6241675445122201845257297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4161116963414801230171531 6241675445122201845257297)
      ·
        refine ⟨4681256583841651383942973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6241675445122201845257297 4681256583841651383942973)
        ·
          refine ⟨1755471218940619268978615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4681256583841651383942973 1755471218940619268978615)
          ·
            refine ⟨2633206828410928903467923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1755471218940619268978615 2633206828410928903467923)
            ·
              refine ⟨3949810242616393355201885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2633206828410928903467923 3949810242616393355201885)
              ·
                refine ⟨1481178840981147508200707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3949810242616393355201885 1481178840981147508200707)
                ·
                  refine ⟨2221768261471721262301061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1481178840981147508200707 2221768261471721262301061)
                  ·
                    refine ⟨416581549025947736681449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2221768261471721262301061 416581549025947736681449)
                    ·
                      rfl

theorem cell23_2433869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_2433869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433869 prefixEnd_2433869 := by exact prefixLift 2433869
  have htrace : WordTrace (prefixWord ++ tailWord_2433869) baseStart_2433869 baseEnd_2433869 := by
    simpa [prefixWord, tailWord_2433869, baseEnd_2433869] using wordTrace_append hprefix tailTrace_2433869
  have hstable : (prefixWord ++ tailWord_2433869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433869).length < 2 ^ (prefixWord ++ tailWord_2433869).sum := by decide
  have hdescent : baseEnd_2433869 < baseStart_2433869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433874 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 3, 6]
def baseStart_2433874 : Nat := 118140960795 + 2433874 * 2 ^ 59
def prefixEnd_2433874 : Nat := 4983230072969 + 3 ^ 40 * 2433874 * 2
def baseEnd_2433874 : Nat := 416582404827038563493941

theorem tailTrace_2433874 : CollatzResearch.WordTrace tailWord_2433874 prefixEnd_2433874 416582404827038563493941 := by
  unfold tailWord_2433874
  simp only [CollatzResearch.WordTrace]
  refine ⟨22192669396124411357731169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59180451722998430287283117 22192669396124411357731169)
  ·
    refine ⟨16644502047093308518298377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22192669396124411357731169 16644502047093308518298377)
    ·
      refine ⟨12483376535319981388723783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16644502047093308518298377 12483376535319981388723783)
      ·
        refine ⟨18725064802979972083085675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12483376535319981388723783 18725064802979972083085675)
        ·
          refine ⟨28087597204469958124628513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18725064802979972083085675 28087597204469958124628513)
          ·
            refine ⟨21065697903352468593471385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28087597204469958124628513 21065697903352468593471385)
            ·
              refine ⟨15799273427514351445103539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21065697903352468593471385 15799273427514351445103539)
              ·
                refine ⟨23698910141271527167655309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15799273427514351445103539 23698910141271527167655309)
                ·
                  refine ⟨8887091302976822687870741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23698910141271527167655309 8887091302976822687870741)
                  ·
                    refine ⟨416582404827038563493941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8887091302976822687870741 416582404827038563493941)
                    ·
                      rfl

theorem cell23_2433874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_2433874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433874 prefixEnd_2433874 := by exact prefixLift 2433874
  have htrace : WordTrace (prefixWord ++ tailWord_2433874) baseStart_2433874 baseEnd_2433874 := by
    simpa [prefixWord, tailWord_2433874, baseEnd_2433874] using wordTrace_append hprefix tailTrace_2433874
  have hstable : (prefixWord ++ tailWord_2433874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433874).length < 2 ^ (prefixWord ++ tailWord_2433874).sum := by decide
  have hdescent : baseEnd_2433874 < baseStart_2433874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433881 : List Nat := [1, 2, 1, 2, 2, 4, 2, 3, 1, 1, 4]
def baseStart_2433881 : Nat := 118140960795 + 2433881 * 2 ^ 59
def prefixEnd_2433881 : Nat := 4983230072969 + 3 ^ 40 * 2433881 * 2
def baseEnd_2433881 : Nat := 1249750808845697163094291

theorem tailTrace_2433881 : CollatzResearch.WordTrace tailWord_2433881 prefixEnd_2433881 1249750808845697163094291 := by
  unfold tailWord_2433881
  simp only [CollatzResearch.WordTrace]
  refine ⟨88770932895472285626429497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59180621930314857084286331 88770932895472285626429497)
  ·
    refine ⟨66578199671604214219822123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88770932895472285626429497 66578199671604214219822123)
    ·
      refine ⟨99867299507406321329733185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66578199671604214219822123 99867299507406321329733185)
      ·
        refine ⟨74900474630554740997299889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99867299507406321329733185 74900474630554740997299889)
        ·
          refine ⟨56175355972916055747974917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74900474630554740997299889 56175355972916055747974917)
          ·
            refine ⟨10532879244921760452745297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56175355972916055747974917 10532879244921760452745297)
            ·
              refine ⟨7899659433691320339558973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10532879244921760452745297 7899659433691320339558973)
              ·
                refine ⟨2962372287634245127334615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7899659433691320339558973 2962372287634245127334615)
                ·
                  refine ⟨4443558431451367691001923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2962372287634245127334615 4443558431451367691001923)
                  ·
                    refine ⟨6665337647177051536502885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4443558431451367691001923 6665337647177051536502885)
                    ·
                      refine ⟨1249750808845697163094291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6665337647177051536502885 1249750808845697163094291)
                      ·
                        rfl

theorem cell23_2433881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 1, 4].length) (baseStart_2433881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433881 prefixEnd_2433881 := by exact prefixLift 2433881
  have htrace : WordTrace (prefixWord ++ tailWord_2433881) baseStart_2433881 baseEnd_2433881 := by
    simpa [prefixWord, tailWord_2433881, baseEnd_2433881] using wordTrace_append hprefix tailTrace_2433881
  have hstable : (prefixWord ++ tailWord_2433881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433881).length < 2 ^ (prefixWord ++ tailWord_2433881).sum := by decide
  have hdescent : baseEnd_2433881 < baseStart_2433881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433891 : List Nat := [1, 1, 1, 5, 3, 1, 2, 1, 4, 4]
def baseStart_2433891 : Nat := 118140960795 + 2433891 * 2 ^ 59
def prefixEnd_2433891 : Nat := 4983230072969 + 3 ^ 40 * 2433891 * 2
def baseEnd_2433891 : Nat := 416585314550747374656415

theorem tailTrace_2433891 : CollatzResearch.WordTrace tailWord_2433891 prefixEnd_2433891 416585314550747374656415 := by
  unfold tailWord_2433891
  simp only [CollatzResearch.WordTrace]
  refine ⟨88771297625436057334293527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59180865083624038222862351 88771297625436057334293527)
  ·
    refine ⟨133156946438154086001440291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88771297625436057334293527 133156946438154086001440291)
    ·
      refine ⟨199735419657231129002160437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133156946438154086001440291 199735419657231129002160437)
      ·
        refine ⟨18725195592865418343952541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 199735419657231129002160437 18725195592865418343952541)
        ·
          refine ⟨7021948347324531878982203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18725195592865418343952541 7021948347324531878982203)
          ·
            refine ⟨10532922520986797818473305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7021948347324531878982203 10532922520986797818473305)
            ·
              refine ⟨7899691890740098363854979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10532922520986797818473305 7899691890740098363854979)
              ·
                refine ⟨11849537836110147545782469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7899691890740098363854979 11849537836110147545782469)
                ·
                  refine ⟨2221788344270652664834213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11849537836110147545782469 2221788344270652664834213)
                  ·
                    refine ⟨416585314550747374656415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2221788344270652664834213 416585314550747374656415)
                    ·
                      rfl

theorem cell23_2433891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4, 4].length) (baseStart_2433891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433891 prefixEnd_2433891 := by exact prefixLift 2433891
  have htrace : WordTrace (prefixWord ++ tailWord_2433891) baseStart_2433891 baseEnd_2433891 := by
    simpa [prefixWord, tailWord_2433891, baseEnd_2433891] using wordTrace_append hprefix tailTrace_2433891
  have hstable : (prefixWord ++ tailWord_2433891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433891).length < 2 ^ (prefixWord ++ tailWord_2433891).sum := by decide
  have hdescent : baseEnd_2433891 < baseStart_2433891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433892 : List Nat := [2, 3, 1, 1, 4, 2, 3, 2, 1, 1, 3]
def baseStart_2433892 : Nat := 118140960795 + 2433892 * 2 ^ 59
def prefixEnd_2433892 : Nat := 4983230072969 + 3 ^ 40 * 2433892 * 2
def baseEnd_2433892 : Nat := 1249756457132896620056741

theorem tailTrace_2433892 : CollatzResearch.WordTrace tailWord_2433892 prefixEnd_2433892 1249756457132896620056741 := by
  unfold tailWord_2433892
  simp only [CollatzResearch.WordTrace]
  refine ⟨44385667049216217252539965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59180889398954956336719953 44385667049216217252539965)
  ·
    refine ⟨16644625143456081469702487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44385667049216217252539965 16644625143456081469702487)
    ·
      refine ⟨24966937715184122204553731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16644625143456081469702487 24966937715184122204553731)
      ·
        refine ⟨37450406572776183306830597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24966937715184122204553731 37450406572776183306830597)
        ·
          refine ⟨7021951232395534370030737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37450406572776183306830597 7021951232395534370030737)
          ·
            refine ⟨5266463424296650777523053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7021951232395534370030737 5266463424296650777523053)
            ·
              refine ⟨1974923784111244041571145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5266463424296650777523053 1974923784111244041571145)
              ·
                refine ⟨1481192838083433031178359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1974923784111244041571145 1481192838083433031178359)
                ·
                  refine ⟨2221789257125149546767539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1481192838083433031178359 2221789257125149546767539)
                  ·
                    refine ⟨3332683885687724320151309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2221789257125149546767539 3332683885687724320151309)
                    ·
                      refine ⟨1249756457132896620056741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3332683885687724320151309 1249756457132896620056741)
                      ·
                        rfl

theorem cell23_2433892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2, 1, 1, 3].length) (baseStart_2433892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433892 prefixEnd_2433892 := by exact prefixLift 2433892
  have htrace : WordTrace (prefixWord ++ tailWord_2433892) baseStart_2433892 baseEnd_2433892 := by
    simpa [prefixWord, tailWord_2433892, baseEnd_2433892] using wordTrace_append hprefix tailTrace_2433892
  have hstable : (prefixWord ++ tailWord_2433892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433892).length < 2 ^ (prefixWord ++ tailWord_2433892).sum := by decide
  have hdescent : baseEnd_2433892 < baseStart_2433892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433901 : List Nat := [1, 5, 1, 1, 1, 1, 1, 4, 3, 2, 3]
def baseStart_2433901 : Nat := 118140960795 + 2433901 * 2 ^ 59
def prefixEnd_2433901 : Nat := 4983230072969 + 3 ^ 40 * 2433901 * 2
def baseEnd_2433901 : Nat := 1249761078458787084844199

theorem tailTrace_2433901 : CollatzResearch.WordTrace tailWord_2433901 prefixEnd_2433901 1249761078458787084844199 := by
  unfold tailWord_2433901
  simp only [CollatzResearch.WordTrace]
  refine ⟨88771662355399829042157557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59181108236933219361438371 88771662355399829042157557)
  ·
    refine ⟨8322343345818733972702271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88771662355399829042157557 8322343345818733972702271)
    ·
      refine ⟨12483515018728100959053407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8322343345818733972702271 12483515018728100959053407)
      ·
        refine ⟨18725272528092151438580111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12483515018728100959053407 18725272528092151438580111)
        ·
          refine ⟨28087908792138227157870167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18725272528092151438580111 28087908792138227157870167)
          ·
            refine ⟨42131863188207340736805251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28087908792138227157870167 42131863188207340736805251)
            ·
              refine ⟨63197794782311011105207877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42131863188207340736805251 63197794782311011105207877)
              ·
                refine ⟨11849586521683314582226477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63197794782311011105207877 11849586521683314582226477)
                ·
                  refine ⟨4443594945631242968334929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11849586521683314582226477 4443594945631242968334929)
                  ·
                    refine ⟨3332696209223432226251197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4443594945631242968334929 3332696209223432226251197)
                    ·
                      refine ⟨1249761078458787084844199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3332696209223432226251197 1249761078458787084844199)
                      ·
                        rfl

theorem cell23_2433901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_2433901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433901 prefixEnd_2433901 := by exact prefixLift 2433901
  have htrace : WordTrace (prefixWord ++ tailWord_2433901) baseStart_2433901 baseEnd_2433901 := by
    simpa [prefixWord, tailWord_2433901, baseEnd_2433901] using wordTrace_append hprefix tailTrace_2433901
  have hstable : (prefixWord ++ tailWord_2433901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433901).length < 2 ^ (prefixWord ++ tailWord_2433901).sum := by decide
  have hdescent : baseEnd_2433901 < baseStart_2433901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433931 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 6, 1, 3]
def baseStart_2433931 : Nat := 118140960795 + 2433931 * 2 ^ 59
def prefixEnd_2433931 : Nat := 4983230072969 + 3 ^ 40 * 2433931 * 2
def baseEnd_2433931 : Nat := 1249776482878421967469061

theorem tailTrace_2433931 : CollatzResearch.WordTrace tailWord_2433931 prefixEnd_2433931 1249776482878421967469061 := by
  unfold tailWord_2433931
  simp only [CollatzResearch.WordTrace]
  refine ⟨88772756545291144165749647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59181837696860762777166431 88772756545291144165749647)
  ·
    refine ⟨133159134817936716248624471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88772756545291144165749647 133159134817936716248624471)
    ·
      refine ⟨199738702226905074372936707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133159134817936716248624471 199738702226905074372936707)
      ·
        refine ⟨299608053340357611559405061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199738702226905074372936707 299608053340357611559405061)
        ·
          refine ⟨56176510001317052167388449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 299608053340357611559405061 56176510001317052167388449)
          ·
            refine ⟨42132382500987789125541337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56176510001317052167388449 42132382500987789125541337)
            ·
              refine ⟨31599286875740841844156003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42132382500987789125541337 31599286875740841844156003)
              ·
                refine ⟨47398930313611262766234005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31599286875740841844156003 47398930313611262766234005)
                ·
                  refine ⟨2221824858450527942167219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47398930313611262766234005 2221824858450527942167219)
                  ·
                    refine ⟨3332737287675791913250829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2221824858450527942167219 3332737287675791913250829)
                    ·
                      refine ⟨1249776482878421967469061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3332737287675791913250829 1249776482878421967469061)
                      ·
                        rfl

theorem cell23_2433931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6, 1, 3].length) (baseStart_2433931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433931 prefixEnd_2433931 := by exact prefixLift 2433931
  have htrace : WordTrace (prefixWord ++ tailWord_2433931) baseStart_2433931 baseEnd_2433931 := by
    simpa [prefixWord, tailWord_2433931, baseEnd_2433931] using wordTrace_append hprefix tailTrace_2433931
  have hstable : (prefixWord ++ tailWord_2433931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433931).length < 2 ^ (prefixWord ++ tailWord_2433931).sum := by decide
  have hdescent : baseEnd_2433931 < baseStart_2433931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433942 : List Nat := [5, 3, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_2433942 : Nat := 118140960795 + 2433942 * 2 ^ 59
def prefixEnd_2433942 : Nat := 4983230072969 + 3 ^ 40 * 2433942 * 2
def baseEnd_2433942 : Nat := 416594043721873808143837

theorem tailTrace_2433942 : CollatzResearch.WordTrace tailWord_2433942 prefixEnd_2433942 416594043721873808143837 := by
  unfold tailWord_2433942
  simp only [CollatzResearch.WordTrace]
  refine ⟨5548322359265705815275005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59182105165500862029600053 5548322359265705815275005)
  ·
    refine ⟨2080620884724639680728127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5548322359265705815275005 2080620884724639680728127)
    ·
      refine ⟨3120931327086959521092191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2080620884724639680728127 3120931327086959521092191)
      ·
        refine ⟨4681396990630439281638287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3120931327086959521092191 4681396990630439281638287)
        ·
          refine ⟨7022095485945658922457431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4681396990630439281638287 7022095485945658922457431)
          ·
            refine ⟨10533143228918488383686147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7022095485945658922457431 10533143228918488383686147)
            ·
              refine ⟨15799714843377732575529221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10533143228918488383686147 15799714843377732575529221)
              ·
                refine ⟨2962446533133324857911729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15799714843377732575529221 2962446533133324857911729)
                ·
                  refine ⟨2221834899849993643433797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2962446533133324857911729 2221834899849993643433797)
                  ·
                    refine ⟨416594043721873808143837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2221834899849993643433797 416594043721873808143837)
                    ·
                      rfl

theorem cell23_2433942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_2433942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433942 prefixEnd_2433942 := by exact prefixLift 2433942
  have htrace : WordTrace (prefixWord ++ tailWord_2433942) baseStart_2433942 baseEnd_2433942 := by
    simpa [prefixWord, tailWord_2433942, baseEnd_2433942] using wordTrace_append hprefix tailTrace_2433942
  have hstable : (prefixWord ++ tailWord_2433942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433942).length < 2 ^ (prefixWord ++ tailWord_2433942).sum := by decide
  have hdescent : baseEnd_2433942 < baseStart_2433942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433964 : List Nat := [2, 2, 1, 1, 1, 1, 2, 5, 2, 6]
def baseStart_2433964 : Nat := 118140960795 + 2433964 * 2 ^ 59
def prefixEnd_2433964 : Nat := 4983230072969 + 3 ^ 40 * 2433964 * 2
def baseEnd_2433964 : Nat := 416597809246673446118803

theorem tailTrace_2433964 : CollatzResearch.WordTrace tailWord_2433964 prefixEnd_2433964 416597809246673446118803 := by
  unfold tailWord_2433964
  simp only [CollatzResearch.WordTrace]
  refine ⟨44386980077085795400850473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59182640102781060534467297 44386980077085795400850473)
  ·
    refine ⟨33290235057814346550637855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44386980077085795400850473 33290235057814346550637855)
    ·
      refine ⟨49935352586721519825956783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33290235057814346550637855 49935352586721519825956783)
      ·
        refine ⟨74903028880082279738935175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49935352586721519825956783 74903028880082279738935175)
        ·
          refine ⟨112354543320123419608402763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74903028880082279738935175 112354543320123419608402763)
          ·
            refine ⟨168531814980185129412604145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112354543320123419608402763 168531814980185129412604145)
            ·
              refine ⟨126398861235138847059453109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168531814980185129412604145 126398861235138847059453109)
              ·
                refine ⟨11849893240794266911823729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126398861235138847059453109 11849893240794266911823729)
                ·
                  refine ⟨8887419930595700183867797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11849893240794266911823729 8887419930595700183867797)
                  ·
                    refine ⟨416597809246673446118803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8887419930595700183867797 416597809246673446118803)
                    ·
                      rfl

theorem cell23_2433964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 6].length) (baseStart_2433964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433964 prefixEnd_2433964 := by exact prefixLift 2433964
  have htrace : WordTrace (prefixWord ++ tailWord_2433964) baseStart_2433964 baseEnd_2433964 := by
    simpa [prefixWord, tailWord_2433964, baseEnd_2433964] using wordTrace_append hprefix tailTrace_2433964
  have hstable : (prefixWord ++ tailWord_2433964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433964).length < 2 ^ (prefixWord ++ tailWord_2433964).sum := by decide
  have hdescent : baseEnd_2433964 < baseStart_2433964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2433994 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 11]
def baseStart_2433994 : Nat := 118140960795 + 2433994 * 2 ^ 59
def prefixEnd_2433994 : Nat := 4983230072969 + 3 ^ 40 * 2433994 * 2
def baseEnd_2433994 : Nat := 138867648017739468997919

theorem tailTrace_2433994 : CollatzResearch.WordTrace tailWord_2433994 prefixEnd_2433994 138867648017739468997919 := by
  unfold tailWord_2433994
  simp only [CollatzResearch.WordTrace]
  refine ⟨22193763586015726481323259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59183369562708603950195357 22193763586015726481323259)
  ·
    refine ⟨33290645379023589721984889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22193763586015726481323259 33290645379023589721984889)
    ·
      refine ⟨24967984034267692291488667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33290645379023589721984889 24967984034267692291488667)
      ·
        refine ⟨37451976051401538437233001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24967984034267692291488667 37451976051401538437233001)
        ·
          refine ⟨28088982038551153827924751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37451976051401538437233001 28088982038551153827924751)
          ·
            refine ⟨42133473057826730741887127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28088982038551153827924751 42133473057826730741887127)
            ·
              refine ⟨63200209586740096112830691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42133473057826730741887127 63200209586740096112830691)
              ·
                refine ⟨94800314380110144169246037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63200209586740096112830691 94800314380110144169246037)
                ·
                  refine ⟨138867648017739468997919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 94800314380110144169246037 138867648017739468997919)
                  ·
                    rfl

theorem cell23_2433994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 11].length) (baseStart_2433994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2433994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2433994 prefixEnd_2433994 := by exact prefixLift 2433994
  have htrace : WordTrace (prefixWord ++ tailWord_2433994) baseStart_2433994 baseEnd_2433994 := by
    simpa [prefixWord, tailWord_2433994, baseEnd_2433994] using wordTrace_append hprefix tailTrace_2433994
  have hstable : (prefixWord ++ tailWord_2433994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2433994).length < 2 ^ (prefixWord ++ tailWord_2433994).sum := by decide
  have hdescent : baseEnd_2433994 < baseStart_2433994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2433994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434041 : List Nat := [1, 2, 1, 3, 1, 3, 2, 3, 2, 5]
def baseStart_2434041 : Nat := 118140960795 + 2434041 * 2 ^ 59
def prefixEnd_2434041 : Nat := 4983230072969 + 3 ^ 40 * 2434041 * 2
def baseEnd_2434041 : Nat := 416610988583472179031185

theorem tailTrace_2434041 : CollatzResearch.WordTrace tailWord_2434041 prefixEnd_2434041 416610988583472179031185 := by
  unfold tailWord_2434041
  simp only [CollatzResearch.WordTrace]
  refine ⟨88776768574892632952253977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59184512383261755301502651 88776768574892632952253977)
  ·
    refine ⟨66582576431169474714190483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88776768574892632952253977 66582576431169474714190483)
    ·
      refine ⟨99873864646754212071285725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66582576431169474714190483 99873864646754212071285725)
      ·
        refine ⟨37452699242532829526732147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99873864646754212071285725 37452699242532829526732147)
        ·
          refine ⟨56179048863799244290098221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37452699242532829526732147 56179048863799244290098221)
          ·
            refine ⟨21067143323924716608786833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56179048863799244290098221 21067143323924716608786833)
            ·
              refine ⟨15800357492943537456590125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21067143323924716608786833 15800357492943537456590125)
              ·
                refine ⟨5925134059853826546221297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15800357492943537456590125 5925134059853826546221297)
                ·
                  refine ⟨4443850544890369909665973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5925134059853826546221297 4443850544890369909665973)
                  ·
                    refine ⟨416610988583472179031185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4443850544890369909665973 416610988583472179031185)
                    ·
                      rfl

theorem cell23_2434041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 5].length) (baseStart_2434041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434041 prefixEnd_2434041 := by exact prefixLift 2434041
  have htrace : WordTrace (prefixWord ++ tailWord_2434041) baseStart_2434041 baseEnd_2434041 := by
    simpa [prefixWord, tailWord_2434041, baseEnd_2434041] using wordTrace_append hprefix tailTrace_2434041
  have hstable : (prefixWord ++ tailWord_2434041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434041).length < 2 ^ (prefixWord ++ tailWord_2434041).sum := by decide
  have hdescent : baseEnd_2434041 < baseStart_2434041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434058 : List Nat := [3, 1, 2, 2, 3, 2, 1, 2, 2, 5]
def baseStart_2434058 : Nat := 118140960795 + 2434058 * 2 ^ 59
def prefixEnd_2434058 : Nat := 4983230072969 + 3 ^ 40 * 2434058 * 2
def baseEnd_2434058 : Nat := 416613898307180990193659

theorem tailTrace_2434058 : CollatzResearch.WordTrace tailWord_2434058 prefixEnd_2434058 416613898307180990193659 := by
  unfold tailWord_2434058
  simp only [CollatzResearch.WordTrace]
  refine ⟨22194347153957761213905707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59184925743887363237081885 22194347153957761213905707)
  ·
    refine ⟨33291520730936641820858561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22194347153957761213905707 33291520730936641820858561)
    ·
      refine ⟨24968640548202481365643921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33291520730936641820858561 24968640548202481365643921)
      ·
        refine ⟨18726480411151861024232941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24968640548202481365643921 18726480411151861024232941)
        ·
          refine ⟨7022430154181947884087353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18726480411151861024232941 7022430154181947884087353)
          ·
            refine ⟨5266822615636460913065515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7022430154181947884087353 5266822615636460913065515)
            ·
              refine ⟨7900233923454691369598273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5266822615636460913065515 7900233923454691369598273)
              ·
                refine ⟨5925175442591018527198705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7900233923454691369598273 5925175442591018527198705)
                ·
                  refine ⟨4443881581943263895399029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5925175442591018527198705 4443881581943263895399029)
                  ·
                    refine ⟨416613898307180990193659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4443881581943263895399029 416613898307180990193659)
                    ·
                      rfl

theorem cell23_2434058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_2434058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434058 prefixEnd_2434058 := by exact prefixLift 2434058
  have htrace : WordTrace (prefixWord ++ tailWord_2434058) baseStart_2434058 baseEnd_2434058 := by
    simpa [prefixWord, tailWord_2434058, baseEnd_2434058] using wordTrace_append hprefix tailTrace_2434058
  have hstable : (prefixWord ++ tailWord_2434058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434058).length < 2 ^ (prefixWord ++ tailWord_2434058).sum := by decide
  have hdescent : baseEnd_2434058 < baseStart_2434058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434122 : List Nat := [3, 1, 2, 1, 1, 2, 6, 2, 1, 4]
def baseStart_2434122 : Nat := 118140960795 + 2434122 * 2 ^ 59
def prefixEnd_2434122 : Nat := 4983230072969 + 3 ^ 40 * 2434122 * 2
def baseEnd_2434122 : Nat := 416624852561143573393561

theorem tailTrace_2434122 : CollatzResearch.WordTrace tailWord_2434122 prefixEnd_2434122 416624852561143573393561 := by
  unfold tailWord_2434122
  simp only [CollatzResearch.WordTrace]
  refine ⟨22194930721899795946488155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59186481925066122523968413 22194930721899795946488155)
  ·
    refine ⟨33292396082849693919732233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22194930721899795946488155 33292396082849693919732233)
    ·
      refine ⟨24969297062137270439799175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33292396082849693919732233 24969297062137270439799175)
      ·
        refine ⟨37453945593205905659698763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24969297062137270439799175 37453945593205905659698763)
        ·
          refine ⟨56180918389808858489548145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37453945593205905659698763 56180918389808858489548145)
          ·
            refine ⟨42135688792356643867161109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56180918389808858489548145 42135688792356643867161109)
            ·
              refine ⟨1975110412141717681273177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42135688792356643867161109 1975110412141717681273177)
              ·
                refine ⟨1481332809106288260954883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1975110412141717681273177 1481332809106288260954883)
                ·
                  refine ⟨2221999213659432391432325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1481332809106288260954883 2221999213659432391432325)
                  ·
                    refine ⟨416624852561143573393561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2221999213659432391432325 416624852561143573393561)
                    ·
                      rfl

theorem cell23_2434122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_2434122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434122 prefixEnd_2434122 := by exact prefixLift 2434122
  have htrace : WordTrace (prefixWord ++ tailWord_2434122) baseStart_2434122 baseEnd_2434122 := by
    simpa [prefixWord, tailWord_2434122, baseEnd_2434122] using wordTrace_append hprefix tailTrace_2434122
  have hstable : (prefixWord ++ tailWord_2434122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434122).length < 2 ^ (prefixWord ++ tailWord_2434122).sum := by decide
  have hdescent : baseEnd_2434122 < baseStart_2434122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434128 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 7, 1, 3]
def baseStart_2434128 : Nat := 118140960795 + 2434128 * 2 ^ 59
def prefixEnd_2434128 : Nat := 4983230072969 + 3 ^ 40 * 2434128 * 2
def baseEnd_2434128 : Nat := 1249877638567357696705655

theorem tailTrace_2434128 : CollatzResearch.WordTrace tailWord_2434128 prefixEnd_2434128 1249877638567357696705655 := by
  unfold tailWord_2434128
  simp only [CollatzResearch.WordTrace]
  refine ⟨44389970862788723405335519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59186627817051631207114025 44389970862788723405335519)
  ·
    refine ⟨66584956294183085108003279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44389970862788723405335519 66584956294183085108003279)
    ·
      refine ⟨99877434441274627662004919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66584956294183085108003279 99877434441274627662004919)
      ·
        refine ⟨149816151661911941493007379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99877434441274627662004919 149816151661911941493007379)
        ·
          refine ⟨224724227492867912239511069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149816151661911941493007379 224724227492867912239511069)
          ·
            refine ⟨84271585309825467089816651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 224724227492867912239511069 84271585309825467089816651)
            ·
              refine ⟨126407377964738200634724977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84271585309825467089816651 126407377964738200634724977)
              ·
                refine ⟨94805533473553650476043733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126407377964738200634724977 94805533473553650476043733)
                ·
                  refine ⟨2222004690786413683032275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 94805533473553650476043733 2222004690786413683032275)
                  ·
                    refine ⟨3333007036179620524548413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2222004690786413683032275 3333007036179620524548413)
                    ·
                      refine ⟨1249877638567357696705655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3333007036179620524548413 1249877638567357696705655)
                      ·
                        rfl

theorem cell23_2434128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 7, 1, 3].length) (baseStart_2434128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434128 prefixEnd_2434128 := by exact prefixLift 2434128
  have htrace : WordTrace (prefixWord ++ tailWord_2434128) baseStart_2434128 baseEnd_2434128 := by
    simpa [prefixWord, tailWord_2434128, baseEnd_2434128] using wordTrace_append hprefix tailTrace_2434128
  have hstable : (prefixWord ++ tailWord_2434128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434128).length < 2 ^ (prefixWord ++ tailWord_2434128).sum := by decide
  have hdescent : baseEnd_2434128 < baseStart_2434128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434131 : List Nat := [1, 1, 1, 2, 1, 1, 2, 6, 3, 5]
def baseStart_2434131 : Nat := 118140960795 + 2434131 * 2 ^ 59
def prefixEnd_2434131 : Nat := 4983230072969 + 3 ^ 40 * 2434131 * 2
def baseEnd_2434131 : Nat := 416626393003107061656047

theorem tailTrace_2434131 : CollatzResearch.WordTrace tailWord_2434131 prefixEnd_2434131 416626393003107061656047 := by
  unfold tailWord_2434131
  simp only [CollatzResearch.WordTrace]
  refine ⟨88780051144566578323030247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59186700763044385548686831 88780051144566578323030247)
  ·
    refine ⟨133170076716849867484545371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88780051144566578323030247 133170076716849867484545371)
    ·
      refine ⟨199755115075274801226818057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133170076716849867484545371 199755115075274801226818057)
      ·
        refine ⟨149816336306456100920113543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199755115075274801226818057 149816336306456100920113543)
        ·
          refine ⟨224724504459684151380170315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149816336306456100920113543 224724504459684151380170315)
          ·
            refine ⟨337086756689526227070255473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224724504459684151380170315 337086756689526227070255473)
            ·
              refine ⟨252815067517144670302691605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 337086756689526227070255473 252815067517144670302691605)
              ·
                refine ⟨11850706289866156420438669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 252815067517144670302691605 11850706289866156420438669)
                ·
                  refine ⟨4444014858699808657664501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11850706289866156420438669 4444014858699808657664501)
                  ·
                    refine ⟨416626393003107061656047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4444014858699808657664501 416626393003107061656047)
                    ·
                      rfl

theorem cell23_2434131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 5].length) (baseStart_2434131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434131 prefixEnd_2434131 := by exact prefixLift 2434131
  have htrace : WordTrace (prefixWord ++ tailWord_2434131) baseStart_2434131 baseEnd_2434131 := by
    simpa [prefixWord, tailWord_2434131, baseEnd_2434131] using wordTrace_append hprefix tailTrace_2434131
  have hstable : (prefixWord ++ tailWord_2434131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434131).length < 2 ^ (prefixWord ++ tailWord_2434131).sum := by decide
  have hdescent : baseEnd_2434131 < baseStart_2434131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434148 : List Nat := [2, 3, 1, 1, 2, 1, 1, 6, 1, 5]
def baseStart_2434148 : Nat := 118140960795 + 2434148 * 2 ^ 59
def prefixEnd_2434148 : Nat := 4983230072969 + 3 ^ 40 * 2434148 * 2
def baseEnd_2434148 : Nat := 416629302726815872818521

theorem tailTrace_2434148 : CollatzResearch.WordTrace tailWord_2434148 prefixEnd_2434148 416629302726815872818521 := by
  unfold tailWord_2434148
  simp only [CollatzResearch.WordTrace]
  refine ⟨44390335592752495113199549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59187114123669993484266065 44390335592752495113199549)
  ·
    refine ⟨16646375847282185667449831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44390335592752495113199549 16646375847282185667449831)
    ·
      refine ⟨24969563770923278501174747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16646375847282185667449831 24969563770923278501174747)
      ·
        refine ⟨37454345656384917751762121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24969563770923278501174747 37454345656384917751762121)
        ·
          refine ⟨28090759242288688313821591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37454345656384917751762121 28090759242288688313821591)
          ·
            refine ⟨42136138863433032470732387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28090759242288688313821591 42136138863433032470732387)
            ·
              refine ⟨63204208295149548706098581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42136138863433032470732387 63204208295149548706098581)
              ·
                refine ⟨2962697263835135095598371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63204208295149548706098581 2962697263835135095598371)
                ·
                  refine ⟨4444045895752702643397557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2962697263835135095598371 4444045895752702643397557)
                  ·
                    refine ⟨416629302726815872818521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4444045895752702643397557 416629302726815872818521)
                    ·
                      rfl

theorem cell23_2434148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_2434148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434148 prefixEnd_2434148 := by exact prefixLift 2434148
  have htrace : WordTrace (prefixWord ++ tailWord_2434148) baseStart_2434148 baseEnd_2434148 := by
    simpa [prefixWord, tailWord_2434148, baseEnd_2434148] using wordTrace_append hprefix tailTrace_2434148
  have hstable : (prefixWord ++ tailWord_2434148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434148).length < 2 ^ (prefixWord ++ tailWord_2434148).sum := by decide
  have hdescent : baseEnd_2434148 < baseStart_2434148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434161 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 3, 6]
def baseStart_2434161 : Nat := 118140960795 + 2434161 * 2 ^ 59
def prefixEnd_2434161 : Nat := 4983230072969 + 3 ^ 40 * 2434161 * 2
def baseEnd_2434161 : Nat := 416631527809652022531001

theorem tailTrace_2434161 : CollatzResearch.WordTrace tailWord_2434161 prefixEnd_2434161 416631527809652022531001 := by
  unfold tailWord_2434161
  simp only [CollatzResearch.WordTrace]
  refine ⟨88781145334457893446622337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59187430222971928964414891 88781145334457893446622337)
  ·
    refine ⟨66585859000843420084966753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88781145334457893446622337 66585859000843420084966753)
    ·
      refine ⟨49939394250632565063725065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66585859000843420084966753 49939394250632565063725065)
      ·
        refine ⟨37454545687974423797793799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49939394250632565063725065 37454545687974423797793799)
        ·
          refine ⟨56181818531961635696690699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37454545687974423797793799 56181818531961635696690699)
          ·
            refine ⟨84272727797942453545036049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56181818531961635696690699 84272727797942453545036049)
            ·
              refine ⟨63204545848456840158777037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84272727797942453545036049 63204545848456840158777037)
              ·
                refine ⟨23701704693171315059541389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63204545848456840158777037 23701704693171315059541389)
                ·
                  refine ⟨8888139259939243147328021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23701704693171315059541389 8888139259939243147328021)
                  ·
                    refine ⟨416631527809652022531001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8888139259939243147328021 416631527809652022531001)
                    ·
                      rfl

theorem cell23_2434161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 6].length) (baseStart_2434161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434161 prefixEnd_2434161 := by exact prefixLift 2434161
  have htrace : WordTrace (prefixWord ++ tailWord_2434161) baseStart_2434161 baseEnd_2434161 := by
    simpa [prefixWord, tailWord_2434161, baseEnd_2434161] using wordTrace_append hprefix tailTrace_2434161
  have hstable : (prefixWord ++ tailWord_2434161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434161).length < 2 ^ (prefixWord ++ tailWord_2434161).sum := by decide
  have hdescent : baseEnd_2434161 < baseStart_2434161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434171 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 5]
def baseStart_2434171 : Nat := 118140960795 + 2434171 * 2 ^ 59
def prefixEnd_2434171 : Nat := 4983230072969 + 3 ^ 40 * 2434171 * 2
def baseEnd_2434171 : Nat := 1249899718235501028467957

theorem tailTrace_2434171 : CollatzResearch.WordTrace tailWord_2434171 prefixEnd_2434171 1249899718235501028467957 := by
  unfold tailWord_2434171
  simp only [CollatzResearch.WordTrace]
  refine ⟨88781510064421665154486367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59187673376281110102990911 88781510064421665154486367)
  ·
    refine ⟨133172265096632497731729551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88781510064421665154486367 133172265096632497731729551)
    ·
      refine ⟨199758397644948746597594327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133172265096632497731729551 199758397644948746597594327)
      ·
        refine ⟨299637596467423119896391491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199758397644948746597594327 299637596467423119896391491)
        ·
          refine ⟨449456394701134679844587237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299637596467423119896391491 449456394701134679844587237)
          ·
            refine ⟨84273074006462752470860107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 449456394701134679844587237 84273074006462752470860107)
            ·
              refine ⟨126409611009694128706290161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84273074006462752470860107 126409611009694128706290161)
              ·
                refine ⟨94807208257270596529717621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126409611009694128706290161 94807208257270596529717621)
                ·
                  refine ⟨8888175774119118424661027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94807208257270596529717621 8888175774119118424661027)
                  ·
                    refine ⟨13332263661178677636991541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8888175774119118424661027 13332263661178677636991541)
                    ·
                      refine ⟨1249899718235501028467957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13332263661178677636991541 1249899718235501028467957)
                      ·
                        rfl

theorem cell23_2434171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 5].length) (baseStart_2434171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434171 prefixEnd_2434171 := by exact prefixLift 2434171
  have htrace : WordTrace (prefixWord ++ tailWord_2434171) baseStart_2434171 baseEnd_2434171 := by
    simpa [prefixWord, tailWord_2434171, baseEnd_2434171] using wordTrace_append hprefix tailTrace_2434171
  have hstable : (prefixWord ++ tailWord_2434171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434171).length < 2 ^ (prefixWord ++ tailWord_2434171).sum := by decide
  have hdescent : baseEnd_2434171 < baseStart_2434171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434188 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 5, 2, 3]
def baseStart_2434188 : Nat := 118140960795 + 2434188 * 2 ^ 59
def prefixEnd_2434188 : Nat := 4983230072969 + 3 ^ 40 * 2434188 * 2
def baseEnd_2434188 : Nat := 1249908447406627461955379

theorem tailTrace_2434188 : CollatzResearch.WordTrace tailWord_2434188 prefixEnd_2434188 1249908447406627461955379 := by
  unfold tailWord_2434188
  simp only [CollatzResearch.WordTrace]
  refine ⟨44391065052680038528927609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59188086736906718038570145 44391065052680038528927609)
  ·
    refine ⟨33293298789510028896695707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44391065052680038528927609 33293298789510028896695707)
    ·
      refine ⟨49939948184265043345043561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33293298789510028896695707 49939948184265043345043561)
      ·
        refine ⟨37454961138198782508782671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49939948184265043345043561 37454961138198782508782671)
        ·
          refine ⟨56182441707298173763174007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37454961138198782508782671 56182441707298173763174007)
          ·
            refine ⟨84273662560947260644761011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56182441707298173763174007 84273662560947260644761011)
            ·
              refine ⟨126410493841420890967141517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84273662560947260644761011 126410493841420890967141517)
              ·
                refine ⟨47403935190532834112678069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126410493841420890967141517 47403935190532834112678069)
                ·
                  refine ⟨4444118924112453198063569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47403935190532834112678069 4444118924112453198063569)
                  ·
                    refine ⟨3333089193084339898547677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4444118924112453198063569 3333089193084339898547677)
                    ·
                      refine ⟨1249908447406627461955379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3333089193084339898547677 1249908447406627461955379)
                      ·
                        rfl

theorem cell23_2434188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_2434188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434188 prefixEnd_2434188 := by exact prefixLift 2434188
  have htrace : WordTrace (prefixWord ++ tailWord_2434188) baseStart_2434188 baseEnd_2434188 := by
    simpa [prefixWord, tailWord_2434188, baseEnd_2434188] using wordTrace_append hprefix tailTrace_2434188
  have hstable : (prefixWord ++ tailWord_2434188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434188).length < 2 ^ (prefixWord ++ tailWord_2434188).sum := by decide
  have hdescent : baseEnd_2434188 < baseStart_2434188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434202 : List Nat := [3, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4]
def baseStart_2434202 : Nat := 118140960795 + 2434202 * 2 ^ 59
def prefixEnd_2434202 : Nat := 4983230072969 + 3 ^ 40 * 2434202 * 2
def baseEnd_2434202 : Nat := 1249915636135790407180315

theorem tailTrace_2434202 : CollatzResearch.WordTrace tailWord_2434202 prefixEnd_2434202 1249915636135790407180315 := by
  unfold tailWord_2434202
  simp only [CollatzResearch.WordTrace]
  refine ⟨22195660181827339362216215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59188427151539571632576573 22195660181827339362216215)
  ·
    refine ⟨33293490272741009043324323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22195660181827339362216215 33293490272741009043324323)
    ·
      refine ⟨49940235409111513564986485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33293490272741009043324323 49940235409111513564986485)
      ·
        refine ⟨4681897069604204396717483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49940235409111513564986485 4681897069604204396717483)
        ·
          refine ⟨7022845604406306595076225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4681897069604204396717483 7022845604406306595076225)
          ·
            refine ⟨5267134203304729946307169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7022845604406306595076225 5267134203304729946307169)
            ·
              refine ⟨3950350652478547459730377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5267134203304729946307169 3950350652478547459730377)
              ·
                refine ⟨2962762989358910594797783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3950350652478547459730377 2962762989358910594797783)
                ·
                  refine ⟨4444144484038365892196675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2962762989358910594797783 4444144484038365892196675)
                  ·
                    refine ⟨6666216726057548838295013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4444144484038365892196675 6666216726057548838295013)
                    ·
                      refine ⟨1249915636135790407180315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6666216726057548838295013 1249915636135790407180315)
                      ·
                        rfl

theorem cell23_2434202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_2434202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434202 prefixEnd_2434202 := by exact prefixLift 2434202
  have htrace : WordTrace (prefixWord ++ tailWord_2434202) baseStart_2434202 baseEnd_2434202 := by
    simpa [prefixWord, tailWord_2434202, baseEnd_2434202] using wordTrace_append hprefix tailTrace_2434202
  have hstable : (prefixWord ++ tailWord_2434202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434202).length < 2 ^ (prefixWord ++ tailWord_2434202).sum := by decide
  have hdescent : baseEnd_2434202 < baseStart_2434202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434211 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 6]
def baseStart_2434211 : Nat := 118140960795 + 2434211 * 2 ^ 59
def prefixEnd_2434211 : Nat := 4983230072969 + 3 ^ 40 * 2434211 * 2
def baseEnd_2434211 : Nat := 1249920257461680871967773

theorem tailTrace_2434211 : CollatzResearch.WordTrace tailWord_2434211 prefixEnd_2434211 1249920257461680871967773 := by
  unfold tailWord_2434211
  simp only [CollatzResearch.WordTrace]
  refine ⟨88782968984276751985942487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59188645989517834657294991 88782968984276751985942487)
  ·
    refine ⟨133174453476415127978913731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88782968984276751985942487 133174453476415127978913731)
    ·
      refine ⟨199761680214622691968370597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133174453476415127978913731 199761680214622691968370597)
      ·
        refine ⟨37455315040241754744069487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 199761680214622691968370597 37455315040241754744069487)
        ·
          refine ⟨56182972560362632116104231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37455315040241754744069487 56182972560362632116104231)
          ·
            refine ⟨84274458840543948174156347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56182972560362632116104231 84274458840543948174156347)
            ·
              refine ⟨126411688260815922261234521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84274458840543948174156347 126411688260815922261234521)
              ·
                refine ⟨94808766195611941695925891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126411688260815922261234521 94808766195611941695925891)
                ·
                  refine ⟨142213149293417912543888837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94808766195611941695925891 142213149293417912543888837)
                  ·
                    refine ⟨26664965492515858601979157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 142213149293417912543888837 26664965492515858601979157)
                    ·
                      refine ⟨1249920257461680871967773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26664965492515858601979157 1249920257461680871967773)
                      ·
                        rfl

theorem cell23_2434211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_2434211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434211 prefixEnd_2434211 := by exact prefixLift 2434211
  have htrace : WordTrace (prefixWord ++ tailWord_2434211) baseStart_2434211 baseEnd_2434211 := by
    simpa [prefixWord, tailWord_2434211, baseEnd_2434211] using wordTrace_append hprefix tailTrace_2434211
  have hstable : (prefixWord ++ tailWord_2434211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434211).length < 2 ^ (prefixWord ++ tailWord_2434211).sum := by decide
  have hdescent : baseEnd_2434211 < baseStart_2434211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434230 : List Nat := [5, 1, 3, 2, 1, 1, 3, 2, 1, 1, 3]
def baseStart_2434230 : Nat := 118140960795 + 2434230 * 2 ^ 59
def prefixEnd_2434230 : Nat := 4983230072969 + 3 ^ 40 * 2434230 * 2
def baseEnd_2434230 : Nat := 1249930013594116297630187

theorem tailTrace_2434230 : CollatzResearch.WordTrace tailWord_2434230 prefixEnd_2434230 1249930013594116297630187 := by
  unfold tailWord_2434230
  simp only [CollatzResearch.WordTrace]
  refine ⟨5548978873200494889430259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59189107980805278820589429 5548978873200494889430259)
  ·
    refine ⟨8323468309800742334145389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5548978873200494889430259 8323468309800742334145389)
    ·
      refine ⟨3121300616175278375304521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8323468309800742334145389 3121300616175278375304521)
      ·
        refine ⟨2340975462131458781478391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3121300616175278375304521 2340975462131458781478391)
        ·
          refine ⟨3511463193197188172217587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2340975462131458781478391 3511463193197188172217587)
          ·
            refine ⟨5267194789795782258326381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3511463193197188172217587 5267194789795782258326381)
            ·
              refine ⟨1975198046173418346872393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5267194789795782258326381 1975198046173418346872393)
              ·
                refine ⟨1481398534630063760154295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1975198046173418346872393 1481398534630063760154295)
                ·
                  refine ⟨2222097801945095640231443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1481398534630063760154295 2222097801945095640231443)
                  ·
                    refine ⟨3333146702917643460347165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2222097801945095640231443 3333146702917643460347165)
                    ·
                      refine ⟨1249930013594116297630187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3333146702917643460347165 1249930013594116297630187)
                      ·
                        rfl

theorem cell23_2434230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_2434230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434230 prefixEnd_2434230 := by exact prefixLift 2434230
  have htrace : WordTrace (prefixWord ++ tailWord_2434230) baseStart_2434230 baseEnd_2434230 := by
    simpa [prefixWord, tailWord_2434230, baseEnd_2434230] using wordTrace_append hprefix tailTrace_2434230
  have hstable : (prefixWord ++ tailWord_2434230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434230).length < 2 ^ (prefixWord ++ tailWord_2434230).sum := by decide
  have hdescent : baseEnd_2434230 < baseStart_2434230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434245 : List Nat := [1, 3, 1, 1, 1, 1, 3, 4, 3, 3, 2]
def baseStart_2434245 : Nat := 118140960795 + 2434245 * 2 ^ 59
def prefixEnd_2434245 : Nat := 4983230072969 + 3 ^ 40 * 2434245 * 2
def baseEnd_2434245 : Nat := 1249937715803933738942617

theorem tailTrace_2434245 : CollatzResearch.WordTrace tailWord_2434245 prefixEnd_2434245 1249937715803933738942617 := by
  unfold tailWord_2434245
  simp only [CollatzResearch.WordTrace]
  refine ⟨88784209066153575792680189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59189472710769050528453459 88784209066153575792680189)
  ·
    refine ⟨33294078399807590922255071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88784209066153575792680189 33294078399807590922255071)
    ·
      refine ⟨49941117599711386383382607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33294078399807590922255071 49941117599711386383382607)
      ·
        refine ⟨74911676399567079575073911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49941117599711386383382607 74911676399567079575073911)
        ·
          refine ⟨112367514599350619362610867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74911676399567079575073911 112367514599350619362610867)
          ·
            refine ⟨168551271899025929043916301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112367514599350619362610867 168551271899025929043916301)
            ·
              refine ⟨63206726962134723391468613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168551271899025929043916301 63206726962134723391468613)
              ·
                refine ⟨11851261305400260635900365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63206726962134723391468613 11851261305400260635900365)
                ·
                  refine ⟨4444222989525097738462637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11851261305400260635900365 4444222989525097738462637)
                  ·
                    refine ⟨1666583621071911651923489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4444222989525097738462637 1666583621071911651923489)
                    ·
                      refine ⟨1249937715803933738942617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1666583621071911651923489 1249937715803933738942617)
                      ·
                        rfl

theorem cell23_2434245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 3, 2].length) (baseStart_2434245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434245 prefixEnd_2434245 := by exact prefixLift 2434245
  have htrace : WordTrace (prefixWord ++ tailWord_2434245) baseStart_2434245 baseEnd_2434245 := by
    simpa [prefixWord, tailWord_2434245, baseEnd_2434245] using wordTrace_append hprefix tailTrace_2434245
  have hstable : (prefixWord ++ tailWord_2434245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434245).length < 2 ^ (prefixWord ++ tailWord_2434245).sum := by decide
  have hdescent : baseEnd_2434245 < baseStart_2434245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434253 : List Nat := [1, 6, 2, 2, 2, 1, 1, 2, 1, 1, 4]
def baseStart_2434253 : Nat := 118140960795 + 2434253 * 2 ^ 59
def prefixEnd_2434253 : Nat := 4983230072969 + 3 ^ 40 * 2434253 * 2
def baseEnd_2434253 : Nat := 1249941823649169707642581

theorem tailTrace_2434253 : CollatzResearch.WordTrace tailWord_2434253 prefixEnd_2434253 1249941823649169707642581 := by
  unfold tailWord_2434253
  simp only [CollatzResearch.WordTrace]
  refine ⟨88784500850124593158971413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59189667233416395439314275 88784500850124593158971413)
  ·
    refine ⟨4161773477349590304326785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 88784500850124593158971413 4161773477349590304326785)
    ·
      refine ⟨3121330108012192728245089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4161773477349590304326785 3121330108012192728245089)
      ·
        refine ⟨2340997581009144546183817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3121330108012192728245089 2340997581009144546183817)
        ·
          refine ⟨1755748185756858409637863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2340997581009144546183817 1755748185756858409637863)
          ·
            refine ⟨2633622278635287614456795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1755748185756858409637863 2633622278635287614456795)
            ·
              refine ⟨3950433417952931421685193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2633622278635287614456795 3950433417952931421685193)
              ·
                refine ⟨2962825063464698566263895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3950433417952931421685193 2962825063464698566263895)
                ·
                  refine ⟨4444237595197047849395843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2962825063464698566263895 4444237595197047849395843)
                  ·
                    refine ⟨6666356392795571774093765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4444237595197047849395843 6666356392795571774093765)
                    ·
                      refine ⟨1249941823649169707642581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6666356392795571774093765 1249941823649169707642581)
                      ·
                        rfl

theorem cell23_2434253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_2434253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434253 prefixEnd_2434253 := by exact prefixLift 2434253
  have htrace : WordTrace (prefixWord ++ tailWord_2434253) baseStart_2434253 baseEnd_2434253 := by
    simpa [prefixWord, tailWord_2434253, baseEnd_2434253] using wordTrace_append hprefix tailTrace_2434253
  have hstable : (prefixWord ++ tailWord_2434253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434253).length < 2 ^ (prefixWord ++ tailWord_2434253).sum := by decide
  have hdescent : baseEnd_2434253 < baseStart_2434253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434298 : List Nat := [3, 1, 1, 1, 1, 4, 2, 3, 7]
def baseStart_2434298 : Nat := 118140960795 + 2434298 * 2 ^ 59
def prefixEnd_2434298 : Nat := 4983230072969 + 3 ^ 40 * 2434298 * 2
def baseEnd_2434298 : Nat := 138884992253180225731097

theorem tailTrace_2434298 : CollatzResearch.WordTrace tailWord_2434298 prefixEnd_2434298 138884992253180225731097 := by
  unfold tailWord_2434298
  simp only [CollatzResearch.WordTrace]
  refine ⟨22196535533740391461089887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59190761423307710562906365 22196535533740391461089887)
  ·
    refine ⟨33294803300610587191634831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22196535533740391461089887 33294803300610587191634831)
    ·
      refine ⟨49942204950915880787452247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33294803300610587191634831 49942204950915880787452247)
      ·
        refine ⟨74913307426373821181178371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49942204950915880787452247 74913307426373821181178371)
        ·
          refine ⟨112369961139560731771767557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74913307426373821181178371 112369961139560731771767557)
          ·
            refine ⟨21069367713667637207206417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112369961139560731771767557 21069367713667637207206417)
            ·
              refine ⟨15802025785250727905404813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21069367713667637207206417 15802025785250727905404813)
              ·
                refine ⟨5925759669469022964526805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15802025785250727905404813 5925759669469022964526805)
                ·
                  refine ⟨138884992253180225731097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5925759669469022964526805 138884992253180225731097)
                  ·
                    rfl

theorem cell23_2434298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 7].length) (baseStart_2434298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434298 prefixEnd_2434298 := by exact prefixLift 2434298
  have htrace : WordTrace (prefixWord ++ tailWord_2434298) baseStart_2434298 baseEnd_2434298 := by
    simpa [prefixWord, tailWord_2434298, baseEnd_2434298] using wordTrace_append hprefix tailTrace_2434298
  have hstable : (prefixWord ++ tailWord_2434298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434298).length < 2 ^ (prefixWord ++ tailWord_2434298).sum := by decide
  have hdescent : baseEnd_2434298 < baseStart_2434298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434305 : List Nat := [1, 2, 4, 1, 1, 4, 1, 1, 2, 2, 4]
def baseStart_2434305 : Nat := 118140960795 + 2434305 * 2 ^ 59
def prefixEnd_2434305 : Nat := 4983230072969 + 3 ^ 40 * 2434305 * 2
def baseEnd_2434305 : Nat := 1249968524643203504192341

theorem tailTrace_2434305 : CollatzResearch.WordTrace tailWord_2434305 prefixEnd_2434305 1249968524643203504192341 := by
  unfold tailWord_2434305
  simp only [CollatzResearch.WordTrace]
  refine ⟨88786397445936206039864369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59190931630624137359909579 88786397445936206039864369)
  ·
    refine ⟨66589798084452154529898277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88786397445936206039864369 66589798084452154529898277)
    ·
      refine ⟨12485587140834778974355927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66589798084452154529898277 12485587140834778974355927)
      ·
        refine ⟨18728380711252168461533891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12485587140834778974355927 18728380711252168461533891)
        ·
          refine ⟨28092571066878252692300837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18728380711252168461533891 28092571066878252692300837)
          ·
            refine ⟨5267357075039672379806407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28092571066878252692300837 5267357075039672379806407)
            ·
              refine ⟨7901035612559508569709611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5267357075039672379806407 7901035612559508569709611)
              ·
                refine ⟨11851553418839262854564417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7901035612559508569709611 11851553418839262854564417)
                ·
                  refine ⟨8888665064129447140923313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11851553418839262854564417 8888665064129447140923313)
                  ·
                    refine ⟨6666498798097085355692485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8888665064129447140923313 6666498798097085355692485)
                    ·
                      refine ⟨1249968524643203504192341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6666498798097085355692485 1249968524643203504192341)
                      ·
                        rfl

theorem cell23_2434305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_2434305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434305 prefixEnd_2434305 := by exact prefixLift 2434305
  have htrace : WordTrace (prefixWord ++ tailWord_2434305) baseStart_2434305 baseEnd_2434305 := by
    simpa [prefixWord, tailWord_2434305, baseEnd_2434305] using wordTrace_append hprefix tailTrace_2434305
  have hstable : (prefixWord ++ tailWord_2434305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434305).length < 2 ^ (prefixWord ++ tailWord_2434305).sum := by decide
  have hdescent : baseEnd_2434305 < baseStart_2434305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434349 : List Nat := [1, 5, 3, 1, 1, 1, 2, 4, 5]
def baseStart_2434349 : Nat := 118140960795 + 2434349 * 2 ^ 59
def prefixEnd_2434349 : Nat := 4983230072969 + 3 ^ 40 * 2434349 * 2
def baseEnd_2434349 : Nat := 138887901976889036893571

theorem tailTrace_2434349 : CollatzResearch.WordTrace tailWord_2434349 prefixEnd_2434349 138887901976889036893571 := by
  unfold tailWord_2434349
  simp only [CollatzResearch.WordTrace]
  refine ⟨88788002257776801554466101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59192001505184534369644067 88788002257776801554466101)
  ·
    refine ⟨8323875211666575145731197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88788002257776801554466101 8323875211666575145731197)
    ·
      refine ⟨3121453204374965679649199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8323875211666575145731197 3121453204374965679649199)
      ·
        refine ⟨4682179806562448519473799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3121453204374965679649199 4682179806562448519473799)
        ·
          refine ⟨7023269709843672779210699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4682179806562448519473799 7023269709843672779210699)
          ·
            refine ⟨10534904564765509168816049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7023269709843672779210699 10534904564765509168816049)
            ·
              refine ⟨7901178423574131876612037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10534904564765509168816049 7901178423574131876612037)
              ·
                refine ⟨1481470954420149726864757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7901178423574131876612037 1481470954420149726864757)
                ·
                  refine ⟨138887901976889036893571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1481470954420149726864757 138887901976889036893571)
                  ·
                    rfl

theorem cell23_2434349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_2434349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434349 prefixEnd_2434349 := by exact prefixLift 2434349
  have htrace : WordTrace (prefixWord ++ tailWord_2434349) baseStart_2434349 baseEnd_2434349 := by
    simpa [prefixWord, tailWord_2434349, baseEnd_2434349] using wordTrace_append hprefix tailTrace_2434349
  have hstable : (prefixWord ++ tailWord_2434349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434349).length < 2 ^ (prefixWord ++ tailWord_2434349).sum := by decide
  have hdescent : baseEnd_2434349 < baseStart_2434349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434385 : List Nat := [1, 2, 2, 1, 4, 1, 1, 3, 1, 4, 3]
def baseStart_2434385 : Nat := 118140960795 + 2434385 * 2 ^ 59
def prefixEnd_2434385 : Nat := 4983230072969 + 3 ^ 40 * 2434385 * 2
def baseEnd_2434385 : Nat := 1250009603095563191191973

theorem tailTrace_2434385 : CollatzResearch.WordTrace tailWord_2434385 prefixEnd_2434385 1250009603095563191191973 := by
  unfold tailWord_2434385
  simp only [CollatzResearch.WordTrace]
  refine ⟨88789315285646379702776609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59192876857097586468517739 88789315285646379702776609)
  ·
    refine ⟨66591986464234784777082457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88789315285646379702776609 66591986464234784777082457)
    ·
      refine ⟨49943989848176088582811843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66591986464234784777082457 49943989848176088582811843)
      ·
        refine ⟨74915984772264132874217765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49943989848176088582811843 74915984772264132874217765)
        ·
          refine ⟨14046747144799524913915831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74915984772264132874217765 14046747144799524913915831)
          ·
            refine ⟨21070120717199287370873747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14046747144799524913915831 21070120717199287370873747)
            ·
              refine ⟨31605181075798931056310621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21070120717199287370873747 31605181075798931056310621)
              ·
                refine ⟨11851942903424599146116483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31605181075798931056310621 11851942903424599146116483)
                ·
                  refine ⟨17777914355136898719174725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11851942903424599146116483 17777914355136898719174725)
                  ·
                    refine ⟨3333358941588168509845261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17777914355136898719174725 3333358941588168509845261)
                    ·
                      refine ⟨1250009603095563191191973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3333358941588168509845261 1250009603095563191191973)
                      ·
                        rfl

theorem cell23_2434385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 4, 3].length) (baseStart_2434385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434385 prefixEnd_2434385 := by exact prefixLift 2434385
  have htrace : WordTrace (prefixWord ++ tailWord_2434385) baseStart_2434385 baseEnd_2434385 := by
    simpa [prefixWord, tailWord_2434385, baseEnd_2434385] using wordTrace_append hprefix tailTrace_2434385
  have hstable : (prefixWord ++ tailWord_2434385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434385).length < 2 ^ (prefixWord ++ tailWord_2434385).sum := by decide
  have hdescent : baseEnd_2434385 < baseStart_2434385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434405 : List Nat := [1, 3, 1, 3, 1, 2, 2, 4, 6]
def baseStart_2434405 : Nat := 118140960795 + 2434405 * 2 ^ 59
def prefixEnd_2434405 : Nat := 4983230072969 + 3 ^ 40 * 2434405 * 2
def baseEnd_2434405 : Nat := 138891096967628123660209

theorem tailTrace_2434405 : CollatzResearch.WordTrace tailWord_2434405 prefixEnd_2434405 138891096967628123660209 := by
  unfold tailWord_2434405
  simp only [CollatzResearch.WordTrace]
  refine ⟨88790044745573923118504669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59193363163715948745669779 88790044745573923118504669)
  ·
    refine ⟨33296266779590221169439251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88790044745573923118504669 33296266779590221169439251)
    ·
      refine ⟨49944400169385331754158877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33296266779590221169439251 49944400169385331754158877)
      ·
        refine ⟨18729150063519499407809579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49944400169385331754158877 18729150063519499407809579)
        ·
          refine ⟨28093725095279249111714369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18729150063519499407809579 28093725095279249111714369)
          ·
            refine ⟨21070293821459436833785777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28093725095279249111714369 21070293821459436833785777)
            ·
              refine ⟨15802720366094577625339333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21070293821459436833785777 15802720366094577625339333)
              ·
                refine ⟨2963010068642733304751125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15802720366094577625339333 2963010068642733304751125)
                ·
                  refine ⟨138891096967628123660209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2963010068642733304751125 138891096967628123660209)
                  ·
                    rfl

theorem cell23_2434405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 6].length) (baseStart_2434405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434405 prefixEnd_2434405 := by exact prefixLift 2434405
  have htrace : WordTrace (prefixWord ++ tailWord_2434405) baseStart_2434405 baseEnd_2434405 := by
    simpa [prefixWord, tailWord_2434405, baseEnd_2434405] using wordTrace_append hprefix tailTrace_2434405
  have hstable : (prefixWord ++ tailWord_2434405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434405).length < 2 ^ (prefixWord ++ tailWord_2434405).sum := by decide
  have hdescent : baseEnd_2434405 < baseStart_2434405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434432 : List Nat := [2, 1, 1, 2, 1, 2, 1, 6, 3, 1, 3]
def baseStart_2434432 : Nat := 118140960795 + 2434432 * 2 ^ 59
def prefixEnd_2434432 : Nat := 4983230072969 + 3 ^ 40 * 2434432 * 2
def baseEnd_2434432 : Nat := 1250033736686324507304257

theorem tailTrace_2434432 : CollatzResearch.WordTrace tailWord_2434432 prefixEnd_2434432 1250033736686324507304257 := by
  unfold tailWord_2434432
  simp only [CollatzResearch.WordTrace]
  refine ⟨44395514758238053364868775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59194019677650737819825033 44395514758238053364868775)
  ·
    refine ⟨66593272137357080047303163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44395514758238053364868775 66593272137357080047303163)
    ·
      refine ⟨99889908206035620070954745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66593272137357080047303163 99889908206035620070954745)
      ·
        refine ⟨74917431154526715053216059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99889908206035620070954745 74917431154526715053216059)
        ·
          refine ⟨112376146731790072579824089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74917431154526715053216059 112376146731790072579824089)
          ·
            refine ⟨84282110048842554434868067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112376146731790072579824089 84282110048842554434868067)
            ·
              refine ⟨126423165073263831652302101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84282110048842554434868067 126423165073263831652302101)
              ·
                refine ⟨5926085862809242108701661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 126423165073263831652302101 5926085862809242108701661)
                ·
                  refine ⟨2222282198553465790763123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5926085862809242108701661 2222282198553465790763123)
                  ·
                    refine ⟨3333423297830198686144685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2222282198553465790763123 3333423297830198686144685)
                    ·
                      refine ⟨1250033736686324507304257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3333423297830198686144685 1250033736686324507304257)
                      ·
                        rfl

theorem cell23_2434432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 3, 1, 3].length) (baseStart_2434432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434432 prefixEnd_2434432 := by exact prefixLift 2434432
  have htrace : WordTrace (prefixWord ++ tailWord_2434432) baseStart_2434432 baseEnd_2434432 := by
    simpa [prefixWord, tailWord_2434432, baseEnd_2434432] using wordTrace_append hprefix tailTrace_2434432
  have hstable : (prefixWord ++ tailWord_2434432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434432).length < 2 ^ (prefixWord ++ tailWord_2434432).sum := by decide
  have hdescent : baseEnd_2434432 < baseStart_2434432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434460 : List Nat := [2, 2, 3, 4, 1, 2, 2, 2, 1, 4]
def baseStart_2434460 : Nat := 118140960795 + 2434460 * 2 ^ 59
def prefixEnd_2434460 : Nat := 4983230072969 + 3 ^ 40 * 2434460 * 2
def baseEnd_2434460 : Nat := 416682704714883465918043

theorem tailTrace_2434460 : CollatzResearch.WordTrace tailWord_2434460 prefixEnd_2434460 416682704714883465918043 := by
  unfold tailWord_2434460
  simp only [CollatzResearch.WordTrace]
  refine ⟨44396025380187333755878417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59194700506916445007837889 44396025380187333755878417)
  ·
    refine ⟨33297019035140500316908813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44396025380187333755878417 33297019035140500316908813)
    ·
      refine ⟨12486382138177687618840805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33297019035140500316908813 12486382138177687618840805)
      ·
        refine ⟨2341196650908316428532651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12486382138177687618840805 2341196650908316428532651)
        ·
          refine ⟨3511794976362474642798977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2341196650908316428532651 3511794976362474642798977)
          ·
            refine ⟨2633846232271855982099233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3511794976362474642798977 2633846232271855982099233)
            ·
              refine ⟨1975384674203891986574425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2633846232271855982099233 1975384674203891986574425)
              ·
                refine ⟨1481538505652918989930819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1975384674203891986574425 1481538505652918989930819)
                ·
                  refine ⟨2222307758479378484896229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1481538505652918989930819 2222307758479378484896229)
                  ·
                    refine ⟨416682704714883465918043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2222307758479378484896229 416682704714883465918043)
                    ·
                      rfl

theorem cell23_2434460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_2434460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434460 prefixEnd_2434460 := by exact prefixLift 2434460
  have htrace : WordTrace (prefixWord ++ tailWord_2434460) baseStart_2434460 baseEnd_2434460 := by
    simpa [prefixWord, tailWord_2434460, baseEnd_2434460] using wordTrace_append hprefix tailTrace_2434460
  have hstable : (prefixWord ++ tailWord_2434460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434460).length < 2 ^ (prefixWord ++ tailWord_2434460).sum := by decide
  have hdescent : baseEnd_2434460 < baseStart_2434460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434506 : List Nat := [3, 1, 2, 1, 2, 5, 2, 1, 1, 1, 4]
def baseStart_2434506 : Nat := 118140960795 + 2434506 * 2 ^ 59
def prefixEnd_2434506 : Nat := 4983230072969 + 3 ^ 40 * 2434506 * 2
def baseEnd_2434506 : Nat := 1250071734254757217778917

theorem tailTrace_2434506 : CollatzResearch.WordTrace tailWord_2434506 prefixEnd_2434506 1250071734254757217778917 := by
  unfold tailWord_2434506
  simp only [CollatzResearch.WordTrace]
  refine ⟨22198432129552004341982843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59195819012138678245287581 22198432129552004341982843)
  ·
    refine ⟨33297648194328006512974265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22198432129552004341982843 33297648194328006512974265)
    ·
      refine ⟨24973236145746004884730699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33297648194328006512974265 24973236145746004884730699)
      ·
        refine ⟨37459854218619007327096049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24973236145746004884730699 37459854218619007327096049)
        ·
          refine ⟨28094890663964255495322037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37459854218619007327096049 28094890663964255495322037)
          ·
            refine ⟨2633895999746648952686441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28094890663964255495322037 2633895999746648952686441)
            ·
              refine ⟨1975421999809986714514831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2633895999746648952686441 1975421999809986714514831)
              ·
                refine ⟨2963132999714980071772247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1975421999809986714514831 2963132999714980071772247)
                ·
                  refine ⟨4444699499572470107658371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2963132999714980071772247 4444699499572470107658371)
                  ·
                    refine ⟨6667049249358705161487557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4444699499572470107658371 6667049249358705161487557)
                    ·
                      refine ⟨1250071734254757217778917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6667049249358705161487557 1250071734254757217778917)
                      ·
                        rfl

theorem cell23_2434506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 1, 1, 4].length) (baseStart_2434506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434506 prefixEnd_2434506 := by exact prefixLift 2434506
  have htrace : WordTrace (prefixWord ++ tailWord_2434506) baseStart_2434506 baseEnd_2434506 := by
    simpa [prefixWord, tailWord_2434506, baseEnd_2434506] using wordTrace_append hprefix tailTrace_2434506
  have hstable : (prefixWord ++ tailWord_2434506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434506).length < 2 ^ (prefixWord ++ tailWord_2434506).sum := by decide
  have hdescent : baseEnd_2434506 < baseStart_2434506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434600 : List Nat := [2, 1, 5, 2, 2, 2, 1, 2, 1, 3, 2]
def baseStart_2434600 : Nat := 118140960795 + 2434600 * 2 ^ 59
def prefixEnd_2434600 : Nat := 4983230072969 + 3 ^ 40 * 2434600 * 2
def baseEnd_2434600 : Nat := 1250120001436279850003485

theorem tailTrace_2434600 : CollatzResearch.WordTrace tailWord_2434600 prefixEnd_2434600 1250120001436279850003485 := by
  unfold tailWord_2434600
  simp only [CollatzResearch.WordTrace]
  refine ⟨44398578489933735710926627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59198104653244980947902169 44398578489933735710926627)
  ·
    refine ⟨66597867734900603566389941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44398578489933735710926627 66597867734900603566389941)
    ·
      refine ⟨6243550100146931584349057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66597867734900603566389941 6243550100146931584349057)
      ·
        refine ⟨4682662575110198688261793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6243550100146931584349057 4682662575110198688261793)
        ·
          refine ⟨3511996931332649016196345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4682662575110198688261793 3511996931332649016196345)
          ·
            refine ⟨2633997698499486762147259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3511996931332649016196345 2633997698499486762147259)
            ·
              refine ⟨3950996547749230143220889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2633997698499486762147259 3950996547749230143220889)
              ·
                refine ⟨2963247410811922607415667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3950996547749230143220889 2963247410811922607415667)
                ·
                  refine ⟨4444871116217883911123501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2963247410811922607415667 4444871116217883911123501)
                  ·
                    refine ⟨1666826668581706466671313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4444871116217883911123501 1666826668581706466671313)
                    ·
                      refine ⟨1250120001436279850003485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1666826668581706466671313 1250120001436279850003485)
                      ·
                        rfl

theorem cell23_2434600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_2434600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434600 prefixEnd_2434600 := by exact prefixLift 2434600
  have htrace : WordTrace (prefixWord ++ tailWord_2434600) baseStart_2434600 baseEnd_2434600 := by
    simpa [prefixWord, tailWord_2434600, baseEnd_2434600] using wordTrace_append hprefix tailTrace_2434600
  have hstable : (prefixWord ++ tailWord_2434600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434600).length < 2 ^ (prefixWord ++ tailWord_2434600).sum := by decide
  have hdescent : baseEnd_2434600 < baseStart_2434600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434602 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 9]
def baseStart_2434602 : Nat := 118140960795 + 2434602 * 2 ^ 59
def prefixEnd_2434602 : Nat := 4983230072969 + 3 ^ 40 * 2434602 * 2
def baseEnd_2434602 : Nat := 138902336488620982464275

theorem tailTrace_2434602 : CollatzResearch.WordTrace tailWord_2434602 prefixEnd_2434602 138902336488620982464275 := by
  unfold tailWord_2434602
  simp only [CollatzResearch.WordTrace]
  refine ⟨22199307481465056440856515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59198153283906817175617373 22199307481465056440856515)
  ·
    refine ⟨33298961222197584661284773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22199307481465056440856515 33298961222197584661284773)
    ·
      refine ⟨6243555229162047123990895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33298961222197584661284773 6243555229162047123990895)
      ·
        refine ⟨9365332843743070685986343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6243555229162047123990895 9365332843743070685986343)
        ·
          refine ⟨14047999265614606028979515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9365332843743070685986343 14047999265614606028979515)
          ·
            refine ⟨21071998898421909043469273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14047999265614606028979515 21071998898421909043469273)
            ·
              refine ⟨15803999173816431782601955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21071998898421909043469273 15803999173816431782601955)
              ·
                refine ⟨23705998760724647673902933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15803999173816431782601955 23705998760724647673902933)
                ·
                  refine ⟨138902336488620982464275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23705998760724647673902933 138902336488620982464275)
                  ·
                    rfl

theorem cell23_2434602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 9].length) (baseStart_2434602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434602 prefixEnd_2434602 := by exact prefixLift 2434602
  have htrace : WordTrace (prefixWord ++ tailWord_2434602) baseStart_2434602 baseEnd_2434602 := by
    simpa [prefixWord, tailWord_2434602, baseEnd_2434602] using wordTrace_append hprefix tailTrace_2434602
  have hstable : (prefixWord ++ tailWord_2434602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434602).length < 2 ^ (prefixWord ++ tailWord_2434602).sum := by decide
  have hdescent : baseEnd_2434602 < baseStart_2434602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434636 : List Nat := [2, 2, 1, 3, 1, 3, 4, 2, 5]
def baseStart_2434636 : Nat := 118140960795 + 2434636 * 2 ^ 59
def prefixEnd_2434636 : Nat := 4983230072969 + 3 ^ 40 * 2434636 * 2
def baseEnd_2434636 : Nat := 138904276304426856572591

theorem tailTrace_2434636 : CollatzResearch.WordTrace tailWord_2434636 prefixEnd_2434636 138904276304426856572591 := by
  unfold tailWord_2434636
  simp only [CollatzResearch.WordTrace]
  refine ⟨44399235003868524785081881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59198980005158033046775841 44399235003868524785081881)
  ·
    refine ⟨33299426252901393588811411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44399235003868524785081881 33299426252901393588811411)
    ·
      refine ⟨49949139379352090383217117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33299426252901393588811411 49949139379352090383217117)
      ·
        refine ⟨18730927267257033893706419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49949139379352090383217117 18730927267257033893706419)
        ·
          refine ⟨28096390900885550840559629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18730927267257033893706419 28096390900885550840559629)
          ·
            refine ⟨10536146587832081565209861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28096390900885550840559629 10536146587832081565209861)
            ·
              refine ⟨1975527485218515293476849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10536146587832081565209861 1975527485218515293476849)
              ·
                refine ⟨1481645613913886470107637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1975527485218515293476849 1481645613913886470107637)
                ·
                  refine ⟨138904276304426856572591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1481645613913886470107637 138904276304426856572591)
                  ·
                    rfl

theorem cell23_2434636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2, 5].length) (baseStart_2434636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434636 prefixEnd_2434636 := by exact prefixLift 2434636
  have htrace : WordTrace (prefixWord ++ tailWord_2434636) baseStart_2434636 baseEnd_2434636 := by
    simpa [prefixWord, tailWord_2434636, baseEnd_2434636] using wordTrace_append hprefix tailTrace_2434636
  have hstable : (prefixWord ++ tailWord_2434636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434636).length < 2 ^ (prefixWord ++ tailWord_2434636).sum := by decide
  have hdescent : baseEnd_2434636 < baseStart_2434636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434666 : List Nat := [3, 1, 3, 2, 1, 4, 1, 1, 2, 5]
def baseStart_2434666 : Nat := 118140960795 + 2434666 * 2 ^ 59
def prefixEnd_2434666 : Nat := 4983230072969 + 3 ^ 40 * 2434666 * 2
def baseEnd_2434666 : Nat := 416717963719825530592727

theorem tailTrace_2434666 : CollatzResearch.WordTrace tailWord_2434666 prefixEnd_2434666 416717963719825530592727 := by
  unfold tailWord_2434666
  simp only [CollatzResearch.WordTrace]
  refine ⟨22199891049407091173438963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59199709465085576462503901 22199891049407091173438963)
  ·
    refine ⟨33299836574110636760158445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22199891049407091173438963 33299836574110636760158445)
    ·
      refine ⟨12487438715291488785059417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33299836574110636760158445 12487438715291488785059417)
      ·
        refine ⟨9365579036468616588794563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12487438715291488785059417 9365579036468616588794563)
        ·
          refine ⟨14048368554702924883191845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9365579036468616588794563 14048368554702924883191845)
          ·
            refine ⟨2634069104006798415598471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14048368554702924883191845 2634069104006798415598471)
            ·
              refine ⟨3951103656010197623397707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2634069104006798415598471 3951103656010197623397707)
              ·
                refine ⟨5926655484015296435096561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3951103656010197623397707 5926655484015296435096561)
                ·
                  refine ⟨4444991613011472326322421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5926655484015296435096561 4444991613011472326322421)
                  ·
                    refine ⟨416717963719825530592727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4444991613011472326322421 416717963719825530592727)
                    ·
                      rfl

theorem cell23_2434666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_2434666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434666 prefixEnd_2434666 := by exact prefixLift 2434666
  have htrace : WordTrace (prefixWord ++ tailWord_2434666) baseStart_2434666 baseEnd_2434666 := by
    simpa [prefixWord, tailWord_2434666, baseEnd_2434666] using wordTrace_append hprefix tailTrace_2434666
  have hstable : (prefixWord ++ tailWord_2434666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434666).length < 2 ^ (prefixWord ++ tailWord_2434666).sum := by decide
  have hdescent : baseEnd_2434666 < baseStart_2434666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434729 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 5, 5, 2]
def baseStart_2434729 : Nat := 118140960795 + 2434729 * 2 ^ 59
def prefixEnd_2434729 : Nat := 4983230072969 + 3 ^ 40 * 2434729 * 2
def baseEnd_2434729 : Nat := 1250186240440709845290391

theorem tailTrace_2434729 : CollatzResearch.WordTrace tailWord_2434729 prefixEnd_2434729 1250186240440709845290391 := by
  unfold tailWord_2434729
  simp only [CollatzResearch.WordTrace]
  refine ⟨88801861996400126453299241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59201241330933417635532827 88801861996400126453299241)
  ·
    refine ⟨66601396497300094839974431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88801861996400126453299241 66601396497300094839974431)
    ·
      refine ⟨99902094745950142259961647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66601396497300094839974431 99902094745950142259961647)
      ·
        refine ⟨149853142118925213389942471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99902094745950142259961647 149853142118925213389942471)
        ·
          refine ⟨224779713178387820084913707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149853142118925213389942471 224779713178387820084913707)
          ·
            refine ⟨337169569767581730127370561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224779713178387820084913707 337169569767581730127370561)
            ·
              refine ⟨252877177325686297595527921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 337169569767581730127370561 252877177325686297595527921)
              ·
                refine ⟨189657882994264723196645941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252877177325686297595527921 189657882994264723196645941)
                ·
                  refine ⟨17780426530712317799685557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 189657882994264723196645941 17780426530712317799685557)
                  ·
                    refine ⟨1666914987254279793720521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17780426530712317799685557 1666914987254279793720521)
                    ·
                      refine ⟨1250186240440709845290391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1666914987254279793720521 1250186240440709845290391)
                      ·
                        rfl

theorem cell23_2434729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 5, 2].length) (baseStart_2434729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434729 prefixEnd_2434729 := by exact prefixLift 2434729
  have htrace : WordTrace (prefixWord ++ tailWord_2434729) baseStart_2434729 baseEnd_2434729 := by
    simpa [prefixWord, tailWord_2434729, baseEnd_2434729] using wordTrace_append hprefix tailTrace_2434729
  have hstable : (prefixWord ++ tailWord_2434729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434729).length < 2 ^ (prefixWord ++ tailWord_2434729).sum := by decide
  have hdescent : baseEnd_2434729 < baseStart_2434729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434739 : List Nat := [1, 1, 1, 2, 3, 3, 1, 5, 1, 5]
def baseStart_2434739 : Nat := 118140960795 + 2434739 * 2 ^ 59
def prefixEnd_2434739 : Nat := 4983230072969 + 3 ^ 40 * 2434739 * 2
def baseEnd_2434739 : Nat := 416730458415751602055115

theorem tailTrace_2434739 : CollatzResearch.WordTrace tailWord_2434739 prefixEnd_2434739 416730458415751602055115 := by
  unfold tailWord_2434739
  simp only [CollatzResearch.WordTrace]
  refine ⟨88802226726363898161163271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59201484484242598774108847 88802226726363898161163271)
  ·
    refine ⟨133203340089545847241744907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88802226726363898161163271 133203340089545847241744907)
    ·
      refine ⟨199805010134318770862617361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133203340089545847241744907 199805010134318770862617361)
      ·
        refine ⟨149853757600739078146963021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199805010134318770862617361 149853757600739078146963021)
        ·
          refine ⟨56195159100277154305111133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149853757600739078146963021 56195159100277154305111133)
          ·
            refine ⟨21073184662603932864416675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56195159100277154305111133 21073184662603932864416675)
            ·
              refine ⟨31609776993905899296625013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21073184662603932864416675 31609776993905899296625013)
              ·
                refine ⟨2963416593178678059058595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31609776993905899296625013 2963416593178678059058595)
                ·
                  refine ⟨4445124889768017088587893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2963416593178678059058595 4445124889768017088587893)
                  ·
                    refine ⟨416730458415751602055115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4445124889768017088587893 416730458415751602055115)
                    ·
                      rfl

theorem cell23_2434739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 5].length) (baseStart_2434739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434739 prefixEnd_2434739 := by exact prefixLift 2434739
  have htrace : WordTrace (prefixWord ++ tailWord_2434739) baseStart_2434739 baseEnd_2434739 := by
    simpa [prefixWord, tailWord_2434739, baseEnd_2434739] using wordTrace_append hprefix tailTrace_2434739
  have hstable : (prefixWord ++ tailWord_2434739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434739).length < 2 ^ (prefixWord ++ tailWord_2434739).sum := by decide
  have hdescent : baseEnd_2434739 < baseStart_2434739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434746 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2]
def baseStart_2434746 : Nat := 118140960795 + 2434746 * 2 ^ 59
def prefixEnd_2434746 : Nat := 4983230072969 + 3 ^ 40 * 2434746 * 2
def baseEnd_2434746 : Nat := 1250194969611836278777813

theorem tailTrace_2434746 : CollatzResearch.WordTrace tailWord_2434746 prefixEnd_2434746 1250194969611836278777813 := by
  unfold tailWord_2434746
  simp only [CollatzResearch.WordTrace]
  refine ⟨22200620509334634589167023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59201654691559025571112061 22200620509334634589167023)
  ·
    refine ⟨33300930764001951883750535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22200620509334634589167023 33300930764001951883750535)
    ·
      refine ⟨49951396146002927825625803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33300930764001951883750535 49951396146002927825625803)
      ·
        refine ⟨74927094219004391738438705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49951396146002927825625803 74927094219004391738438705)
        ·
          refine ⟨56195320664253293803829029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74927094219004391738438705 56195320664253293803829029)
          ·
            refine ⟨10536622624547492588217943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56195320664253293803829029 10536622624547492588217943)
            ·
              refine ⟨15804933936821238882326915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10536622624547492588217943 15804933936821238882326915)
              ·
                refine ⟨23707400905231858323490373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15804933936821238882326915 23707400905231858323490373)
                ·
                  refine ⟨4445137669730973435654445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23707400905231858323490373 4445137669730973435654445)
                  ·
                    refine ⟨1666926626149115038370417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4445137669730973435654445 1666926626149115038370417)
                    ·
                      refine ⟨1250194969611836278777813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1666926626149115038370417 1250194969611836278777813)
                      ·
                        rfl

theorem cell23_2434746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2].length) (baseStart_2434746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434746 prefixEnd_2434746 := by exact prefixLift 2434746
  have htrace : WordTrace (prefixWord ++ tailWord_2434746) baseStart_2434746 baseEnd_2434746 := by
    simpa [prefixWord, tailWord_2434746, baseEnd_2434746] using wordTrace_append hprefix tailTrace_2434746
  have hstable : (prefixWord ++ tailWord_2434746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434746).length < 2 ^ (prefixWord ++ tailWord_2434746).sum := by decide
  have hdescent : baseEnd_2434746 < baseStart_2434746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434759 : List Nat := [1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 4]
def baseStart_2434759 : Nat := 118140960795 + 2434759 * 2 ^ 59
def prefixEnd_2434759 : Nat := 4983230072969 + 3 ^ 40 * 2434759 * 2
def baseEnd_2434759 : Nat := 1250201644860344727915253

theorem tailTrace_2434759 : CollatzResearch.WordTrace tailWord_2434759 prefixEnd_2434759 1250201644860344727915253 := by
  unfold tailWord_2434759
  simp only [CollatzResearch.WordTrace]
  refine ⟨88802956186291441576891331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59201970790860961051260887 88802956186291441576891331)
  ·
    refine ⟨133204434279437162365336997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88802956186291441576891331 133204434279437162365336997)
    ·
      refine ⟨24975831427394467943500687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133204434279437162365336997 24975831427394467943500687)
      ·
        refine ⟨37463747141091701915251031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24975831427394467943500687 37463747141091701915251031)
        ·
          refine ⟨56195620711637552872876547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37463747141091701915251031 56195620711637552872876547)
          ·
            refine ⟨84293431067456329309314821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56195620711637552872876547 84293431067456329309314821)
            ·
              refine ⟨15805018325148061745496529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84293431067456329309314821 15805018325148061745496529)
              ·
                refine ⟨11853763743861046309122397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15805018325148061745496529 11853763743861046309122397)
                ·
                  refine ⟨4445161403947892365920899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11853763743861046309122397 4445161403947892365920899)
                  ·
                    refine ⟨6667742105921838548881349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4445161403947892365920899 6667742105921838548881349)
                    ·
                      refine ⟨1250201644860344727915253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6667742105921838548881349 1250201644860344727915253)
                      ·
                        rfl

theorem cell23_2434759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_2434759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434759 prefixEnd_2434759 := by exact prefixLift 2434759
  have htrace : WordTrace (prefixWord ++ tailWord_2434759) baseStart_2434759 baseEnd_2434759 := by
    simpa [prefixWord, tailWord_2434759, baseEnd_2434759] using wordTrace_append hprefix tailTrace_2434759
  have hstable : (prefixWord ++ tailWord_2434759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434759).length < 2 ^ (prefixWord ++ tailWord_2434759).sum := by decide
  have hdescent : baseEnd_2434759 < baseStart_2434759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434796 : List Nat := [2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 3]
def baseStart_2434796 : Nat := 118140960795 + 2434796 * 2 ^ 59
def prefixEnd_2434796 : Nat := 4983230072969 + 3 ^ 40 * 2434796 * 2
def baseEnd_2434796 : Nat := 1250220643644561083152583

theorem tailTrace_2434796 : CollatzResearch.WordTrace tailWord_2434796 prefixEnd_2434796 1250220643644561083152583 := by
  unfold tailWord_2434796
  simp only [CollatzResearch.WordTrace]
  refine ⟨44402152843578698447994121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59202870458104931263992161 44402152843578698447994121)
  ·
    refine ⟨33301614632684023835995591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44402152843578698447994121 33301614632684023835995591)
    ·
      refine ⟨49952421949026035753993387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33301614632684023835995591 49952421949026035753993387)
      ·
        refine ⟨74928632923539053630990081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49952421949026035753993387 74928632923539053630990081)
        ·
          refine ⟨56196474692654290223242561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74928632923539053630990081 56196474692654290223242561)
          ·
            refine ⟨42147356019490717667431921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56196474692654290223242561 42147356019490717667431921)
            ·
              refine ⟨31610517014618038250573941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42147356019490717667431921 31610517014618038250573941)
              ·
                refine ⟨2963485970120441085991307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31610517014618038250573941 2963485970120441085991307)
                ·
                  refine ⟨4445228955180661628986961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2963485970120441085991307 4445228955180661628986961)
                  ·
                    refine ⟨3333921716385496221740221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4445228955180661628986961 3333921716385496221740221)
                    ·
                      refine ⟨1250220643644561083152583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3333921716385496221740221 1250220643644561083152583)
                      ·
                        rfl

theorem cell23_2434796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 3].length) (baseStart_2434796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434796 prefixEnd_2434796 := by exact prefixLift 2434796
  have htrace : WordTrace (prefixWord ++ tailWord_2434796) baseStart_2434796 baseEnd_2434796 := by
    simpa [prefixWord, tailWord_2434796, baseEnd_2434796] using wordTrace_append hprefix tailTrace_2434796
  have hstable : (prefixWord ++ tailWord_2434796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434796).length < 2 ^ (prefixWord ++ tailWord_2434796).sum := by decide
  have hdescent : baseEnd_2434796 < baseStart_2434796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434804 : List Nat := [2, 6, 1, 1, 1, 2, 1, 4, 1, 1, 3]
def baseStart_2434804 : Nat := 118140960795 + 2434804 * 2 ^ 59
def prefixEnd_2434804 : Nat := 4983230072969 + 3 ^ 40 * 2434804 * 2
def baseEnd_2434804 : Nat := 1250224751489797051852547

theorem tailTrace_2434804 : CollatzResearch.WordTrace tailWord_2434804 prefixEnd_2434804 1250224751489797051852547 := by
  unfold tailWord_2434804
  simp only [CollatzResearch.WordTrace]
  refine ⟨44402298735564207131139733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59203064980752276174852977 44402298735564207131139733)
  ·
    refine ⟨2081357753229572209272175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 44402298735564207131139733 2081357753229572209272175)
    ·
      refine ⟨3122036629844358313908263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2081357753229572209272175 3122036629844358313908263)
      ·
        refine ⟨4683054944766537470862395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3122036629844358313908263 4683054944766537470862395)
        ·
          refine ⟨7024582417149806206293593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4683054944766537470862395 7024582417149806206293593)
          ·
            refine ⟨5268436812862354654720195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7024582417149806206293593 5268436812862354654720195)
            ·
              refine ⟨7902655219293531982080293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5268436812862354654720195 7902655219293531982080293)
              ·
                refine ⟨1481747853617537246640055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7902655219293531982080293 1481747853617537246640055)
                ·
                  refine ⟨2222621780426305869960083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1481747853617537246640055 2222621780426305869960083)
                  ·
                    refine ⟨3333932670639458804940125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2222621780426305869960083 3333932670639458804940125)
                    ·
                      refine ⟨1250224751489797051852547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3333932670639458804940125 1250224751489797051852547)
                      ·
                        rfl

theorem cell23_2434804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_2434804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434804 prefixEnd_2434804 := by exact prefixLift 2434804
  have htrace : WordTrace (prefixWord ++ tailWord_2434804) baseStart_2434804 baseEnd_2434804 := by
    simpa [prefixWord, tailWord_2434804, baseEnd_2434804] using wordTrace_append hprefix tailTrace_2434804
  have hstable : (prefixWord ++ tailWord_2434804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434804).length < 2 ^ (prefixWord ++ tailWord_2434804).sum := by decide
  have hdescent : baseEnd_2434804 < baseStart_2434804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434823 : List Nat := [1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 4]
def baseStart_2434823 : Nat := 118140960795 + 2434823 * 2 ^ 59
def prefixEnd_2434823 : Nat := 4983230072969 + 3 ^ 40 * 2434823 * 2
def baseEnd_2434823 : Nat := 1250234507622232477514959

theorem tailTrace_2434823 : CollatzResearch.WordTrace tailWord_2434823 prefixEnd_2434823 1250234507622232477514959 := by
  unfold tailWord_2434823
  simp only [CollatzResearch.WordTrace]
  refine ⟨88805290458059580507221123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59203526972039720338147415 88805290458059580507221123)
  ·
    refine ⟨133207935687089370760831685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88805290458059580507221123 133207935687089370760831685)
    ·
      refine ⟨24976487941329257017655941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133207935687089370760831685 24976487941329257017655941)
      ·
        refine ⟨4683091488999235690810489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24976487941329257017655941 4683091488999235690810489)
        ·
          refine ⟨3512318616749426768107867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4683091488999235690810489 3512318616749426768107867)
          ·
            refine ⟨5268477925124140152161801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3512318616749426768107867 5268477925124140152161801)
            ·
              refine ⟨3951358443843105114121351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5268477925124140152161801 3951358443843105114121351)
              ·
                refine ⟨5927037665764657671182027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3951358443843105114121351 5927037665764657671182027)
                ·
                  refine ⟨8890556498646986506773041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5927037665764657671182027 8890556498646986506773041)
                  ·
                    refine ⟨6667917373985239880079781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8890556498646986506773041 6667917373985239880079781)
                    ·
                      refine ⟨1250234507622232477514959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6667917373985239880079781 1250234507622232477514959)
                      ·
                        rfl

theorem cell23_2434823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_2434823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434823 prefixEnd_2434823 := by exact prefixLift 2434823
  have htrace : WordTrace (prefixWord ++ tailWord_2434823) baseStart_2434823 baseEnd_2434823 := by
    simpa [prefixWord, tailWord_2434823, baseEnd_2434823] using wordTrace_append hprefix tailTrace_2434823
  have hstable : (prefixWord ++ tailWord_2434823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434823).length < 2 ^ (prefixWord ++ tailWord_2434823).sum := by decide
  have hdescent : baseEnd_2434823 < baseStart_2434823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434826 : List Nat := [3, 1, 2, 2, 1, 3, 1, 3, 1, 3, 3]
def baseStart_2434826 : Nat := 118140960795 + 2434826 * 2 ^ 59
def prefixEnd_2434826 : Nat := 4983230072969 + 3 ^ 40 * 2434826 * 2
def baseEnd_2434826 : Nat := 1250236048064195965777445

theorem tailTrace_2434826 : CollatzResearch.WordTrace tailWord_2434826 prefixEnd_2434826 1250236048064195965777445 := by
  unfold tailWord_2434826
  simp only [CollatzResearch.WordTrace]
  refine ⟨22201349969262178004895083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59203599918032474679720221 22201349969262178004895083)
  ·
    refine ⟨33302024953893267007342625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22201349969262178004895083 33302024953893267007342625)
    ·
      refine ⟨24976518715419950255506969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33302024953893267007342625 24976518715419950255506969)
      ·
        refine ⟨18732389036564962691630227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24976518715419950255506969 18732389036564962691630227)
        ·
          refine ⟨28098583554847444037445341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18732389036564962691630227 28098583554847444037445341)
          ·
            refine ⟨10536968833067791514042003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28098583554847444037445341 10536968833067791514042003)
            ·
              refine ⟨15805453249601687271063005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10536968833067791514042003 15805453249601687271063005)
              ·
                refine ⟨5927044968600632726648627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15805453249601687271063005 5927044968600632726648627)
                ·
                  refine ⟨8890567452900949089972941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5927044968600632726648627 8890567452900949089972941)
                  ·
                    refine ⟨3333962794837855908739853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8890567452900949089972941 3333962794837855908739853)
                    ·
                      refine ⟨1250236048064195965777445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3333962794837855908739853 1250236048064195965777445)
                      ·
                        rfl

theorem cell23_2434826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_2434826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434826 prefixEnd_2434826 := by exact prefixLift 2434826
  have htrace : WordTrace (prefixWord ++ tailWord_2434826) baseStart_2434826 baseEnd_2434826 := by
    simpa [prefixWord, tailWord_2434826, baseEnd_2434826] using wordTrace_append hprefix tailTrace_2434826
  have hstable : (prefixWord ++ tailWord_2434826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434826).length < 2 ^ (prefixWord ++ tailWord_2434826).sum := by decide
  have hdescent : baseEnd_2434826 < baseStart_2434826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434860 : List Nat := [2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 3]
def baseStart_2434860 : Nat := 118140960795 + 2434860 * 2 ^ 59
def prefixEnd_2434860 : Nat := 4983230072969 + 3 ^ 40 * 2434860 * 2
def baseEnd_2434860 : Nat := 1250253506406448832752289

theorem tailTrace_2434860 : CollatzResearch.WordTrace tailWord_2434860 prefixEnd_2434860 1250253506406448832752289 := by
  unfold tailWord_2434860
  simp only [CollatzResearch.WordTrace]
  refine ⟨44403319979462767913159017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59204426639283690550878689 44403319979462767913159017)
  ·
    refine ⟨33302489984597075934869263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44403319979462767913159017 33302489984597075934869263)
    ·
      refine ⟨49953734976895613902303895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33302489984597075934869263 49953734976895613902303895)
      ·
        refine ⟨74930602465343420853455843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49953734976895613902303895 74930602465343420853455843)
        ·
          refine ⟨112395903698015131280183765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74930602465343420853455843 112395903698015131280183765)
          ·
            refine ⟨2634278992922229639379307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 112395903698015131280183765 2634278992922229639379307)
            ·
              refine ⟨3951418489383344459068961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2634278992922229639379307 3951418489383344459068961)
              ·
                refine ⟨2963563867037508344301721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3951418489383344459068961 2963563867037508344301721)
                ·
                  refine ⟨2222672900278131258226291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2963563867037508344301721 2222672900278131258226291)
                  ·
                    refine ⟨3334009350417196887339437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2222672900278131258226291 3334009350417196887339437)
                    ·
                      refine ⟨1250253506406448832752289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3334009350417196887339437 1250253506406448832752289)
                      ·
                        rfl

theorem cell23_2434860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 3].length) (baseStart_2434860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434860 prefixEnd_2434860 := by exact prefixLift 2434860
  have htrace : WordTrace (prefixWord ++ tailWord_2434860) baseStart_2434860 baseEnd_2434860 := by
    simpa [prefixWord, tailWord_2434860, baseEnd_2434860] using wordTrace_append hprefix tailTrace_2434860
  have hstable : (prefixWord ++ tailWord_2434860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434860).length < 2 ^ (prefixWord ++ tailWord_2434860).sum := by decide
  have hdescent : baseEnd_2434860 < baseStart_2434860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434877 : List Nat := [1, 4, 1, 4, 1, 2, 3, 1, 2, 1, 3]
def baseStart_2434877 : Nat := 118140960795 + 2434877 * 2 ^ 59
def prefixEnd_2434877 : Nat := 4983230072969 + 3 ^ 40 * 2434877 * 2
def baseEnd_2434877 : Nat := 1250262235577575266239711

theorem tailTrace_2434877 : CollatzResearch.WordTrace tailWord_2434877 prefixEnd_2434877 1250262235577575266239711 := by
  unfold tailWord_2434877
  simp only [CollatzResearch.WordTrace]
  refine ⟨88807259999863947729686885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59204839999909298486457923 88807259999863947729686885)
  ·
    refine ⟨16651361249974490199316291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88807259999863947729686885 16651361249974490199316291)
    ·
      refine ⟨24977041874961735298974437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16651361249974490199316291 24977041874961735298974437)
      ·
        refine ⟨4683195351555325368557707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24977041874961735298974437 4683195351555325368557707)
        ·
          refine ⟨7024793027332988052836561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4683195351555325368557707 7024793027332988052836561)
          ·
            refine ⟨5268594770499741039627421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7024793027332988052836561 5268594770499741039627421)
            ·
              refine ⟨1975723038937402889860283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5268594770499741039627421 1975723038937402889860283)
              ·
                refine ⟨2963584558406104334790425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1975723038937402889860283 2963584558406104334790425)
                ·
                  refine ⟨2222688418804578251092819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2963584558406104334790425 2222688418804578251092819)
                  ·
                    refine ⟨3334032628206867376639229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2222688418804578251092819 3334032628206867376639229)
                    ·
                      refine ⟨1250262235577575266239711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3334032628206867376639229 1250262235577575266239711)
                      ·
                        rfl

theorem cell23_2434877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_2434877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434877 prefixEnd_2434877 := by exact prefixLift 2434877
  have htrace : WordTrace (prefixWord ++ tailWord_2434877) baseStart_2434877 baseEnd_2434877 := by
    simpa [prefixWord, tailWord_2434877, baseEnd_2434877] using wordTrace_append hprefix tailTrace_2434877
  have hstable : (prefixWord ++ tailWord_2434877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434877).length < 2 ^ (prefixWord ++ tailWord_2434877).sum := by decide
  have hdescent : baseEnd_2434877 < baseStart_2434877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434883 : List Nat := [1, 1, 1, 3, 1, 5, 3, 1, 1, 4, 2]
def baseStart_2434883 : Nat := 118140960795 + 2434883 * 2 ^ 59
def prefixEnd_2434883 : Nat := 4983230072969 + 3 ^ 40 * 2434883 * 2
def baseEnd_2434883 : Nat := 1250265316461502242764683

theorem tailTrace_2434883 : CollatzResearch.WordTrace tailWord_2434883 prefixEnd_2434883 1250265316461502242764683 := by
  unfold tailWord_2434883
  simp only [CollatzResearch.WordTrace]
  refine ⟨88807478837842210754405303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59204985891894807169603535 88807478837842210754405303)
  ·
    refine ⟨133211218256763316131607955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88807478837842210754405303 133211218256763316131607955)
    ·
      refine ⟨199816827385144974197411933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133211218256763316131607955 199816827385144974197411933)
      ·
        refine ⟨74931310269429365324029475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199816827385144974197411933 74931310269429365324029475)
        ·
          refine ⟨112396965404144047986044213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74931310269429365324029475 112396965404144047986044213)
          ·
            refine ⟨10537215506638504498691645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 112396965404144047986044213 10537215506638504498691645)
            ·
              refine ⟨3951455814989439187009367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10537215506638504498691645 3951455814989439187009367)
              ·
                refine ⟨5927183722484158780514051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3951455814989439187009367 5927183722484158780514051)
                ·
                  refine ⟨8890775583726238170771077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5927183722484158780514051 8890775583726238170771077)
                  ·
                    refine ⟨1667020421948669657019577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8890775583726238170771077 1667020421948669657019577)
                    ·
                      refine ⟨1250265316461502242764683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1667020421948669657019577 1250265316461502242764683)
                      ·
                        rfl

theorem cell23_2434883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 4, 2].length) (baseStart_2434883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434883 prefixEnd_2434883 := by exact prefixLift 2434883
  have htrace : WordTrace (prefixWord ++ tailWord_2434883) baseStart_2434883 baseEnd_2434883 := by
    simpa [prefixWord, tailWord_2434883, baseEnd_2434883] using wordTrace_append hprefix tailTrace_2434883
  have hstable : (prefixWord ++ tailWord_2434883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434883).length < 2 ^ (prefixWord ++ tailWord_2434883).sum := by decide
  have hdescent : baseEnd_2434883 < baseStart_2434883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434889 : List Nat := [1, 2, 1, 1, 2, 4, 1, 4, 7]
def baseStart_2434889 : Nat := 118140960795 + 2434889 * 2 ^ 59
def prefixEnd_2434889 : Nat := 4983230072969 + 3 ^ 40 * 2434889 * 2
def baseEnd_2434889 : Nat := 138918710816158802143295

theorem tailTrace_2434889 : CollatzResearch.WordTrace tailWord_2434889 prefixEnd_2434889 138918710816158802143295 := by
  unfold tailWord_2434889
  simp only [CollatzResearch.WordTrace]
  refine ⟨88807697675820473779123721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59205131783880315852749147 88807697675820473779123721)
  ·
    refine ⟨66605773256865355334342791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88807697675820473779123721 66605773256865355334342791)
    ·
      refine ⟨99908659885298033001514187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66605773256865355334342791 99908659885298033001514187)
      ·
        refine ⟨149862989827947049502271281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99908659885298033001514187 149862989827947049502271281)
        ·
          refine ⟨112397242370960287126703461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149862989827947049502271281 112397242370960287126703461)
          ·
            refine ⟨21074482944555053836256899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112397242370960287126703461 21074482944555053836256899)
            ·
              refine ⟨31611724416832580754385349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21074482944555053836256899 31611724416832580754385349)
              ·
                refine ⟨5927198328156108891447253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31611724416832580754385349 5927198328156108891447253)
                ·
                  refine ⟨138918710816158802143295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5927198328156108891447253 138918710816158802143295)
                  ·
                    rfl

theorem cell23_2434889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 7].length) (baseStart_2434889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434889 prefixEnd_2434889 := by exact prefixLift 2434889
  have htrace : WordTrace (prefixWord ++ tailWord_2434889) baseStart_2434889 baseEnd_2434889 := by
    simpa [prefixWord, tailWord_2434889, baseEnd_2434889] using wordTrace_append hprefix tailTrace_2434889
  have hstable : (prefixWord ++ tailWord_2434889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434889).length < 2 ^ (prefixWord ++ tailWord_2434889).sum := by decide
  have hdescent : baseEnd_2434889 < baseStart_2434889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434900 : List Nat := [2, 4, 1, 1, 3, 1, 1, 2, 4, 2, 2]
def baseStart_2434900 : Nat := 118140960795 + 2434900 * 2 ^ 59
def prefixEnd_2434900 : Nat := 4983230072969 + 3 ^ 40 * 2434900 * 2
def baseEnd_2434900 : Nat := 1250274045632628676252105

theorem tailTrace_2434900 : CollatzResearch.WordTrace tailWord_2434900 prefixEnd_2434900 1250274045632628676252105 := by
  unfold tailWord_2434900
  simp only [CollatzResearch.WordTrace]
  refine ⟨44404049439390311328887077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59205399252520415105182769 44404049439390311328887077)
  ·
    refine ⟨8325759269885683374166327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44404049439390311328887077 8325759269885683374166327)
    ·
      refine ⟨12488638904828525061249491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8325759269885683374166327 12488638904828525061249491)
      ·
        refine ⟨18732958357242787591874237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12488638904828525061249491 18732958357242787591874237)
        ·
          refine ⟨7024859383966045346952839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18732958357242787591874237 7024859383966045346952839)
          ·
            refine ⟨10537289075949068020429259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7024859383966045346952839 10537289075949068020429259)
            ·
              refine ⟨15805933613923602030643889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10537289075949068020429259 15805933613923602030643889)
              ·
                refine ⟨11854450210442701522982917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15805933613923602030643889 11854450210442701522982917)
                ·
                  refine ⟨2222709414458006535559297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11854450210442701522982917 2222709414458006535559297)
                  ·
                    refine ⟨1667032060843504901669473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2222709414458006535559297 1667032060843504901669473)
                    ·
                      refine ⟨1250274045632628676252105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1667032060843504901669473 1250274045632628676252105)
                      ·
                        rfl

theorem cell23_2434900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_2434900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434900 prefixEnd_2434900 := by exact prefixLift 2434900
  have htrace : WordTrace (prefixWord ++ tailWord_2434900) baseStart_2434900 baseEnd_2434900 := by
    simpa [prefixWord, tailWord_2434900, baseEnd_2434900] using wordTrace_append hprefix tailTrace_2434900
  have hstable : (prefixWord ++ tailWord_2434900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434900).length < 2 ^ (prefixWord ++ tailWord_2434900).sum := by decide
  have hdescent : baseEnd_2434900 < baseStart_2434900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434934 : List Nat := [5, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2]
def baseStart_2434934 : Nat := 118140960795 + 2434934 * 2 ^ 59
def prefixEnd_2434934 : Nat := 4983230072969 + 3 ^ 40 * 2434934 * 2
def baseEnd_2434934 : Nat := 1250291503974881543226949

theorem tailTrace_2434934 : CollatzResearch.WordTrace tailWord_2434934 prefixEnd_2434934 1250291503974881543226949 := by
  unfold tailWord_2434934
  simp only [CollatzResearch.WordTrace]
  refine ⟨5550583685041090404031991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59206225973771630976341237 5550583685041090404031991)
  ·
    refine ⟨8325875527561635606047987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5550583685041090404031991 8325875527561635606047987)
    ·
      refine ⟨12488813291342453409071981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8325875527561635606047987 12488813291342453409071981)
      ·
        refine ⟨4683304984253420028401993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12488813291342453409071981 4683304984253420028401993)
        ·
          refine ⟨3512478738190065021301495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4683304984253420028401993 3512478738190065021301495)
          ·
            refine ⟨5268718107285097531952243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3512478738190065021301495 5268718107285097531952243)
            ·
              refine ⟨7903077160927646297928365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5268718107285097531952243 7903077160927646297928365)
              ·
                refine ⟨2963653935347867361723137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7903077160927646297928365 2963653935347867361723137)
                ·
                  refine ⟨2222740451510900521292353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2963653935347867361723137 2222740451510900521292353)
                  ·
                    refine ⟨1667055338633175390969265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2222740451510900521292353 1667055338633175390969265)
                    ·
                      refine ⟨1250291503974881543226949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1667055338633175390969265 1250291503974881543226949)
                      ·
                        rfl

theorem cell23_2434934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_2434934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434934 prefixEnd_2434934 := by exact prefixLift 2434934
  have htrace : WordTrace (prefixWord ++ tailWord_2434934) baseStart_2434934 baseEnd_2434934 := by
    simpa [prefixWord, tailWord_2434934, baseEnd_2434934] using wordTrace_append hprefix tailTrace_2434934
  have hstable : (prefixWord ++ tailWord_2434934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434934).length < 2 ^ (prefixWord ++ tailWord_2434934).sum := by decide
  have hdescent : baseEnd_2434934 < baseStart_2434934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434973 : List Nat := [1, 4, 2, 1, 2, 2, 2, 2, 2, 1, 4]
def baseStart_2434973 : Nat := 118140960795 + 2434973 * 2 ^ 59
def prefixEnd_2434973 : Nat := 4983230072969 + 3 ^ 40 * 2434973 * 2
def baseEnd_2434973 : Nat := 1250311529720406890639269

theorem tailTrace_2434973 : CollatzResearch.WordTrace tailWord_2434973 prefixEnd_2434973 1250311529720406890639269 := by
  unfold tailWord_2434973
  simp only [CollatzResearch.WordTrace]
  refine ⟨88810761407516156125181573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59207174271677437416787715 88810761407516156125181573)
  ·
    refine ⟨16652017763909279273471545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88810761407516156125181573 16652017763909279273471545)
    ·
      refine ⟨12489013322931959455103659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16652017763909279273471545 12489013322931959455103659)
      ·
        refine ⟨18733519984397939182655489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12489013322931959455103659 18733519984397939182655489)
        ·
          refine ⟨14050139988298454386991617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18733519984397939182655489 14050139988298454386991617)
          ·
            refine ⟨10537604991223840790243713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14050139988298454386991617 10537604991223840790243713)
            ·
              refine ⟨7903203743417880592682785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10537604991223840790243713 7903203743417880592682785)
              ·
                refine ⟨5927402807563410444512089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7903203743417880592682785 5927402807563410444512089)
                ·
                  refine ⟨4445552105672557833384067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5927402807563410444512089 4445552105672557833384067)
                  ·
                    refine ⟨6668328158508836750076101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4445552105672557833384067 6668328158508836750076101)
                    ·
                      refine ⟨1250311529720406890639269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6668328158508836750076101 1250311529720406890639269)
                      ·
                        rfl

theorem cell23_2434973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_2434973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434973 prefixEnd_2434973 := by exact prefixLift 2434973
  have htrace : WordTrace (prefixWord ++ tailWord_2434973) baseStart_2434973 baseEnd_2434973 := by
    simpa [prefixWord, tailWord_2434973, baseEnd_2434973] using wordTrace_append hprefix tailTrace_2434973
  have hstable : (prefixWord ++ tailWord_2434973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434973).length < 2 ^ (prefixWord ++ tailWord_2434973).sum := by decide
  have hdescent : baseEnd_2434973 < baseStart_2434973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434976 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 3]
def baseStart_2434976 : Nat := 118140960795 + 2434976 * 2 ^ 59
def prefixEnd_2434976 : Nat := 4983230072969 + 3 ^ 40 * 2434976 * 2
def baseEnd_2434976 : Nat := 1250313070162370378901755

theorem tailTrace_2434976 : CollatzResearch.WordTrace tailWord_2434976 prefixEnd_2434976 1250313070162370378901755 := by
  unfold tailWord_2434976
  simp only [CollatzResearch.WordTrace]
  refine ⟨44405435413252643818770391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59207247217670191758360521 44405435413252643818770391)
  ·
    refine ⟨66608153119878965728155587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44405435413252643818770391 66608153119878965728155587)
    ·
      refine ⟨99912229679818448592233381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66608153119878965728155587 99912229679818448592233381)
      ·
        refine ⟨18733543064965959111043759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99912229679818448592233381 18733543064965959111043759)
        ·
          refine ⟨28100314597448938666565639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18733543064965959111043759 28100314597448938666565639)
          ·
            refine ⟨42150471896173407999848459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28100314597448938666565639 42150471896173407999848459)
            ·
              refine ⟨63225707844260111999772689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42150471896173407999848459 63225707844260111999772689)
              ·
                refine ⟨47419280883195083999829517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63225707844260111999772689 47419280883195083999829517)
                ·
                  refine ⟨17782230331198156499936069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47419280883195083999829517 17782230331198156499936069)
                  ·
                    refine ⟨3334168187099654343738013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17782230331198156499936069 3334168187099654343738013)
                    ·
                      refine ⟨1250313070162370378901755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3334168187099654343738013 1250313070162370378901755)
                      ·
                        rfl

theorem cell23_2434976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_2434976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2434976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2434976 prefixEnd_2434976 := by exact prefixLift 2434976
  have htrace : WordTrace (prefixWord ++ tailWord_2434976) baseStart_2434976 baseEnd_2434976 := by
    simpa [prefixWord, tailWord_2434976, baseEnd_2434976] using wordTrace_append hprefix tailTrace_2434976
  have hstable : (prefixWord ++ tailWord_2434976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434976).length < 2 ^ (prefixWord ++ tailWord_2434976).sum := by decide
  have hdescent : baseEnd_2434976 < baseStart_2434976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435023 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 5, 1, 3]
def baseStart_2435023 : Nat := 118140960795 + 2435023 * 2 ^ 59
def prefixEnd_2435023 : Nat := 4983230072969 + 3 ^ 40 * 2435023 * 2
def baseEnd_2435023 : Nat := 1250337203753131695014039

theorem tailTrace_2435023 : CollatzResearch.WordTrace tailWord_2435023 prefixEnd_2435023 1250337203753131695014039 := by
  unfold tailWord_2435023
  simp only [CollatzResearch.WordTrace]
  refine ⟨88812585057335014664501723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59208390038223343109667815 88812585057335014664501723)
  ·
    refine ⟨133218877586002521996752585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88812585057335014664501723 133218877586002521996752585)
    ·
      refine ⟨99914158189501891497564439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133218877586002521996752585 99914158189501891497564439)
      ·
        refine ⟨149871237284252837246346659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99914158189501891497564439 149871237284252837246346659)
        ·
          refine ⟨224806855926379255869519989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149871237284252837246346659 224806855926379255869519989)
          ·
            refine ⟨21075642743098055237767499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 224806855926379255869519989 21075642743098055237767499)
            ·
              refine ⟨31613464114647082856651249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21075642743098055237767499 31613464114647082856651249)
              ·
                refine ⟨23710098085985312142488437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31613464114647082856651249 23710098085985312142488437)
                ·
                  refine ⟨2222821695561123013358291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23710098085985312142488437 2222821695561123013358291)
                  ·
                    refine ⟨3334232543341684520037437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2222821695561123013358291 3334232543341684520037437)
                    ·
                      refine ⟨1250337203753131695014039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3334232543341684520037437 1250337203753131695014039)
                      ·
                        rfl

theorem cell23_2435023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5, 1, 3].length) (baseStart_2435023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435023 prefixEnd_2435023 := by exact prefixLift 2435023
  have htrace : WordTrace (prefixWord ++ tailWord_2435023) baseStart_2435023 baseEnd_2435023 := by
    simpa [prefixWord, tailWord_2435023, baseEnd_2435023] using wordTrace_append hprefix tailTrace_2435023
  have hstable : (prefixWord ++ tailWord_2435023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435023).length < 2 ^ (prefixWord ++ tailWord_2435023).sum := by decide
  have hdescent : baseEnd_2435023 < baseStart_2435023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435030 : List Nat := [5, 2, 1, 1, 3, 1, 1, 1, 8]
def baseStart_2435030 : Nat := 118140960795 + 2435030 * 2 ^ 59
def prefixEnd_2435030 : Nat := 4983230072969 + 3 ^ 40 * 2435030 * 2
def baseEnd_2435030 : Nat := 138926755346412574180723

theorem tailTrace_2435030 : CollatzResearch.WordTrace tailWord_2435030 prefixEnd_2435030 138926755346412574180723 := by
  unfold tailWord_2435030
  simp only [CollatzResearch.WordTrace]
  refine ⟨5550802523019353428750409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59208560245539769906671029 5550802523019353428750409)
  ·
    refine ⟨4163101892264515071562807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5550802523019353428750409 4163101892264515071562807)
    ·
      refine ⟨6244652838396772607344211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4163101892264515071562807 6244652838396772607344211)
      ·
        refine ⟨9366979257595158911016317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6244652838396772607344211 9366979257595158911016317)
        ·
          refine ⟨3512617221598184591631119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9366979257595158911016317 3512617221598184591631119)
          ·
            refine ⟨5268925832397276887446679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3512617221598184591631119 5268925832397276887446679)
            ·
              refine ⟨7903388748595915331170019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5268925832397276887446679 7903388748595915331170019)
              ·
                refine ⟨11855083122893872996755029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7903388748595915331170019 11855083122893872996755029)
                ·
                  refine ⟨138926755346412574180723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11855083122893872996755029 138926755346412574180723)
                  ·
                    rfl

theorem cell23_2435030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_2435030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435030 prefixEnd_2435030 := by exact prefixLift 2435030
  have htrace : WordTrace (prefixWord ++ tailWord_2435030) baseStart_2435030 baseEnd_2435030 := by
    simpa [prefixWord, tailWord_2435030, baseEnd_2435030] using wordTrace_append hprefix tailTrace_2435030
  have hstable : (prefixWord ++ tailWord_2435030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435030).length < 2 ^ (prefixWord ++ tailWord_2435030).sum := by decide
  have hdescent : baseEnd_2435030 < baseStart_2435030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435073 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 6, 4]
def baseStart_2435073 : Nat := 118140960795 + 2435073 * 2 ^ 59
def prefixEnd_2435073 : Nat := 4983230072969 + 3 ^ 40 * 2435073 * 2
def baseEnd_2435073 : Nat := 416787625928618833129603

theorem tailTrace_2435073 : CollatzResearch.WordTrace tailWord_2435073 prefixEnd_2435073 416787625928618833129603 := by
  unfold tailWord_2435073
  simp only [CollatzResearch.WordTrace]
  refine ⟨88814408707153873203821873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59209605804769248802547915 88814408707153873203821873)
  ·
    refine ⟨66610806530365404902866405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88814408707153873203821873 66610806530365404902866405)
    ·
      refine ⟨12489526224443513419287451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66610806530365404902866405 12489526224443513419287451)
      ·
        refine ⟨18734289336665270128931177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12489526224443513419287451 18734289336665270128931177)
        ·
          refine ⟨14050717002498952596698383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18734289336665270128931177 14050717002498952596698383)
          ·
            refine ⟨21076075503748428895047575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14050717002498952596698383 21076075503748428895047575)
            ·
              refine ⟨31614113255622643342571363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21076075503748428895047575 31614113255622643342571363)
              ·
                refine ⟨47421169883433965013857045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31614113255622643342571363 47421169883433965013857045)
                ·
                  refine ⟨2222867338285967110024549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47421169883433965013857045 2222867338285967110024549)
                  ·
                    refine ⟨416787625928618833129603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2222867338285967110024549 416787625928618833129603)
                    ·
                      rfl

theorem cell23_2435073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_2435073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435073 prefixEnd_2435073 := by exact prefixLift 2435073
  have htrace : WordTrace (prefixWord ++ tailWord_2435073) baseStart_2435073 baseEnd_2435073 := by
    simpa [prefixWord, tailWord_2435073, baseEnd_2435073] using wordTrace_append hprefix tailTrace_2435073
  have hstable : (prefixWord ++ tailWord_2435073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435073).length < 2 ^ (prefixWord ++ tailWord_2435073).sum := by decide
  have hdescent : baseEnd_2435073 < baseStart_2435073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435083 : List Nat := [1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 5]
def baseStart_2435083 : Nat := 118140960795 + 2435083 * 2 ^ 59
def prefixEnd_2435083 : Nat := 4983230072969 + 3 ^ 40 * 2435083 * 2
def baseEnd_2435083 : Nat := 1250368012592401460263763

theorem tailTrace_2435083 : CollatzResearch.WordTrace tailWord_2435083 prefixEnd_2435083 1250368012592401460263763 := by
  unfold tailWord_2435083
  simp only [CollatzResearch.WordTrace]
  refine ⟨88814773437117644911685903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59209848958078429941123935 88814773437117644911685903)
  ·
    refine ⟨133222160155676467367528855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88814773437117644911685903 133222160155676467367528855)
    ·
      refine ⟨199833240233514701051293283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133222160155676467367528855 199833240233514701051293283)
      ·
        refine ⟨299749860350272051576939925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199833240233514701051293283 299749860350272051576939925)
        ·
          refine ⟨14050774703919002417669059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 299749860350272051576939925 14050774703919002417669059)
          ·
            refine ⟨21076162055878503626503589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14050774703919002417669059 21076162055878503626503589)
            ·
              refine ⟨3951780385477219429969423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21076162055878503626503589 3951780385477219429969423)
              ·
                refine ⟨5927670578215829144954135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3951780385477219429969423 5927670578215829144954135)
                ·
                  refine ⟨8891505867323743717431203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5927670578215829144954135 8891505867323743717431203)
                  ·
                    refine ⟨13337258800985615576146805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8891505867323743717431203 13337258800985615576146805)
                    ·
                      refine ⟨1250368012592401460263763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13337258800985615576146805 1250368012592401460263763)
                      ·
                        rfl

theorem cell23_2435083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 5].length) (baseStart_2435083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435083 prefixEnd_2435083 := by exact prefixLift 2435083
  have htrace : WordTrace (prefixWord ++ tailWord_2435083) baseStart_2435083 baseEnd_2435083 := by
    simpa [prefixWord, tailWord_2435083, baseEnd_2435083] using wordTrace_append hprefix tailTrace_2435083
  have hstable : (prefixWord ++ tailWord_2435083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435083).length < 2 ^ (prefixWord ++ tailWord_2435083).sum := by decide
  have hdescent : baseEnd_2435083 < baseStart_2435083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435116 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 4, 7]
def baseStart_2435116 : Nat := 118140960795 + 2435116 * 2 ^ 59
def prefixEnd_2435116 : Nat := 4983230072969 + 3 ^ 40 * 2435116 * 2
def baseEnd_2435116 : Nat := 416794985817999943717037

theorem tailTrace_2435116 : CollatzResearch.WordTrace tailWord_2435116 prefixEnd_2435116 416794985817999943717037 := by
  unfold tailWord_2435116
  simp only [CollatzResearch.WordTrace]
  refine ⟨44407988522999045773818601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59210651363998727698424801 44407988522999045773818601)
  ·
    refine ⟨33305991392249284330363951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44407988522999045773818601 33305991392249284330363951)
    ·
      refine ⟨49958987088373926495545927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33305991392249284330363951 49958987088373926495545927)
      ·
        refine ⟨74938480632560889743318891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49958987088373926495545927 74938480632560889743318891)
        ·
          refine ⟨112407720948841334614978337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74938480632560889743318891 112407720948841334614978337)
          ·
            refine ⟨84305790711631000961233753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112407720948841334614978337 84305790711631000961233753)
            ·
              refine ⟨63229343033723250720925315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84305790711631000961233753 63229343033723250720925315)
              ·
                refine ⟨94844014550584876081387973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63229343033723250720925315 94844014550584876081387973)
                ·
                  refine ⟨17783252728234664265260245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94844014550584876081387973 17783252728234664265260245)
                  ·
                    refine ⟨416794985817999943717037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17783252728234664265260245 416794985817999943717037)
                    ·
                      rfl

theorem cell23_2435116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 7].length) (baseStart_2435116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435116 prefixEnd_2435116 := by exact prefixLift 2435116
  have htrace : WordTrace (prefixWord ++ tailWord_2435116) baseStart_2435116 baseEnd_2435116 := by
    simpa [prefixWord, tailWord_2435116, baseEnd_2435116] using wordTrace_append hprefix tailTrace_2435116
  have hstable : (prefixWord ++ tailWord_2435116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435116).length < 2 ^ (prefixWord ++ tailWord_2435116).sum := by decide
  have hdescent : baseEnd_2435116 < baseStart_2435116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435134 : List Nat := [4, 2, 1, 3, 3, 1, 1, 1, 1, 1, 5]
def baseStart_2435134 : Nat := 118140960795 + 2435134 * 2 ^ 59
def prefixEnd_2435134 : Nat := 4983230072969 + 3 ^ 40 * 2435134 * 2
def baseEnd_2435134 : Nat := 1250394200105780760726029

theorem tailTrace_2435134 : CollatzResearch.WordTrace tailWord_2435134 prefixEnd_2435134 1250394200105780760726029 := by
  unfold tailWord_2435134
  simp only [CollatzResearch.WordTrace]
  refine ⟨11102079194991610077724057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59211089039955253747861637 11102079194991610077724057)
  ·
    refine ⟨8326559396243707558293043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11102079194991610077724057 8326559396243707558293043)
    ·
      refine ⟨12489839094365561337439565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8326559396243707558293043 12489839094365561337439565)
      ·
        refine ⟨4683689660387085501539837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12489839094365561337439565 4683689660387085501539837)
        ·
          refine ⟨1756383622645157063077439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4683689660387085501539837 1756383622645157063077439)
          ·
            refine ⟨2634575433967735594616159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1756383622645157063077439 2634575433967735594616159)
            ·
              refine ⟨3951863150951603391924239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2634575433967735594616159 3951863150951603391924239)
              ·
                refine ⟨5927794726427405087886359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3951863150951603391924239 5927794726427405087886359)
                ·
                  refine ⟨8891692089641107631829539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5927794726427405087886359 8891692089641107631829539)
                  ·
                    refine ⟨13337538134461661447744309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8891692089641107631829539 13337538134461661447744309)
                    ·
                      refine ⟨1250394200105780760726029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13337538134461661447744309 1250394200105780760726029)
                      ·
                        rfl

theorem cell23_2435134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_2435134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435134 prefixEnd_2435134 := by exact prefixLift 2435134
  have htrace : WordTrace (prefixWord ++ tailWord_2435134) baseStart_2435134 baseEnd_2435134 := by
    simpa [prefixWord, tailWord_2435134, baseEnd_2435134] using wordTrace_append hprefix tailTrace_2435134
  have hstable : (prefixWord ++ tailWord_2435134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435134).length < 2 ^ (prefixWord ++ tailWord_2435134).sum := by decide
  have hdescent : baseEnd_2435134 < baseStart_2435134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435210 : List Nat := [3, 1, 2, 3, 1, 3, 2, 1, 7]
def baseStart_2435210 : Nat := 118140960795 + 2435210 * 2 ^ 59
def prefixEnd_2435210 : Nat := 4983230072969 + 3 ^ 40 * 2435210 * 2
def baseEnd_2435210 : Nat := 138937024959502495930631

theorem tailTrace_2435210 : CollatzResearch.WordTrace tailWord_2435210 prefixEnd_2435210 138937024959502495930631 := by
  unfold tailWord_2435210
  simp only [CollatzResearch.WordTrace]
  refine ⟨22204851376914386400389771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59212937005105030401039389 22204851376914386400389771)
  ·
    refine ⟨33307277065371579600584657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22204851376914386400389771 33307277065371579600584657)
    ·
      refine ⟨24980457799028684700438493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33307277065371579600584657 24980457799028684700438493)
      ·
        refine ⟨9367671674635756762664435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24980457799028684700438493 9367671674635756762664435)
        ·
          refine ⟨14051507511953635143996653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9367671674635756762664435 14051507511953635143996653)
          ·
            refine ⟨5269315316982613178998745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14051507511953635143996653 5269315316982613178998745)
            ·
              refine ⟨3951986487736959884249059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5269315316982613178998745 3951986487736959884249059)
              ·
                refine ⟨5927979731605439826373589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3951986487736959884249059 5927979731605439826373589)
                ·
                  refine ⟨138937024959502495930631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5927979731605439826373589 138937024959502495930631)
                  ·
                    rfl

theorem cell23_2435210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 7].length) (baseStart_2435210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435210 prefixEnd_2435210 := by exact prefixLift 2435210
  have htrace : WordTrace (prefixWord ++ tailWord_2435210) baseStart_2435210 baseEnd_2435210 := by
    simpa [prefixWord, tailWord_2435210, baseEnd_2435210] using wordTrace_append hprefix tailTrace_2435210
  have hstable : (prefixWord ++ tailWord_2435210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435210).length < 2 ^ (prefixWord ++ tailWord_2435210).sum := by decide
  have hdescent : baseEnd_2435210 < baseStart_2435210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435273 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 2, 4, 4]
def baseStart_2435273 : Nat := 118140960795 + 2435273 * 2 ^ 59
def prefixEnd_2435273 : Nat := 4983230072969 + 3 ^ 40 * 2435273 * 2
def baseEnd_2435273 : Nat := 1250465573916755716887889

theorem tailTrace_2435273 : CollatzResearch.WordTrace tailWord_2435273 prefixEnd_2435273 1250465573916755716887889 := by
  unfold tailWord_2435273
  simp only [CollatzResearch.WordTrace]
  refine ⟨88821703306429307361102473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59214468870952871574068315 88821703306429307361102473)
  ·
    refine ⟨66616277479821980520826855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88821703306429307361102473 66616277479821980520826855)
    ·
      refine ⟨99924416219732970781240283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66616277479821980520826855 99924416219732970781240283)
      ·
        refine ⟨149886624329599456171860425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99924416219732970781240283 149886624329599456171860425)
        ·
          refine ⟨112414968247199592128895319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149886624329599456171860425 112414968247199592128895319)
          ·
            refine ⟨168622452370799388193342979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112414968247199592128895319 168622452370799388193342979)
            ·
              refine ⟨252933678556199082290014469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168622452370799388193342979 252933678556199082290014469)
              ·
                refine ⟨47425064729287327929377713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 252933678556199082290014469 47425064729287327929377713)
                ·
                  refine ⟨35568798546965495947033285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47425064729287327929377713 35568798546965495947033285)
                  ·
                    refine ⟨6669149727556030490068741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35568798546965495947033285 6669149727556030490068741)
                    ·
                      refine ⟨1250465573916755716887889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6669149727556030490068741 1250465573916755716887889)
                      ·
                        rfl

theorem cell23_2435273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 4, 4].length) (baseStart_2435273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435273 prefixEnd_2435273 := by exact prefixLift 2435273
  have htrace : WordTrace (prefixWord ++ tailWord_2435273) baseStart_2435273 baseEnd_2435273 := by
    simpa [prefixWord, tailWord_2435273, baseEnd_2435273] using wordTrace_append hprefix tailTrace_2435273
  have hstable : (prefixWord ++ tailWord_2435273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435273).length < 2 ^ (prefixWord ++ tailWord_2435273).sum := by decide
  have hdescent : baseEnd_2435273 < baseStart_2435273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435297 : List Nat := [1, 2, 3, 1, 3, 1, 4, 1, 2, 2, 3]
def baseStart_2435297 : Nat := 118140960795 + 2435297 * 2 ^ 59
def prefixEnd_2435297 : Nat := 4983230072969 + 3 ^ 40 * 2435297 * 2
def baseEnd_2435297 : Nat := 1250477897452463622987779

theorem tailTrace_2435297 : CollatzResearch.WordTrace tailWord_2435297 prefixEnd_2435297 1250477897452463622987779 := by
  unfold tailWord_2435297
  simp only [CollatzResearch.WordTrace]
  refine ⟨88822578658342359459976145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59215052438894906306650763 88822578658342359459976145)
  ·
    refine ⟨66616933993756769594982109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88822578658342359459976145 66616933993756769594982109)
    ·
      refine ⟨24981350247658788598118291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66616933993756769594982109 24981350247658788598118291)
      ·
        refine ⟨37472025371488182897177437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24981350247658788598118291 37472025371488182897177437)
        ·
          refine ⟨14052009514308068586441539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37472025371488182897177437 14052009514308068586441539)
          ·
            refine ⟨21078014271462102879662309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14052009514308068586441539 21078014271462102879662309)
            ·
              refine ⟨3952127675899144289936683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21078014271462102879662309 3952127675899144289936683)
              ·
                refine ⟨5928191513848716434905025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3952127675899144289936683 5928191513848716434905025)
                ·
                  refine ⟨4446143635386537326178769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5928191513848716434905025 4446143635386537326178769)
                  ·
                    refine ⟨3334607726539902994634077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4446143635386537326178769 3334607726539902994634077)
                    ·
                      refine ⟨1250477897452463622987779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3334607726539902994634077 1250477897452463622987779)
                      ·
                        rfl

theorem cell23_2435297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_2435297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435297 prefixEnd_2435297 := by exact prefixLift 2435297
  have htrace : WordTrace (prefixWord ++ tailWord_2435297) baseStart_2435297 baseEnd_2435297 := by
    simpa [prefixWord, tailWord_2435297, baseEnd_2435297] using wordTrace_append hprefix tailTrace_2435297
  have hstable : (prefixWord ++ tailWord_2435297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435297).length < 2 ^ (prefixWord ++ tailWord_2435297).sum := by decide
  have hdescent : baseEnd_2435297 < baseStart_2435297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435323 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 5]
def baseStart_2435323 : Nat := 118140960795 + 2435323 * 2 ^ 59
def prefixEnd_2435323 : Nat := 4983230072969 + 3 ^ 40 * 2435323 * 2
def baseEnd_2435323 : Nat := 1250491247949480521262659

theorem tailTrace_2435323 : CollatzResearch.WordTrace tailWord_2435323 prefixEnd_2435323 1250491247949480521262659 := by
  unfold tailWord_2435323
  simp only [CollatzResearch.WordTrace]
  refine ⟨88823526956248165900422623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59215684637498777266948415 88823526956248165900422623)
  ·
    refine ⟨133235290434372248850633935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88823526956248165900422623 133235290434372248850633935)
    ·
      refine ⟨199852935651558373275950903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133235290434372248850633935 199852935651558373275950903)
      ·
        refine ⟨299779403477337559913926355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199852935651558373275950903 299779403477337559913926355)
        ·
          refine ⟨449669105216006339870889533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299779403477337559913926355 449669105216006339870889533)
          ·
            refine ⟨168625914456002377451583575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 449669105216006339870889533 168625914456002377451583575)
            ·
              refine ⟨252938871684003566177375363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168625914456002377451583575 252938871684003566177375363)
              ·
                refine ⟨379408307526005349266063045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252938871684003566177375363 379408307526005349266063045)
                ·
                  refine ⟨71139057661126002987386821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 379408307526005349266063045 71139057661126002987386821)
                  ·
                    refine ⟨13338573311461125560135029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71139057661126002987386821 13338573311461125560135029)
                    ·
                      refine ⟨1250491247949480521262659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13338573311461125560135029 1250491247949480521262659)
                      ·
                        rfl

theorem cell23_2435323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 5].length) (baseStart_2435323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435323 prefixEnd_2435323 := by exact prefixLift 2435323
  have htrace : WordTrace (prefixWord ++ tailWord_2435323) baseStart_2435323 baseEnd_2435323 := by
    simpa [prefixWord, tailWord_2435323, baseEnd_2435323] using wordTrace_append hprefix tailTrace_2435323
  have hstable : (prefixWord ++ tailWord_2435323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435323).length < 2 ^ (prefixWord ++ tailWord_2435323).sum := by decide
  have hdescent : baseEnd_2435323 < baseStart_2435323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435327 : List Nat := [1, 1, 2, 2, 1, 4, 2, 3, 3, 1, 3]
def baseStart_2435327 : Nat := 118140960795 + 2435327 * 2 ^ 59
def prefixEnd_2435327 : Nat := 4983230072969 + 3 ^ 40 * 2435327 * 2
def baseEnd_2435327 : Nat := 1250493301872098505612641

theorem tailTrace_2435327 : CollatzResearch.WordTrace tailWord_2435327 prefixEnd_2435327 1250493301872098505612641 := by
  unfold tailWord_2435327
  simp only [CollatzResearch.WordTrace]
  refine ⟨88823672848233674583568235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59215781898822449722378823 88823672848233674583568235)
  ·
    refine ⟨133235509272350511875352353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88823672848233674583568235 133235509272350511875352353)
    ·
      refine ⟨99926631954262883906514265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133235509272350511875352353 99926631954262883906514265)
      ·
        refine ⟨74944973965697162929885699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99926631954262883906514265 74944973965697162929885699)
        ·
          refine ⟨112417460948545744394828549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74944973965697162929885699 112417460948545744394828549)
          ·
            refine ⟨21078273927852327074030353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112417460948545744394828549 21078273927852327074030353)
            ·
              refine ⟨15808705445889245305522765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21078273927852327074030353 15808705445889245305522765)
              ·
                refine ⟨5928264542208466989571037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15808705445889245305522765 5928264542208466989571037)
                ·
                  refine ⟨2223099203328175121089139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5928264542208466989571037 2223099203328175121089139)
                  ·
                    refine ⟨3334648804992262681633709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2223099203328175121089139 3334648804992262681633709)
                    ·
                      refine ⟨1250493301872098505612641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3334648804992262681633709 1250493301872098505612641)
                      ·
                        rfl

theorem cell23_2435327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3, 1, 3].length) (baseStart_2435327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435327 prefixEnd_2435327 := by exact prefixLift 2435327
  have htrace : WordTrace (prefixWord ++ tailWord_2435327) baseStart_2435327 baseEnd_2435327 := by
    simpa [prefixWord, tailWord_2435327, baseEnd_2435327] using wordTrace_append hprefix tailTrace_2435327
  have hstable : (prefixWord ++ tailWord_2435327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435327).length < 2 ^ (prefixWord ++ tailWord_2435327).sum := by decide
  have hdescent : baseEnd_2435327 < baseStart_2435327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435354 : List Nat := [3, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2]
def baseStart_2435354 : Nat := 118140960795 + 2435354 * 2 ^ 59
def prefixEnd_2435354 : Nat := 4983230072969 + 3 ^ 40 * 2435354 * 2
def baseEnd_2435354 : Nat := 1250507165849769899975017

theorem tailTrace_2435354 : CollatzResearch.WordTrace tailWord_2435354 prefixEnd_2435354 1250507165849769899975017 := by
  unfold tailWord_2435354
  simp only [CollatzResearch.WordTrace]
  refine ⟨22206164404783964548700279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59216438412757238796534077 22206164404783964548700279)
  ·
    refine ⟨33309246607175946823050419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22206164404783964548700279 33309246607175946823050419)
    ·
      refine ⟨49963869910763920234575629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33309246607175946823050419 49963869910763920234575629)
      ·
        refine ⟨18736451216536470087965861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49963869910763920234575629 18736451216536470087965861)
        ·
          refine ⟨3513084603100588141493599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18736451216536470087965861 3513084603100588141493599)
          ·
            refine ⟨5269626904650882212240399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3513084603100588141493599 5269626904650882212240399)
            ·
              refine ⟨7904440356976323318360599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5269626904650882212240399 7904440356976323318360599)
              ·
                refine ⟨11856660535464484977540899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7904440356976323318360599 11856660535464484977540899)
                ·
                  refine ⟨17784990803196727466311349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11856660535464484977540899 17784990803196727466311349)
                  ·
                    refine ⟨1667342887799693199966689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17784990803196727466311349 1667342887799693199966689)
                    ·
                      refine ⟨1250507165849769899975017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1667342887799693199966689 1250507165849769899975017)
                      ·
                        rfl

theorem cell23_2435354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_2435354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435354 prefixEnd_2435354 := by exact prefixLift 2435354
  have htrace : WordTrace (prefixWord ++ tailWord_2435354) baseStart_2435354 baseEnd_2435354 := by
    simpa [prefixWord, tailWord_2435354, baseEnd_2435354] using wordTrace_append hprefix tailTrace_2435354
  have hstable : (prefixWord ++ tailWord_2435354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435354).length < 2 ^ (prefixWord ++ tailWord_2435354).sum := by decide
  have hdescent : baseEnd_2435354 < baseStart_2435354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435364 : List Nat := [2, 3, 1, 3, 1, 2, 4, 1, 1, 5]
def baseStart_2435364 : Nat := 118140960795 + 2435364 * 2 ^ 59
def prefixEnd_2435364 : Nat := 4983230072969 + 3 ^ 40 * 2435364 * 2
def baseEnd_2435364 : Nat := 416837433552104953616657

theorem tailTrace_2435364 : CollatzResearch.WordTrace tailWord_2435364 prefixEnd_2435364 416837433552104953616657 := by
  unfold tailWord_2435364
  simp only [CollatzResearch.WordTrace]
  refine ⟨44412511174549814951332573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59216681566066419935110097 44412511174549814951332573)
  ·
    refine ⟨16654691690456180606749715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44412511174549814951332573 16654691690456180606749715)
    ·
      refine ⟨24982037535684270910124573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16654691690456180606749715 24982037535684270910124573)
      ·
        refine ⟨9368264075881601591296715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24982037535684270910124573 9368264075881601591296715)
        ·
          refine ⟨14052396113822402386945073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9368264075881601591296715 14052396113822402386945073)
          ·
            refine ⟨10539297085366801790208805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14052396113822402386945073 10539297085366801790208805)
            ·
              refine ⟨1976118203506275335664151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10539297085366801790208805 1976118203506275335664151)
              ·
                refine ⟨2964177305259413003496227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1976118203506275335664151 2964177305259413003496227)
                ·
                  refine ⟨4446265957889119505244341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2964177305259413003496227 4446265957889119505244341)
                  ·
                    refine ⟨416837433552104953616657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4446265957889119505244341 416837433552104953616657)
                    ·
                      rfl

theorem cell23_2435364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_2435364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435364 prefixEnd_2435364 := by exact prefixLift 2435364
  have htrace : WordTrace (prefixWord ++ tailWord_2435364) baseStart_2435364 baseEnd_2435364 := by
    simpa [prefixWord, tailWord_2435364, baseEnd_2435364] using wordTrace_append hprefix tailTrace_2435364
  have hstable : (prefixWord ++ tailWord_2435364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435364).length < 2 ^ (prefixWord ++ tailWord_2435364).sum := by decide
  have hdescent : baseEnd_2435364 < baseStart_2435364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435384 : List Nat := [2, 1, 2, 1, 3, 1, 3, 3, 3, 2, 2]
def baseStart_2435384 : Nat := 118140960795 + 2435384 * 2 ^ 59
def prefixEnd_2435384 : Nat := 4983230072969 + 3 ^ 40 * 2435384 * 2
def baseEnd_2435384 : Nat := 1250522570269404782599879

theorem tailTrace_2435384 : CollatzResearch.WordTrace tailWord_2435384 prefixEnd_2435384 1250522570269404782599879 := by
  unfold tailWord_2435384
  simp only [CollatzResearch.WordTrace]
  refine ⟨44412875904513586659196603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59217167872684782212262137 44412875904513586659196603)
  ·
    refine ⟨66619313856770379988794905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44412875904513586659196603 66619313856770379988794905)
    ·
      refine ⟨49964485392577784991596179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66619313856770379988794905 49964485392577784991596179)
      ·
        refine ⟨74946728088866677487394269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49964485392577784991596179 74946728088866677487394269)
        ·
          refine ⟨28105023033325004057772851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74946728088866677487394269 28105023033325004057772851)
          ·
            refine ⟨42157534549987506086659277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28105023033325004057772851 42157534549987506086659277)
            ·
              refine ⟨15809075456245314782497229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42157534549987506086659277 15809075456245314782497229)
              ·
                refine ⟨5928403296091993043436461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15809075456245314782497229 5928403296091993043436461)
                ·
                  refine ⟨2223151236034497391288673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5928403296091993043436461 2223151236034497391288673)
                  ·
                    refine ⟨1667363427025873043466505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2223151236034497391288673 1667363427025873043466505)
                    ·
                      refine ⟨1250522570269404782599879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1667363427025873043466505 1250522570269404782599879)
                      ·
                        rfl

theorem cell23_2435384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 3, 2, 2].length) (baseStart_2435384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435384 prefixEnd_2435384 := by exact prefixLift 2435384
  have htrace : WordTrace (prefixWord ++ tailWord_2435384) baseStart_2435384 baseEnd_2435384 := by
    simpa [prefixWord, tailWord_2435384, baseEnd_2435384] using wordTrace_append hprefix tailTrace_2435384
  have hstable : (prefixWord ++ tailWord_2435384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435384).length < 2 ^ (prefixWord ++ tailWord_2435384).sum := by decide
  have hdescent : baseEnd_2435384 < baseStart_2435384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435404 : List Nat := [2, 2, 1, 3, 2, 1, 4, 2, 1, 2, 3]
def baseStart_2435404 : Nat := 118140960795 + 2435404 * 2 ^ 59
def prefixEnd_2435404 : Nat := 4983230072969 + 3 ^ 40 * 2435404 * 2
def baseEnd_2435404 : Nat := 1250532839882494704349787

theorem tailTrace_2435404 : CollatzResearch.WordTrace tailWord_2435404 prefixEnd_2435404 1250532839882494704349787 := by
  unfold tailWord_2435404
  simp only [CollatzResearch.WordTrace]
  refine ⟨44413240634477358367060633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59217654179303144489414177 44413240634477358367060633)
  ·
    refine ⟨33309930475858018775295475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44413240634477358367060633 33309930475858018775295475)
    ·
      refine ⟨49964895713787028162943213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33309930475858018775295475 49964895713787028162943213)
      ·
        refine ⟨18736835892670135561103705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49964895713787028162943213 18736835892670135561103705)
        ·
          refine ⟨14052626919502601670827779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18736835892670135561103705 14052626919502601670827779)
          ·
            refine ⟨21078940379253902506241669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14052626919502601670827779 21078940379253902506241669)
            ·
              refine ⟨3952301321110106719920313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21078940379253902506241669 3952301321110106719920313)
              ·
                refine ⟨2964225990832580039940235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3952301321110106719920313 2964225990832580039940235)
                ·
                  refine ⟨4446338986248870059910353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2964225990832580039940235 4446338986248870059910353)
                  ·
                    refine ⟨3334754239686652544932765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4446338986248870059910353 3334754239686652544932765)
                    ·
                      refine ⟨1250532839882494704349787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3334754239686652544932765 1250532839882494704349787)
                      ·
                        rfl

theorem cell23_2435404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_2435404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435404 prefixEnd_2435404 := by exact prefixLift 2435404
  have htrace : WordTrace (prefixWord ++ tailWord_2435404) baseStart_2435404 baseEnd_2435404 := by
    simpa [prefixWord, tailWord_2435404, baseEnd_2435404] using wordTrace_append hprefix tailTrace_2435404
  have hstable : (prefixWord ++ tailWord_2435404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435404).length < 2 ^ (prefixWord ++ tailWord_2435404).sum := by decide
  have hdescent : baseEnd_2435404 < baseStart_2435404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435422 : List Nat := [4, 4, 2, 1, 1, 1, 1, 2, 2, 3, 2]
def baseStart_2435422 : Nat := 118140960795 + 2435422 * 2 ^ 59
def prefixEnd_2435422 : Nat := 4983230072969 + 3 ^ 40 * 2435422 * 2
def baseEnd_2435422 : Nat := 1250542082534275633924705

theorem tailTrace_2435422 : CollatzResearch.WordTrace tailWord_2435422 prefixEnd_2435422 1250542082534275633924705 := by
  unfold tailWord_2435422
  simp only [CollatzResearch.WordTrace]
  refine ⟨11103392222861188226034565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59218091855259670538851013 11103392222861188226034565)
  ·
    refine ⟨2081886041786472792381481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11103392222861188226034565 2081886041786472792381481)
    ·
      refine ⟨1561414531339854594286111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2081886041786472792381481 1561414531339854594286111)
      ·
        refine ⟨2342121797009781891429167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1561414531339854594286111 2342121797009781891429167)
        ·
          refine ⟨3513182695514672837143751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2342121797009781891429167 3513182695514672837143751)
          ·
            refine ⟨5269774043272009255715627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3513182695514672837143751 5269774043272009255715627)
            ·
              refine ⟨7904661064908013883573441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5269774043272009255715627 7904661064908013883573441)
              ·
                refine ⟨5928495798681010412680081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7904661064908013883573441 5928495798681010412680081)
                ·
                  refine ⟨4446371849010757809510061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5928495798681010412680081 4446371849010757809510061)
                  ·
                    refine ⟨1667389443379034178566273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4446371849010757809510061 1667389443379034178566273)
                    ·
                      refine ⟨1250542082534275633924705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1667389443379034178566273 1250542082534275633924705)
                      ·
                        rfl

theorem cell23_2435422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_2435422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435422 prefixEnd_2435422 := by exact prefixLift 2435422
  have htrace : WordTrace (prefixWord ++ tailWord_2435422) baseStart_2435422 baseEnd_2435422 := by
    simpa [prefixWord, tailWord_2435422, baseEnd_2435422] using wordTrace_append hprefix tailTrace_2435422
  have hstable : (prefixWord ++ tailWord_2435422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435422).length < 2 ^ (prefixWord ++ tailWord_2435422).sum := by decide
  have hdescent : baseEnd_2435422 < baseStart_2435422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435451 : List Nat := [1, 1, 1, 1, 1, 7, 4, 1, 2, 1, 3]
def baseStart_2435451 : Nat := 118140960795 + 2435451 * 2 ^ 59
def prefixEnd_2435451 : Nat := 4983230072969 + 3 ^ 40 * 2435451 * 2
def baseEnd_2435451 : Nat := 1250556973473256020462071

theorem tailTrace_2435451 : CollatzResearch.WordTrace tailWord_2435451 prefixEnd_2435451 1250556973473256020462071 := by
  unfold tailWord_2435451
  simp only [CollatzResearch.WordTrace]
  refine ⟨88828195499784443761082207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59218796999856295840721471 88828195499784443761082207)
  ·
    refine ⟨133242293249676665641623311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88828195499784443761082207 133242293249676665641623311)
    ·
      refine ⟨199863439874514998462434967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133242293249676665641623311 199863439874514998462434967)
      ·
        refine ⟨299795159811772497693652451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199863439874514998462434967 299795159811772497693652451)
        ·
          refine ⟨449692739717658746540478677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299795159811772497693652451 449692739717658746540478677)
          ·
            refine ⟨10539673587132626872042469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 449692739717658746540478677 10539673587132626872042469)
            ·
              refine ⟨1976188797587367538507963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10539673587132626872042469 1976188797587367538507963)
              ·
                refine ⟨2964283196381051307761945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1976188797587367538507963 2964283196381051307761945)
                ·
                  refine ⟨2223212397285788480821459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2964283196381051307761945 2223212397285788480821459)
                  ·
                    refine ⟨3334818595928682721232189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2223212397285788480821459 3334818595928682721232189)
                    ·
                      refine ⟨1250556973473256020462071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3334818595928682721232189 1250556973473256020462071)
                      ·
                        rfl

theorem cell23_2435451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 2, 1, 3].length) (baseStart_2435451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435451 prefixEnd_2435451 := by exact prefixLift 2435451
  have htrace : WordTrace (prefixWord ++ tailWord_2435451) baseStart_2435451 baseEnd_2435451 := by
    simpa [prefixWord, tailWord_2435451, baseEnd_2435451] using wordTrace_append hprefix tailTrace_2435451
  have hstable : (prefixWord ++ tailWord_2435451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435451).length < 2 ^ (prefixWord ++ tailWord_2435451).sum := by decide
  have hdescent : baseEnd_2435451 < baseStart_2435451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435487 : List Nat := [1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 4]
def baseStart_2435487 : Nat := 118140960795 + 2435487 * 2 ^ 59
def prefixEnd_2435487 : Nat := 4983230072969 + 3 ^ 40 * 2435487 * 2
def baseEnd_2435487 : Nat := 1250575458776817879611905

theorem tailTrace_2435487 : CollatzResearch.WordTrace tailWord_2435487 prefixEnd_2435487 1250575458776817879611905 := by
  unfold tailWord_2435487
  simp only [CollatzResearch.WordTrace]
  refine ⟨88829508527654021909392715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59219672351769347939595143 88829508527654021909392715)
  ·
    refine ⟨133244262791481032864089073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88829508527654021909392715 133244262791481032864089073)
    ·
      refine ⟨99933197093610774648066805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133244262791481032864089073 99933197093610774648066805)
      ·
        refine ⟨9368737227526010123256263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99933197093610774648066805 9368737227526010123256263)
        ·
          refine ⟨14053105841289015184884395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9368737227526010123256263 14053105841289015184884395)
          ·
            refine ⟨21079658761933522777326593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14053105841289015184884395 21079658761933522777326593)
            ·
              refine ⟨15809744071450142082994945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21079658761933522777326593 15809744071450142082994945)
              ·
                refine ⟨11857308053587606562246209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15809744071450142082994945 11857308053587606562246209)
                ·
                  refine ⟨8892981040190704921684657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11857308053587606562246209 8892981040190704921684657)
                  ·
                    refine ⟨6669735780143028691263493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8892981040190704921684657 6669735780143028691263493)
                    ·
                      refine ⟨1250575458776817879611905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6669735780143028691263493 1250575458776817879611905)
                      ·
                        rfl

theorem cell23_2435487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_2435487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435487 prefixEnd_2435487 := by exact prefixLift 2435487
  have htrace : WordTrace (prefixWord ++ tailWord_2435487) baseStart_2435487 baseEnd_2435487 := by
    simpa [prefixWord, tailWord_2435487, baseEnd_2435487] using wordTrace_append hprefix tailTrace_2435487
  have hstable : (prefixWord ++ tailWord_2435487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435487).length < 2 ^ (prefixWord ++ tailWord_2435487).sum := by decide
  have hdescent : baseEnd_2435487 < baseStart_2435487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435491 : List Nat := [1, 1, 1, 4, 1, 4, 1, 4, 2, 2, 2]
def baseStart_2435491 : Nat := 118140960795 + 2435491 * 2 ^ 59
def prefixEnd_2435491 : Nat := 4983230072969 + 3 ^ 40 * 2435491 * 2
def baseEnd_2435491 : Nat := 1250577512699435863961887

theorem tailTrace_2435491 : CollatzResearch.WordTrace tailWord_2435491 prefixEnd_2435491 1250577512699435863961887 := by
  unfold tailWord_2435491
  simp only [CollatzResearch.WordTrace]
  refine ⟨88829654419639530592538327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59219769613093020395025551 88829654419639530592538327)
  ·
    refine ⟨133244481629459295888807491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88829654419639530592538327 133244481629459295888807491)
    ·
      refine ⟨199866722444188943833211237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133244481629459295888807491 199866722444188943833211237)
      ·
        refine ⟨37475010458285426968727107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 199866722444188943833211237 37475010458285426968727107)
        ·
          refine ⟨56212515687428140453090661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37475010458285426968727107 56212515687428140453090661)
          ·
            refine ⟨10539846691392776334954499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56212515687428140453090661 10539846691392776334954499)
            ·
              refine ⟨15809770037089164502431749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10539846691392776334954499 15809770037089164502431749)
              ·
                refine ⟨2964331881954218344205953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15809770037089164502431749 2964331881954218344205953)
                ·
                  refine ⟨2223248911465663758154465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2964331881954218344205953 2223248911465663758154465)
                  ·
                    refine ⟨1667436683599247818615849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2223248911465663758154465 1667436683599247818615849)
                    ·
                      refine ⟨1250577512699435863961887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1667436683599247818615849 1250577512699435863961887)
                      ·
                        rfl

theorem cell23_2435491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2, 2, 2].length) (baseStart_2435491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435491 prefixEnd_2435491 := by exact prefixLift 2435491
  have htrace : WordTrace (prefixWord ++ tailWord_2435491) baseStart_2435491 baseEnd_2435491 := by
    simpa [prefixWord, tailWord_2435491, baseEnd_2435491] using wordTrace_append hprefix tailTrace_2435491
  have hstable : (prefixWord ++ tailWord_2435491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435491).length < 2 ^ (prefixWord ++ tailWord_2435491).sum := by decide
  have hdescent : baseEnd_2435491 < baseStart_2435491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435500 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 8]
def baseStart_2435500 : Nat := 118140960795 + 2435500 * 2 ^ 59
def prefixEnd_2435500 : Nat := 4983230072969 + 3 ^ 40 * 2435500 * 2
def baseEnd_2435500 : Nat := 1250582134025326328749345

theorem tailTrace_2435500 : CollatzResearch.WordTrace tailWord_2435500 prefixEnd_2435500 1250582134025326328749345 := by
  unfold tailWord_2435500
  simp only [CollatzResearch.WordTrace]
  refine ⟨44414991338303462564807977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59219988451071283419743969 44414991338303462564807977)
  ·
    refine ⟨33311243503727596923605983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44414991338303462564807977 33311243503727596923605983)
    ·
      refine ⟨49966865255591395385408975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33311243503727596923605983 49966865255591395385408975)
      ·
        refine ⟨74950297883387093078113463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49966865255591395385408975 74950297883387093078113463)
        ·
          refine ⟨112425446825080639617170195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74950297883387093078113463 112425446825080639617170195)
          ·
            refine ⟨168638170237620959425755293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112425446825080639617170195 168638170237620959425755293)
            ·
              refine ⟨63239313839107859784658235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168638170237620959425755293 63239313839107859784658235)
              ·
                refine ⟨94858970758661789676987353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63239313839107859784658235 94858970758661789676987353)
                ·
                  refine ⟨71144228068996342257740515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94858970758661789676987353 71144228068996342257740515)
                  ·
                    refine ⟨106716342103494513386610773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71144228068996342257740515 106716342103494513386610773)
                    ·
                      refine ⟨1250582134025326328749345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 106716342103494513386610773 1250582134025326328749345)
                      ·
                        rfl

theorem cell23_2435500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_2435500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435500 prefixEnd_2435500 := by exact prefixLift 2435500
  have htrace : WordTrace (prefixWord ++ tailWord_2435500) baseStart_2435500 baseEnd_2435500 := by
    simpa [prefixWord, tailWord_2435500, baseEnd_2435500] using wordTrace_append hprefix tailTrace_2435500
  have hstable : (prefixWord ++ tailWord_2435500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435500).length < 2 ^ (prefixWord ++ tailWord_2435500).sum := by decide
  have hdescent : baseEnd_2435500 < baseStart_2435500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435527 : List Nat := [1, 1, 4, 1, 1, 5, 1, 1, 1, 7]
def baseStart_2435527 : Nat := 118140960795 + 2435527 * 2 ^ 59
def prefixEnd_2435527 : Nat := 4983230072969 + 3 ^ 40 * 2435527 * 2
def baseEnd_2435527 : Nat := 416865332667665907703907

theorem tailTrace_2435527 : CollatzResearch.WordTrace tailWord_2435527 prefixEnd_2435527 416865332667665907703907 := by
  unfold tailWord_2435527
  simp only [CollatzResearch.WordTrace]
  refine ⟨88830967447509108740848835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59220644965006072493899223 88830967447509108740848835)
  ·
    refine ⟨133246451171263663111273253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88830967447509108740848835 133246451171263663111273253)
    ·
      refine ⟨24983709594611936833363735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133246451171263663111273253 24983709594611936833363735)
      ·
        refine ⟨37475564391917905250045603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24983709594611936833363735 37475564391917905250045603)
        ·
          refine ⟨56213346587876857875068405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37475564391917905250045603 56213346587876857875068405)
          ·
            refine ⟨5270001242613455425787663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56213346587876857875068405 5270001242613455425787663)
            ·
              refine ⟨7905001863920183138681495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5270001242613455425787663 7905001863920183138681495)
              ·
                refine ⟨11857502795880274708022243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7905001863920183138681495 11857502795880274708022243)
                ·
                  refine ⟨17786254193820412062033365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11857502795880274708022243 17786254193820412062033365)
                  ·
                    refine ⟨416865332667665907703907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17786254193820412062033365 416865332667665907703907)
                    ·
                      rfl

theorem cell23_2435527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_2435527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435527 prefixEnd_2435527 := by exact prefixLift 2435527
  have htrace : WordTrace (prefixWord ++ tailWord_2435527) baseStart_2435527 baseEnd_2435527 := by
    simpa [prefixWord, tailWord_2435527, baseEnd_2435527] using wordTrace_append hprefix tailTrace_2435527
  have hstable : (prefixWord ++ tailWord_2435527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435527).length < 2 ^ (prefixWord ++ tailWord_2435527).sum := by decide
  have hdescent : baseEnd_2435527 < baseStart_2435527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435564 : List Nat := [2, 2, 1, 1, 2, 1, 3, 3, 2, 4, 2]
def baseStart_2435564 : Nat := 118140960795 + 2435564 * 2 ^ 59
def prefixEnd_2435564 : Nat := 4983230072969 + 3 ^ 40 * 2435564 * 2
def baseEnd_2435564 : Nat := 1250614996787214078349051

theorem tailTrace_2435564 : CollatzResearch.WordTrace tailWord_2435564 prefixEnd_2435564 1250614996787214078349051 := by
  unfold tailWord_2435564
  simp only [CollatzResearch.WordTrace]
  refine ⟨44416158474187532029972873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59221544632250042706630497 44416158474187532029972873)
  ·
    refine ⟨33312118855640649022479655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44416158474187532029972873 33312118855640649022479655)
    ·
      refine ⟨49968178283460973533719483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33312118855640649022479655 49968178283460973533719483)
      ·
        refine ⟨74952267425191460300579225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49968178283460973533719483 74952267425191460300579225)
        ·
          refine ⟨56214200568893595225434419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74952267425191460300579225 56214200568893595225434419)
          ·
            refine ⟨84321300853340392838151629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56214200568893595225434419 84321300853340392838151629)
            ·
              refine ⟨31620487820002647314306861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84321300853340392838151629 31620487820002647314306861)
              ·
                refine ⟨11857682932500992742865073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31620487820002647314306861 11857682932500992742865073)
                ·
                  refine ⟨8893262199375744557148805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11857682932500992742865073 8893262199375744557148805)
                  ·
                    refine ⟨1667486662382952104465401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8893262199375744557148805 1667486662382952104465401)
                    ·
                      refine ⟨1250614996787214078349051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1667486662382952104465401 1250614996787214078349051)
                      ·
                        rfl

theorem cell23_2435564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 4, 2].length) (baseStart_2435564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435564 prefixEnd_2435564 := by exact prefixLift 2435564
  have htrace : WordTrace (prefixWord ++ tailWord_2435564) baseStart_2435564 baseEnd_2435564 := by
    simpa [prefixWord, tailWord_2435564, baseEnd_2435564] using wordTrace_append hprefix tailTrace_2435564
  have hstable : (prefixWord ++ tailWord_2435564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435564).length < 2 ^ (prefixWord ++ tailWord_2435564).sum := by decide
  have hdescent : baseEnd_2435564 < baseStart_2435564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435665 : List Nat := [1, 2, 2, 1, 3, 3, 4, 2, 1, 1, 3]
def baseStart_2435665 : Nat := 118140960795 + 2435665 * 2 ^ 59
def prefixEnd_2435665 : Nat := 4983230072969 + 3 ^ 40 * 2435665 * 2
def baseEnd_2435665 : Nat := 1250666858333318183186087

theorem tailTrace_2435665 : CollatzResearch.WordTrace tailWord_2435665 prefixEnd_2435665 1250666858333318183186087 := by
  unfold tailWord_2435665
  simp only [CollatzResearch.WordTrace]
  refine ⟨88836000721009158309372449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59224000480672772206248299 88836000721009158309372449)
  ·
    refine ⟨66627000540756868732029337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88836000721009158309372449 66627000540756868732029337)
    ·
      refine ⟨49970250405567651549022003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66627000540756868732029337 49970250405567651549022003)
      ·
        refine ⟨74955375608351477323533005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49970250405567651549022003 74955375608351477323533005)
        ·
          refine ⟨28108265853131803996324877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74955375608351477323533005 28108265853131803996324877)
          ·
            refine ⟨10540599694924426498621829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28108265853131803996324877 10540599694924426498621829)
            ·
              refine ⟨1976362442798329968491593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10540599694924426498621829 1976362442798329968491593)
              ·
                refine ⟨1482271832098747476368695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1976362442798329968491593 1482271832098747476368695)
                ·
                  refine ⟨2223407748148121214553043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1482271832098747476368695 2223407748148121214553043)
                  ·
                    refine ⟨3335111622222181821829565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2223407748148121214553043 3335111622222181821829565)
                    ·
                      refine ⟨1250666858333318183186087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3335111622222181821829565 1250666858333318183186087)
                      ·
                        rfl

theorem cell23_2435665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2, 1, 1, 3].length) (baseStart_2435665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435665 prefixEnd_2435665 := by exact prefixLift 2435665
  have htrace : WordTrace (prefixWord ++ tailWord_2435665) baseStart_2435665 baseEnd_2435665 := by
    simpa [prefixWord, tailWord_2435665, baseEnd_2435665] using wordTrace_append hprefix tailTrace_2435665
  have hstable : (prefixWord ++ tailWord_2435665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435665).length < 2 ^ (prefixWord ++ tailWord_2435665).sum := by decide
  have hdescent : baseEnd_2435665 < baseStart_2435665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435667 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 4]
def baseStart_2435667 : Nat := 118140960795 + 2435667 * 2 ^ 59
def prefixEnd_2435667 : Nat := 4983230072969 + 3 ^ 40 * 2435667 * 2
def baseEnd_2435667 : Nat := 1250667885294627175361077

theorem tailTrace_2435667 : CollatzResearch.WordTrace tailWord_2435667 prefixEnd_2435667 1250667885294627175361077 := by
  unfold tailWord_2435667
  simp only [CollatzResearch.WordTrace]
  refine ⟨88836073667001912650945255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59224049111334608433963503 88836073667001912650945255)
  ·
    refine ⟨133254110500502868976417883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88836073667001912650945255 133254110500502868976417883)
    ·
      refine ⟨199881165750754303464626825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133254110500502868976417883 199881165750754303464626825)
      ·
        refine ⟨149910874313065727598470119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199881165750754303464626825 149910874313065727598470119)
        ·
          refine ⟨224866311469598591397705179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149910874313065727598470119 224866311469598591397705179)
          ·
            refine ⟨337299467204397887096557769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224866311469598591397705179 337299467204397887096557769)
            ·
              refine ⟨252974600403298415322418327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 337299467204397887096557769 252974600403298415322418327)
              ·
                refine ⟨379461900604947622983627491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252974600403298415322418327 379461900604947622983627491)
                ·
                  refine ⟨569192850907421434475441237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 379461900604947622983627491 569192850907421434475441237)
                  ·
                    refine ⟨6670228721571344935259077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 569192850907421434475441237 6670228721571344935259077)
                    ·
                      refine ⟨1250667885294627175361077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6670228721571344935259077 1250667885294627175361077)
                      ·
                        rfl

theorem cell23_2435667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 4].length) (baseStart_2435667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435667 prefixEnd_2435667 := by exact prefixLift 2435667
  have htrace : WordTrace (prefixWord ++ tailWord_2435667) baseStart_2435667 baseEnd_2435667 := by
    simpa [prefixWord, tailWord_2435667, baseEnd_2435667] using wordTrace_append hprefix tailTrace_2435667
  have hstable : (prefixWord ++ tailWord_2435667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435667).length < 2 ^ (prefixWord ++ tailWord_2435667).sum := by decide
  have hdescent : baseEnd_2435667 < baseStart_2435667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435681 : List Nat := [1, 2, 3, 1, 1, 4, 2, 3, 2, 4]
def baseStart_2435681 : Nat := 118140960795 + 2435681 * 2 ^ 59
def prefixEnd_2435681 : Nat := 4983230072969 + 3 ^ 40 * 2435681 * 2
def baseEnd_2435681 : Nat := 416891691341263373528671

theorem tailTrace_2435681 : CollatzResearch.WordTrace tailWord_2435681 prefixEnd_2435681 416891691341263373528671 := by
  unfold tailWord_2435681
  simp only [CollatzResearch.WordTrace]
  refine ⟨88836584288951193041954897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59224389525967462027969931 88836584288951193041954897)
  ·
    refine ⟨66627438216713394781466173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88836584288951193041954897 66627438216713394781466173)
    ·
      refine ⟨24985289331267523043049815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66627438216713394781466173 24985289331267523043049815)
      ·
        refine ⟨37477933996901284564574723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24985289331267523043049815 37477933996901284564574723)
        ·
          refine ⟨56216900995351926846862085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37477933996901284564574723 56216900995351926846862085)
          ·
            refine ⟨10540668936628486283786641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56216900995351926846862085 10540668936628486283786641)
            ·
              refine ⟨7905501702471364712839981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10540668936628486283786641 7905501702471364712839981)
              ·
                refine ⟨2964563138426761767314993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7905501702471364712839981 2964563138426761767314993)
                ·
                  refine ⟨2223422353820071325486245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2964563138426761767314993 2223422353820071325486245)
                  ·
                    refine ⟨416891691341263373528671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2223422353820071325486245 416891691341263373528671)
                    ·
                      rfl

theorem cell23_2435681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_2435681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435681 prefixEnd_2435681 := by exact prefixLift 2435681
  have htrace : WordTrace (prefixWord ++ tailWord_2435681) baseStart_2435681 baseEnd_2435681 := by
    simpa [prefixWord, tailWord_2435681, baseEnd_2435681] using wordTrace_append hprefix tailTrace_2435681
  have hstable : (prefixWord ++ tailWord_2435681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435681).length < 2 ^ (prefixWord ++ tailWord_2435681).sum := by decide
  have hdescent : baseEnd_2435681 < baseStart_2435681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435702 : List Nat := [5, 1, 1, 2, 4, 1, 2, 1, 1, 5]
def baseStart_2435702 : Nat := 118140960795 + 2435702 * 2 ^ 59
def prefixEnd_2435702 : Nat := 4983230072969 + 3 ^ 40 * 2435702 * 2
def baseEnd_2435702 : Nat := 416895285705844846141139

theorem tailTrace_2435702 : CollatzResearch.WordTrace tailWord_2435702 prefixEnd_2435702 416895285705844846141139 := by
  unfold tailWord_2435702
  simp only [CollatzResearch.WordTrace]
  refine ⟨5552334388867194601779335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59224900147916742418979573 5552334388867194601779335)
  ·
    refine ⟨8328501583300791902669003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5552334388867194601779335 8328501583300791902669003)
    ·
      refine ⟨12492752374951187854003505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8328501583300791902669003 12492752374951187854003505)
      ·
        refine ⟨9369564281213390890502629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12492752374951187854003505 9369564281213390890502629)
        ·
          refine ⟨1756793302727510791969243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9369564281213390890502629 1756793302727510791969243)
          ·
            refine ⟨2635189954091266187953865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1756793302727510791969243 2635189954091266187953865)
            ·
              refine ⟨1976392465568449640965399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2635189954091266187953865 1976392465568449640965399)
              ·
                refine ⟨2964588698352674461448099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1976392465568449640965399 2964588698352674461448099)
                ·
                  refine ⟨4446883047529011692172149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2964588698352674461448099 4446883047529011692172149)
                  ·
                    refine ⟨416895285705844846141139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4446883047529011692172149 416895285705844846141139)
                    ·
                      rfl

theorem cell23_2435702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_2435702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435702 prefixEnd_2435702 := by exact prefixLift 2435702
  have htrace : WordTrace (prefixWord ++ tailWord_2435702) baseStart_2435702 baseEnd_2435702 := by
    simpa [prefixWord, tailWord_2435702, baseEnd_2435702] using wordTrace_append hprefix tailTrace_2435702
  have hstable : (prefixWord ++ tailWord_2435702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435702).length < 2 ^ (prefixWord ++ tailWord_2435702).sum := by decide
  have hdescent : baseEnd_2435702 < baseStart_2435702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435705 : List Nat := [1, 2, 1, 3, 3, 2, 1, 5, 1, 2, 2]
def baseStart_2435705 : Nat := 118140960795 + 2435705 * 2 ^ 59
def prefixEnd_2435705 : Nat := 4983230072969 + 3 ^ 40 * 2435705 * 2
def baseEnd_2435705 : Nat := 1250687397559498026685903

theorem tailTrace_2435705 : CollatzResearch.WordTrace tailWord_2435705 prefixEnd_2435705 1250687397559498026685903 := by
  unfold tailWord_2435705
  simp only [CollatzResearch.WordTrace]
  refine ⟨88837459640864245140828569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59224973093909496760552379 88837459640864245140828569)
  ·
    refine ⟨66628094730648183855621427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88837459640864245140828569 66628094730648183855621427)
    ·
      refine ⟨99942142095972275783432141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66628094730648183855621427 99942142095972275783432141)
      ·
        refine ⟨37478303285989603418787053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99942142095972275783432141 37478303285989603418787053)
        ·
          refine ⟨14054363732246101282045145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37478303285989603418787053 14054363732246101282045145)
          ·
            refine ⟨10540772799184575961533859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14054363732246101282045145 10540772799184575961533859)
            ·
              refine ⟨15811159198776863942300789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10540772799184575961533859 15811159198776863942300789)
              ·
                refine ⟨1482296174885330994590699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15811159198776863942300789 1482296174885330994590699)
                ·
                  refine ⟨2223444262327996491886049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1482296174885330994590699 2223444262327996491886049)
                  ·
                    refine ⟨1667583196745997368914537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2223444262327996491886049 1667583196745997368914537)
                    ·
                      refine ⟨1250687397559498026685903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1667583196745997368914537 1250687397559498026685903)
                      ·
                        rfl

theorem cell23_2435705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5, 1, 2, 2].length) (baseStart_2435705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435705 prefixEnd_2435705 := by exact prefixLift 2435705
  have htrace : WordTrace (prefixWord ++ tailWord_2435705) baseStart_2435705 baseEnd_2435705 := by
    simpa [prefixWord, tailWord_2435705, baseEnd_2435705] using wordTrace_append hprefix tailTrace_2435705
  have hstable : (prefixWord ++ tailWord_2435705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435705).length < 2 ^ (prefixWord ++ tailWord_2435705).sum := by decide
  have hdescent : baseEnd_2435705 < baseStart_2435705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435707 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 1, 9]
def baseStart_2435707 : Nat := 118140960795 + 2435707 * 2 ^ 59
def prefixEnd_2435707 : Nat := 4983230072969 + 3 ^ 40 * 2435707 * 2
def baseEnd_2435707 : Nat := 416896141506935672953631

theorem tailTrace_2435707 : CollatzResearch.WordTrace tailWord_2435707 prefixEnd_2435707 416896141506935672953631 := by
  unfold tailWord_2435707
  simp only [CollatzResearch.WordTrace]
  refine ⟨88837532586856999482401375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59225021724571332988267583 88837532586856999482401375)
  ·
    refine ⟨133256298880285499223602063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88837532586856999482401375 133256298880285499223602063)
    ·
      refine ⟨199884448320428248835403095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133256298880285499223602063 199884448320428248835403095)
      ·
        refine ⟨299826672480642373253104643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199884448320428248835403095 299826672480642373253104643)
        ·
          refine ⟨449740008720963559879656965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299826672480642373253104643 449740008720963559879656965)
          ·
            refine ⟨84326251635180667477435681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 449740008720963559879656965 84326251635180667477435681)
            ·
              refine ⟨63244688726385500608076761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84326251635180667477435681 63244688726385500608076761)
              ·
                refine ⟨47433516544789125456057571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63244688726385500608076761 47433516544789125456057571)
                ·
                  refine ⟨71150274817183688184086357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47433516544789125456057571 71150274817183688184086357)
                  ·
                    refine ⟨416896141506935672953631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 71150274817183688184086357 416896141506935672953631)
                    ·
                      rfl

theorem cell23_2435707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 9].length) (baseStart_2435707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435707 prefixEnd_2435707 := by exact prefixLift 2435707
  have htrace : WordTrace (prefixWord ++ tailWord_2435707) baseStart_2435707 baseEnd_2435707 := by
    simpa [prefixWord, tailWord_2435707, baseEnd_2435707] using wordTrace_append hprefix tailTrace_2435707
  have hstable : (prefixWord ++ tailWord_2435707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435707).length < 2 ^ (prefixWord ++ tailWord_2435707).sum := by decide
  have hdescent : baseEnd_2435707 < baseStart_2435707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435708 : List Nat := [2, 2, 2, 1, 1, 2, 6, 1, 1, 2, 3]
def baseStart_2435708 : Nat := 118140960795 + 2435708 * 2 ^ 59
def prefixEnd_2435708 : Nat := 4983230072969 + 3 ^ 40 * 2435708 * 2
def baseEnd_2435708 : Nat := 1250688938001461514948389

theorem tailTrace_2435708 : CollatzResearch.WordTrace tailWord_2435708 prefixEnd_2435708 1250688938001461514948389 := by
  unfold tailWord_2435708
  simp only [CollatzResearch.WordTrace]
  refine ⟨44418784529926688326593889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59225046039902251102125185 44418784529926688326593889)
  ·
    refine ⟨33314088397445016244945417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44418784529926688326593889 33314088397445016244945417)
    ·
      refine ⟨24985566298083762183709063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33314088397445016244945417 24985566298083762183709063)
      ·
        refine ⟨37478349447125643275563595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24985566298083762183709063 37478349447125643275563595)
        ·
          refine ⟨56217524170688464913345393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37478349447125643275563595 56217524170688464913345393)
          ·
            refine ⟨42163143128016348685009045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56217524170688464913345393 42163143128016348685009045)
            ·
              refine ⟨1976397334125766344609799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42163143128016348685009045 1976397334125766344609799)
              ·
                refine ⟨2964596001188649516914699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1976397334125766344609799 2964596001188649516914699)
                ·
                  refine ⟨4446894001782974275372049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2964596001188649516914699 4446894001782974275372049)
                  ·
                    refine ⟨3335170501337230706529037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4446894001782974275372049 3335170501337230706529037)
                    ·
                      refine ⟨1250688938001461514948389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3335170501337230706529037 1250688938001461514948389)
                      ·
                        rfl

theorem cell23_2435708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 1, 2, 3].length) (baseStart_2435708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435708 prefixEnd_2435708 := by exact prefixLift 2435708
  have htrace : WordTrace (prefixWord ++ tailWord_2435708) baseStart_2435708 baseEnd_2435708 := by
    simpa [prefixWord, tailWord_2435708, baseEnd_2435708] using wordTrace_append hprefix tailTrace_2435708
  have hstable : (prefixWord ++ tailWord_2435708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435708).length < 2 ^ (prefixWord ++ tailWord_2435708).sum := by decide
  have hdescent : baseEnd_2435708 < baseStart_2435708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435765 : List Nat := [1, 3, 3, 3, 1, 1, 2, 3, 1, 3, 2]
def baseStart_2435765 : Nat := 118140960795 + 2435765 * 2 ^ 59
def prefixEnd_2435765 : Nat := 4983230072969 + 3 ^ 40 * 2435765 * 2
def baseEnd_2435765 : Nat := 1250718206398767791935627

theorem tailTrace_2435765 : CollatzResearch.WordTrace tailWord_2435765 prefixEnd_2435765 1250718206398767791935627 := by
  unfold tailWord_2435765
  simp only [CollatzResearch.WordTrace]
  refine ⟨88839648020646875388012749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59226432013764583592008499 88839648020646875388012749)
  ·
    refine ⟨33314868007742578270504781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88839648020646875388012749 33314868007742578270504781)
    ·
      refine ⟨12493075502903466851439293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33314868007742578270504781 12493075502903466851439293)
      ·
        refine ⟨4684903313588800069289735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12493075502903466851439293 4684903313588800069289735)
        ·
          refine ⟨7027354970383200103934603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4684903313588800069289735 7027354970383200103934603)
          ·
            refine ⟨10541032455574800155901905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7027354970383200103934603 10541032455574800155901905)
            ·
              refine ⟨7905774341681100116926429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10541032455574800155901905 7905774341681100116926429)
              ·
                refine ⟨2964665378130412543847411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7905774341681100116926429 2964665378130412543847411)
                ·
                  refine ⟨4446998067195618815771117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2964665378130412543847411 4446998067195618815771117)
                  ·
                    refine ⟨1667624275198357055914169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4446998067195618815771117 1667624275198357055914169)
                    ·
                      refine ⟨1250718206398767791935627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1667624275198357055914169 1250718206398767791935627)
                      ·
                        rfl

theorem cell23_2435765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_2435765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435765 prefixEnd_2435765 := by exact prefixLift 2435765
  have htrace : WordTrace (prefixWord ++ tailWord_2435765) baseStart_2435765 baseEnd_2435765 := by
    simpa [prefixWord, tailWord_2435765, baseEnd_2435765] using wordTrace_append hprefix tailTrace_2435765
  have hstable : (prefixWord ++ tailWord_2435765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435765).length < 2 ^ (prefixWord ++ tailWord_2435765).sum := by decide
  have hdescent : baseEnd_2435765 < baseStart_2435765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435824 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 5]
def baseStart_2435824 : Nat := 118140960795 + 2435824 * 2 ^ 59
def prefixEnd_2435824 : Nat := 4983230072969 + 3 ^ 40 * 2435824 * 2
def baseEnd_2435824 : Nat := 1250748501757383061097855

theorem tailTrace_2435824 : CollatzResearch.WordTrace tailWord_2435824 prefixEnd_2435824 1250748501757383061097855 := by
  unfold tailWord_2435824
  simp only [CollatzResearch.WordTrace]
  refine ⟨44420899963716564232205263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59227866618288752309607017 44420899963716564232205263)
  ·
    refine ⟨66631349945574846348307895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44420899963716564232205263 66631349945574846348307895)
    ·
      refine ⟨99947024918362269522461843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66631349945574846348307895 99947024918362269522461843)
      ·
        refine ⟨149920537377543404283692765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99947024918362269522461843 149920537377543404283692765)
        ·
          refine ⟨56220201516578776606384787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149920537377543404283692765 56220201516578776606384787)
          ·
            refine ⟨84330302274868164909577181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56220201516578776606384787 84330302274868164909577181)
            ·
              refine ⟨31623863353075561841091443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84330302274868164909577181 31623863353075561841091443)
              ·
                refine ⟨47435795029613342761637165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31623863353075561841091443 47435795029613342761637165)
                ·
                  refine ⟨17788423136105003535613937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47435795029613342761637165 17788423136105003535613937)
                  ·
                    refine ⟨13341317352078752651710453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17788423136105003535613937 13341317352078752651710453)
                    ·
                      refine ⟨1250748501757383061097855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13341317352078752651710453 1250748501757383061097855)
                      ·
                        rfl

theorem cell23_2435824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 5].length) (baseStart_2435824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435824 prefixEnd_2435824 := by exact prefixLift 2435824
  have htrace : WordTrace (prefixWord ++ tailWord_2435824) baseStart_2435824 baseEnd_2435824 := by
    simpa [prefixWord, tailWord_2435824, baseEnd_2435824] using wordTrace_append hprefix tailTrace_2435824
  have hstable : (prefixWord ++ tailWord_2435824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435824).length < 2 ^ (prefixWord ++ tailWord_2435824).sum := by decide
  have hdescent : baseEnd_2435824 < baseStart_2435824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435868 : List Nat := [2, 2, 3, 1, 1, 3, 3, 1, 2, 1, 4]
def baseStart_2435868 : Nat := 118140960795 + 2435868 * 2 ^ 59
def prefixEnd_2435868 : Nat := 4983230072969 + 3 ^ 40 * 2435868 * 2
def baseEnd_2435868 : Nat := 1250771094906180888947653

theorem tailTrace_2435868 : CollatzResearch.WordTrace tailWord_2435868 prefixEnd_2435868 1250771094906180888947653 := by
  unfold tailWord_2435868
  simp only [CollatzResearch.WordTrace]
  refine ⟨44421702369636861989506129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59228936492849149319341505 44421702369636861989506129)
  ·
    refine ⟨33316276777227646492129597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44421702369636861989506129 33316276777227646492129597)
    ·
      refine ⟨12493603791460367434548599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33316276777227646492129597 12493603791460367434548599)
      ·
        refine ⟨18740405687190551151822899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12493603791460367434548599 18740405687190551151822899)
        ·
          refine ⟨28110608530785826727734349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18740405687190551151822899 28110608530785826727734349)
          ·
            refine ⟨10541478199044685022900381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28110608530785826727734349 10541478199044685022900381)
            ·
              refine ⟨3953054324641756883587643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10541478199044685022900381 3953054324641756883587643)
              ·
                refine ⟨5929581486962635325381465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3953054324641756883587643 5929581486962635325381465)
                ·
                  refine ⟨4447186115221976494036099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5929581486962635325381465 4447186115221976494036099)
                  ·
                    refine ⟨6670779172832964741054149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4447186115221976494036099 6670779172832964741054149)
                    ·
                      refine ⟨1250771094906180888947653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6670779172832964741054149 1250771094906180888947653)
                      ·
                        rfl

theorem cell23_2435868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_2435868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435868 prefixEnd_2435868 := by exact prefixLift 2435868
  have htrace : WordTrace (prefixWord ++ tailWord_2435868) baseStart_2435868 baseEnd_2435868 := by
    simpa [prefixWord, tailWord_2435868, baseEnd_2435868] using wordTrace_append hprefix tailTrace_2435868
  have hstable : (prefixWord ++ tailWord_2435868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435868).length < 2 ^ (prefixWord ++ tailWord_2435868).sum := by decide
  have hdescent : baseEnd_2435868 < baseStart_2435868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435891 : List Nat := [1, 1, 1, 2, 6, 2, 1, 1, 8]
def baseStart_2435891 : Nat := 118140960795 + 2435891 * 2 ^ 59
def prefixEnd_2435891 : Nat := 4983230072969 + 3 ^ 40 * 2435891 * 2
def baseEnd_2435891 : Nat := 138975878329026033217783

theorem tailTrace_2435891 : CollatzResearch.WordTrace tailWord_2435891 prefixEnd_2435891 138975878329026033217783 := by
  unfold tailWord_2435891
  simp only [CollatzResearch.WordTrace]
  refine ⟨88844243618190398907099527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59229495745460265938066351 88844243618190398907099527)
  ·
    refine ⟨133266365427285598360649291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88844243618190398907099527 133266365427285598360649291)
    ·
      refine ⟨199899548140928397540973937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133266365427285598360649291 199899548140928397540973937)
      ·
        refine ⟨149924661105696298155730453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199899548140928397540973937 149924661105696298155730453)
        ·
          refine ⟨7027718489329513976049865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 149924661105696298155730453 7027718489329513976049865)
          ·
            refine ⟨5270788866997135482037399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7027718489329513976049865 5270788866997135482037399)
            ·
              refine ⟨7906183300495703223056099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5270788866997135482037399 7906183300495703223056099)
              ·
                refine ⟨11859274950743554834584149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7906183300495703223056099 11859274950743554834584149)
                ·
                  refine ⟨138975878329026033217783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11859274950743554834584149 138975878329026033217783)
                  ·
                    rfl

theorem cell23_2435891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 8].length) (baseStart_2435891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435891 prefixEnd_2435891 := by exact prefixLift 2435891
  have htrace : WordTrace (prefixWord ++ tailWord_2435891) baseStart_2435891 baseEnd_2435891 := by
    simpa [prefixWord, tailWord_2435891, baseEnd_2435891] using wordTrace_append hprefix tailTrace_2435891
  have hstable : (prefixWord ++ tailWord_2435891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435891).length < 2 ^ (prefixWord ++ tailWord_2435891).sum := by decide
  have hdescent : baseEnd_2435891 < baseStart_2435891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435928 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 6, 3, 2]
def baseStart_2435928 : Nat := 118140960795 + 2435928 * 2 ^ 59
def prefixEnd_2435928 : Nat := 4983230072969 + 3 ^ 40 * 2435928 * 2
def baseEnd_2435928 : Nat := 1250801903745450654197377

theorem tailTrace_2435928 : CollatzResearch.WordTrace tailWord_2435928 prefixEnd_2435928 1250801903745450654197377 := by
  unfold tailWord_2435928
  simp only [CollatzResearch.WordTrace]
  refine ⟨44422796559528177113098219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59230395412704236150797625 44422796559528177113098219)
  ·
    refine ⟨66634194839292265669647329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44422796559528177113098219 66634194839292265669647329)
    ·
      refine ⟨49975646129469199252235497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66634194839292265669647329 49975646129469199252235497)
      ·
        refine ⟨37481734597101899439176623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49975646129469199252235497 37481734597101899439176623)
        ·
          refine ⟨56222601895652849158764935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37481734597101899439176623 56222601895652849158764935)
          ·
            refine ⟨84333902843479273738147403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56222601895652849158764935 84333902843479273738147403)
            ·
              refine ⟨126500854265218910607221105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84333902843479273738147403 126500854265218910607221105)
              ·
                refine ⟨94875640698914182955415829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126500854265218910607221105 94875640698914182955415829)
                ·
                  refine ⟨4447295657761602326035117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 94875640698914182955415829 4447295657761602326035117)
                  ·
                    refine ⟨1667735871660600872263169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4447295657761602326035117 1667735871660600872263169)
                    ·
                      refine ⟨1250801903745450654197377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1667735871660600872263169 1250801903745450654197377)
                      ·
                        rfl

theorem cell23_2435928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 6, 3, 2].length) (baseStart_2435928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435928 prefixEnd_2435928 := by exact prefixLift 2435928
  have htrace : WordTrace (prefixWord ++ tailWord_2435928) baseStart_2435928 baseEnd_2435928 := by
    simpa [prefixWord, tailWord_2435928, baseEnd_2435928] using wordTrace_append hprefix tailTrace_2435928
  have hstable : (prefixWord ++ tailWord_2435928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435928).length < 2 ^ (prefixWord ++ tailWord_2435928).sum := by decide
  have hdescent : baseEnd_2435928 < baseStart_2435928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435971 : List Nat := [1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 6]
def baseStart_2435971 : Nat := 118140960795 + 2435971 * 2 ^ 59
def prefixEnd_2435971 : Nat := 4983230072969 + 3 ^ 40 * 2435971 * 2
def baseEnd_2435971 : Nat := 1250823983413593985959679

theorem tailTrace_2435971 : CollatzResearch.WordTrace tailWord_2435971 prefixEnd_2435971 1250823983413593985959679 := by
  unfold tailWord_2435971
  simp only [CollatzResearch.WordTrace]
  refine ⟨88847161457900572570011767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59231440971933715046674511 88847161457900572570011767)
  ·
    refine ⟨133270742186850858855017651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88847161457900572570011767 133270742186850858855017651)
    ·
      refine ⟨199906113280276288282526477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133270742186850858855017651 199906113280276288282526477)
      ·
        refine ⟨74964792480103608105947429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199906113280276288282526477 74964792480103608105947429)
        ·
          refine ⟨14055898590019426519865143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74964792480103608105947429 14055898590019426519865143)
          ·
            refine ⟨21083847885029139779797715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14055898590019426519865143 21083847885029139779797715)
            ·
              refine ⟨31625771827543709669696573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21083847885029139779797715 31625771827543709669696573)
              ·
                refine ⟨11859664435328891126136215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31625771827543709669696573 11859664435328891126136215)
                ·
                  refine ⟨17789496652993336689204323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11859664435328891126136215 17789496652993336689204323)
                  ·
                    refine ⟨26684244979490005033806485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17789496652993336689204323 26684244979490005033806485)
                    ·
                      refine ⟨1250823983413593985959679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26684244979490005033806485 1250823983413593985959679)
                      ·
                        rfl

theorem cell23_2435971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_2435971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435971 prefixEnd_2435971 := by exact prefixLift 2435971
  have htrace : WordTrace (prefixWord ++ tailWord_2435971) baseStart_2435971 baseEnd_2435971 := by
    simpa [prefixWord, tailWord_2435971, baseEnd_2435971] using wordTrace_append hprefix tailTrace_2435971
  have hstable : (prefixWord ++ tailWord_2435971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435971).length < 2 ^ (prefixWord ++ tailWord_2435971).sum := by decide
  have hdescent : baseEnd_2435971 < baseStart_2435971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435975 : List Nat := [1, 1, 4, 2, 3, 1, 3, 2, 1, 1, 4]
def baseStart_2435975 : Nat := 118140960795 + 2435975 * 2 ^ 59
def prefixEnd_2435975 : Nat := 4983230072969 + 3 ^ 40 * 2435975 * 2
def baseEnd_2435975 : Nat := 1250826037336211970309661

theorem tailTrace_2435975 : CollatzResearch.WordTrace tailWord_2435975 prefixEnd_2435975 1250826037336211970309661 := by
  unfold tailWord_2435975
  simp only [CollatzResearch.WordTrace]
  refine ⟨88847307349886081253157379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59231538233257387502104919 88847307349886081253157379)
  ·
    refine ⟨133270961024829121879736069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88847307349886081253157379 133270961024829121879736069)
    ·
      refine ⟨24988305192155460352450513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133270961024829121879736069 24988305192155460352450513)
      ·
        refine ⟨18741228894116595264337885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24988305192155460352450513 18741228894116595264337885)
        ·
          refine ⟨7027960835293723224126707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18741228894116595264337885 7027960835293723224126707)
          ·
            refine ⟨10541941252940584836190061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7027960835293723224126707 10541941252940584836190061)
            ·
              refine ⟨3953227969852719313571273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10541941252940584836190061 3953227969852719313571273)
              ·
                refine ⟨2964920977389539485178455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3953227969852719313571273 2964920977389539485178455)
                ·
                  refine ⟨4447381466084309227767683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2964920977389539485178455 4447381466084309227767683)
                  ·
                    refine ⟨6671072199126463841651525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4447381466084309227767683 6671072199126463841651525)
                    ·
                      refine ⟨1250826037336211970309661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6671072199126463841651525 1250826037336211970309661)
                      ·
                        rfl

theorem cell23_2435975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_2435975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2435975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2435975 prefixEnd_2435975 := by exact prefixLift 2435975
  have htrace : WordTrace (prefixWord ++ tailWord_2435975) baseStart_2435975 baseEnd_2435975 := by
    simpa [prefixWord, tailWord_2435975, baseEnd_2435975] using wordTrace_append hprefix tailTrace_2435975
  have hstable : (prefixWord ++ tailWord_2435975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435975).length < 2 ^ (prefixWord ++ tailWord_2435975).sum := by decide
  have hdescent : baseEnd_2435975 < baseStart_2435975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436002 : List Nat := [3, 3, 1, 2, 2, 2, 2, 2, 2, 4]
def baseStart_2436002 : Nat := 118140960795 + 2436002 * 2 ^ 59
def prefixEnd_2436002 : Nat := 4983230072969 + 3 ^ 40 * 2436002 * 2
def baseEnd_2436002 : Nat := 416946633771294454890679

theorem tailTrace_2436002 : CollatzResearch.WordTrace tailWord_2436002 prefixEnd_2436002 416946633771294454890679 := by
  unfold tailWord_2436002
  simp only [CollatzResearch.WordTrace]
  refine ⟨22212073030197066216097565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59232194747192176576260173 22212073030197066216097565)
  ·
    refine ⟨8329527386323899831036587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22212073030197066216097565 8329527386323899831036587)
    ·
      refine ⟨12494291079485849746554881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8329527386323899831036587 12494291079485849746554881)
      ·
        refine ⟨9370718309614387309916161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12494291079485849746554881 9370718309614387309916161)
        ·
          refine ⟨7028038732210790482437121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9370718309614387309916161 7028038732210790482437121)
          ·
            refine ⟨5271029049158092861827841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7028038732210790482437121 5271029049158092861827841)
            ·
              refine ⟨3953271786868569646370881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5271029049158092861827841 3953271786868569646370881)
              ·
                refine ⟨2964953840151427234778161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3953271786868569646370881 2964953840151427234778161)
                ·
                  refine ⟨2223715380113570426083621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2964953840151427234778161 2223715380113570426083621)
                  ·
                    refine ⟨416946633771294454890679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2223715380113570426083621 416946633771294454890679)
                    ·
                      rfl

theorem cell23_2436002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_2436002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436002 prefixEnd_2436002 := by exact prefixLift 2436002
  have htrace : WordTrace (prefixWord ++ tailWord_2436002) baseStart_2436002 baseEnd_2436002 := by
    simpa [prefixWord, tailWord_2436002, baseEnd_2436002] using wordTrace_append hprefix tailTrace_2436002
  have hstable : (prefixWord ++ tailWord_2436002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436002).length < 2 ^ (prefixWord ++ tailWord_2436002).sum := by decide
  have hdescent : baseEnd_2436002 < baseStart_2436002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436025 : List Nat := [1, 2, 1, 4, 2, 3, 2, 1, 1, 3, 3]
def baseStart_2436025 : Nat := 118140960795 + 2436025 * 2 ^ 59
def prefixEnd_2436025 : Nat := 4983230072969 + 3 ^ 40 * 2436025 * 2
def baseEnd_2436025 : Nat := 1250851711368936774684431

theorem tailTrace_2436025 : CollatzResearch.WordTrace tailWord_2436025 prefixEnd_2436025 1250851711368936774684431 := by
  unfold tailWord_2436025
  simp only [CollatzResearch.WordTrace]
  refine ⟨88849130999704939792477529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59232753999803293194985019 88849130999704939792477529)
  ·
    refine ⟨66636848249778704844358147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88849130999704939792477529 66636848249778704844358147)
    ·
      refine ⟨99955272374668057266537221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66636848249778704844358147 99955272374668057266537221)
      ·
        refine ⟨18741613570250260737475729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99955272374668057266537221 18741613570250260737475729)
        ·
          refine ⟨14056210177687695553106797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18741613570250260737475729 14056210177687695553106797)
          ·
            refine ⟨5271078816632885832415049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14056210177687695553106797 5271078816632885832415049)
            ·
              refine ⟨3953309112474664374311287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5271078816632885832415049 3953309112474664374311287)
              ·
                refine ⟨5929963668711996561466931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3953309112474664374311287 5929963668711996561466931)
                ·
                  refine ⟨8894945503067994842200397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5929963668711996561466931 8894945503067994842200397)
                  ·
                    refine ⟨3335604563650498065825149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8894945503067994842200397 3335604563650498065825149)
                    ·
                      refine ⟨1250851711368936774684431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3335604563650498065825149 1250851711368936774684431)
                      ·
                        rfl

theorem cell23_2436025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_2436025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2436025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2436025 prefixEnd_2436025 := by exact prefixLift 2436025
  have htrace : WordTrace (prefixWord ++ tailWord_2436025) baseStart_2436025 baseEnd_2436025 := by
    simpa [prefixWord, tailWord_2436025, baseEnd_2436025] using wordTrace_append hprefix tailTrace_2436025
  have hstable : (prefixWord ++ tailWord_2436025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436025).length < 2 ^ (prefixWord ++ tailWord_2436025).sum := by decide
  have hdescent : baseEnd_2436025 < baseStart_2436025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
