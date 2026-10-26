import V185TrunkScan23Chunk0584

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3459433 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 4, 3, 3]
def baseStart_3459433 : Nat := 118140960795 + 3459433 * 2 ^ 59
def prefixEnd_3459433 : Nat := 4983230072969 + 3 ^ 40 * 3459433 * 2
def baseEnd_3459433 : Nat := 1776351921025468686177863

theorem tailTrace_3459433 : CollatzResearch.WordTrace tailWord_3459433 prefixEnd_3459433 1776351921025468686177863 := by
  unfold tailWord_3459433
  simp only [CollatzResearch.WordTrace]
  refine ⟨126175887276072539963598953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84117258184048359975732635 126175887276072539963598953)
  ·
    refine ⟨94631915457054404972699215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126175887276072539963598953 94631915457054404972699215)
    ·
      refine ⟨141947873185581607459048823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94631915457054404972699215 141947873185581607459048823)
      ·
        refine ⟨212921809778372411188573235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141947873185581607459048823 212921809778372411188573235)
        ·
          refine ⟨319382714667558616782859853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212921809778372411188573235 319382714667558616782859853)
          ·
            refine ⟨119768518000334481293572445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 319382714667558616782859853 119768518000334481293572445)
            ·
              refine ⟨44913194250125430485089667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119768518000334481293572445 44913194250125430485089667)
              ·
                refine ⟨67369791375188145727634501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44913194250125430485089667 67369791375188145727634501)
                ·
                  refine ⟨12631835882847777323931469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67369791375188145727634501 12631835882847777323931469)
                  ·
                    refine ⟨4736938456067916496474301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12631835882847777323931469 4736938456067916496474301)
                    ·
                      refine ⟨1776351921025468686177863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4736938456067916496474301 1776351921025468686177863)
                      ·
                        rfl

theorem cell23_3459433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 3, 3].length) (baseStart_3459433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459433 prefixEnd_3459433 := by exact prefixLift 3459433
  have htrace : WordTrace (prefixWord ++ tailWord_3459433) baseStart_3459433 baseEnd_3459433 := by
    simpa [prefixWord, tailWord_3459433, baseEnd_3459433] using wordTrace_append hprefix tailTrace_3459433
  have hstable : (prefixWord ++ tailWord_3459433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459433).length < 2 ^ (prefixWord ++ tailWord_3459433).sum := by decide
  have hdescent : baseEnd_3459433 < baseStart_3459433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459434 : List Nat := [3, 1, 3, 3, 1, 2, 1, 1, 4, 2, 2]
def baseStart_3459434 : Nat := 118140960795 + 3459434 * 2 ^ 59
def prefixEnd_3459434 : Nat := 4983230072969 + 3 ^ 40 * 3459434 * 2
def baseEnd_3459434 : Nat := 1776352434506123182265359

theorem tailTrace_3459434 : CollatzResearch.WordTrace tailWord_3459434 prefixEnd_3459434 1776352434506123182265359 := by
  unfold tailWord_3459434
  simp only [CollatzResearch.WordTrace]
  refine ⟨31543980937267229283596339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84117282499379278089590237 31543980937267229283596339)
  ·
    refine ⟨47315971405900843925394509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31543980937267229283596339 47315971405900843925394509)
    ·
      refine ⟨17743489277212816472022941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47315971405900843925394509 17743489277212816472022941)
      ·
        refine ⟨6653808478954806177008603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17743489277212816472022941 6653808478954806177008603)
        ·
          refine ⟨9980712718432209265512905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6653808478954806177008603 9980712718432209265512905)
          ·
            refine ⟨7485534538824156949134679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9980712718432209265512905 7485534538824156949134679)
            ·
              refine ⟨11228301808236235423702019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7485534538824156949134679 11228301808236235423702019)
              ·
                refine ⟨16842452712354353135553029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11228301808236235423702019 16842452712354353135553029)
                ·
                  refine ⟨3157959883566441212916193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16842452712354353135553029 3157959883566441212916193)
                  ·
                    refine ⟨2368469912674830909687145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3157959883566441212916193 2368469912674830909687145)
                    ·
                      refine ⟨1776352434506123182265359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2368469912674830909687145 1776352434506123182265359)
                      ·
                        rfl

theorem cell23_3459434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_3459434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459434 prefixEnd_3459434 := by exact prefixLift 3459434
  have htrace : WordTrace (prefixWord ++ tailWord_3459434) baseStart_3459434 baseEnd_3459434 := by
    simpa [prefixWord, tailWord_3459434, baseEnd_3459434] using wordTrace_append hprefix tailTrace_3459434
  have hstable : (prefixWord ++ tailWord_3459434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459434).length < 2 ^ (prefixWord ++ tailWord_3459434).sum := by decide
  have hdescent : baseEnd_3459434 < baseStart_3459434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459440 : List Nat := [2, 1, 1, 1, 4, 3, 2, 4, 5]
def baseStart_3459440 : Nat := 118140960795 + 3459440 * 2 ^ 59
def prefixEnd_3459440 : Nat := 4983230072969 + 3 ^ 40 * 3459440 * 2
def baseEnd_3459440 : Nat := 197372835043338906532259

theorem tailTrace_3459440 : CollatzResearch.WordTrace tailWord_3459440 prefixEnd_3459440 197372835043338906532259 := by
  unfold tailWord_3459440
  simp only [CollatzResearch.WordTrace]
  refine ⟨63088071293523590079551887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84117428391364786772735849 63088071293523590079551887)
  ·
    refine ⟨94632106940285385119327831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63088071293523590079551887 94632106940285385119327831)
    ·
      refine ⟨141948160410428077678991747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94632106940285385119327831 141948160410428077678991747)
      ·
        refine ⟨212922240615642116518487621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141948160410428077678991747 212922240615642116518487621)
        ·
          refine ⟨39922920115432896847216429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212922240615642116518487621 39922920115432896847216429)
          ·
            refine ⟨14971095043287336317706161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39922920115432896847216429 14971095043287336317706161)
            ·
              refine ⟨11228321282465502238279621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14971095043287336317706161 11228321282465502238279621)
              ·
                refine ⟨2105310240462281669677429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11228321282465502238279621 2105310240462281669677429)
                ·
                  refine ⟨197372835043338906532259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2105310240462281669677429 197372835043338906532259)
                  ·
                    rfl

theorem cell23_3459440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4, 5].length) (baseStart_3459440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459440 prefixEnd_3459440 := by exact prefixLift 3459440
  have htrace : WordTrace (prefixWord ++ tailWord_3459440) baseStart_3459440 baseEnd_3459440 := by
    simpa [prefixWord, tailWord_3459440, baseEnd_3459440] using wordTrace_append hprefix tailTrace_3459440
  have hstable : (prefixWord ++ tailWord_3459440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459440).length < 2 ^ (prefixWord ++ tailWord_3459440).sum := by decide
  have hdescent : baseEnd_3459440 < baseStart_3459440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459453 : List Nat := [1, 4, 1, 1, 2, 3, 1, 2, 1, 7]
def baseStart_3459453 : Nat := 118140960795 + 3459453 * 2 ^ 59
def prefixEnd_3459453 : Nat := 4983230072969 + 3 ^ 40 * 3459453 * 2
def baseEnd_3459453 : Nat := 592120730212852869309257

theorem tailTrace_3459453 : CollatzResearch.WordTrace tailWord_3459453 prefixEnd_3459453 592120730212852869309257 := by
  unfold tailWord_3459453
  simp only [CollatzResearch.WordTrace]
  refine ⟨126176616736000083379327013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84117744490666722252884675 126176616736000083379327013)
  ·
    refine ⟨23658115638000015633623815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126176616736000083379327013 23658115638000015633623815)
    ·
      refine ⟨35487173457000023450435723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23658115638000015633623815 35487173457000023450435723)
      ·
        refine ⟨53230760185500035175653585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35487173457000023450435723 53230760185500035175653585)
        ·
          refine ⟨39923070139125026381740189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53230760185500035175653585 39923070139125026381740189)
          ·
            refine ⟨14971151302171884893152571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39923070139125026381740189 14971151302171884893152571)
            ·
              refine ⟨22456726953257827339728857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14971151302171884893152571 22456726953257827339728857)
              ·
                refine ⟨16842545214943370504796643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22456726953257827339728857 16842545214943370504796643)
                ·
                  refine ⟨25263817822415055757194965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16842545214943370504796643 25263817822415055757194965)
                  ·
                    refine ⟨592120730212852869309257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25263817822415055757194965 592120730212852869309257)
                    ·
                      rfl

theorem cell23_3459453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_3459453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459453 prefixEnd_3459453 := by exact prefixLift 3459453
  have htrace : WordTrace (prefixWord ++ tailWord_3459453) baseStart_3459453 baseEnd_3459453 := by
    simpa [prefixWord, tailWord_3459453, baseEnd_3459453] using wordTrace_append hprefix tailTrace_3459453
  have hstable : (prefixWord ++ tailWord_3459453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459453).length < 2 ^ (prefixWord ++ tailWord_3459453).sum := by decide
  have hdescent : baseEnd_3459453 < baseStart_3459453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459470 : List Nat := [4, 1, 1, 4, 1, 1, 2, 1, 1, 7]
def baseStart_3459470 : Nat := 118140960795 + 3459470 * 2 ^ 59
def prefixEnd_3459470 : Nat := 4983230072969 + 3 ^ 40 * 3459470 * 2
def baseEnd_3459470 : Nat := 592123639936561680471731

theorem tailTrace_3459470 : CollatzResearch.WordTrace tailWord_3459470 prefixEnd_3459470 592123639936561680471731 := by
  unfold tailWord_3459470
  simp only [CollatzResearch.WordTrace]
  refine ⟨15772154597117311910336983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84118157851292330188463909 15772154597117311910336983)
  ·
    refine ⟨23658231895675967865505475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15772154597117311910336983 23658231895675967865505475)
    ·
      refine ⟨35487347843513951798258213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23658231895675967865505475 35487347843513951798258213)
      ·
        refine ⟨6653877720658865962173415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35487347843513951798258213 6653877720658865962173415)
        ·
          refine ⟨9980816580988298943260123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6653877720658865962173415 9980816580988298943260123)
          ·
            refine ⟨14971224871482448414890185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9980816580988298943260123 14971224871482448414890185)
            ·
              refine ⟨11228418653611836311167639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14971224871482448414890185 11228418653611836311167639)
              ·
                refine ⟨16842627980417754466751459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11228418653611836311167639 16842627980417754466751459)
                ·
                  refine ⟨25263941970626631700127189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16842627980417754466751459 25263941970626631700127189)
                  ·
                    refine ⟨592123639936561680471731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25263941970626631700127189 592123639936561680471731)
                    ·
                      rfl

theorem cell23_3459470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_3459470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459470 prefixEnd_3459470 := by exact prefixLift 3459470
  have htrace : WordTrace (prefixWord ++ tailWord_3459470) baseStart_3459470 baseEnd_3459470 := by
    simpa [prefixWord, tailWord_3459470, baseEnd_3459470] using wordTrace_append hprefix tailTrace_3459470
  have hstable : (prefixWord ++ tailWord_3459470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459470).length < 2 ^ (prefixWord ++ tailWord_3459470).sum := by decide
  have hdescent : baseEnd_3459470 < baseStart_3459470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459521 : List Nat := [1, 2, 7, 1, 1, 1, 2, 1, 2, 5]
def baseStart_3459521 : Nat := 118140960795 + 3459521 * 2 ^ 59
def prefixEnd_3459521 : Nat := 4983230072969 + 3 ^ 40 * 3459521 * 2
def baseEnd_3459521 : Nat := 592132369107688113959153

theorem tailTrace_3459521 : CollatzResearch.WordTrace tailWord_3459521 prefixEnd_3459521 592132369107688113959153 := by
  unfold tailWord_3459521
  simp only [CollatzResearch.WordTrace]
  refine ⟨126179096899753730992802417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84119397933169153995201611 126179096899753730992802417)
  ·
    refine ⟨94634322674815298244601813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126179096899753730992802417 94634322674815298244601813)
    ·
      refine ⟨2217991937690983552607855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 94634322674815298244601813 2217991937690983552607855)
      ·
        refine ⟨3326987906536475328911783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2217991937690983552607855 3326987906536475328911783)
        ·
          refine ⟨4990481859804712993367675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3326987906536475328911783 4990481859804712993367675)
          ·
            refine ⟨7485722789707069490051513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4990481859804712993367675 7485722789707069490051513)
            ·
              refine ⟨5614292092280302117538635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7485722789707069490051513 5614292092280302117538635)
              ·
                refine ⟨8421438138420453176307953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5614292092280302117538635 8421438138420453176307953)
                ·
                  refine ⟨6316078603815339882230965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8421438138420453176307953 6316078603815339882230965)
                  ·
                    refine ⟨592132369107688113959153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6316078603815339882230965 592132369107688113959153)
                    ·
                      rfl

theorem cell23_3459521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_3459521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459521 prefixEnd_3459521 := by exact prefixLift 3459521
  have htrace : WordTrace (prefixWord ++ tailWord_3459521) baseStart_3459521 baseEnd_3459521 := by
    simpa [prefixWord, tailWord_3459521, baseEnd_3459521] using wordTrace_append hprefix tailTrace_3459521
  have hstable : (prefixWord ++ tailWord_3459521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459521).length < 2 ^ (prefixWord ++ tailWord_3459521).sum := by decide
  have hdescent : baseEnd_3459521 < baseStart_3459521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459524 : List Nat := [2, 3, 3, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_3459524 : Nat := 118140960795 + 3459524 * 2 ^ 59
def prefixEnd_3459524 : Nat := 4983230072969 + 3 ^ 40 * 3459524 * 2
def baseEnd_3459524 : Nat := 1776398647765027830139945

theorem tailTrace_3459524 : CollatzResearch.WordTrace tailWord_3459524 prefixEnd_3459524 1776398647765027830139945 := by
  unfold tailWord_3459524
  simp only [CollatzResearch.WordTrace]
  refine ⟨63089603159371431252580813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84119470879161908336774417 63089603159371431252580813)
  ·
    refine ⟨23658601184764286719717805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63089603159371431252580813 23658601184764286719717805)
    ·
      refine ⟨8871975444286607519894177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23658601184764286719717805 8871975444286607519894177)
      ·
        refine ⟨6653981583214955639920633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8871975444286607519894177 6653981583214955639920633)
        ·
          refine ⟨4990486187411216729940475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6653981583214955639920633 4990486187411216729940475)
          ·
            refine ⟨7485729281116825094910713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4990486187411216729940475 7485729281116825094910713)
            ·
              refine ⟨5614296960837618821183035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7485729281116825094910713 5614296960837618821183035)
              ·
                refine ⟨8421445441256428231774553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5614296960837618821183035 8421445441256428231774553)
                ·
                  refine ⟨6316084080942321173830915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8421445441256428231774553 6316084080942321173830915)
                  ·
                    refine ⟨9474126121413481760746373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6316084080942321173830915 9474126121413481760746373)
                    ·
                      refine ⟨1776398647765027830139945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9474126121413481760746373 1776398647765027830139945)
                      ·
                        rfl

theorem cell23_3459524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_3459524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459524 prefixEnd_3459524 := by exact prefixLift 3459524
  have htrace : WordTrace (prefixWord ++ tailWord_3459524) baseStart_3459524 baseEnd_3459524 := by
    simpa [prefixWord, tailWord_3459524, baseEnd_3459524] using wordTrace_append hprefix tailTrace_3459524
  have hstable : (prefixWord ++ tailWord_3459524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459524).length < 2 ^ (prefixWord ++ tailWord_3459524).sum := by decide
  have hdescent : baseEnd_3459524 < baseStart_3459524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459527 : List Nat := [1, 1, 4, 1, 1, 5, 2, 1, 2, 2, 3]
def baseStart_3459527 : Nat := 118140960795 + 3459527 * 2 ^ 59
def prefixEnd_3459527 : Nat := 4983230072969 + 3 ^ 40 * 3459527 * 2
def baseEnd_3459527 : Nat := 1776400188206991318402431

theorem tailTrace_3459527 : CollatzResearch.WordTrace tailWord_3459527 prefixEnd_3459527 1776400188206991318402431 := by
  unfold tailWord_3459527
  simp only [CollatzResearch.WordTrace]
  refine ⟨126179315737731994017520835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84119543825154662678347223 126179315737731994017520835)
  ·
    refine ⟨189268973606597991026281253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126179315737731994017520835 189268973606597991026281253)
    ·
      refine ⟨35487932551237123317427735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189268973606597991026281253 35487932551237123317427735)
      ·
        refine ⟨53231898826855684976141603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35487932551237123317427735 53231898826855684976141603)
        ·
          refine ⟨79847848240283527464212405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53231898826855684976141603 79847848240283527464212405)
          ·
            refine ⟨7485735772526580699769913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79847848240283527464212405 7485735772526580699769913)
            ·
              refine ⟨5614301829394935524827435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7485735772526580699769913 5614301829394935524827435)
              ·
                refine ⟨8421452744092403287241153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5614301829394935524827435 8421452744092403287241153)
                ·
                  refine ⟨6316089558069302465430865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8421452744092403287241153 6316089558069302465430865)
                  ·
                    refine ⟨4737067168551976849073149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6316089558069302465430865 4737067168551976849073149)
                    ·
                      refine ⟨1776400188206991318402431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4737067168551976849073149 1776400188206991318402431)
                      ·
                        rfl

theorem cell23_3459527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_3459527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459527 prefixEnd_3459527 := by exact prefixLift 3459527
  have htrace : WordTrace (prefixWord ++ tailWord_3459527) baseStart_3459527 baseEnd_3459527 := by
    simpa [prefixWord, tailWord_3459527, baseEnd_3459527] using wordTrace_append hprefix tailTrace_3459527
  have hstable : (prefixWord ++ tailWord_3459527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459527).length < 2 ^ (prefixWord ++ tailWord_3459527).sum := by decide
  have hdescent : baseEnd_3459527 < baseStart_3459527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459551 : List Nat := [1, 1, 2, 3, 3, 4, 2, 2, 1, 4]
def baseStart_3459551 : Nat := 118140960795 + 3459551 * 2 ^ 59
def prefixEnd_3459551 : Nat := 4983230072969 + 3 ^ 40 * 3459551 * 2
def baseEnd_3459551 : Nat := 592137503914233074834107

theorem tailTrace_3459551 : CollatzResearch.WordTrace tailWord_3459551 prefixEnd_3459551 592137503914233074834107 := by
  unfold tailWord_3459551
  simp only [CollatzResearch.WordTrace]
  refine ⟨126180191089645046116394507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84120127393096697410929671 126180191089645046116394507)
  ·
    refine ⟨189270286634467569174591761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126180191089645046116394507 189270286634467569174591761)
    ·
      refine ⟨141952714975850676880943821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189270286634467569174591761 141952714975850676880943821)
      ·
        refine ⟨53232268115944003830353933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141952714975850676880943821 53232268115944003830353933)
        ·
          refine ⟨19962100543479001436382725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53232268115944003830353933 19962100543479001436382725)
          ·
            refine ⟨3742893851902312769321761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19962100543479001436382725 3742893851902312769321761)
            ·
              refine ⟨2807170388926734576991321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3742893851902312769321761 2807170388926734576991321)
              ·
                refine ⟨2105377791695050932743491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2807170388926734576991321 2105377791695050932743491)
                ·
                  refine ⟨3158066687542576399115237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2105377791695050932743491 3158066687542576399115237)
                  ·
                    refine ⟨592137503914233074834107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3158066687542576399115237 592137503914233074834107)
                    ·
                      rfl

theorem cell23_3459551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2, 1, 4].length) (baseStart_3459551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459551 prefixEnd_3459551 := by exact prefixLift 3459551
  have htrace : WordTrace (prefixWord ++ tailWord_3459551) baseStart_3459551 baseEnd_3459551 := by
    simpa [prefixWord, tailWord_3459551, baseEnd_3459551] using wordTrace_append hprefix tailTrace_3459551
  have hstable : (prefixWord ++ tailWord_3459551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459551).length < 2 ^ (prefixWord ++ tailWord_3459551).sum := by decide
  have hdescent : baseEnd_3459551 < baseStart_3459551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459560 : List Nat := [2, 1, 4, 1, 1, 3, 1, 2, 3, 5]
def baseStart_3459560 : Nat := 118140960795 + 3459560 * 2 ^ 59
def prefixEnd_3459560 : Nat := 4983230072969 + 3 ^ 40 * 3459560 * 2
def baseEnd_3459560 : Nat := 592139044356196563096593

theorem tailTrace_3459560 : CollatzResearch.WordTrace tailWord_3459560 prefixEnd_3459560 592139044356196563096593 := by
  unfold tailWord_3459560
  simp only [CollatzResearch.WordTrace]
  refine ⟨63090259673306220326736067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84120346231074960435648089 63090259673306220326736067)
  ·
    refine ⟨94635389509959330490104101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63090259673306220326736067 94635389509959330490104101)
    ·
      refine ⟨17744135533117374466894519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94635389509959330490104101 17744135533117374466894519)
      ·
        refine ⟨26616203299676061700341779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17744135533117374466894519 26616203299676061700341779)
        ·
          refine ⟨39924304949514092550512669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26616203299676061700341779 39924304949514092550512669)
          ·
            refine ⟨14971614356067784706442251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39924304949514092550512669 14971614356067784706442251)
            ·
              refine ⟨22457421534101677059663377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14971614356067784706442251 22457421534101677059663377)
              ·
                refine ⟨16843066150576257794747533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22457421534101677059663377 16843066150576257794747533)
                ·
                  refine ⟨6316149806466096673030325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16843066150576257794747533 6316149806466096673030325)
                  ·
                    refine ⟨592139044356196563096593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6316149806466096673030325 592139044356196563096593)
                    ·
                      rfl

theorem cell23_3459560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_3459560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459560 prefixEnd_3459560 := by exact prefixLift 3459560
  have htrace : WordTrace (prefixWord ++ tailWord_3459560) baseStart_3459560 baseEnd_3459560 := by
    simpa [prefixWord, tailWord_3459560, baseEnd_3459560] using wordTrace_append hprefix tailTrace_3459560
  have hstable : (prefixWord ++ tailWord_3459560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459560).length < 2 ^ (prefixWord ++ tailWord_3459560).sum := by decide
  have hdescent : baseEnd_3459560 < baseStart_3459560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459574 : List Nat := [5, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3]
def baseStart_3459574 : Nat := 118140960795 + 3459574 * 2 ^ 59
def prefixEnd_3459574 : Nat := 4983230072969 + 3 ^ 40 * 3459574 * 2
def baseEnd_3459574 : Nat := 1776424321797752634514715

theorem tailTrace_3459574 : CollatzResearch.WordTrace tailWord_3459574 prefixEnd_3459574 1776424321797752634514715 := by
  unfold tailWord_3459574
  simp only [CollatzResearch.WordTrace]
  refine ⟨7886314373035107565280111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84120686645707814029654517 7886314373035107565280111)
  ·
    refine ⟨11829471559552661347920167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7886314373035107565280111 11829471559552661347920167)
    ·
      refine ⟨17744207339328992021880251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11829471559552661347920167 17744207339328992021880251)
      ·
        refine ⟨26616311008993488032820377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17744207339328992021880251 26616311008993488032820377)
        ·
          refine ⟨19962233256745116024615283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26616311008993488032820377 19962233256745116024615283)
          ·
            refine ⟨29943349885117674036922925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19962233256745116024615283 29943349885117674036922925)
            ·
              refine ⟨11228756206919127763846097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29943349885117674036922925 11228756206919127763846097)
              ·
                refine ⟨8421567155189345822884573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11228756206919127763846097 8421567155189345822884573)
                ·
                  refine ⟨3158087683196004683581715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8421567155189345822884573 3158087683196004683581715)
                  ·
                    refine ⟨4737131524794007025372573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3158087683196004683581715 4737131524794007025372573)
                    ·
                      refine ⟨1776424321797752634514715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4737131524794007025372573 1776424321797752634514715)
                      ·
                        rfl

theorem cell23_3459574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_3459574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459574 prefixEnd_3459574 := by exact prefixLift 3459574
  have htrace : WordTrace (prefixWord ++ tailWord_3459574) baseStart_3459574 baseEnd_3459574 := by
    simpa [prefixWord, tailWord_3459574, baseEnd_3459574] using wordTrace_append hprefix tailTrace_3459574
  have hstable : (prefixWord ++ tailWord_3459574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459574).length < 2 ^ (prefixWord ++ tailWord_3459574).sum := by decide
  have hdescent : baseEnd_3459574 < baseStart_3459574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459603 : List Nat := [1, 1, 1, 2, 1, 5, 12]
def baseStart_3459603 : Nat := 118140960795 + 3459603 * 2 ^ 59
def prefixEnd_3459603 : Nat := 4983230072969 + 3 ^ 40 * 3459603 * 2
def baseEnd_3459603 : Nat := 21931348305391765692001

theorem tailTrace_3459603 : CollatzResearch.WordTrace tailWord_3459603 prefixEnd_3459603 21931348305391765692001 := by
  unfold tailWord_3459603
  simp only [CollatzResearch.WordTrace]
  refine ⟨126182087685456658997287463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84121391790304439331524975 126182087685456658997287463)
  ·
    refine ⟨189273131528184988495931195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126182087685456658997287463 189273131528184988495931195)
    ·
      refine ⟨283909697292277482743896793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189273131528184988495931195 283909697292277482743896793)
      ·
        refine ⟨212932272969208112057922595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283909697292277482743896793 212932272969208112057922595)
        ·
          refine ⟨319398409453812168086883893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212932272969208112057922595 319398409453812168086883893)
          ·
            refine ⟨29943600886294890758145365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 319398409453812168086883893 29943600886294890758145365)
            ·
              refine ⟨21931348305391765692001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 29943600886294890758145365 21931348305391765692001)
              ·
                rfl

theorem cell23_3459603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 12].length) (baseStart_3459603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459603 prefixEnd_3459603 := by exact prefixLift 3459603
  have htrace : WordTrace (prefixWord ++ tailWord_3459603) baseStart_3459603 baseEnd_3459603 := by
    simpa [prefixWord, tailWord_3459603, baseEnd_3459603] using wordTrace_append hprefix tailTrace_3459603
  have hstable : (prefixWord ++ tailWord_3459603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459603).length < 2 ^ (prefixWord ++ tailWord_3459603).sum := by decide
  have hdescent : baseEnd_3459603 < baseStart_3459603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459610 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4]
def baseStart_3459610 : Nat := 118140960795 + 3459610 * 2 ^ 59
def prefixEnd_3459610 : Nat := 4983230072969 + 3 ^ 40 * 3459610 * 2
def baseEnd_3459610 : Nat := 1776442807101314493664549

theorem tailTrace_3459610 : CollatzResearch.WordTrace tailWord_3459610 prefixEnd_3459610 1776442807101314493664549 := by
  unfold tailWord_3459610
  simp only [CollatzResearch.WordTrace]
  refine ⟨31545585749107824798198071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84121561997620866128528189 31545585749107824798198071)
  ·
    refine ⟨47318378623661737197297107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31545585749107824798198071 47318378623661737197297107)
    ·
      refine ⟨70977567935492605795945661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47318378623661737197297107 70977567935492605795945661)
      ·
        refine ⟨26616587975809727173479623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70977567935492605795945661 26616587975809727173479623)
        ·
          refine ⟨39924881963714590760219435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26616587975809727173479623 39924881963714590760219435)
          ·
            refine ⟨59887322945571886140329153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39924881963714590760219435 59887322945571886140329153)
            ·
              refine ⟨44915492209178914605246865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59887322945571886140329153 44915492209178914605246865)
              ·
                refine ⟨33686619156884185953935149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44915492209178914605246865 33686619156884185953935149)
                ·
                  refine ⟨12632482183831569732725681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33686619156884185953935149 12632482183831569732725681)
                  ·
                    refine ⟨9474361637873677299544261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12632482183831569732725681 9474361637873677299544261)
                    ·
                      refine ⟨1776442807101314493664549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9474361637873677299544261 1776442807101314493664549)
                      ·
                        rfl

theorem cell23_3459610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_3459610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459610 prefixEnd_3459610 := by exact prefixLift 3459610
  have htrace : WordTrace (prefixWord ++ tailWord_3459610) baseStart_3459610 baseEnd_3459610 := by
    simpa [prefixWord, tailWord_3459610, baseEnd_3459610] using wordTrace_append hprefix tailTrace_3459610
  have hstable : (prefixWord ++ tailWord_3459610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459610).length < 2 ^ (prefixWord ++ tailWord_3459610).sum := by decide
  have hdescent : baseEnd_3459610 < baseStart_3459610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459624 : List Nat := [2, 1, 5, 2, 1, 3, 1, 1, 1, 6]
def baseStart_3459624 : Nat := 118140960795 + 3459624 * 2 ^ 59
def prefixEnd_3459624 : Nat := 4983230072969 + 3 ^ 40 * 3459624 * 2
def baseEnd_3459624 : Nat := 592149998610159146296495

theorem tailTrace_3459624 : CollatzResearch.WordTrace tailWord_3459624 prefixEnd_3459624 592149998610159146296495 := by
  unfold tailWord_3459624
  simp only [CollatzResearch.WordTrace]
  refine ⟨63091426809190289791900963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84121902412253719722534617 63091426809190289791900963)
  ·
    refine ⟨94637140213785434687851445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63091426809190289791900963 94637140213785434687851445)
    ·
      refine ⟨8872231895042384501986073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94637140213785434687851445 8872231895042384501986073)
      ·
        refine ⟨6654173921281788376489555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8872231895042384501986073 6654173921281788376489555)
        ·
          refine ⟨9981260881922682564734333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6654173921281788376489555 9981260881922682564734333)
          ·
            refine ⟨3742972830721005961775375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9981260881922682564734333 3742972830721005961775375)
            ·
              refine ⟨5614459246081508942663063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3742972830721005961775375 5614459246081508942663063)
              ·
                refine ⟨8421688869122263413994595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5614459246081508942663063 8421688869122263413994595)
                ·
                  refine ⟨12632533303683395120991893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8421688869122263413994595 12632533303683395120991893)
                  ·
                    refine ⟨592149998610159146296495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12632533303683395120991893 592149998610159146296495)
                    ·
                      rfl

theorem cell23_3459624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_3459624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459624 prefixEnd_3459624 := by exact prefixLift 3459624
  have htrace : WordTrace (prefixWord ++ tailWord_3459624) baseStart_3459624 baseEnd_3459624 := by
    simpa [prefixWord, tailWord_3459624, baseEnd_3459624] using wordTrace_append hprefix tailTrace_3459624
  have hstable : (prefixWord ++ tailWord_3459624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459624).length < 2 ^ (prefixWord ++ tailWord_3459624).sum := by decide
  have hdescent : baseEnd_3459624 < baseStart_3459624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459647 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 6, 1, 3]
def baseStart_3459647 : Nat := 118140960795 + 3459647 * 2 ^ 59
def prefixEnd_3459647 : Nat := 4983230072969 + 3 ^ 40 * 3459647 * 2
def baseEnd_3459647 : Nat := 1776461805885530848901879

theorem tailTrace_3459647 : CollatzResearch.WordTrace tailWord_3459647 prefixEnd_3459647 1776461805885530848901879 := by
  unfold tailWord_3459647
  simp only [CollatzResearch.WordTrace]
  refine ⟨126183692497297254511889195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84122461664864836341259463 126183692497297254511889195)
  ·
    refine ⟨189275538745945881767833793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126183692497297254511889195 189275538745945881767833793)
    ·
      refine ⟨141956654059459411325875345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189275538745945881767833793 141956654059459411325875345)
      ·
        refine ⟨106467490544594558494406509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141956654059459411325875345 106467490544594558494406509)
        ·
          refine ⟨39925308954222959435402441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106467490544594558494406509 39925308954222959435402441)
          ·
            refine ⟨29943981715667219576551831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39925308954222959435402441 29943981715667219576551831)
            ·
              refine ⟨44915972573500829364827747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29943981715667219576551831 44915972573500829364827747)
              ·
                refine ⟨67373958860251244047241621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44915972573500829364827747 67373958860251244047241621)
                ·
                  refine ⟨3158154321574277064714451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67373958860251244047241621 3158154321574277064714451)
                  ·
                    refine ⟨4737231482361415597071677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3158154321574277064714451 4737231482361415597071677)
                    ·
                      refine ⟨1776461805885530848901879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4737231482361415597071677 1776461805885530848901879)
                      ·
                        rfl

theorem cell23_3459647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6, 1, 3].length) (baseStart_3459647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459647 prefixEnd_3459647 := by exact prefixLift 3459647
  have htrace : WordTrace (prefixWord ++ tailWord_3459647) baseStart_3459647 baseEnd_3459647 := by
    simpa [prefixWord, tailWord_3459647, baseEnd_3459647] using wordTrace_append hprefix tailTrace_3459647
  have hstable : (prefixWord ++ tailWord_3459647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459647).length < 2 ^ (prefixWord ++ tailWord_3459647).sum := by decide
  have hdescent : baseEnd_3459647 < baseStart_3459647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459654 : List Nat := [6, 1, 1, 1, 2, 3, 9]
def baseStart_3459654 : Nat := 118140960795 + 3459654 * 2 ^ 59
def prefixEnd_3459654 : Nat := 4983230072969 + 3 ^ 40 * 3459654 * 2
def baseEnd_3459654 : Nat := 21931671608026078043387

theorem tailTrace_3459654 : CollatzResearch.WordTrace tailWord_3459654 prefixEnd_3459654 21931671608026078043387 := by
  unfold tailWord_3459654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3943248369008496709606063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84122631872181263138262677 3943248369008496709606063)
  ·
    refine ⟨5914872553512745064409095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3943248369008496709606063 5914872553512745064409095)
    ·
      refine ⟨8872308830269117596613643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5914872553512745064409095 8872308830269117596613643)
      ·
        refine ⟨13308463245403676394920465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8872308830269117596613643 13308463245403676394920465)
        ·
          refine ⟨9981347434052757296190349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13308463245403676394920465 9981347434052757296190349)
          ·
            refine ⟨3743005287769783986071381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9981347434052757296190349 3743005287769783986071381)
            ·
              refine ⟨21931671608026078043387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3743005287769783986071381 21931671608026078043387)
              ·
                rfl

theorem cell23_3459654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 9].length) (baseStart_3459654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459654 prefixEnd_3459654 := by exact prefixLift 3459654
  have htrace : WordTrace (prefixWord ++ tailWord_3459654) baseStart_3459654 baseEnd_3459654 := by
    simpa [prefixWord, tailWord_3459654, baseEnd_3459654] using wordTrace_append hprefix tailTrace_3459654
  have hstable : (prefixWord ++ tailWord_3459654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459654).length < 2 ^ (prefixWord ++ tailWord_3459654).sum := by decide
  have hdescent : baseEnd_3459654 < baseStart_3459654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459657 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 7, 3, 2]
def baseStart_3459657 : Nat := 118140960795 + 3459657 * 2 ^ 59
def prefixEnd_3459657 : Nat := 4983230072969 + 3 ^ 40 * 3459657 * 2
def baseEnd_3459657 : Nat := 1776466940692075809776833

theorem tailTrace_3459657 : CollatzResearch.WordTrace tailWord_3459657 prefixEnd_3459657 1776466940692075809776833 := by
  unfold tailWord_3459657
  simp only [CollatzResearch.WordTrace]
  refine ⟨126184057227261026219753225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84122704818174017479835483 126184057227261026219753225)
  ·
    refine ⟨94638042920445769664814919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126184057227261026219753225 94638042920445769664814919)
    ·
      refine ⟨141957064380668654497222379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94638042920445769664814919 141957064380668654497222379)
      ·
        refine ⟨212935596571002981745833569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141957064380668654497222379 212935596571002981745833569)
        ·
          refine ⟨159701697428252236309375177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212935596571002981745833569 159701697428252236309375177)
          ·
            refine ⟨119776273071189177232031383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159701697428252236309375177 119776273071189177232031383)
            ·
              refine ⟨179664409606783765848047075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119776273071189177232031383 179664409606783765848047075)
              ·
                refine ⟨269496614410175648772070613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179664409606783765848047075 269496614410175648772070613)
                ·
                  refine ⟨6316326900238491768095405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 269496614410175648772070613 6316326900238491768095405)
                  ·
                    refine ⟨2368622587589434413035777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6316326900238491768095405 2368622587589434413035777)
                    ·
                      refine ⟨1776466940692075809776833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2368622587589434413035777 1776466940692075809776833)
                      ·
                        rfl

theorem cell23_3459657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 3, 2].length) (baseStart_3459657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459657 prefixEnd_3459657 := by exact prefixLift 3459657
  have htrace : WordTrace (prefixWord ++ tailWord_3459657) baseStart_3459657 baseEnd_3459657 := by
    simpa [prefixWord, tailWord_3459657, baseEnd_3459657] using wordTrace_append hprefix tailTrace_3459657
  have hstable : (prefixWord ++ tailWord_3459657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459657).length < 2 ^ (prefixWord ++ tailWord_3459657).sum := by decide
  have hdescent : baseEnd_3459657 < baseStart_3459657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459660 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 2, 2, 5]
def baseStart_3459660 : Nat := 118140960795 + 3459660 * 2 ^ 59
def prefixEnd_3459660 : Nat := 4983230072969 + 3 ^ 40 * 3459660 * 2
def baseEnd_3459660 : Nat := 1776468481134039298039319

theorem tailTrace_3459660 : CollatzResearch.WordTrace tailWord_3459660 prefixEnd_3459660 1776468481134039298039319 := by
  unfold tailWord_3459660
  simp only [CollatzResearch.WordTrace]
  refine ⟨63092083323125078866056217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84122777764166771821408289 63092083323125078866056217)
  ·
    refine ⟨47319062492343809149542163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63092083323125078866056217 47319062492343809149542163)
    ·
      refine ⟨70978593738515713724313245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47319062492343809149542163 70978593738515713724313245)
      ·
        refine ⟨26616972651943392646617467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70978593738515713724313245 26616972651943392646617467)
        ·
          refine ⟨39925458977915088969926201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26616972651943392646617467 39925458977915088969926201)
          ·
            refine ⟨29944094233436316727444651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39925458977915088969926201 29944094233436316727444651)
            ·
              refine ⟨44916141350154475091166977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29944094233436316727444651 44916141350154475091166977)
              ·
                refine ⟨33687106012615856318375233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44916141350154475091166977 33687106012615856318375233)
                ·
                  refine ⟨25265329509461892238781425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33687106012615856318375233 25265329509461892238781425)
                  ·
                    refine ⟨18948997132096419179086069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25265329509461892238781425 18948997132096419179086069)
                    ·
                      refine ⟨1776468481134039298039319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18948997132096419179086069 1776468481134039298039319)
                      ·
                        rfl

theorem cell23_3459660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_3459660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459660 prefixEnd_3459660 := by exact prefixLift 3459660
  have htrace : WordTrace (prefixWord ++ tailWord_3459660) baseStart_3459660 baseEnd_3459660 := by
    simpa [prefixWord, tailWord_3459660, baseEnd_3459660] using wordTrace_append hprefix tailTrace_3459660
  have hstable : (prefixWord ++ tailWord_3459660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459660).length < 2 ^ (prefixWord ++ tailWord_3459660).sum := by decide
  have hdescent : baseEnd_3459660 < baseStart_3459660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459680 : List Nat := [2, 1, 1, 3, 2, 1, 2, 3, 2, 6]
def baseStart_3459680 : Nat := 118140960795 + 3459680 * 2 ^ 59
def prefixEnd_3459680 : Nat := 4983230072969 + 3 ^ 40 * 3459680 * 2
def baseEnd_3459680 : Nat := 592159583582376406596409

theorem tailTrace_3459680 : CollatzResearch.WordTrace tailWord_3459680 prefixEnd_3459680 592159583582376406596409 := by
  unfold tailWord_3459680
  simp only [CollatzResearch.WordTrace]
  refine ⟨63092448053088850573920247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84123264070785134098560329 63092448053088850573920247)
  ·
    refine ⟨94638672079633275860880371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63092448053088850573920247 94638672079633275860880371)
    ·
      refine ⟨141958008119449913791320557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94638672079633275860880371 141958008119449913791320557)
      ·
        refine ⟨53234253044793717671745209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141958008119449913791320557 53234253044793717671745209)
        ·
          refine ⟨39925689783595288253808907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53234253044793717671745209 39925689783595288253808907)
          ·
            refine ⟨59888534675392932380713361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39925689783595288253808907 59888534675392932380713361)
            ·
              refine ⟨44916401006544699285535021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59888534675392932380713361 44916401006544699285535021)
              ·
                refine ⟨16843650377454262232075633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44916401006544699285535021 16843650377454262232075633)
                ·
                  refine ⟨12632737783090696674056725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16843650377454262232075633 12632737783090696674056725)
                  ·
                    refine ⟨592159583582376406596409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12632737783090696674056725 592159583582376406596409)
                    ·
                      rfl

theorem cell23_3459680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 2, 6].length) (baseStart_3459680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459680 prefixEnd_3459680 := by exact prefixLift 3459680
  have htrace : WordTrace (prefixWord ++ tailWord_3459680) baseStart_3459680 baseEnd_3459680 := by
    simpa [prefixWord, tailWord_3459680, baseEnd_3459680] using wordTrace_append hprefix tailTrace_3459680
  have hstable : (prefixWord ++ tailWord_3459680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459680).length < 2 ^ (prefixWord ++ tailWord_3459680).sum := by decide
  have hdescent : baseEnd_3459680 < baseStart_3459680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459681 : List Nat := [1, 2, 3, 1, 1, 4, 4, 1, 2, 1, 3]
def baseStart_3459681 : Nat := 118140960795 + 3459681 * 2 ^ 59
def prefixEnd_3459681 : Nat := 4983230072969 + 3 ^ 40 * 3459681 * 2
def baseEnd_3459681 : Nat := 1776479264227783715876723

theorem tailTrace_3459681 : CollatzResearch.WordTrace tailWord_3459681 prefixEnd_3459681 1776479264227783715876723 := by
  unfold tailWord_3459681
  simp only [CollatzResearch.WordTrace]
  refine ⟨126184932579174078318626897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84123288386116052212417931 126184932579174078318626897)
  ·
    refine ⟨94638699434380558738970173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126184932579174078318626897 94638699434380558738970173)
    ·
      refine ⟨35489512287892709527113815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94638699434380558738970173 35489512287892709527113815)
      ·
        refine ⟨53234268431839064290670723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35489512287892709527113815 53234268431839064290670723)
        ·
          refine ⟨79851402647758596436006085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53234268431839064290670723 79851402647758596436006085)
          ·
            refine ⟨14972137996454736831751141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79851402647758596436006085 14972137996454736831751141)
            ·
              refine ⟨2807275874335263155953339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14972137996454736831751141 2807275874335263155953339)
              ·
                refine ⟨4210913811502894733930009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2807275874335263155953339 4210913811502894733930009)
                ·
                  refine ⟨3158185358627171050447507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4210913811502894733930009 3158185358627171050447507)
                  ·
                    refine ⟨4737278037940756575671261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3158185358627171050447507 4737278037940756575671261)
                    ·
                      refine ⟨1776479264227783715876723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4737278037940756575671261 1776479264227783715876723)
                      ·
                        rfl

theorem cell23_3459681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 2, 1, 3].length) (baseStart_3459681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459681 prefixEnd_3459681 := by exact prefixLift 3459681
  have htrace : WordTrace (prefixWord ++ tailWord_3459681) baseStart_3459681 baseEnd_3459681 := by
    simpa [prefixWord, tailWord_3459681, baseEnd_3459681] using wordTrace_append hprefix tailTrace_3459681
  have hstable : (prefixWord ++ tailWord_3459681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459681).length < 2 ^ (prefixWord ++ tailWord_3459681).sum := by decide
  have hdescent : baseEnd_3459681 < baseStart_3459681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459727 : List Nat := [1, 1, 2, 1, 1, 1, 1, 10, 5]
def baseStart_3459727 : Nat := 118140960795 + 3459727 * 2 ^ 59
def prefixEnd_3459727 : Nat := 4983230072969 + 3 ^ 40 * 3459727 * 2
def baseEnd_3459727 : Nat := 197389209370876726211279

theorem tailTrace_3459727 : CollatzResearch.WordTrace tailWord_3459727 prefixEnd_3459727 197389209370876726211279 := by
  unfold tailWord_3459727
  simp only [CollatzResearch.WordTrace]
  refine ⟨126186610337007428174801435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84124406891338285449867623 126186610337007428174801435)
  ·
    refine ⟨189279915505511142262202153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126186610337007428174801435 189279915505511142262202153)
    ·
      refine ⟨141959936629133356696651615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189279915505511142262202153 141959936629133356696651615)
      ·
        refine ⟨212939904943700035044977423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141959936629133356696651615 212939904943700035044977423)
        ·
          refine ⟨319409857415550052567466135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212939904943700035044977423 319409857415550052567466135)
          ·
            refine ⟨479114786123325078851199203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319409857415550052567466135 479114786123325078851199203)
            ·
              refine ⟨718672179184987618276798805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479114786123325078851199203 718672179184987618276798805)
              ·
                refine ⟨2105484899956018412920309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 718672179184987618276798805 2105484899956018412920309)
                ·
                  refine ⟨197389209370876726211279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2105484899956018412920309 197389209370876726211279)
                  ·
                    rfl

theorem cell23_3459727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10, 5].length) (baseStart_3459727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459727 prefixEnd_3459727 := by exact prefixLift 3459727
  have htrace : WordTrace (prefixWord ++ tailWord_3459727) baseStart_3459727 baseEnd_3459727 := by
    simpa [prefixWord, tailWord_3459727, baseEnd_3459727] using wordTrace_append hprefix tailTrace_3459727
  have hstable : (prefixWord ++ tailWord_3459727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459727).length < 2 ^ (prefixWord ++ tailWord_3459727).sum := by decide
  have hdescent : baseEnd_3459727 < baseStart_3459727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459737 : List Nat := [1, 2, 1, 2, 1, 2, 5, 1, 2, 3, 3]
def baseStart_3459737 : Nat := 118140960795 + 3459737 * 2 ^ 59
def prefixEnd_3459737 : Nat := 4983230072969 + 3 ^ 40 * 3459737 * 2
def baseEnd_3459737 : Nat := 1776508019144435496776465

theorem tailTrace_3459737 : CollatzResearch.WordTrace tailWord_3459737 prefixEnd_3459737 1776508019144435496776465 := by
  unfold tailWord_3459737
  simp only [CollatzResearch.WordTrace]
  refine ⟨126186975066971199882665465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84124650044647466588443643 126186975066971199882665465)
  ·
    refine ⟨94640231300228399911999099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126186975066971199882665465 94640231300228399911999099)
    ·
      refine ⟨141960346950342599867998649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94640231300228399911999099 141960346950342599867998649)
      ·
        refine ⟨106470260212756949900998987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141960346950342599867998649 106470260212756949900998987)
        ·
          refine ⟨159705390319135424851498481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106470260212756949900998987 159705390319135424851498481)
          ·
            refine ⟨119779042739351568638623861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159705390319135424851498481 119779042739351568638623861)
            ·
              refine ⟨11229285256814209559870987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119779042739351568638623861 11229285256814209559870987)
              ·
                refine ⟨16843927885221314339806481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11229285256814209559870987 16843927885221314339806481)
                ·
                  refine ⟨12632945913915985754854861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16843927885221314339806481 12632945913915985754854861)
                  ·
                    refine ⟨4737354717718494658070573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12632945913915985754854861 4737354717718494658070573)
                    ·
                      refine ⟨1776508019144435496776465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4737354717718494658070573 1776508019144435496776465)
                      ·
                        rfl

theorem cell23_3459737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 3, 3].length) (baseStart_3459737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459737 prefixEnd_3459737 := by exact prefixLift 3459737
  have htrace : WordTrace (prefixWord ++ tailWord_3459737) baseStart_3459737 baseEnd_3459737 := by
    simpa [prefixWord, tailWord_3459737, baseEnd_3459737] using wordTrace_append hprefix tailTrace_3459737
  have hstable : (prefixWord ++ tailWord_3459737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459737).length < 2 ^ (prefixWord ++ tailWord_3459737).sum := by decide
  have hdescent : baseEnd_3459737 < baseStart_3459737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459738 : List Nat := [3, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2]
def baseStart_3459738 : Nat := 118140960795 + 3459738 * 2 ^ 59
def prefixEnd_3459738 : Nat := 4983230072969 + 3 ^ 40 * 3459738 * 2
def baseEnd_3459738 : Nat := 1776508532625089992863961

theorem tailTrace_3459738 : CollatzResearch.WordTrace tailWord_3459738 prefixEnd_3459738 1776508532625089992863961 := by
  unfold tailWord_3459738
  simp only [CollatzResearch.WordTrace]
  refine ⟨31546752884991894263362967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84124674359978384702301245 31546752884991894263362967)
  ·
    refine ⟨47320129327487841395044451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31546752884991894263362967 47320129327487841395044451)
    ·
      refine ⟨70980193991231762092566677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47320129327487841395044451 70980193991231762092566677)
      ·
        refine ⟨3327196593338988848089063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 70980193991231762092566677 3327196593338988848089063)
        ·
          refine ⟨4990794890008483272133595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3327196593338988848089063 4990794890008483272133595)
          ·
            refine ⟨7486192335012724908200393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4990794890008483272133595 7486192335012724908200393)
            ·
              refine ⟨5614644251259543681150295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7486192335012724908200393 5614644251259543681150295)
              ·
                refine ⟨8421966376889315521725443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5614644251259543681150295 8421966376889315521725443)
                ·
                  refine ⟨12632949565333973282588165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8421966376889315521725443 12632949565333973282588165)
                  ·
                    refine ⟨2368678043500119990485281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12632949565333973282588165 2368678043500119990485281)
                    ·
                      refine ⟨1776508532625089992863961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2368678043500119990485281 1776508532625089992863961)
                      ·
                        rfl

theorem cell23_3459738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_3459738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459738 prefixEnd_3459738 := by exact prefixLift 3459738
  have htrace : WordTrace (prefixWord ++ tailWord_3459738) baseStart_3459738 baseEnd_3459738 := by
    simpa [prefixWord, tailWord_3459738, baseEnd_3459738] using wordTrace_append hprefix tailTrace_3459738
  have hstable : (prefixWord ++ tailWord_3459738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459738).length < 2 ^ (prefixWord ++ tailWord_3459738).sum := by decide
  have hdescent : baseEnd_3459738 < baseStart_3459738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459838 : List Nat := [4, 2, 2, 1, 2, 3, 1, 1, 3, 4]
def baseStart_3459838 : Nat := 118140960795 + 3459838 * 2 ^ 59
def prefixEnd_3459838 : Nat := 4983230072969 + 3 ^ 40 * 3459838 * 2
def baseEnd_3459838 : Nat := 592186626896846533871167

theorem tailTrace_3459838 : CollatzResearch.WordTrace tailWord_3459838 prefixEnd_3459838 592186626896846533871167 := by
  unfold tailWord_3459838
  simp only [CollatzResearch.WordTrace]
  refine ⟨15773832354950661766511521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84127105893070196088061445 15773832354950661766511521)
  ·
    refine ⟨11830374266212996324883641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15773832354950661766511521 11830374266212996324883641)
    ·
      refine ⟨8872780699659747243662731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11830374266212996324883641 8872780699659747243662731)
      ·
        refine ⟨13309171049489620865494097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8872780699659747243662731 13309171049489620865494097)
        ·
          refine ⟨9981878287117215649120573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13309171049489620865494097 9981878287117215649120573)
          ·
            refine ⟨3743204357668955868420215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9981878287117215649120573 3743204357668955868420215)
            ·
              refine ⟨5614806536503433802630323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3743204357668955868420215 5614806536503433802630323)
              ·
                refine ⟨8422209804755150703945485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5614806536503433802630323 8422209804755150703945485)
                ·
                  refine ⟨3158328676783181513979557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8422209804755150703945485 3158328676783181513979557)
                  ·
                    refine ⟨592186626896846533871167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3158328676783181513979557 592186626896846533871167)
                    ·
                      rfl

theorem cell23_3459838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_3459838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459838 prefixEnd_3459838 := by exact prefixLift 3459838
  have htrace : WordTrace (prefixWord ++ tailWord_3459838) baseStart_3459838 baseEnd_3459838 := by
    simpa [prefixWord, tailWord_3459838, baseEnd_3459838] using wordTrace_append hprefix tailTrace_3459838
  have hstable : (prefixWord ++ tailWord_3459838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459838).length < 2 ^ (prefixWord ++ tailWord_3459838).sum := by decide
  have hdescent : baseEnd_3459838 < baseStart_3459838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459871 : List Nat := [1, 1, 2, 4, 2, 2, 1, 3, 2, 3, 2]
def baseStart_3459871 : Nat := 118140960795 + 3459871 * 2 ^ 59
def prefixEnd_3459871 : Nat := 4983230072969 + 3 ^ 40 * 3459871 * 2
def baseEnd_3459871 : Nat := 1776576825552137972500849

theorem tailTrace_3459871 : CollatzResearch.WordTrace tailWord_3459871 prefixEnd_3459871 1776576825552137972500849 := by
  unfold tailWord_3459871
  simp only [CollatzResearch.WordTrace]
  refine ⟨126191862448485740768043467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84127908298990493845362311 126191862448485740768043467)
  ·
    refine ⟨189287793672728611152065201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126191862448485740768043467 189287793672728611152065201)
    ·
      refine ⟨141965845254546458364048901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189287793672728611152065201 141965845254546458364048901)
      ·
        refine ⟨26618595985227460943259169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141965845254546458364048901 26618595985227460943259169)
        ·
          refine ⟨19963946988920595707444377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26618595985227460943259169 19963946988920595707444377)
          ·
            refine ⟨14972960241690446780583283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19963946988920595707444377 14972960241690446780583283)
            ·
              refine ⟨22459440362535670170874925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14972960241690446780583283 22459440362535670170874925)
              ·
                refine ⟨8422290135950876314078097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22459440362535670170874925 8422290135950876314078097)
                ·
                  refine ⟨6316717601963157235558573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8422290135950876314078097 6316717601963157235558573)
                  ·
                    refine ⟨2368769100736183963334465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6316717601963157235558573 2368769100736183963334465)
                    ·
                      refine ⟨1776576825552137972500849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2368769100736183963334465 1776576825552137972500849)
                      ·
                        rfl

theorem cell23_3459871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_3459871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459871 prefixEnd_3459871 := by exact prefixLift 3459871
  have htrace : WordTrace (prefixWord ++ tailWord_3459871) baseStart_3459871 baseEnd_3459871 := by
    simpa [prefixWord, tailWord_3459871, baseEnd_3459871] using wordTrace_append hprefix tailTrace_3459871
  have hstable : (prefixWord ++ tailWord_3459871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459871).length < 2 ^ (prefixWord ++ tailWord_3459871).sum := by decide
  have hdescent : baseEnd_3459871 < baseStart_3459871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459935 : List Nat := [1, 1, 2, 3, 1, 3, 4, 3, 1, 2, 2]
def baseStart_3459935 : Nat := 118140960795 + 3459935 * 2 ^ 59
def prefixEnd_3459935 : Nat := 4983230072969 + 3 ^ 40 * 3459935 * 2
def baseEnd_3459935 : Nat := 1776609688314025722100555

theorem tailTrace_3459935 : CollatzResearch.WordTrace tailWord_3459935 prefixEnd_3459935 1776609688314025722100555 := by
  unfold tailWord_3459935
  simp only [CollatzResearch.WordTrace]
  refine ⟨126194196720253879698373259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84129464480169253132248839 126194196720253879698373259)
  ·
    refine ⟨189291295080380819547559889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126194196720253879698373259 189291295080380819547559889)
    ·
      refine ⟨141968471310285614660669917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189291295080380819547559889 141968471310285614660669917)
      ·
        refine ⟨53238176741357105497751219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141968471310285614660669917 53238176741357105497751219)
        ·
          refine ⟨79857265112035658246626829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53238176741357105497751219 79857265112035658246626829)
          ·
            refine ⟨29946474417013371842485061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79857265112035658246626829 29946474417013371842485061)
            ·
              refine ⟨5614963953190007220465949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29946474417013371842485061 5614963953190007220465949)
              ·
                refine ⟨2105611482446252707674731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5614963953190007220465949 2105611482446252707674731)
                ·
                  refine ⟨3158417223669379061512097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2105611482446252707674731 3158417223669379061512097)
                  ·
                    refine ⟨2368812917752034296134073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3158417223669379061512097 2368812917752034296134073)
                    ·
                      refine ⟨1776609688314025722100555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2368812917752034296134073 1776609688314025722100555)
                      ·
                        rfl

theorem cell23_3459935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3, 1, 2, 2].length) (baseStart_3459935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459935 prefixEnd_3459935 := by exact prefixLift 3459935
  have htrace : WordTrace (prefixWord ++ tailWord_3459935) baseStart_3459935 baseEnd_3459935 := by
    simpa [prefixWord, tailWord_3459935, baseEnd_3459935] using wordTrace_append hprefix tailTrace_3459935
  have hstable : (prefixWord ++ tailWord_3459935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459935).length < 2 ^ (prefixWord ++ tailWord_3459935).sum := by decide
  have hdescent : baseEnd_3459935 < baseStart_3459935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459937 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 1, 9]
def baseStart_3459937 : Nat := 118140960795 + 3459937 * 2 ^ 59
def prefixEnd_3459937 : Nat := 4983230072969 + 3 ^ 40 * 3459937 * 2
def baseEnd_3459937 : Nat := 592203571758444904758515

theorem tailTrace_3459937 : CollatzResearch.WordTrace tailWord_3459937 prefixEnd_3459937 592203571758444904758515 := by
  unfold tailWord_3459937
  simp only [CollatzResearch.WordTrace]
  refine ⟨126194269666246634039946065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84129513110831089359964043 126194269666246634039946065)
  ·
    refine ⟨94645702249684975529959549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126194269666246634039946065 94645702249684975529959549)
    ·
      refine ⟨35492138343631865823734831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94645702249684975529959549 35492138343631865823734831)
      ·
        refine ⟨53238207515447798735602247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35492138343631865823734831 53238207515447798735602247)
        ·
          refine ⟨79857311273171698103403371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53238207515447798735602247 79857311273171698103403371)
          ·
            refine ⟨119785966909757547155105057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79857311273171698103403371 119785966909757547155105057)
            ·
              refine ⟨89839475182318160366328793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119785966909757547155105057 89839475182318160366328793)
              ·
                refine ⟨67379606386738620274746595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89839475182318160366328793 67379606386738620274746595)
                ·
                  refine ⟨101069409580107930412119893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67379606386738620274746595 101069409580107930412119893)
                  ·
                    refine ⟨592203571758444904758515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 101069409580107930412119893 592203571758444904758515)
                    ·
                      rfl

theorem cell23_3459937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_3459937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459937 prefixEnd_3459937 := by exact prefixLift 3459937
  have htrace : WordTrace (prefixWord ++ tailWord_3459937) baseStart_3459937 baseEnd_3459937 := by
    simpa [prefixWord, tailWord_3459937, baseEnd_3459937] using wordTrace_append hprefix tailTrace_3459937
  have hstable : (prefixWord ++ tailWord_3459937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459937).length < 2 ^ (prefixWord ++ tailWord_3459937).sum := by decide
  have hdescent : baseEnd_3459937 < baseStart_3459937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459986 : List Nat := [3, 2, 3, 2, 3, 1, 1, 3, 1, 2, 2]
def baseStart_3459986 : Nat := 118140960795 + 3459986 * 2 ^ 59
def prefixEnd_3459986 : Nat := 4983230072969 + 3 ^ 40 * 3459986 * 2
def baseEnd_3459986 : Nat := 1776635875827405022562821

theorem tailTrace_3459986 : CollatzResearch.WordTrace tailWord_3459986 prefixEnd_3459986 1776635875827405022562821 := by
  unfold tailWord_3459986
  simp only [CollatzResearch.WordTrace]
  refine ⟨31549014210767278852119953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84130704562046076938986541 31549014210767278852119953)
  ·
    refine ⟨23661760658075459139089965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31549014210767278852119953 23661760658075459139089965)
    ·
      refine ⟨8873160246778297177158737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23661760658075459139089965 8873160246778297177158737)
      ·
        refine ⟨6654870185083722882869053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8873160246778297177158737 6654870185083722882869053)
        ·
          refine ⟨2495576319406396081075895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6654870185083722882869053 2495576319406396081075895)
          ·
            refine ⟨3743364479109594121613843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2495576319406396081075895 3743364479109594121613843)
            ·
              refine ⟨5615046718664391182420765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3743364479109594121613843 5615046718664391182420765)
              ·
                refine ⟨2105642519499146693407787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5615046718664391182420765 2105642519499146693407787)
                ·
                  refine ⟨3158463779248720040111681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2105642519499146693407787 3158463779248720040111681)
                  ·
                    refine ⟨2368847834436540030083761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3158463779248720040111681 2368847834436540030083761)
                    ·
                      refine ⟨1776635875827405022562821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2368847834436540030083761 1776635875827405022562821)
                      ·
                        rfl

theorem cell23_3459986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_3459986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459986 prefixEnd_3459986 := by exact prefixLift 3459986
  have htrace : WordTrace (prefixWord ++ tailWord_3459986) baseStart_3459986 baseEnd_3459986 := by
    simpa [prefixWord, tailWord_3459986, baseEnd_3459986] using wordTrace_append hprefix tailTrace_3459986
  have hstable : (prefixWord ++ tailWord_3459986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459986).length < 2 ^ (prefixWord ++ tailWord_3459986).sum := by decide
  have hdescent : baseEnd_3459986 < baseStart_3459986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459991 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 3, 4, 2]
def baseStart_3459991 : Nat := 118140960795 + 3459991 * 2 ^ 59
def prefixEnd_3459991 : Nat := 4983230072969 + 3 ^ 40 * 3459991 * 2
def baseEnd_3459991 : Nat := 1776638443230677503000297

theorem tailTrace_3459991 : CollatzResearch.WordTrace tailWord_3459991 prefixEnd_3459991 1776638443230677503000297 := by
  unfold tailWord_3459991
  simp only [CollatzResearch.WordTrace]
  refine ⟨126196239208051001262411827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84130826138700667508274551 126196239208051001262411827)
  ·
    refine ⟨189294358812076501893617741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126196239208051001262411827 189294358812076501893617741)
    ·
      refine ⟨70985384554528688210106653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189294358812076501893617741 70985384554528688210106653)
      ·
        refine ⟨26619519207948258078789995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70985384554528688210106653 26619519207948258078789995)
        ·
          refine ⟨39929278811922387118184993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26619519207948258078789995 39929278811922387118184993)
          ·
            refine ⟨29946959108941790338638745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39929278811922387118184993 29946959108941790338638745)
            ·
              refine ⟨22460219331706342753979059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29946959108941790338638745 22460219331706342753979059)
              ·
                refine ⟨33690328997559514130968589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22460219331706342753979059 33690328997559514130968589)
                ·
                  refine ⟨12633873374084817799113221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33690328997559514130968589 12633873374084817799113221)
                  ·
                    refine ⟨2368851257640903337333729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12633873374084817799113221 2368851257640903337333729)
                    ·
                      refine ⟨1776638443230677503000297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2368851257640903337333729 1776638443230677503000297)
                      ·
                        rfl

theorem cell23_3459991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_3459991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3459991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3459991 prefixEnd_3459991 := by exact prefixLift 3459991
  have htrace : WordTrace (prefixWord ++ tailWord_3459991) baseStart_3459991 baseEnd_3459991 := by
    simpa [prefixWord, tailWord_3459991, baseEnd_3459991] using wordTrace_append hprefix tailTrace_3459991
  have hstable : (prefixWord ++ tailWord_3459991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459991).length < 2 ^ (prefixWord ++ tailWord_3459991).sum := by decide
  have hdescent : baseEnd_3459991 < baseStart_3459991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460025 : List Nat := [1, 2, 1, 4, 2, 3, 1, 3, 2, 2, 2]
def baseStart_3460025 : Nat := 118140960795 + 3460025 * 2 ^ 59
def prefixEnd_3460025 : Nat := 4983230072969 + 3 ^ 40 * 3460025 * 2
def baseEnd_3460025 : Nat := 1776655901572930369975141

theorem tailTrace_3460025 : CollatzResearch.WordTrace tailWord_3460025 prefixEnd_3460025 1776655901572930369975141 := by
  unfold tailWord_3460025
  simp only [CollatzResearch.WordTrace]
  refine ⟨126197479289927825069149529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84131652859951883379433019 126197479289927825069149529)
  ·
    refine ⟨94648109467445868801862147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126197479289927825069149529 94648109467445868801862147)
    ·
      refine ⟨141972164201168803202793221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94648109467445868801862147 141972164201168803202793221)
      ·
        refine ⟨26619780787719150600523729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141972164201168803202793221 26619780787719150600523729)
        ·
          refine ⟨19964835590789362950392797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26619780787719150600523729 19964835590789362950392797)
          ·
            refine ⟨7486813346546011106397299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19964835590789362950392797 7486813346546011106397299)
            ·
              refine ⟨11230220019819016659595949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7486813346546011106397299 11230220019819016659595949)
              ·
                refine ⟨4211332507432131247348481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11230220019819016659595949 4211332507432131247348481)
                ·
                  refine ⟨3158499380574098435511361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4211332507432131247348481 3158499380574098435511361)
                  ·
                    refine ⟨2368874535430573826633521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3158499380574098435511361 2368874535430573826633521)
                    ·
                      refine ⟨1776655901572930369975141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2368874535430573826633521 1776655901572930369975141)
                      ·
                        rfl

theorem cell23_3460025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_3460025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460025 prefixEnd_3460025 := by exact prefixLift 3460025
  have htrace : WordTrace (prefixWord ++ tailWord_3460025) baseStart_3460025 baseEnd_3460025 := by
    simpa [prefixWord, tailWord_3460025, baseEnd_3460025] using wordTrace_append hprefix tailTrace_3460025
  have hstable : (prefixWord ++ tailWord_3460025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460025).length < 2 ^ (prefixWord ++ tailWord_3460025).sum := by decide
  have hdescent : baseEnd_3460025 < baseStart_3460025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460064 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 4]
def baseStart_3460064 : Nat := 118140960795 + 3460064 * 2 ^ 59
def prefixEnd_3460064 : Nat := 4983230072969 + 3 ^ 40 * 3460064 * 2
def baseEnd_3460064 : Nat := 1776675927318455717387461

theorem tailTrace_3460064 : CollatzResearch.WordTrace tailWord_3460064 prefixEnd_3460064 1776675927318455717387461 := by
  unfold tailWord_3460064
  simp only [CollatzResearch.WordTrace]
  refine ⟨63099450868393267364909623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84132601157857689819879497 63099450868393267364909623)
  ·
    refine ⟨94649176302589901047364435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63099450868393267364909623 94649176302589901047364435)
    ·
      refine ⟨141973764453884851571046653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94649176302589901047364435 141973764453884851571046653)
      ·
        refine ⟨53240161670206819339142495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141973764453884851571046653 53240161670206819339142495)
        ·
          refine ⟨79860242505310229008713743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53240161670206819339142495 79860242505310229008713743)
          ·
            refine ⟨119790363757965343513070615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79860242505310229008713743 119790363757965343513070615)
            ·
              refine ⟨179685545636948015269605923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119790363757965343513070615 179685545636948015269605923)
              ·
                refine ⟨269528318455422022904408885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179685545636948015269605923 269528318455422022904408885)
                ·
                  refine ⟨25268279855195814647288333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 269528318455422022904408885 25268279855195814647288333)
                  ·
                    refine ⟨9475604945698430492733125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25268279855195814647288333 9475604945698430492733125)
                    ·
                      refine ⟨1776675927318455717387461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9475604945698430492733125 1776675927318455717387461)
                      ·
                        rfl

theorem cell23_3460064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_3460064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460064 prefixEnd_3460064 := by exact prefixLift 3460064
  have htrace : WordTrace (prefixWord ++ tailWord_3460064) baseStart_3460064 baseEnd_3460064 := by
    simpa [prefixWord, tailWord_3460064, baseEnd_3460064] using wordTrace_append hprefix tailTrace_3460064
  have hstable : (prefixWord ++ tailWord_3460064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460064).length < 2 ^ (prefixWord ++ tailWord_3460064).sum := by decide
  have hdescent : baseEnd_3460064 < baseStart_3460064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460071 : List Nat := [1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_3460071 : Nat := 118140960795 + 3460071 * 2 ^ 59
def prefixEnd_3460071 : Nat := 4983230072969 + 3 ^ 40 * 3460071 * 2
def baseEnd_3460071 : Nat := 1776679521683037189999929

theorem tailTrace_3460071 : CollatzResearch.WordTrace tailWord_3460071 prefixEnd_3460071 1776679521683037189999929 := by
  unfold tailWord_3460071
  simp only [CollatzResearch.WordTrace]
  refine ⟨126199157047761174925324067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84132771365174116616882711 126199157047761174925324067)
  ·
    refine ⟨189298735571641762387986101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126199157047761174925324067 189298735571641762387986101)
    ·
      refine ⟨17746756459841415223873697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189298735571641762387986101 17746756459841415223873697)
      ·
        refine ⟨13310067344881061417905273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17746756459841415223873697 13310067344881061417905273)
        ·
          refine ⟨9982550508660796063428955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13310067344881061417905273 9982550508660796063428955)
          ·
            refine ⟨14973825762991194095143433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9982550508660796063428955 14973825762991194095143433)
            ·
              refine ⟨11230369322243395571357575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14973825762991194095143433 11230369322243395571357575)
              ·
                refine ⟨16845553983365093357036363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11230369322243395571357575 16845553983365093357036363)
                ·
                  refine ⟨25268330975047640035554545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16845553983365093357036363 25268330975047640035554545)
                  ·
                    refine ⟨18951248231285730026665909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25268330975047640035554545 18951248231285730026665909)
                    ·
                      refine ⟨1776679521683037189999929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18951248231285730026665909 1776679521683037189999929)
                      ·
                        rfl

theorem cell23_3460071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_3460071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460071 prefixEnd_3460071 := by exact prefixLift 3460071
  have htrace : WordTrace (prefixWord ++ tailWord_3460071) baseStart_3460071 baseEnd_3460071 := by
    simpa [prefixWord, tailWord_3460071, baseEnd_3460071] using wordTrace_append hprefix tailTrace_3460071
  have hstable : (prefixWord ++ tailWord_3460071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460071).length < 2 ^ (prefixWord ++ tailWord_3460071).sum := by decide
  have hdescent : baseEnd_3460071 < baseStart_3460071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460101 : List Nat := [1, 3, 1, 1, 2, 3, 3, 1, 1, 4, 3]
def baseStart_3460101 : Nat := 118140960795 + 3460101 * 2 ^ 59
def prefixEnd_3460101 : Nat := 4983230072969 + 3 ^ 40 * 3460101 * 2
def baseEnd_3460101 : Nat := 1776694926102672072624791

theorem tailTrace_3460101 : CollatzResearch.WordTrace tailWord_3460101 prefixEnd_3460101 1776694926102672072624791 := by
  unfold tailWord_3460101
  simp only [CollatzResearch.WordTrace]
  refine ⟨126200251237652490048916157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84133500825101660032610771 126200251237652490048916157)
  ·
    refine ⟨47325094214119683768343559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126200251237652490048916157 47325094214119683768343559)
    ·
      refine ⟨70987641321179525652515339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47325094214119683768343559 70987641321179525652515339)
      ·
        refine ⟨106481461981769288478773009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70987641321179525652515339 106481461981769288478773009)
        ·
          refine ⟨79861096486326966359079757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106481461981769288478773009 79861096486326966359079757)
          ·
            refine ⟨29947911182372612384654909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79861096486326966359079757 29947911182372612384654909)
            ·
              refine ⟨11230466693389729644245591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29947911182372612384654909 11230466693389729644245591)
              ·
                refine ⟨16845700040084594466368387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11230466693389729644245591 16845700040084594466368387)
                ·
                  refine ⟨25268550060126891699552581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16845700040084594466368387 25268550060126891699552581)
                  ·
                    refine ⟨4737853136273792193666109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25268550060126891699552581 4737853136273792193666109)
                    ·
                      refine ⟨1776694926102672072624791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4737853136273792193666109 1776694926102672072624791)
                      ·
                        rfl

theorem cell23_3460101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 4, 3].length) (baseStart_3460101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460101 prefixEnd_3460101 := by exact prefixLift 3460101
  have htrace : WordTrace (prefixWord ++ tailWord_3460101) baseStart_3460101 baseEnd_3460101 := by
    simpa [prefixWord, tailWord_3460101, baseEnd_3460101] using wordTrace_append hprefix tailTrace_3460101
  have hstable : (prefixWord ++ tailWord_3460101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460101).length < 2 ^ (prefixWord ++ tailWord_3460101).sum := by decide
  have hdescent : baseEnd_3460101 < baseStart_3460101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460121 : List Nat := [1, 2, 1, 2, 1, 1, 7, 2, 6]
def baseStart_3460121 : Nat := 118140960795 + 3460121 * 2 ^ 59
def prefixEnd_3460121 : Nat := 4983230072969 + 3 ^ 40 * 3460121 * 2
def baseEnd_3460121 : Nat := 197411688412862443819411

theorem tailTrace_3460121 : CollatzResearch.WordTrace tailWord_3460121 prefixEnd_3460121 197411688412862443819411 := by
  unfold tailWord_3460121
  simp only [CollatzResearch.WordTrace]
  refine ⟨126200980697580033464644217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84133987131720022309762811 126200980697580033464644217)
  ·
    refine ⟨94650735523185025098483163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126200980697580033464644217 94650735523185025098483163)
    ·
      refine ⟨141976103284777537647724745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94650735523185025098483163 141976103284777537647724745)
      ·
        refine ⟨106482077463583153235793559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141976103284777537647724745 106482077463583153235793559)
        ·
          refine ⟨159723116195374729853690339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106482077463583153235793559 159723116195374729853690339)
          ·
            refine ⟨239584674293062094780535509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159723116195374729853690339 239584674293062094780535509)
            ·
              refine ⟨5615265803743642846418801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 239584674293062094780535509 5615265803743642846418801)
              ·
                refine ⟨4211449352807732134814101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5615265803743642846418801 4211449352807732134814101)
                ·
                  refine ⟨197411688412862443819411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4211449352807732134814101 197411688412862443819411)
                  ·
                    rfl

theorem cell23_3460121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 6].length) (baseStart_3460121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460121 prefixEnd_3460121 := by exact prefixLift 3460121
  have htrace : WordTrace (prefixWord ++ tailWord_3460121) baseStart_3460121 baseEnd_3460121 := by
    simpa [prefixWord, tailWord_3460121, baseEnd_3460121] using wordTrace_append hprefix tailTrace_3460121
  have hstable : (prefixWord ++ tailWord_3460121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460121).length < 2 ^ (prefixWord ++ tailWord_3460121).sum := by decide
  have hdescent : baseEnd_3460121 < baseStart_3460121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460125 : List Nat := [1, 4, 2, 2, 3, 1, 2, 1, 3, 4]
def baseStart_3460125 : Nat := 118140960795 + 3460125 * 2 ^ 59
def prefixEnd_3460125 : Nat := 4983230072969 + 3 ^ 40 * 3460125 * 2
def baseEnd_3460125 : Nat := 592235749879459992908227

theorem tailTrace_3460125 : CollatzResearch.WordTrace tailWord_3460125 prefixEnd_3460125 592235749879459992908227 := by
  unfold tailWord_3460125
  simp only [CollatzResearch.WordTrace]
  refine ⟨126201126589565542147789829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84134084393043694765193219 126201126589565542147789829)
  ·
    refine ⟨23662711235543539152710593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126201126589565542147789829 23662711235543539152710593)
    ·
      refine ⟨17747033426657654364532945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23662711235543539152710593 17747033426657654364532945)
      ·
        refine ⟨13310275069993240773399709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17747033426657654364532945 13310275069993240773399709)
        ·
          refine ⟨4991353151247465290024891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13310275069993240773399709 4991353151247465290024891)
          ·
            refine ⟨7487029726871197935037337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4991353151247465290024891 7487029726871197935037337)
            ·
              refine ⟨5615272295153398451278003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7487029726871197935037337 5615272295153398451278003)
              ·
                refine ⟨8422908442730097676917005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5615272295153398451278003 8422908442730097676917005)
                ·
                  refine ⟨3158590666023786628843877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8422908442730097676917005 3158590666023786628843877)
                  ·
                    refine ⟨592235749879459992908227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3158590666023786628843877 592235749879459992908227)
                    ·
                      rfl

theorem cell23_3460125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_3460125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460125 prefixEnd_3460125 := by exact prefixLift 3460125
  have htrace : WordTrace (prefixWord ++ tailWord_3460125) baseStart_3460125 baseEnd_3460125 := by
    simpa [prefixWord, tailWord_3460125, baseEnd_3460125] using wordTrace_append hprefix tailTrace_3460125
  have hstable : (prefixWord ++ tailWord_3460125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460125).length < 2 ^ (prefixWord ++ tailWord_3460125).sum := by decide
  have hdescent : baseEnd_3460125 < baseStart_3460125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460188 : List Nat := [2, 2, 4, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_3460188 : Nat := 118140960795 + 3460188 * 2 ^ 59
def prefixEnd_3460188 : Nat := 4983230072969 + 3 ^ 40 * 3460188 * 2
def baseEnd_3460188 : Nat := 1776739598919613232236891

theorem tailTrace_3460188 : CollatzResearch.WordTrace tailWord_3460188 prefixEnd_3460188 1776739598919613232236891 := by
  unfold tailWord_3460188
  simp only [CollatzResearch.WordTrace]
  refine ⟨63101712194168651953666609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84135616258891535938222145 63101712194168651953666609)
  ·
    refine ⟨47326284145626488965249957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63101712194168651953666609 47326284145626488965249957)
    ·
      refine ⟨8873678277304966680984367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47326284145626488965249957 8873678277304966680984367)
      ·
        refine ⟨13310517415957450021476551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8873678277304966680984367 13310517415957450021476551)
        ·
          refine ⟨19965776123936175032214827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13310517415957450021476551 19965776123936175032214827)
          ·
            refine ⟨29948664185904262548322241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19965776123936175032214827 29948664185904262548322241)
            ·
              refine ⟨22461498139428196911241681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29948664185904262548322241 22461498139428196911241681)
              ·
                refine ⟨16846123604571147683431261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22461498139428196911241681 16846123604571147683431261)
                ·
                  refine ⟨6317296351714180381286723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16846123604571147683431261 6317296351714180381286723)
                  ·
                    refine ⟨9475944527571270571930085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6317296351714180381286723 9475944527571270571930085)
                    ·
                      refine ⟨1776739598919613232236891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9475944527571270571930085 1776739598919613232236891)
                      ·
                        rfl

theorem cell23_3460188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_3460188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460188 prefixEnd_3460188 := by exact prefixLift 3460188
  have htrace : WordTrace (prefixWord ++ tailWord_3460188) baseStart_3460188 baseEnd_3460188 := by
    simpa [prefixWord, tailWord_3460188, baseEnd_3460188] using wordTrace_append hprefix tailTrace_3460188
  have hstable : (prefixWord ++ tailWord_3460188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460188).length < 2 ^ (prefixWord ++ tailWord_3460188).sum := by decide
  have hdescent : baseEnd_3460188 < baseStart_3460188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460189 : List Nat := [1, 4, 4, 1, 3, 1, 2, 1, 6]
def baseStart_3460189 : Nat := 118140960795 + 3460189 * 2 ^ 59
def prefixEnd_3460189 : Nat := 4983230072969 + 3 ^ 40 * 3460189 * 2
def baseEnd_3460189 : Nat := 197415568044474192036043

theorem tailTrace_3460189 : CollatzResearch.WordTrace tailWord_3460189 prefixEnd_3460189 197415568044474192036043 := by
  unfold tailWord_3460189
  simp only [CollatzResearch.WordTrace]
  refine ⟨126203460861333681078119621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84135640574222454052079747 126203460861333681078119621)
  ·
    refine ⟨23663148911500065202147429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126203460861333681078119621 23663148911500065202147429)
    ·
      refine ⟨4436840420906262225402643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23663148911500065202147429 4436840420906262225402643)
      ·
        refine ⟨6655260631359393338103965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4436840420906262225402643 6655260631359393338103965)
        ·
          refine ⟨2495722736759772501788987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6655260631359393338103965 2495722736759772501788987)
          ·
            refine ⟨3743584105139658752683481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2495722736759772501788987 3743584105139658752683481)
            ·
              refine ⟨2807688078854744064512611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3743584105139658752683481 2807688078854744064512611)
              ·
                refine ⟨4211532118282116096768917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2807688078854744064512611 4211532118282116096768917)
                ·
                  refine ⟨197415568044474192036043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4211532118282116096768917 197415568044474192036043)
                  ·
                    rfl

theorem cell23_3460189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 6].length) (baseStart_3460189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460189 prefixEnd_3460189 := by exact prefixLift 3460189
  have htrace : WordTrace (prefixWord ++ tailWord_3460189) baseStart_3460189 baseEnd_3460189 := by
    simpa [prefixWord, tailWord_3460189, baseEnd_3460189] using wordTrace_append hprefix tailTrace_3460189
  have hstable : (prefixWord ++ tailWord_3460189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460189).length < 2 ^ (prefixWord ++ tailWord_3460189).sum := by decide
  have hdescent : baseEnd_3460189 < baseStart_3460189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460191 : List Nat := [1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 5]
def baseStart_3460191 : Nat := 118140960795 + 3460191 * 2 ^ 59
def prefixEnd_3460191 : Nat := 4983230072969 + 3 ^ 40 * 3460191 * 2
def baseEnd_3460191 : Nat := 1776741139361576720499377

theorem tailTrace_3460191 : CollatzResearch.WordTrace tailWord_3460191 prefixEnd_3460191 1776741139361576720499377 := by
  unfold tailWord_3460191
  simp only [CollatzResearch.WordTrace]
  refine ⟨126203533807326435419692427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84135689204884290279794951 126203533807326435419692427)
  ·
    refine ⟨189305300710989653129538641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126203533807326435419692427 189305300710989653129538641)
    ·
      refine ⟨141978975533242239847153981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189305300710989653129538641 141978975533242239847153981)
      ·
        refine ⟨53242115824965839942682743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141978975533242239847153981 53242115824965839942682743)
        ·
          refine ⟨79863173737448759914024115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53242115824965839942682743 79863173737448759914024115)
          ·
            refine ⟨119794760606173139871036173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79863173737448759914024115 119794760606173139871036173)
            ·
              refine ⟨44923035227314927451638565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119794760606173139871036173 44923035227314927451638565)
              ·
                refine ⟨8423069105121548897182231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44923035227314927451638565 8423069105121548897182231)
                ·
                  refine ⟨12634603657682323345773347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8423069105121548897182231 12634603657682323345773347)
                  ·
                    refine ⟨18951905486523485018660021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12634603657682323345773347 18951905486523485018660021)
                    ·
                      refine ⟨1776741139361576720499377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18951905486523485018660021 1776741139361576720499377)
                      ·
                        rfl

theorem cell23_3460191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_3460191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460191 prefixEnd_3460191 := by exact prefixLift 3460191
  have htrace : WordTrace (prefixWord ++ tailWord_3460191) baseStart_3460191 baseEnd_3460191 := by
    simpa [prefixWord, tailWord_3460191, baseEnd_3460191] using wordTrace_append hprefix tailTrace_3460191
  have hstable : (prefixWord ++ tailWord_3460191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460191).length < 2 ^ (prefixWord ++ tailWord_3460191).sum := by decide
  have hdescent : baseEnd_3460191 < baseStart_3460191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460201 : List Nat := [1, 2, 1, 1, 1, 6, 2, 1, 1, 1, 6]
def baseStart_3460201 : Nat := 118140960795 + 3460201 * 2 ^ 59
def prefixEnd_3460201 : Nat := 4983230072969 + 3 ^ 40 * 3460201 * 2
def baseEnd_3460201 : Nat := 1776746274168121681374331

theorem tailTrace_3460201 : CollatzResearch.WordTrace tailWord_3460201 prefixEnd_3460201 1776746274168121681374331 := by
  unfold tailWord_3460201
  simp only [CollatzResearch.WordTrace]
  refine ⟨126203898537290207127556457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84135932358193471418370971 126203898537290207127556457)
  ·
    refine ⟨94652923902967655345667343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126203898537290207127556457 94652923902967655345667343)
    ·
      refine ⟨141979385854451483018501015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94652923902967655345667343 141979385854451483018501015)
      ·
        refine ⟨212969078781677224527751523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141979385854451483018501015 212969078781677224527751523)
        ·
          refine ⟨319453618172515836791627285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212969078781677224527751523 319453618172515836791627285)
          ·
            refine ⟨14974388351836679849607529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 319453618172515836791627285 14974388351836679849607529)
            ·
              refine ⟨11230791263877509887205647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14974388351836679849607529 11230791263877509887205647)
              ·
                refine ⟨16846186895816264830808471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11230791263877509887205647 16846186895816264830808471)
                ·
                  refine ⟨25269280343724397246212707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16846186895816264830808471 25269280343724397246212707)
                  ·
                    refine ⟨37903920515586595869319061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25269280343724397246212707 37903920515586595869319061)
                    ·
                      refine ⟨1776746274168121681374331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37903920515586595869319061 1776746274168121681374331)
                      ·
                        rfl

theorem cell23_3460201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 1, 6].length) (baseStart_3460201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460201 prefixEnd_3460201 := by exact prefixLift 3460201
  have htrace : WordTrace (prefixWord ++ tailWord_3460201) baseStart_3460201 baseEnd_3460201 := by
    simpa [prefixWord, tailWord_3460201, baseEnd_3460201] using wordTrace_append hprefix tailTrace_3460201
  have hstable : (prefixWord ++ tailWord_3460201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460201).length < 2 ^ (prefixWord ++ tailWord_3460201).sum := by decide
  have hdescent : baseEnd_3460201 < baseStart_3460201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460205 : List Nat := [1, 5, 1, 1, 2, 2, 3, 2, 1, 1, 4]
def baseStart_3460205 : Nat := 118140960795 + 3460205 * 2 ^ 59
def prefixEnd_3460205 : Nat := 4983230072969 + 3 ^ 40 * 3460205 * 2
def baseEnd_3460205 : Nat := 1776748328090739665724313

theorem tailTrace_3460205 : CollatzResearch.WordTrace tailWord_3460205 prefixEnd_3460205 1776748328090739665724313 := by
  unfold tailWord_3460205
  simp only [CollatzResearch.WordTrace]
  refine ⟨126204044429275715810702069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84136029619517143873801379 126204044429275715810702069)
  ·
    refine ⟨11831629165244598357253319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126204044429275715810702069 11831629165244598357253319)
    ·
      refine ⟨17747443747866897535879979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11831629165244598357253319 17747443747866897535879979)
      ·
        refine ⟨26621165621800346303819969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17747443747866897535879979 26621165621800346303819969)
        ·
          refine ⟨19965874216350259727864977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26621165621800346303819969 19965874216350259727864977)
          ·
            refine ⟨14974405662262694795898733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19965874216350259727864977 14974405662262694795898733)
            ·
              refine ⟨5615402123348510548462025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14974405662262694795898733 5615402123348510548462025)
              ·
                refine ⟨4211551592511382911346519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5615402123348510548462025 4211551592511382911346519)
                ·
                  refine ⟨6317327388767074367019779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4211551592511382911346519 6317327388767074367019779)
                  ·
                    refine ⟨9475991083150611550529669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6317327388767074367019779 9475991083150611550529669)
                    ·
                      refine ⟨1776748328090739665724313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9475991083150611550529669 1776748328090739665724313)
                      ·
                        rfl

theorem cell23_3460205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_3460205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460205 prefixEnd_3460205 := by exact prefixLift 3460205
  have htrace : WordTrace (prefixWord ++ tailWord_3460205) baseStart_3460205 baseEnd_3460205 := by
    simpa [prefixWord, tailWord_3460205, baseEnd_3460205] using wordTrace_append hprefix tailTrace_3460205
  have hstable : (prefixWord ++ tailWord_3460205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460205).length < 2 ^ (prefixWord ++ tailWord_3460205).sum := by decide
  have hdescent : baseEnd_3460205 < baseStart_3460205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460208 : List Nat := [2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 3]
def baseStart_3460208 : Nat := 118140960795 + 3460208 * 2 ^ 59
def prefixEnd_3460208 : Nat := 4983230072969 + 3 ^ 40 * 3460208 * 2
def baseEnd_3460208 : Nat := 1776749868532703153986799

theorem tailTrace_3460208 : CollatzResearch.WordTrace tailWord_3460208 prefixEnd_3460208 1776749868532703153986799 := by
  unfold tailWord_3460208
  simp only [CollatzResearch.WordTrace]
  refine ⟨63102076924132423661530639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84136102565509898215374185 63102076924132423661530639)
  ·
    refine ⟨94653115386198635492295959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63102076924132423661530639 94653115386198635492295959)
    ·
      refine ⟨141979673079297953238443939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94653115386198635492295959 141979673079297953238443939)
      ·
        refine ⟨212969509618946929857665909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141979673079297953238443939 212969509618946929857665909)
        ·
          refine ⟨19965891526776274674156179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 212969509618946929857665909 19965891526776274674156179)
          ·
            refine ⟨29948837290164412011234269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19965891526776274674156179 29948837290164412011234269)
            ·
              refine ⟨11230813983811654504212851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29948837290164412011234269 11230813983811654504212851)
              ·
                refine ⟨16846220975717481756319277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11230813983811654504212851 16846220975717481756319277)
                ·
                  refine ⟨6317332865894055658619729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16846220975717481756319277 6317332865894055658619729)
                  ·
                    refine ⟨4737999649420541743964797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6317332865894055658619729 4737999649420541743964797)
                    ·
                      refine ⟨1776749868532703153986799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4737999649420541743964797 1776749868532703153986799)
                      ·
                        rfl

theorem cell23_3460208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 3].length) (baseStart_3460208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460208 prefixEnd_3460208 := by exact prefixLift 3460208
  have htrace : WordTrace (prefixWord ++ tailWord_3460208) baseStart_3460208 baseEnd_3460208 := by
    simpa [prefixWord, tailWord_3460208, baseEnd_3460208] using wordTrace_append hprefix tailTrace_3460208
  have hstable : (prefixWord ++ tailWord_3460208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460208).length < 2 ^ (prefixWord ++ tailWord_3460208).sum := by decide
  have hdescent : baseEnd_3460208 < baseStart_3460208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460225 : List Nat := [1, 2, 4, 2, 2, 3, 1, 1, 1, 1, 5]
def baseStart_3460225 : Nat := 118140960795 + 3460225 * 2 ^ 59
def prefixEnd_3460225 : Nat := 4983230072969 + 3 ^ 40 * 3460225 * 2
def baseEnd_3460225 : Nat := 1776758597703829587474221

theorem tailTrace_3460225 : CollatzResearch.WordTrace tailWord_3460225 prefixEnd_3460225 1776758597703829587474221 := by
  unfold tailWord_3460225
  simp only [CollatzResearch.WordTrace]
  refine ⟨126204773889203259226430129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84136515926135506150953419 126204773889203259226430129)
  ·
    refine ⟨94653580416902444419822597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126204773889203259226430129 94653580416902444419822597)
    ·
      refine ⟨17747546328169208328716737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94653580416902444419822597 17747546328169208328716737)
      ·
        refine ⟨13310659746126906246537553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17747546328169208328716737 13310659746126906246537553)
        ·
          refine ⟨9982994809595179684903165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13310659746126906246537553 9982994809595179684903165)
          ·
            refine ⟨3743623053598192381838687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9982994809595179684903165 3743623053598192381838687)
            ·
              refine ⟨5615434580397288572758031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3743623053598192381838687 5615434580397288572758031)
              ·
                refine ⟨8423151870595932859137047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5615434580397288572758031 8423151870595932859137047)
                ·
                  refine ⟨12634727805893899288705571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8423151870595932859137047 12634727805893899288705571)
                  ·
                    refine ⟨18952091708840848933058357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12634727805893899288705571 18952091708840848933058357)
                    ·
                      refine ⟨1776758597703829587474221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18952091708840848933058357 1776758597703829587474221)
                      ·
                        rfl

theorem cell23_3460225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_3460225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460225 prefixEnd_3460225 := by exact prefixLift 3460225
  have htrace : WordTrace (prefixWord ++ tailWord_3460225) baseStart_3460225 baseEnd_3460225 := by
    simpa [prefixWord, tailWord_3460225, baseEnd_3460225] using wordTrace_append hprefix tailTrace_3460225
  have hstable : (prefixWord ++ tailWord_3460225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460225).length < 2 ^ (prefixWord ++ tailWord_3460225).sum := by decide
  have hdescent : baseEnd_3460225 < baseStart_3460225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460232 : List Nat := [2, 1, 3, 4, 2, 1, 2, 2, 2, 4]
def baseStart_3460232 : Nat := 118140960795 + 3460232 * 2 ^ 59
def prefixEnd_3460232 : Nat := 4983230072969 + 3 ^ 40 * 3460232 * 2
def baseEnd_3460232 : Nat := 592254064022803686695563

theorem tailTrace_3460232 : CollatzResearch.WordTrace tailWord_3460232 prefixEnd_3460232 592254064022803686695563 := by
  unfold tailWord_3460232
  simp only [CollatzResearch.WordTrace]
  refine ⟨63102514600088949710967475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84136686133451932947956633 63102514600088949710967475)
  ·
    refine ⟨94653771900133424566451213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63102514600088949710967475 94653771900133424566451213)
    ·
      refine ⟨35495164462550034212419205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94653771900133424566451213 35495164462550034212419205)
      ·
        refine ⟨6655343336728131414828601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35495164462550034212419205 6655343336728131414828601)
        ·
          refine ⟨4991507502546098561121451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6655343336728131414828601 4991507502546098561121451)
          ·
            refine ⟨7487261253819147841682177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4991507502546098561121451 7487261253819147841682177)
            ·
              refine ⟨5615445940364360881261633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7487261253819147841682177 5615445940364360881261633)
              ·
                refine ⟨4211584455273270660946225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5615445940364360881261633 4211584455273270660946225)
                ·
                  refine ⟨3158688341454952995709669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4211584455273270660946225 3158688341454952995709669)
                  ·
                    refine ⟨592254064022803686695563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3158688341454952995709669 592254064022803686695563)
                    ·
                      rfl

theorem cell23_3460232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_3460232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460232 prefixEnd_3460232 := by exact prefixLift 3460232
  have htrace : WordTrace (prefixWord ++ tailWord_3460232) baseStart_3460232 baseEnd_3460232 := by
    simpa [prefixWord, tailWord_3460232, baseEnd_3460232] using wordTrace_append hprefix tailTrace_3460232
  have hstable : (prefixWord ++ tailWord_3460232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460232).length < 2 ^ (prefixWord ++ tailWord_3460232).sum := by decide
  have hdescent : baseEnd_3460232 < baseStart_3460232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460289 : List Nat := [1, 2, 6, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_3460289 : Nat := 118140960795 + 3460289 * 2 ^ 59
def prefixEnd_3460289 : Nat := 4983230072969 + 3 ^ 40 * 3460289 * 2
def baseEnd_3460289 : Nat := 1776791460465717337073927

theorem tailTrace_3460289 : CollatzResearch.WordTrace tailWord_3460289 prefixEnd_3460289 1776791460465717337073927 := by
  unfold tailWord_3460289
  simp only [CollatzResearch.WordTrace]
  refine ⟨126207108160971398156759921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84138072107314265437839947 126207108160971398156759921)
  ·
    refine ⟨94655331120728548617569941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126207108160971398156759921 94655331120728548617569941)
    ·
      refine ⟨4436968646284150716448591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 94655331120728548617569941 4436968646284150716448591)
      ·
        refine ⟨6655452969426226074672887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4436968646284150716448591 6655452969426226074672887)
        ·
          refine ⟨9983179454139339112009331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6655452969426226074672887 9983179454139339112009331)
          ·
            refine ⟨14974769181209008668013997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9983179454139339112009331 14974769181209008668013997)
            ·
              refine ⟨5615538442953378250505249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14974769181209008668013997 5615538442953378250505249)
              ·
                refine ⟨4211653832215033687878937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5615538442953378250505249 4211653832215033687878937)
                ·
                  refine ⟨3158740374161275265909203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4211653832215033687878937 3158740374161275265909203)
                  ·
                    refine ⟨4738110561241912898863805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3158740374161275265909203 4738110561241912898863805)
                    ·
                      refine ⟨1776791460465717337073927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4738110561241912898863805 1776791460465717337073927)
                      ·
                        rfl

theorem cell23_3460289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_3460289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460289 prefixEnd_3460289 := by exact prefixLift 3460289
  have htrace : WordTrace (prefixWord ++ tailWord_3460289) baseStart_3460289 baseEnd_3460289 := by
    simpa [prefixWord, tailWord_3460289, baseEnd_3460289] using wordTrace_append hprefix tailTrace_3460289
  have hstable : (prefixWord ++ tailWord_3460289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460289).length < 2 ^ (prefixWord ++ tailWord_3460289).sum := by decide
  have hdescent : baseEnd_3460289 < baseStart_3460289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460385 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 4, 4, 2]
def baseStart_3460385 : Nat := 118140960795 + 3460385 * 2 ^ 59
def prefixEnd_3460385 : Nat := 4983230072969 + 3 ^ 40 * 3460385 * 2
def baseEnd_3460385 : Nat := 1776840754608548961473485

theorem tailTrace_3460385 : CollatzResearch.WordTrace tailWord_3460385 prefixEnd_3460385 1776840754608548961473485 := by
  unfold tailWord_3460385
  simp only [CollatzResearch.WordTrace]
  refine ⟨126210609568623606552254609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84140406379082404368169739 126210609568623606552254609)
  ·
    refine ⟨94657957176467704914190957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126210609568623606552254609 94657957176467704914190957)
    ·
      refine ⟨35496733941175389342821609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94657957176467704914190957 35496733941175389342821609)
      ·
        refine ⟨26622550455881542007116207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35496733941175389342821609 26622550455881542007116207)
        ·
          refine ⟨39933825683822313010674311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26622550455881542007116207 39933825683822313010674311)
          ·
            refine ⟨59900738525733469516011467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39933825683822313010674311 59900738525733469516011467)
            ·
              refine ⟨89851107788600204274017201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59900738525733469516011467 89851107788600204274017201)
              ·
                refine ⟨67388330841450153205512901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89851107788600204274017201 67388330841450153205512901)
                ·
                  refine ⟨12635312032771903726033669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67388330841450153205512901 12635312032771903726033669)
                  ·
                    refine ⟨2369121006144731948631313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12635312032771903726033669 2369121006144731948631313)
                    ·
                      refine ⟨1776840754608548961473485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2369121006144731948631313 1776840754608548961473485)
                      ·
                        rfl

theorem cell23_3460385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_3460385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460385 prefixEnd_3460385 := by exact prefixLift 3460385
  have htrace : WordTrace (prefixWord ++ tailWord_3460385) baseStart_3460385 baseEnd_3460385 := by
    simpa [prefixWord, tailWord_3460385, baseEnd_3460385] using wordTrace_append hprefix tailTrace_3460385
  have hstable : (prefixWord ++ tailWord_3460385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460385).length < 2 ^ (prefixWord ++ tailWord_3460385).sum := by decide
  have hdescent : baseEnd_3460385 < baseStart_3460385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460485 : List Nat := [1, 3, 1, 1, 3, 1, 5, 1, 1, 6]
def baseStart_3460485 : Nat := 118140960795 + 3460485 * 2 ^ 59
def prefixEnd_3460485 : Nat := 4983230072969 + 3 ^ 40 * 3460485 * 2
def baseEnd_3460485 : Nat := 592297367557999523407675

theorem tailTrace_3460485 : CollatzResearch.WordTrace tailWord_3460485 prefixEnd_3460485 592297367557999523407675 := by
  unfold tailWord_3460485
  simp only [CollatzResearch.WordTrace]
  refine ⟨126214256868261323630894909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84142837912174215753929939 126214256868261323630894909)
  ·
    refine ⟨47330346325597996361585591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126214256868261323630894909 47330346325597996361585591)
    ·
      refine ⟨70995519488396994542378387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47330346325597996361585591 70995519488396994542378387)
      ·
        refine ⟨106493279232595491813567581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70995519488396994542378387 106493279232595491813567581)
        ·
          refine ⟨39934979712223309430087843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106493279232595491813567581 39934979712223309430087843)
          ·
            refine ⟨59902469568334964145131765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39934979712223309430087843 59902469568334964145131765)
            ·
              refine ⟨5615856522031402888606103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59902469568334964145131765 5615856522031402888606103)
              ·
                refine ⟨8423784783047104332909155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5615856522031402888606103 8423784783047104332909155)
                ·
                  refine ⟨12635677174570656499363733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8423784783047104332909155 12635677174570656499363733)
                  ·
                    refine ⟨592297367557999523407675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12635677174570656499363733 592297367557999523407675)
                    ·
                      rfl

theorem cell23_3460485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 6].length) (baseStart_3460485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460485 prefixEnd_3460485 := by exact prefixLift 3460485
  have htrace : WordTrace (prefixWord ++ tailWord_3460485) baseStart_3460485 baseEnd_3460485 := by
    simpa [prefixWord, tailWord_3460485, baseEnd_3460485] using wordTrace_append hprefix tailTrace_3460485
  have hstable : (prefixWord ++ tailWord_3460485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460485).length < 2 ^ (prefixWord ++ tailWord_3460485).sum := by decide
  have hdescent : baseEnd_3460485 < baseStart_3460485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460492 : List Nat := [2, 2, 1, 2, 1, 3, 4, 2, 1, 1, 4]
def baseStart_3460492 : Nat := 118140960795 + 3460492 * 2 ^ 59
def prefixEnd_3460492 : Nat := 4983230072969 + 3 ^ 40 * 3460492 * 2
def baseEnd_3460492 : Nat := 1776895697038580042835493

theorem tailTrace_3460492 : CollatzResearch.WordTrace tailWord_3460492 prefixEnd_3460492 1776895697038580042835493 := by
  unfold tailWord_3460492
  simp only [CollatzResearch.WordTrace]
  refine ⟨63107256089617981913199865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84143008119490642550933153 63107256089617981913199865)
  ·
    refine ⟨47330442067213486434899899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63107256089617981913199865 47330442067213486434899899)
    ·
      refine ⟨70995663100820229652349849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47330442067213486434899899 70995663100820229652349849)
      ·
        refine ⟨53246747325615172239262387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70995663100820229652349849 53246747325615172239262387)
        ·
          refine ⟨79870120988422758358893581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53246747325615172239262387 79870120988422758358893581)
          ·
            refine ⟨29951295370658534384585093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79870120988422758358893581 29951295370658534384585093)
            ·
              refine ⟨5615867881998475197109705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29951295370658534384585093 5615867881998475197109705)
              ·
                refine ⟨4211900911498856397832279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5615867881998475197109705 4211900911498856397832279)
                ·
                  refine ⟨6317851367248284596748419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4211900911498856397832279 6317851367248284596748419)
                  ·
                    refine ⟨9476777050872426895122629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6317851367248284596748419 9476777050872426895122629)
                    ·
                      refine ⟨1776895697038580042835493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9476777050872426895122629 1776895697038580042835493)
                      ·
                        rfl

theorem cell23_3460492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_3460492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460492 prefixEnd_3460492 := by exact prefixLift 3460492
  have htrace : WordTrace (prefixWord ++ tailWord_3460492) baseStart_3460492 baseEnd_3460492 := by
    simpa [prefixWord, tailWord_3460492, baseEnd_3460492] using wordTrace_append hprefix tailTrace_3460492
  have hstable : (prefixWord ++ tailWord_3460492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460492).length < 2 ^ (prefixWord ++ tailWord_3460492).sum := by decide
  have hdescent : baseEnd_3460492 < baseStart_3460492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460512 : List Nat := [2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 3]
def baseStart_3460512 : Nat := 118140960795 + 3460512 * 2 ^ 59
def prefixEnd_3460512 : Nat := 4983230072969 + 3 ^ 40 * 3460512 * 2
def baseEnd_3460512 : Nat := 1776905966651669964585401

theorem tailTrace_3460512 : CollatzResearch.WordTrace tailWord_3460512 prefixEnd_3460512 1776905966651669964585401 := by
  unfold tailWord_3460512
  simp only [CollatzResearch.WordTrace]
  refine ⟨63107620819581753621063895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84143494426109004828085193 63107620819581753621063895)
  ·
    refine ⟨94661431229372630431595843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63107620819581753621063895 94661431229372630431595843)
    ·
      refine ⟨141992146844058945647393765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94661431229372630431595843 141992146844058945647393765)
      ·
        refine ⟨26623527533261052308886331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141992146844058945647393765 26623527533261052308886331)
        ·
          refine ⟨39935291299891578463329497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26623527533261052308886331 39935291299891578463329497)
          ·
            refine ⟨29951468474918683847497123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39935291299891578463329497 29951468474918683847497123)
            ·
              refine ⟨44927202712378025771245685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29951468474918683847497123 44927202712378025771245685)
              ·
                refine ⟨4211925254285439916054283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44927202712378025771245685 4211925254285439916054283)
                ·
                  refine ⟨6317887881428159874081425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4211925254285439916054283 6317887881428159874081425)
                  ·
                    refine ⟨4738415911071119905561069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6317887881428159874081425 4738415911071119905561069)
                    ·
                      refine ⟨1776905966651669964585401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4738415911071119905561069 1776905966651669964585401)
                      ·
                        rfl

theorem cell23_3460512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_3460512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460512 prefixEnd_3460512 := by exact prefixLift 3460512
  have htrace : WordTrace (prefixWord ++ tailWord_3460512) baseStart_3460512 baseEnd_3460512 := by
    simpa [prefixWord, tailWord_3460512, baseEnd_3460512] using wordTrace_append hprefix tailTrace_3460512
  have hstable : (prefixWord ++ tailWord_3460512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460512).length < 2 ^ (prefixWord ++ tailWord_3460512).sum := by decide
  have hdescent : baseEnd_3460512 < baseStart_3460512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460520 : List Nat := [2, 1, 6, 1, 2, 1, 3, 2, 1, 1, 3]
def baseStart_3460520 : Nat := 118140960795 + 3460520 * 2 ^ 59
def prefixEnd_3460520 : Nat := 4983230072969 + 3 ^ 40 * 3460520 * 2
def baseEnd_3460520 : Nat := 1776910074496905933285365

theorem tailTrace_3460520 : CollatzResearch.WordTrace tailWord_3460520 prefixEnd_3460520 1776910074496905933285365 := by
  unfold tailWord_3460520
  simp only [CollatzResearch.WordTrace]
  refine ⟨63107766711567262304209507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84143688948756349738946009 63107766711567262304209507)
  ·
    refine ⟨94661650067350893456314261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63107766711567262304209507 94661650067350893456314261)
    ·
      refine ⟨4437264846907073130764731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 94661650067350893456314261 4437264846907073130764731)
      ·
        refine ⟨6655897270360609696147097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4437264846907073130764731 6655897270360609696147097)
        ·
          refine ⟨4991922952770457272110323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6655897270360609696147097 4991922952770457272110323)
          ·
            refine ⟨7487884429155685908165485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4991922952770457272110323 7487884429155685908165485)
            ·
              refine ⟨2807956660933382215562057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7487884429155685908165485 2807956660933382215562057)
              ·
                refine ⟨2105967495700036661671543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2807956660933382215562057 2105967495700036661671543)
                ·
                  refine ⟨3158951243550054992507315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2105967495700036661671543 3158951243550054992507315)
                  ·
                    refine ⟨4738426865325082488760973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3158951243550054992507315 4738426865325082488760973)
                    ·
                      refine ⟨1776910074496905933285365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4738426865325082488760973 1776910074496905933285365)
                      ·
                        rfl

theorem cell23_3460520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_3460520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460520 prefixEnd_3460520 := by exact prefixLift 3460520
  have htrace : WordTrace (prefixWord ++ tailWord_3460520) baseStart_3460520 baseEnd_3460520 := by
    simpa [prefixWord, tailWord_3460520, baseEnd_3460520] using wordTrace_append hprefix tailTrace_3460520
  have hstable : (prefixWord ++ tailWord_3460520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460520).length < 2 ^ (prefixWord ++ tailWord_3460520).sum := by decide
  have hdescent : baseEnd_3460520 < baseStart_3460520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460542 : List Nat := [4, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3]
def baseStart_3460542 : Nat := 118140960795 + 3460542 * 2 ^ 59
def prefixEnd_3460542 : Nat := 4983230072969 + 3 ^ 40 * 3460542 * 2
def baseEnd_3460542 : Nat := 1776921371071304847210263

theorem tailTrace_3460542 : CollatzResearch.WordTrace tailWord_3460542 prefixEnd_3460542 1776921371071304847210263 := by
  unfold tailWord_3460542
  simp only [CollatzResearch.WordTrace]
  refine ⟨15777041978631852795714985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84144223886036548243813253 15777041978631852795714985)
  ·
    refine ⟨11832781483973889596786239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15777041978631852795714985 11832781483973889596786239)
    ·
      refine ⟨17749172225960834395179359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11832781483973889596786239 17749172225960834395179359)
      ·
        refine ⟨26623758338941251592769039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17749172225960834395179359 26623758338941251592769039)
        ·
          refine ⟨39935637508411877389153559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26623758338941251592769039 39935637508411877389153559)
          ·
            refine ⟨59903456262617816083730339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39935637508411877389153559 59903456262617816083730339)
            ·
              refine ⟨89855184393926724125595509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59903456262617816083730339 89855184393926724125595509)
              ·
                refine ⟨8423923536930630386774579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89855184393926724125595509 8423923536930630386774579)
                ·
                  refine ⟨12635885305395945580161869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8423923536930630386774579 12635885305395945580161869)
                  ·
                    refine ⟨4738456989523479592560701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12635885305395945580161869 4738456989523479592560701)
                    ·
                      refine ⟨1776921371071304847210263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4738456989523479592560701 1776921371071304847210263)
                      ·
                        rfl

theorem cell23_3460542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_3460542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460542 prefixEnd_3460542 := by exact prefixLift 3460542
  have htrace : WordTrace (prefixWord ++ tailWord_3460542) baseStart_3460542 baseEnd_3460542 := by
    simpa [prefixWord, tailWord_3460542, baseEnd_3460542] using wordTrace_append hprefix tailTrace_3460542
  have hstable : (prefixWord ++ tailWord_3460542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460542).length < 2 ^ (prefixWord ++ tailWord_3460542).sum := by decide
  have hdescent : baseEnd_3460542 < baseStart_3460542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460575 : List Nat := [1, 1, 2, 3, 3, 1, 2, 2, 2, 6]
def baseStart_3460575 : Nat := 118140960795 + 3460575 * 2 ^ 59
def prefixEnd_3460575 : Nat := 4983230072969 + 3 ^ 40 * 3460575 * 2
def baseEnd_3460575 : Nat := 592312771977634406032537

theorem tailTrace_3460575 : CollatzResearch.WordTrace tailWord_3460575 prefixEnd_3460575 592312771977634406032537 := by
  unfold tailWord_3460575
  simp only [CollatzResearch.WordTrace]
  refine ⟨126217539437935269001671179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84145026291956846001114119 126217539437935269001671179)
  ·
    refine ⟨189326309156902903502506769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126217539437935269001671179 189326309156902903502506769)
    ·
      refine ⟨141994731867677177626880077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189326309156902903502506769 141994731867677177626880077)
      ·
        refine ⟨53248024450378941610080029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141994731867677177626880077 53248024450378941610080029)
        ·
          refine ⟨19968009168892103103780011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53248024450378941610080029 19968009168892103103780011)
          ·
            refine ⟨29952013753338154655670017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19968009168892103103780011 29952013753338154655670017)
            ·
              refine ⟨22464010315003615991752513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29952013753338154655670017 22464010315003615991752513)
              ·
                refine ⟨16848007736252711993814385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22464010315003615991752513 16848007736252711993814385)
                ·
                  refine ⟨12636005802189533995360789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16848007736252711993814385 12636005802189533995360789)
                  ·
                    refine ⟨592312771977634406032537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12636005802189533995360789 592312771977634406032537)
                    ·
                      rfl

theorem cell23_3460575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 6].length) (baseStart_3460575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460575 prefixEnd_3460575 := by exact prefixLift 3460575
  have htrace : WordTrace (prefixWord ++ tailWord_3460575) baseStart_3460575 baseEnd_3460575 := by
    simpa [prefixWord, tailWord_3460575, baseEnd_3460575] using wordTrace_append hprefix tailTrace_3460575
  have hstable : (prefixWord ++ tailWord_3460575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460575).length < 2 ^ (prefixWord ++ tailWord_3460575).sum := by decide
  have hdescent : baseEnd_3460575 < baseStart_3460575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460605 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 9]
def baseStart_3460605 : Nat := 118140960795 + 3460605 * 2 ^ 59
def prefixEnd_3460605 : Nat := 4983230072969 + 3 ^ 40 * 3460605 * 2
def baseEnd_3460605 : Nat := 197439302261393122302497

theorem tailTrace_3460605 : CollatzResearch.WordTrace tailWord_3460605 prefixEnd_3460605 197439302261393122302497 := by
  unfold tailWord_3460605
  simp only [CollatzResearch.WordTrace]
  refine ⟨126218633627826584125263269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84145755751884389416842179 126218633627826584125263269)
  ·
    refine ⟨23665993805217484523486863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126218633627826584125263269 23665993805217484523486863)
    ·
      refine ⟨35498990707826226785230295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23665993805217484523486863 35498990707826226785230295)
      ·
        refine ⟨53248486061739340177845443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35498990707826226785230295 53248486061739340177845443)
        ·
          refine ⟨79872729092609010266768165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53248486061739340177845443 79872729092609010266768165)
          ·
            refine ⟨14976136704864189425019031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79872729092609010266768165 14976136704864189425019031)
            ·
              refine ⟨22464205057296284137528547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14976136704864189425019031 22464205057296284137528547)
              ·
                refine ⟨33696307585944426206292821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22464205057296284137528547 33696307585944426206292821)
                ·
                  refine ⟨197439302261393122302497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33696307585944426206292821 197439302261393122302497)
                  ·
                    rfl

theorem cell23_3460605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 9].length) (baseStart_3460605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460605 prefixEnd_3460605 := by exact prefixLift 3460605
  have htrace : WordTrace (prefixWord ++ tailWord_3460605) baseStart_3460605 baseEnd_3460605 := by
    simpa [prefixWord, tailWord_3460605, baseEnd_3460605] using wordTrace_append hprefix tailTrace_3460605
  have hstable : (prefixWord ++ tailWord_3460605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460605).length < 2 ^ (prefixWord ++ tailWord_3460605).sum := by decide
  have hdescent : baseEnd_3460605 < baseStart_3460605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460614 : List Nat := [6, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3]
def baseStart_3460614 : Nat := 118140960795 + 3460614 * 2 ^ 59
def prefixEnd_3460614 : Nat := 4983230072969 + 3 ^ 40 * 3460614 * 2
def baseEnd_3460614 : Nat := 1776958341678428565509933

theorem tailTrace_3460614 : CollatzResearch.WordTrace tailWord_3460614 prefixEnd_3460614 1776958341678428565509933 := by
  unfold tailWord_3460614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3944342558899811833198153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84145974589862652441560597 3944342558899811833198153)
  ·
    refine ⟨2958256919174858874898615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3944342558899811833198153 2958256919174858874898615)
    ·
      refine ⟨4437385378762288312347923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2958256919174858874898615 4437385378762288312347923)
      ·
        refine ⟨6656078068143432468521885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4437385378762288312347923 6656078068143432468521885)
        ·
          refine ⟨2496029275553787175695707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6656078068143432468521885 2496029275553787175695707)
          ·
            refine ⟨3744043913330680763543561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2496029275553787175695707 3744043913330680763543561)
            ·
              refine ⟨2808032934998010572657671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3744043913330680763543561 2808032934998010572657671)
              ·
                refine ⟨4212049402497015858986507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2808032934998010572657671 4212049402497015858986507)
                ·
                  refine ⟨6318074103745523788479761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4212049402497015858986507 6318074103745523788479761)
                  ·
                    refine ⟨4738555577809142841359821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6318074103745523788479761 4738555577809142841359821)
                    ·
                      refine ⟨1776958341678428565509933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4738555577809142841359821 1776958341678428565509933)
                      ·
                        rfl

theorem cell23_3460614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_3460614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460614 prefixEnd_3460614 := by exact prefixLift 3460614
  have htrace : WordTrace (prefixWord ++ tailWord_3460614) baseStart_3460614 baseEnd_3460614 := by
    simpa [prefixWord, tailWord_3460614, baseEnd_3460614] using wordTrace_append hprefix tailTrace_3460614
  have hstable : (prefixWord ++ tailWord_3460614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460614).length < 2 ^ (prefixWord ++ tailWord_3460614).sum := by decide
  have hdescent : baseEnd_3460614 < baseStart_3460614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460620 : List Nat := [2, 2, 1, 2, 6, 1, 2, 1, 1, 3, 2]
def baseStart_3460620 : Nat := 118140960795 + 3460620 * 2 ^ 59
def prefixEnd_3460620 : Nat := 4983230072969 + 3 ^ 40 * 3460620 * 2
def baseEnd_3460620 : Nat := 1776961422562355542034905

theorem tailTrace_3460620 : CollatzResearch.WordTrace tailWord_3460620 prefixEnd_3460620 1776961422562355542034905 := by
  unfold tailWord_3460620
  simp only [CollatzResearch.WordTrace]
  refine ⟨63109590361386120843529657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84146120481848161124706209 63109590361386120843529657)
  ·
    refine ⟨47332192771039590632647243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63109590361386120843529657 47332192771039590632647243)
    ·
      refine ⟨70998289156559385948970865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47332192771039590632647243 70998289156559385948970865)
      ·
        refine ⟨53248716867419539461728149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70998289156559385948970865 53248716867419539461728149)
        ·
          refine ⟨2496033603160290912268507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53248716867419539461728149 2496033603160290912268507)
          ·
            refine ⟨3744050404740436368402761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2496033603160290912268507 3744050404740436368402761)
            ·
              refine ⟨2808037803555327276302071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3744050404740436368402761 2808037803555327276302071)
              ·
                refine ⟨4212056705332990914453107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2808037803555327276302071 4212056705332990914453107)
                ·
                  refine ⟨6318085057999486371679661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4212056705332990914453107 6318085057999486371679661)
                  ·
                    refine ⟨2369281896749807389379873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6318085057999486371679661 2369281896749807389379873)
                    ·
                      refine ⟨1776961422562355542034905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2369281896749807389379873 1776961422562355542034905)
                      ·
                        rfl

theorem cell23_3460620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 1, 3, 2].length) (baseStart_3460620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460620 prefixEnd_3460620 := by exact prefixLift 3460620
  have htrace : WordTrace (prefixWord ++ tailWord_3460620) baseStart_3460620 baseEnd_3460620 := by
    simpa [prefixWord, tailWord_3460620, baseEnd_3460620] using wordTrace_append hprefix tailTrace_3460620
  have hstable : (prefixWord ++ tailWord_3460620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460620).length < 2 ^ (prefixWord ++ tailWord_3460620).sum := by decide
  have hdescent : baseEnd_3460620 < baseStart_3460620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460645 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 1, 1, 7]
def baseStart_3460645 : Nat := 118140960795 + 3460645 * 2 ^ 59
def prefixEnd_3460645 : Nat := 4983230072969 + 3 ^ 40 * 3460645 * 2
def baseEnd_3460645 : Nat := 1776974259578717944222289

theorem tailTrace_3460645 : CollatzResearch.WordTrace tailWord_3460645 prefixEnd_3460645 1776974259578717944222289 := by
  unfold tailWord_3460645
  simp only [CollatzResearch.WordTrace]
  refine ⟨126220092547681670956719389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84146728365121113971146259 126220092547681670956719389)
  ·
    refine ⟨47332534705380626608769771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126220092547681670956719389 47332534705380626608769771)
    ·
      refine ⟨70998802058070939913154657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47332534705380626608769771 70998802058070939913154657)
      ·
        refine ⟨53249101543553204934865993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70998802058070939913154657 53249101543553204934865993)
        ·
          refine ⟨39936826157664903701149495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53249101543553204934865993 39936826157664903701149495)
          ·
            refine ⟨59905239236497355551724243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39936826157664903701149495 59905239236497355551724243)
            ·
              refine ⟨89857858854746033327586365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59905239236497355551724243 89857858854746033327586365)
              ·
                refine ⟨33696697070529762497844887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89857858854746033327586365 33696697070529762497844887)
                ·
                  refine ⟨50545045605794643746767331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33696697070529762497844887 50545045605794643746767331)
                  ·
                    refine ⟨75817568408691965620150997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50545045605794643746767331 75817568408691965620150997)
                    ·
                      refine ⟨1776974259578717944222289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 75817568408691965620150997 1776974259578717944222289)
                      ·
                        rfl

theorem cell23_3460645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_3460645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460645 prefixEnd_3460645 := by exact prefixLift 3460645
  have htrace : WordTrace (prefixWord ++ tailWord_3460645) baseStart_3460645 baseEnd_3460645 := by
    simpa [prefixWord, tailWord_3460645, baseEnd_3460645] using wordTrace_append hprefix tailTrace_3460645
  have hstable : (prefixWord ++ tailWord_3460645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460645).length < 2 ^ (prefixWord ++ tailWord_3460645).sum := by decide
  have hdescent : baseEnd_3460645 < baseStart_3460645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460672 : List Nat := [2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 4]
def baseStart_3460672 : Nat := 118140960795 + 3460672 * 2 ^ 59
def prefixEnd_3460672 : Nat := 4983230072969 + 3 ^ 40 * 3460672 * 2
def baseEnd_3460672 : Nat := 1776988123556389338584665

theorem tailTrace_3460672 : CollatzResearch.WordTrace tailWord_3460672 prefixEnd_3460672 1776988123556389338584665 := by
  unfold tailWord_3460672
  simp only [CollatzResearch.WordTrace]
  refine ⟨63110538659291927283976135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84147384879055903045301513 63110538659291927283976135)
  ·
    refine ⟨94665807988937890925964203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63110538659291927283976135 94665807988937890925964203)
    ·
      refine ⟨141998711983406836388946305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94665807988937890925964203 141998711983406836388946305)
      ·
        refine ⟨106499033987555127291709729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141998711983406836388946305 106499033987555127291709729)
        ·
          refine ⟨79874275490666345468782297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106499033987555127291709729 79874275490666345468782297)
          ·
            refine ⟨59905706617999759101586723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79874275490666345468782297 59905706617999759101586723)
            ·
              refine ⟨89858559926999638652380085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59905706617999759101586723 89858559926999638652380085)
              ·
                refine ⟨8424239993156216123660633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89858559926999638652380085 8424239993156216123660633)
                ·
                  refine ⟨6318179994867162092745475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8424239993156216123660633 6318179994867162092745475)
                  ·
                    refine ⟨9477269992300743139118213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6318179994867162092745475 9477269992300743139118213)
                    ·
                      refine ⟨1776988123556389338584665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9477269992300743139118213 1776988123556389338584665)
                      ·
                        rfl

theorem cell23_3460672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_3460672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460672 prefixEnd_3460672 := by exact prefixLift 3460672
  have htrace : WordTrace (prefixWord ++ tailWord_3460672) baseStart_3460672 baseEnd_3460672 := by
    simpa [prefixWord, tailWord_3460672, baseEnd_3460672] using wordTrace_append hprefix tailTrace_3460672
  have hstable : (prefixWord ++ tailWord_3460672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460672).length < 2 ^ (prefixWord ++ tailWord_3460672).sum := by decide
  have hdescent : baseEnd_3460672 < baseStart_3460672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460675 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 5]
def baseStart_3460675 : Nat := 118140960795 + 3460675 * 2 ^ 59
def prefixEnd_3460675 : Nat := 4983230072969 + 3 ^ 40 * 3460675 * 2
def baseEnd_3460675 : Nat := 1776989663998352826847151

theorem tailTrace_3460675 : CollatzResearch.WordTrace tailWord_3460675 prefixEnd_3460675 1776989663998352826847151 := by
  unfold tailWord_3460675
  simp only [CollatzResearch.WordTrace]
  refine ⟨126221186737572986080311479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84147457825048657386874319 126221186737572986080311479)
  ·
    refine ⟨189331780106359479120467219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126221186737572986080311479 189331780106359479120467219)
    ·
      refine ⟨283997670159539218680700829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189331780106359479120467219 283997670159539218680700829)
      ·
        refine ⟨106499126309827207005262811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283997670159539218680700829 106499126309827207005262811)
        ·
          refine ⟨159748689464740810507894217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106499126309827207005262811 159748689464740810507894217)
          ·
            refine ⟨119811517098555607880920663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159748689464740810507894217 119811517098555607880920663)
            ·
              refine ⟨179717275647833411821380995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119811517098555607880920663 179717275647833411821380995)
              ·
                refine ⟨269575913471750117732071493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179717275647833411821380995 269575913471750117732071493)
                ·
                  refine ⟨50545483775953147074763405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 269575913471750117732071493 50545483775953147074763405)
                  ·
                    refine ⟨18954556415982430153036277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50545483775953147074763405 18954556415982430153036277)
                    ·
                      refine ⟨1776989663998352826847151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18954556415982430153036277 1776989663998352826847151)
                      ·
                        rfl

theorem cell23_3460675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_3460675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460675 prefixEnd_3460675 := by exact prefixLift 3460675
  have htrace : WordTrace (prefixWord ++ tailWord_3460675) baseStart_3460675 baseEnd_3460675 := by
    simpa [prefixWord, tailWord_3460675, baseEnd_3460675] using wordTrace_append hprefix tailTrace_3460675
  have hstable : (prefixWord ++ tailWord_3460675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460675).length < 2 ^ (prefixWord ++ tailWord_3460675).sum := by decide
  have hdescent : baseEnd_3460675 < baseStart_3460675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460715 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 8]
def baseStart_3460715 : Nat := 118140960795 + 3460715 * 2 ^ 59
def prefixEnd_3460715 : Nat := 4983230072969 + 3 ^ 40 * 3460715 * 2
def baseEnd_3460715 : Nat := 1777010203224532670346967

theorem tailTrace_3460715 : CollatzResearch.WordTrace tailWord_3460715 prefixEnd_3460715 1777010203224532670346967 := by
  unfold tailWord_3460715
  simp only [CollatzResearch.WordTrace]
  refine ⟨126222645657428072911767599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84148430438285381941178399 126222645657428072911767599)
  ·
    refine ⟨189333968486142109367651399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126222645657428072911767599 189333968486142109367651399)
    ·
      refine ⟨284000952729213164051477099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189333968486142109367651399 284000952729213164051477099)
      ·
        refine ⟨426001429093819746077215649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284000952729213164051477099 426001429093819746077215649)
        ·
          refine ⟨319501071820364809557911737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426001429093819746077215649 319501071820364809557911737)
          ·
            refine ⟨239625803865273607168433803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319501071820364809557911737 239625803865273607168433803)
            ·
              refine ⟨359438705797910410752650705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239625803865273607168433803 359438705797910410752650705)
              ·
                refine ⟨269579029348432808064488029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359438705797910410752650705 269579029348432808064488029)
                ·
                  refine ⟨101092136005662303024183011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269579029348432808064488029 101092136005662303024183011)
                  ·
                    refine ⟨151638204008493454536274517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101092136005662303024183011 151638204008493454536274517)
                    ·
                      refine ⟨1777010203224532670346967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 151638204008493454536274517 1777010203224532670346967)
                      ·
                        rfl

theorem cell23_3460715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 8].length) (baseStart_3460715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460715 prefixEnd_3460715 := by exact prefixLift 3460715
  have htrace : WordTrace (prefixWord ++ tailWord_3460715) baseStart_3460715 baseEnd_3460715 := by
    simpa [prefixWord, tailWord_3460715, baseEnd_3460715] using wordTrace_append hprefix tailTrace_3460715
  have hstable : (prefixWord ++ tailWord_3460715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460715).length < 2 ^ (prefixWord ++ tailWord_3460715).sum := by decide
  have hdescent : baseEnd_3460715 < baseStart_3460715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460726 : List Nat := [5, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3]
def baseStart_3460726 : Nat := 118140960795 + 3460726 * 2 ^ 59
def prefixEnd_3460726 : Nat := 4983230072969 + 3 ^ 40 * 3460726 * 2
def baseEnd_3460726 : Nat := 1777015851511732127309417

theorem tailTrace_3460726 : CollatzResearch.WordTrace tailWord_3460726 prefixEnd_3460726 1777015851511732127309417 := by
  unfold tailWord_3460726
  simp only [CollatzResearch.WordTrace]
  refine ⟨7888940428774263861901127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84148697906925481193612021 7888940428774263861901127)
  ·
    refine ⟨11833410643161395792851691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7888940428774263861901127 11833410643161395792851691)
    ·
      refine ⟨17750115964742093689277537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11833410643161395792851691 17750115964742093689277537)
      ·
        refine ⟨13312586973556570266958153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17750115964742093689277537 13312586973556570266958153)
        ·
          refine ⟨9984440230167427700218615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13312586973556570266958153 9984440230167427700218615)
          ·
            refine ⟨14976660345251141550327923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9984440230167427700218615 14976660345251141550327923)
            ·
              refine ⟨22464990517876712325491885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14976660345251141550327923 22464990517876712325491885)
              ·
                refine ⟨8424371444203767122059457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22464990517876712325491885 8424371444203767122059457)
                ·
                  refine ⟨6318278583152825341544593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8424371444203767122059457 6318278583152825341544593)
                  ·
                    refine ⟨4738708937364619006158445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6318278583152825341544593 4738708937364619006158445)
                    ·
                      refine ⟨1777015851511732127309417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4738708937364619006158445 1777015851511732127309417)
                      ·
                        rfl

theorem cell23_3460726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_3460726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460726 prefixEnd_3460726 := by exact prefixLift 3460726
  have htrace : WordTrace (prefixWord ++ tailWord_3460726) baseStart_3460726 baseEnd_3460726 := by
    simpa [prefixWord, tailWord_3460726, baseEnd_3460726] using wordTrace_append hprefix tailTrace_3460726
  have hstable : (prefixWord ++ tailWord_3460726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460726).length < 2 ^ (prefixWord ++ tailWord_3460726).sum := by decide
  have hdescent : baseEnd_3460726 < baseStart_3460726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460750 : List Nat := [4, 1, 1, 3, 1, 4, 2, 2, 1, 4]
def baseStart_3460750 : Nat := 118140960795 + 3460750 * 2 ^ 59
def prefixEnd_3460750 : Nat := 4983230072969 + 3 ^ 40 * 3460750 * 2
def baseEnd_3460750 : Nat := 592342725015813344469769

theorem tailTrace_3460750 : CollatzResearch.WordTrace tailWord_3460750 prefixEnd_3460750 592342725015813344469769 := by
  unfold tailWord_3460750
  simp only [CollatzResearch.WordTrace]
  refine ⟨15777990276537659236161463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84149281474867515926194469 15777990276537659236161463)
  ·
    refine ⟨23666985414806488854242195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15777990276537659236161463 23666985414806488854242195)
    ·
      refine ⟨35500478122209733281363293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23666985414806488854242195 35500478122209733281363293)
      ·
        refine ⟨13312679295828649980511235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35500478122209733281363293 13312679295828649980511235)
        ·
          refine ⟨19969018943742974970766853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13312679295828649980511235 19969018943742974970766853)
          ·
            refine ⟨3744191051951807807018785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19969018943742974970766853 3744191051951807807018785)
            ·
              refine ⟨2808143288963855855264089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3744191051951807807018785 2808143288963855855264089)
              ·
                refine ⟨2106107466722891891448067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2808143288963855855264089 2106107466722891891448067)
                ·
                  refine ⟨3159161200084337837172101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2106107466722891891448067 3159161200084337837172101)
                  ·
                    refine ⟨592342725015813344469769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3159161200084337837172101 592342725015813344469769)
                    ·
                      rfl

theorem cell23_3460750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_3460750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460750 prefixEnd_3460750 := by exact prefixLift 3460750
  have htrace : WordTrace (prefixWord ++ tailWord_3460750) baseStart_3460750 baseEnd_3460750 := by
    simpa [prefixWord, tailWord_3460750, baseEnd_3460750] using wordTrace_append hprefix tailTrace_3460750
  have hstable : (prefixWord ++ tailWord_3460750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460750).length < 2 ^ (prefixWord ++ tailWord_3460750).sum := by decide
  have hdescent : baseEnd_3460750 < baseStart_3460750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460796 : List Nat := [2, 2, 2, 3, 1, 3, 1, 3, 1, 1, 4]
def baseStart_3460796 : Nat := 118140960795 + 3460796 * 2 ^ 59
def prefixEnd_3460796 : Nat := 4983230072969 + 3 ^ 40 * 3460796 * 2
def baseEnd_3460796 : Nat := 1777051795157546853434095

theorem tailTrace_3460796 : CollatzResearch.WordTrace tailWord_3460796 prefixEnd_3460796 1777051795157546853434095 := by
  unfold tailWord_3460796
  simp only [CollatzResearch.WordTrace]
  refine ⟨63112799985067311872733121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84150399980089749163644161 63112799985067311872733121)
  ·
    refine ⟨47334599988800483904549841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63112799985067311872733121 47334599988800483904549841)
    ·
      refine ⟨35500949991600362928412381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47334599988800483904549841 35500949991600362928412381)
      ·
        refine ⟨13312856246850136098154643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35500949991600362928412381 13312856246850136098154643)
        ·
          refine ⟨19969284370275204147231965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13312856246850136098154643 19969284370275204147231965)
          ·
            refine ⟨7488481638853201555211987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19969284370275204147231965 7488481638853201555211987)
            ·
              refine ⟨11232722458279802332817981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7488481638853201555211987 11232722458279802332817981)
              ·
                refine ⟨4212270921854925874806743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11232722458279802332817981 4212270921854925874806743)
                ·
                  refine ⟨6318406382782388812210115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4212270921854925874806743 6318406382782388812210115)
                  ·
                    refine ⟨9477609574173583218315173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6318406382782388812210115 9477609574173583218315173)
                    ·
                      refine ⟨1777051795157546853434095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9477609574173583218315173 1777051795157546853434095)
                      ·
                        rfl

theorem cell23_3460796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_3460796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460796 prefixEnd_3460796 := by exact prefixLift 3460796
  have htrace : WordTrace (prefixWord ++ tailWord_3460796) baseStart_3460796 baseEnd_3460796 := by
    simpa [prefixWord, tailWord_3460796, baseEnd_3460796] using wordTrace_append hprefix tailTrace_3460796
  have hstable : (prefixWord ++ tailWord_3460796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460796).length < 2 ^ (prefixWord ++ tailWord_3460796).sum := by decide
  have hdescent : baseEnd_3460796 < baseStart_3460796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460826 : List Nat := [3, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4]
def baseStart_3460826 : Nat := 118140960795 + 3460826 * 2 ^ 59
def prefixEnd_3460826 : Nat := 4983230072969 + 3 ^ 40 * 3460826 * 2
def baseEnd_3460826 : Nat := 1777067199577181736058957

theorem tailTrace_3460826 : CollatzResearch.WordTrace tailWord_3460826 prefixEnd_3460826 1777067199577181736058957 := by
  unfold tailWord_3460826
  simp only [CollatzResearch.WordTrace]
  refine ⟨31556673540006484717264583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84151129440017292579372221 31556673540006484717264583)
  ·
    refine ⟨47335010310009727075896875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31556673540006484717264583 47335010310009727075896875)
    ·
      refine ⟨71002515465014590613845313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47335010310009727075896875 71002515465014590613845313)
      ·
        refine ⟨53251886598760942960383985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71002515465014590613845313 53251886598760942960383985)
        ·
          refine ⟨39938914949070707220287989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53251886598760942960383985 39938914949070707220287989)
          ·
            refine ⟨3744273276475378801901999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39938914949070707220287989 3744273276475378801901999)
            ·
              refine ⟨5616409914713068202852999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3744273276475378801901999 5616409914713068202852999)
              ·
                refine ⟨8424614872069602304279499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5616409914713068202852999 8424614872069602304279499)
                ·
                  refine ⟨12636922308104403456419249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8424614872069602304279499 12636922308104403456419249)
                  ·
                    refine ⟨9477691731078302592314437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12636922308104403456419249 9477691731078302592314437)
                    ·
                      refine ⟨1777067199577181736058957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9477691731078302592314437 1777067199577181736058957)
                      ·
                        rfl

theorem cell23_3460826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_3460826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460826 prefixEnd_3460826 := by exact prefixLift 3460826
  have htrace : WordTrace (prefixWord ++ tailWord_3460826) baseStart_3460826 baseEnd_3460826 := by
    simpa [prefixWord, tailWord_3460826, baseEnd_3460826] using wordTrace_append hprefix tailTrace_3460826
  have hstable : (prefixWord ++ tailWord_3460826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460826).length < 2 ^ (prefixWord ++ tailWord_3460826).sum := by decide
  have hdescent : baseEnd_3460826 < baseStart_3460826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460832 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 2, 7]
def baseStart_3460832 : Nat := 118140960795 + 3460832 * 2 ^ 59
def prefixEnd_3460832 : Nat := 4983230072969 + 3 ^ 40 * 3460832 * 2
def baseEnd_3460832 : Nat := 592356760153702904194643

theorem tailTrace_3460832 : CollatzResearch.WordTrace tailWord_3460832 prefixEnd_3460832 592356760153702904194643 := by
  unfold tailWord_3460832
  simp only [CollatzResearch.WordTrace]
  refine ⟨63113456499002100946888375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84151275332002801262517833 63113456499002100946888375)
  ·
    refine ⟨94670184748503151420332563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63113456499002100946888375 94670184748503151420332563)
    ·
      refine ⟨142005277122754727130498845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94670184748503151420332563 142005277122754727130498845)
      ·
        refine ⟨53251978921033022673937067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142005277122754727130498845 53251978921033022673937067)
        ·
          refine ⟨79877968381549534010905601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53251978921033022673937067 79877968381549534010905601)
          ·
            refine ⟨59908476286162150508179201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79877968381549534010905601 59908476286162150508179201)
            ·
              refine ⟨44931357214621612881134401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59908476286162150508179201 44931357214621612881134401)
              ·
                refine ⟨33698517910966209660850801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44931357214621612881134401 33698517910966209660850801)
                ·
                  refine ⟨25273888433224657245638101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33698517910966209660850801 25273888433224657245638101)
                  ·
                    refine ⟨592356760153702904194643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25273888433224657245638101 592356760153702904194643)
                    ·
                      rfl

theorem cell23_3460832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 2, 7].length) (baseStart_3460832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460832 prefixEnd_3460832 := by exact prefixLift 3460832
  have htrace : WordTrace (prefixWord ++ tailWord_3460832) baseStart_3460832 baseEnd_3460832 := by
    simpa [prefixWord, tailWord_3460832, baseEnd_3460832] using wordTrace_append hprefix tailTrace_3460832
  have hstable : (prefixWord ++ tailWord_3460832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460832).length < 2 ^ (prefixWord ++ tailWord_3460832).sum := by decide
  have hdescent : baseEnd_3460832 < baseStart_3460832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460833 : List Nat := [1, 2, 3, 1, 5, 1, 2, 2, 1, 2, 3]
def baseStart_3460833 : Nat := 118140960795 + 3460833 * 2 ^ 59
def prefixEnd_3460833 : Nat := 4983230072969 + 3 ^ 40 * 3460833 * 2
def baseEnd_3460833 : Nat := 1777070793941763208671425

theorem tailTrace_3460833 : CollatzResearch.WordTrace tailWord_3460833 prefixEnd_3460833 1777070793941763208671425 := by
  unfold tailWord_3460833
  simp only [CollatzResearch.WordTrace]
  refine ⟨126226949471000579064563153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84151299647333719376375435 126226949471000579064563153)
  ·
    refine ⟨94670212103250434298422365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126226949471000579064563153 94670212103250434298422365)
    ·
      refine ⟨35501329538718912861908387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94670212103250434298422365 35501329538718912861908387)
      ·
        refine ⟨53251994308078369292862581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35501329538718912861908387 53251994308078369292862581)
        ·
          refine ⟨4992374466382347121205867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53251994308078369292862581 4992374466382347121205867)
          ·
            refine ⟨7488561699573520681808801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4992374466382347121205867 7488561699573520681808801)
            ·
              refine ⟨5616421274680140511356601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7488561699573520681808801 5616421274680140511356601)
              ·
                refine ⟨4212315956010105383517451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5616421274680140511356601 4212315956010105383517451)
                ·
                  refine ⟨6318473934015158075276177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4212315956010105383517451 6318473934015158075276177)
                  ·
                    refine ⟨4738855450511368556457133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6318473934015158075276177 4738855450511368556457133)
                    ·
                      refine ⟨1777070793941763208671425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4738855450511368556457133 1777070793941763208671425)
                      ·
                        rfl

theorem cell23_3460833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_3460833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460833 prefixEnd_3460833 := by exact prefixLift 3460833
  have htrace : WordTrace (prefixWord ++ tailWord_3460833) baseStart_3460833 baseEnd_3460833 := by
    simpa [prefixWord, tailWord_3460833, baseEnd_3460833] using wordTrace_append hprefix tailTrace_3460833
  have hstable : (prefixWord ++ tailWord_3460833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460833).length < 2 ^ (prefixWord ++ tailWord_3460833).sum := by decide
  have hdescent : baseEnd_3460833 < baseStart_3460833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460846 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 6, 1, 3]
def baseStart_3460846 : Nat := 118140960795 + 3460846 * 2 ^ 59
def prefixEnd_3460846 : Nat := 4983230072969 + 3 ^ 40 * 3460846 * 2
def baseEnd_3460846 : Nat := 1777077469190271657808865

theorem tailTrace_3460846 : CollatzResearch.WordTrace tailWord_3460846 prefixEnd_3460846 1777077469190271657808865 := by
  unfold tailWord_3460846
  simp only [CollatzResearch.WordTrace]
  refine ⟨15778427952494185285598299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84151615746635654856524261 15778427952494185285598299)
  ·
    refine ⟨23667641928741277928397449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15778427952494185285598299 23667641928741277928397449)
    ·
      refine ⟨17750731446555958446298087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23667641928741277928397449 17750731446555958446298087)
      ·
        refine ⟨26626097169833937669447131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17750731446555958446298087 26626097169833937669447131)
        ·
          refine ⟨39939145754750906504170697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26626097169833937669447131 39939145754750906504170697)
          ·
            refine ⟨29954359316063179878128023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39939145754750906504170697 29954359316063179878128023)
            ·
              refine ⟨44931538974094769817192035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29954359316063179878128023 44931538974094769817192035)
              ·
                refine ⟨67397308461142154725788053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44931538974094769817192035 67397308461142154725788053)
                ·
                  refine ⟨3159248834116038502771315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67397308461142154725788053 3159248834116038502771315)
                  ·
                    refine ⟨4738873251174057754156973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3159248834116038502771315 4738873251174057754156973)
                    ·
                      refine ⟨1777077469190271657808865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4738873251174057754156973 1777077469190271657808865)
                      ·
                        rfl

theorem cell23_3460846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_3460846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460846 prefixEnd_3460846 := by exact prefixLift 3460846
  have htrace : WordTrace (prefixWord ++ tailWord_3460846) baseStart_3460846 baseEnd_3460846 := by
    simpa [prefixWord, tailWord_3460846, baseEnd_3460846] using wordTrace_append hprefix tailTrace_3460846
  have hstable : (prefixWord ++ tailWord_3460846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460846).length < 2 ^ (prefixWord ++ tailWord_3460846).sum := by decide
  have hdescent : baseEnd_3460846 < baseStart_3460846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460884 : List Nat := [2, 4, 4, 1, 1, 2, 1, 2, 1, 2, 3]
def baseStart_3460884 : Nat := 118140960795 + 3460884 * 2 ^ 59
def prefixEnd_3460884 : Nat := 4983230072969 + 3 ^ 40 * 3460884 * 2
def baseEnd_3460884 : Nat := 1777096981455142509133691

theorem tailTrace_3460884 : CollatzResearch.WordTrace tailWord_3460884 prefixEnd_3460884 1777096981455142509133691 := by
  unfold tailWord_3460884
  simp only [CollatzResearch.WordTrace]
  refine ⟨63114404796907907387334853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84152539729210543183113137 63114404796907907387334853)
  ·
    refine ⟨11833950899420232635125285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63114404796907907387334853 11833950899420232635125285)
    ·
      refine ⟨2218865793641293619085991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11833950899420232635125285 2218865793641293619085991)
      ·
        refine ⟨3328298690461940428628987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2218865793641293619085991 3328298690461940428628987)
        ·
          refine ⟨4992448035692910642943481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3328298690461940428628987 4992448035692910642943481)
          ·
            refine ⟨3744336026769682982207611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4992448035692910642943481 3744336026769682982207611)
            ·
              refine ⟨5616504040154524473311417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3744336026769682982207611 5616504040154524473311417)
              ·
                refine ⟨4212378030115893354983563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5616504040154524473311417 4212378030115893354983563)
                ·
                  refine ⟨6318567045173840032475345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4212378030115893354983563 6318567045173840032475345)
                  ·
                    refine ⟨4738925283880380024356509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6318567045173840032475345 4738925283880380024356509)
                    ·
                      refine ⟨1777096981455142509133691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4738925283880380024356509 1777096981455142509133691)
                      ·
                        rfl

theorem cell23_3460884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_3460884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460884 prefixEnd_3460884 := by exact prefixLift 3460884
  have htrace : WordTrace (prefixWord ++ tailWord_3460884) baseStart_3460884 baseEnd_3460884 := by
    simpa [prefixWord, tailWord_3460884, baseEnd_3460884] using wordTrace_append hprefix tailTrace_3460884
  have hstable : (prefixWord ++ tailWord_3460884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460884).length < 2 ^ (prefixWord ++ tailWord_3460884).sum := by decide
  have hdescent : baseEnd_3460884 < baseStart_3460884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460890 : List Nat := [3, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2]
def baseStart_3460890 : Nat := 118140960795 + 3460890 * 2 ^ 59
def prefixEnd_3460890 : Nat := 4983230072969 + 3 ^ 40 * 3460890 * 2
def baseEnd_3460890 : Nat := 1777100062339069485658663

theorem tailTrace_3460890 : CollatzResearch.WordTrace tailWord_3460890 prefixEnd_3460890 1777100062339069485658663 := by
  unfold tailWord_3460890
  simp only [CollatzResearch.WordTrace]
  refine ⟨31557257107948519449847031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84152685621196051866258749 31557257107948519449847031)
  ·
    refine ⟨47335885661922779174770547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31557257107948519449847031 47335885661922779174770547)
    ·
      refine ⟨71003828492884168762155821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47335885661922779174770547 71003828492884168762155821)
      ·
        refine ⟨26626435684831563285808433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71003828492884168762155821 26626435684831563285808433)
        ·
          refine ⟨19969826763623672464356325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26626435684831563285808433 19969826763623672464356325)
          ·
            refine ⟨3744342518179438587066811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19969826763623672464356325 3744342518179438587066811)
            ·
              refine ⟨5616513777269157880600217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3744342518179438587066811 5616513777269157880600217)
              ·
                refine ⟨4212385332951868410450163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5616513777269157880600217 4212385332951868410450163)
                ·
                  refine ⟨6318577999427802615675245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4212385332951868410450163 6318577999427802615675245)
                  ·
                    refine ⟨2369466749785425980878217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6318577999427802615675245 2369466749785425980878217)
                    ·
                      refine ⟨1777100062339069485658663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2369466749785425980878217 1777100062339069485658663)
                      ·
                        rfl

theorem cell23_3460890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_3460890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460890 prefixEnd_3460890 := by exact prefixLift 3460890
  have htrace : WordTrace (prefixWord ++ tailWord_3460890) baseStart_3460890 baseEnd_3460890 := by
    simpa [prefixWord, tailWord_3460890, baseEnd_3460890] using wordTrace_append hprefix tailTrace_3460890
  have hstable : (prefixWord ++ tailWord_3460890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460890).length < 2 ^ (prefixWord ++ tailWord_3460890).sum := by decide
  have hdescent : baseEnd_3460890 < baseStart_3460890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460920 : List Nat := [2, 1, 2, 1, 3, 4, 2, 2, 2, 2, 2]
def baseStart_3460920 : Nat := 118140960795 + 3460920 * 2 ^ 59
def prefixEnd_3460920 : Nat := 4983230072969 + 3 ^ 40 * 3460920 * 2
def baseEnd_3460920 : Nat := 1777115466758704368283525

theorem tailTrace_3460920 : CollatzResearch.WordTrace tailWord_3460920 prefixEnd_3460920 1777115466758704368283525 := by
  unfold tailWord_3460920
  simp only [CollatzResearch.WordTrace]
  refine ⟨63115061310842696461490107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84153415081123595281986809 63115061310842696461490107)
  ·
    refine ⟨94672591966264044692235161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63115061310842696461490107 94672591966264044692235161)
    ·
      refine ⟨71004443974698033519176371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94672591966264044692235161 71004443974698033519176371)
      ·
        refine ⟨106506665962047050278764557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71004443974698033519176371 106506665962047050278764557)
        ·
          refine ⟨39939999735767643854536709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106506665962047050278764557 39939999735767643854536709)
          ·
            refine ⟨7488749950456433222725633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39939999735767643854536709 7488749950456433222725633)
            ·
              refine ⟨5616562462842324917044225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7488749950456433222725633 5616562462842324917044225)
              ·
                refine ⟨4212421847131743687783169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5616562462842324917044225 4212421847131743687783169)
                ·
                  refine ⟨3159316385348807765837377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4212421847131743687783169 3159316385348807765837377)
                  ·
                    refine ⟨2369487289011605824378033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3159316385348807765837377 2369487289011605824378033)
                    ·
                      refine ⟨1777115466758704368283525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2369487289011605824378033 1777115466758704368283525)
                      ·
                        rfl

theorem cell23_3460920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 2, 2, 2].length) (baseStart_3460920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460920 prefixEnd_3460920 := by exact prefixLift 3460920
  have htrace : WordTrace (prefixWord ++ tailWord_3460920) baseStart_3460920 baseEnd_3460920 := by
    simpa [prefixWord, tailWord_3460920, baseEnd_3460920] using wordTrace_append hprefix tailTrace_3460920
  have hstable : (prefixWord ++ tailWord_3460920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460920).length < 2 ^ (prefixWord ++ tailWord_3460920).sum := by decide
  have hdescent : baseEnd_3460920 < baseStart_3460920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460936 : List Nat := [2, 1, 3, 1, 1, 5, 1, 1, 2, 3, 3]
def baseStart_3460936 : Nat := 118140960795 + 3460936 * 2 ^ 59
def prefixEnd_3460936 : Nat := 4983230072969 + 3 ^ 40 * 3460936 * 2
def baseEnd_3460936 : Nat := 1777123682449176305683451

theorem tailTrace_3460936 : CollatzResearch.WordTrace tailWord_3460936 prefixEnd_3460936 1777123682449176305683451 := by
  unfold tailWord_3460936
  simp only [CollatzResearch.WordTrace]
  refine ⟨63115353094813713827781331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84153804126418285103708441 63115353094813713827781331)
  ·
    refine ⟨94673029642220570741671997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63115353094813713827781331 94673029642220570741671997)
    ·
      refine ⟨35502386115832714028126999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94673029642220570741671997 35502386115832714028126999)
      ·
        refine ⟨53253579173749071042190499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35502386115832714028126999 53253579173749071042190499)
        ·
          refine ⟨79880368760623606563285749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53253579173749071042190499 79880368760623606563285749)
          ·
            refine ⟨7488784571308463115308039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79880368760623606563285749 7488784571308463115308039)
            ·
              refine ⟨11233176856962694672962059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7488784571308463115308039 11233176856962694672962059)
              ·
                refine ⟨16849765285444042009443089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11233176856962694672962059 16849765285444042009443089)
                ·
                  refine ⟨12637323964083031507082317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16849765285444042009443089 12637323964083031507082317)
                  ·
                    refine ⟨4738996486531136815155869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12637323964083031507082317 4738996486531136815155869)
                    ·
                      refine ⟨1777123682449176305683451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4738996486531136815155869 1777123682449176305683451)
                      ·
                        rfl

theorem cell23_3460936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_3460936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460936 prefixEnd_3460936 := by exact prefixLift 3460936
  have htrace : WordTrace (prefixWord ++ tailWord_3460936) baseStart_3460936 baseEnd_3460936 := by
    simpa [prefixWord, tailWord_3460936, baseEnd_3460936] using wordTrace_append hprefix tailTrace_3460936
  have hstable : (prefixWord ++ tailWord_3460936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460936).length < 2 ^ (prefixWord ++ tailWord_3460936).sum := by decide
  have hdescent : baseEnd_3460936 < baseStart_3460936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460986 : List Nat := [3, 1, 1, 1, 1, 1, 5, 3, 3, 4]
def baseStart_3460986 : Nat := 118140960795 + 3460986 * 2 ^ 59
def prefixEnd_3460986 : Nat := 4983230072969 + 3 ^ 40 * 3460986 * 2
def baseEnd_3460986 : Nat := 592383118827300370019407

theorem tailTrace_3460986 : CollatzResearch.WordTrace tailWord_3460986 prefixEnd_3460986 592383118827300370019407 := by
  unfold tailWord_3460986
  simp only [CollatzResearch.WordTrace]
  refine ⟨31558132459861571548720703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84155019892964190796588541 31558132459861571548720703)
  ·
    refine ⟨47337198689792357323081055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31558132459861571548720703 47337198689792357323081055)
    ·
      refine ⟨71005798034688535984621583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47337198689792357323081055 71005798034688535984621583)
      ·
        refine ⟨106508697052032803976932375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71005798034688535984621583 106508697052032803976932375)
        ·
          refine ⟨159763045578049205965398563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106508697052032803976932375 159763045578049205965398563)
          ·
            refine ⟨239644568367073808948097845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159763045578049205965398563 239644568367073808948097845)
            ·
              refine ⟨22466678284413169588884173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 239644568367073808948097845 22466678284413169588884173)
              ·
                refine ⟨8425004356654938595831565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22466678284413169588884173 8425004356654938595831565)
                ·
                  refine ⟨3159376633745601973436837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8425004356654938595831565 3159376633745601973436837)
                  ·
                    refine ⟨592383118827300370019407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3159376633745601973436837 592383118827300370019407)
                    ·
                      rfl

theorem cell23_3460986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 3, 4].length) (baseStart_3460986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460986 prefixEnd_3460986 := by exact prefixLift 3460986
  have htrace : WordTrace (prefixWord ++ tailWord_3460986) baseStart_3460986 baseEnd_3460986 := by
    simpa [prefixWord, tailWord_3460986, baseEnd_3460986] using wordTrace_append hprefix tailTrace_3460986
  have hstable : (prefixWord ++ tailWord_3460986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460986).length < 2 ^ (prefixWord ++ tailWord_3460986).sum := by decide
  have hdescent : baseEnd_3460986 < baseStart_3460986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460989 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 4, 1, 6]
def baseStart_3460989 : Nat := 118140960795 + 3460989 * 2 ^ 59
def prefixEnd_3460989 : Nat := 4983230072969 + 3 ^ 40 * 3460989 * 2
def baseEnd_3460989 : Nat := 1777150896923864598320707

theorem tailTrace_3460989 : CollatzResearch.WordTrace tailWord_3460989 prefixEnd_3460989 1777150896923864598320707 := by
  unfold tailWord_3460989
  simp only [CollatzResearch.WordTrace]
  refine ⟨126232639258435417707242021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84155092838956945138161347 126232639258435417707242021)
  ·
    refine ⟨23668619860956640820107879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126232639258435417707242021 23668619860956640820107879)
    ·
      refine ⟨35502929791434961230161819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23668619860956640820107879 35502929791434961230161819)
      ·
        refine ⟨53254394687152441845242729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35502929791434961230161819 53254394687152441845242729)
        ·
          refine ⟨39940796015364331383932047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53254394687152441845242729 39940796015364331383932047)
          ·
            refine ⟨59911194023046497075898071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39940796015364331383932047 59911194023046497075898071)
            ·
              refine ⟨89866791034569745613847107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59911194023046497075898071 89866791034569745613847107)
              ·
                refine ⟨134800186551854618420770661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89866791034569745613847107 134800186551854618420770661)
                ·
                  refine ⟨25275034978472740953894499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134800186551854618420770661 25275034978472740953894499)
                  ·
                    refine ⟨37912552467709111430841749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25275034978472740953894499 37912552467709111430841749)
                    ·
                      refine ⟨1777150896923864598320707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37912552467709111430841749 1777150896923864598320707)
                      ·
                        rfl

theorem cell23_3460989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_3460989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460989 prefixEnd_3460989 := by exact prefixLift 3460989
  have htrace : WordTrace (prefixWord ++ tailWord_3460989) baseStart_3460989 baseEnd_3460989 := by
    simpa [prefixWord, tailWord_3460989, baseEnd_3460989] using wordTrace_append hprefix tailTrace_3460989
  have hstable : (prefixWord ++ tailWord_3460989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460989).length < 2 ^ (prefixWord ++ tailWord_3460989).sum := by decide
  have hdescent : baseEnd_3460989 < baseStart_3460989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3460996 : List Nat := [2, 3, 2, 1, 1, 1, 3, 2, 1, 4, 3]
def baseStart_3460996 : Nat := 118140960795 + 3460996 * 2 ^ 59
def prefixEnd_3460996 : Nat := 4983230072969 + 3 ^ 40 * 3460996 * 2
def baseEnd_3460996 : Nat := 1777154491288446070933175

theorem tailTrace_3460996 : CollatzResearch.WordTrace tailWord_3460996 prefixEnd_3460996 1777154491288446070933175 := by
  unfold tailWord_3460996
  simp only [CollatzResearch.WordTrace]
  refine ⟨63116447284705028951373421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84155263046273371935164561 63116447284705028951373421)
  ·
    refine ⟨23668667731764385856765033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63116447284705028951373421 23668667731764385856765033)
    ·
      refine ⟨17751500798823289392573775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23668667731764385856765033 17751500798823289392573775)
      ·
        refine ⟨26627251198234934088860663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17751500798823289392573775 26627251198234934088860663)
        ·
          refine ⟨39940876797352401133290995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26627251198234934088860663 39940876797352401133290995)
          ·
            refine ⟨59911315196028601699936493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39940876797352401133290995 59911315196028601699936493)
            ·
              refine ⟨22466743198510725637476185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59911315196028601699936493 22466743198510725637476185)
              ·
                refine ⟨16850057398883044228107139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22466743198510725637476185 16850057398883044228107139)
                ·
                  refine ⟨25275086098324566342160709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16850057398883044228107139 25275086098324566342160709)
                  ·
                    refine ⟨4739078643435856189155133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25275086098324566342160709 4739078643435856189155133)
                    ·
                      refine ⟨1777154491288446070933175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4739078643435856189155133 1777154491288446070933175)
                      ·
                        rfl

theorem cell23_3460996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_3460996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3460996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3460996 prefixEnd_3460996 := by exact prefixLift 3460996
  have htrace : WordTrace (prefixWord ++ tailWord_3460996) baseStart_3460996 baseEnd_3460996 := by
    simpa [prefixWord, tailWord_3460996, baseEnd_3460996] using wordTrace_append hprefix tailTrace_3460996
  have hstable : (prefixWord ++ tailWord_3460996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3460996).length < 2 ^ (prefixWord ++ tailWord_3460996).sum := by decide
  have hdescent : baseEnd_3460996 < baseStart_3460996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3460996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461070 : List Nat := [4, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2]
def baseStart_3461070 : Nat := 118140960795 + 3461070 * 2 ^ 59
def prefixEnd_3461070 : Nat := 4983230072969 + 3 ^ 40 * 3461070 * 2
def baseEnd_3461070 : Nat := 1777192488856878781407835

theorem tailTrace_3461070 : CollatzResearch.WordTrace tailWord_3461070 prefixEnd_3461070 1777192488856878781407835 := by
  unfold tailWord_3461070
  simp only [CollatzResearch.WordTrace]
  refine ⟨15779449196392746067617583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84157062380761312360627109 15779449196392746067617583)
  ·
    refine ⟨23669173794589119101426375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15779449196392746067617583 23669173794589119101426375)
    ·
      refine ⟨35503760691883678652139563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23669173794589119101426375 35503760691883678652139563)
      ·
        refine ⟨53255641037825517978209345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35503760691883678652139563 53255641037825517978209345)
        ·
          refine ⟨39941730778369138483657009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53255641037825517978209345 39941730778369138483657009)
          ·
            refine ⟨29956298083776853862742757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39941730778369138483657009 29956298083776853862742757)
            ·
              refine ⟨5616805890708160099264267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29956298083776853862742757 5616805890708160099264267)
              ·
                refine ⟨8425208836062240148896401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5616805890708160099264267 8425208836062240148896401)
                ·
                  refine ⟨6318906627046680111672301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8425208836062240148896401 6318906627046680111672301)
                  ·
                    refine ⟨2369589985142505041877113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6318906627046680111672301 2369589985142505041877113)
                    ·
                      refine ⟨1777192488856878781407835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2369589985142505041877113 1777192488856878781407835)
                      ·
                        rfl

theorem cell23_3461070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2].length) (baseStart_3461070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461070 prefixEnd_3461070 := by exact prefixLift 3461070
  have htrace : WordTrace (prefixWord ++ tailWord_3461070) baseStart_3461070 baseEnd_3461070 := by
    simpa [prefixWord, tailWord_3461070, baseEnd_3461070] using wordTrace_append hprefix tailTrace_3461070
  have hstable : (prefixWord ++ tailWord_3461070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461070).length < 2 ^ (prefixWord ++ tailWord_3461070).sum := by decide
  have hdescent : baseEnd_3461070 < baseStart_3461070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461096 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_3461096 : Nat := 118140960795 + 3461096 * 2 ^ 59
def prefixEnd_3461096 : Nat := 4983230072969 + 3 ^ 40 * 3461096 * 2
def baseEnd_3461096 : Nat := 1777205839353895679682715

theorem tailTrace_3461096 : CollatzResearch.WordTrace tailWord_3461096 prefixEnd_3461096 1777205839353895679682715 := by
  unfold tailWord_3461096
  simp only [CollatzResearch.WordTrace]
  refine ⟨63118270934523887490693571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84157694579365183320924761 63118270934523887490693571)
  ·
    refine ⟨94677406401785831236040357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63118270934523887490693571 94677406401785831236040357)
    ·
      refine ⟨17752013700334843356757567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94677406401785831236040357 17752013700334843356757567)
      ·
        refine ⟨26628020550502265035136351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17752013700334843356757567 26628020550502265035136351)
        ·
          refine ⟨39942030825753397552704527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26628020550502265035136351 39942030825753397552704527)
          ·
            refine ⟨59913046238630096329056791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39942030825753397552704527 59913046238630096329056791)
            ·
              refine ⟨89869569357945144493585187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59913046238630096329056791 89869569357945144493585187)
              ·
                refine ⟨134804354036917716740377781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89869569357945144493585187 134804354036917716740377781)
                ·
                  refine ⟨12637908190961035944410417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134804354036917716740377781 12637908190961035944410417)
                  ·
                    refine ⟨9478431143220776958307813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12637908190961035944410417 9478431143220776958307813)
                    ·
                      refine ⟨1777205839353895679682715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9478431143220776958307813 1777205839353895679682715)
                      ·
                        rfl

theorem cell23_3461096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_3461096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461096 prefixEnd_3461096 := by exact prefixLift 3461096
  have htrace : WordTrace (prefixWord ++ tailWord_3461096) baseStart_3461096 baseEnd_3461096 := by
    simpa [prefixWord, tailWord_3461096, baseEnd_3461096] using wordTrace_append hprefix tailTrace_3461096
  have hstable : (prefixWord ++ tailWord_3461096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461096).length < 2 ^ (prefixWord ++ tailWord_3461096).sum := by decide
  have hdescent : baseEnd_3461096 < baseStart_3461096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461110 : List Nat := [5, 1, 1, 1, 4, 1, 2, 1, 1, 6]
def baseStart_3461110 : Nat := 118140960795 + 3461110 * 2 ^ 59
def prefixEnd_3461110 : Nat := 4983230072969 + 3 ^ 40 * 3461110 * 2
def baseEnd_3461110 : Nat := 592404342694352874969217

theorem tailTrace_3461110 : CollatzResearch.WordTrace tailWord_3461110 prefixEnd_3461110 592404342694352874969217 := by
  unfold tailWord_3461110
  simp only [CollatzResearch.WordTrace]
  refine ⟨7889815780687315960774799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84158034993998036914931189 7889815780687315960774799)
  ·
    refine ⟨11834723671030973941162199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7889815780687315960774799 11834723671030973941162199)
    ·
      refine ⟨17752085506546460911743299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11834723671030973941162199 17752085506546460911743299)
      ·
        refine ⟨26628128259819691367614949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17752085506546460911743299 26628128259819691367614949)
        ·
          refine ⟨4992774048716192131427803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26628128259819691367614949 4992774048716192131427803)
          ·
            refine ⟨7489161073074288197141705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4992774048716192131427803 7489161073074288197141705)
            ·
              refine ⟨5616870804805716147856279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7489161073074288197141705 5616870804805716147856279)
              ·
                refine ⟨8425306207208574221784419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5616870804805716147856279 8425306207208574221784419)
                ·
                  refine ⟨12637959310812861332676629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8425306207208574221784419 12637959310812861332676629)
                  ·
                    refine ⟨592404342694352874969217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12637959310812861332676629 592404342694352874969217)
                    ·
                      rfl

theorem cell23_3461110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_3461110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461110 prefixEnd_3461110 := by exact prefixLift 3461110
  have htrace : WordTrace (prefixWord ++ tailWord_3461110) baseStart_3461110 baseEnd_3461110 := by
    simpa [prefixWord, tailWord_3461110, baseEnd_3461110] using wordTrace_append hprefix tailTrace_3461110
  have hstable : (prefixWord ++ tailWord_3461110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461110).length < 2 ^ (prefixWord ++ tailWord_3461110).sum := by decide
  have hdescent : baseEnd_3461110 < baseStart_3461110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461113 : List Nat := [1, 2, 1, 3, 1, 5, 2, 1, 1, 2, 4]
def baseStart_3461113 : Nat := 118140960795 + 3461113 * 2 ^ 59
def prefixEnd_3461113 : Nat := 4983230072969 + 3 ^ 40 * 3461113 * 2
def baseEnd_3461113 : Nat := 1777214568525022113170137

theorem tailTrace_3461113 : CollatzResearch.WordTrace tailWord_3461113 prefixEnd_3461113 1777214568525022113170137 := by
  unfold tailWord_3461113
  simp only [CollatzResearch.WordTrace]
  refine ⟨126237161909986186884755993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84158107939990791256503995 126237161909986186884755993)
  ·
    refine ⟨94677871432489640163566995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126237161909986186884755993 94677871432489640163566995)
    ·
      refine ⟨142016807148734460245350493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94677871432489640163566995 142016807148734460245350493)
      ·
        refine ⟨53256302680775422592006435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142016807148734460245350493 53256302680775422592006435)
        ·
          refine ⟨79884454021163133888009653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53256302680775422592006435 79884454021163133888009653)
          ·
            refine ⟨7489167564484043802000905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79884454021163133888009653 7489167564484043802000905)
            ·
              refine ⟨5616875673363032851500679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7489167564484043802000905 5616875673363032851500679)
              ·
                refine ⟨8425313510044549277251019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5616875673363032851500679 8425313510044549277251019)
                ·
                  refine ⟨12637970265066823915876529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8425313510044549277251019 12637970265066823915876529)
                  ·
                    refine ⟨9478477698800117936907397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12637970265066823915876529 9478477698800117936907397)
                    ·
                      refine ⟨1777214568525022113170137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9478477698800117936907397 1777214568525022113170137)
                      ·
                        rfl

theorem cell23_3461113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_3461113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461113 prefixEnd_3461113 := by exact prefixLift 3461113
  have htrace : WordTrace (prefixWord ++ tailWord_3461113) baseStart_3461113 baseEnd_3461113 := by
    simpa [prefixWord, tailWord_3461113, baseEnd_3461113] using wordTrace_append hprefix tailTrace_3461113
  have hstable : (prefixWord ++ tailWord_3461113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461113).length < 2 ^ (prefixWord ++ tailWord_3461113).sum := by decide
  have hdescent : baseEnd_3461113 < baseStart_3461113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461134 : List Nat := [4, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2]
def baseStart_3461134 : Nat := 118140960795 + 3461134 * 2 ^ 59
def prefixEnd_3461134 : Nat := 4983230072969 + 3 ^ 40 * 3461134 * 2
def baseEnd_3461134 : Nat := 1777225351618766531007541

theorem tailTrace_3461134 : CollatzResearch.WordTrace tailWord_3461134 prefixEnd_3461134 1777225351618766531007541 := by
  unfold tailWord_3461134
  simp only [CollatzResearch.WordTrace]
  refine ⟨15779740980363763433908807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84158618561940071647513637 15779740980363763433908807)
  ·
    refine ⟨23669611470545645150863211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15779740980363763433908807 23669611470545645150863211)
    ·
      refine ⟨35504417205818467726294817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23669611470545645150863211 35504417205818467726294817)
      ·
        refine ⟨26628312904363850794721113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35504417205818467726294817 26628312904363850794721113)
        ·
          refine ⟨19971234678272888096040835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26628312904363850794721113 19971234678272888096040835)
          ·
            refine ⟨29956852017409332144061253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19971234678272888096040835 29956852017409332144061253)
            ·
              refine ⟨5616909753264249777011485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29956852017409332144061253 5616909753264249777011485)
              ·
                refine ⟨2106341157474093666379307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5616909753264249777011485 2106341157474093666379307)
                ·
                  refine ⟨3159511736211140499568961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2106341157474093666379307 3159511736211140499568961)
                  ·
                    refine ⟨2369633802158355374676721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3159511736211140499568961 2369633802158355374676721)
                    ·
                      refine ⟨1777225351618766531007541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2369633802158355374676721 1777225351618766531007541)
                      ·
                        rfl

theorem cell23_3461134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_3461134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461134 prefixEnd_3461134 := by exact prefixLift 3461134
  have htrace : WordTrace (prefixWord ++ tailWord_3461134) baseStart_3461134 baseEnd_3461134 := by
    simpa [prefixWord, tailWord_3461134, baseEnd_3461134] using wordTrace_append hprefix tailTrace_3461134
  have hstable : (prefixWord ++ tailWord_3461134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461134).length < 2 ^ (prefixWord ++ tailWord_3461134).sum := by decide
  have hdescent : baseEnd_3461134 < baseStart_3461134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461140 : List Nat := [2, 4, 3, 2, 1, 1, 10]
def baseStart_3461140 : Nat := 118140960795 + 3461140 * 2 ^ 59
def prefixEnd_3461140 : Nat := 4983230072969 + 3 ^ 40 * 3461140 * 2
def baseEnd_3461140 : Nat := 21941091759292512438673

theorem tailTrace_3461140 : CollatzResearch.WordTrace tailWord_3461140 prefixEnd_3461140 21941091759292512438673 := by
  unfold tailWord_3461140
  simp only [CollatzResearch.WordTrace]
  refine ⟨63119073340444185247994437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84158764453925580330659249 63119073340444185247994437)
  ·
    refine ⟨11834826251333284733998957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63119073340444185247994437 11834826251333284733998957)
    ·
      refine ⟨4438059844249981775249609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11834826251333284733998957 4438059844249981775249609)
      ·
        refine ⟨3328544883187486331437207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4438059844249981775249609 3328544883187486331437207)
        ·
          refine ⟨4992817324781229497155811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3328544883187486331437207 4992817324781229497155811)
          ·
            refine ⟨7489225987171844245733717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4992817324781229497155811 7489225987171844245733717)
            ·
              refine ⟨21941091759292512438673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7489225987171844245733717 21941091759292512438673)
              ·
                rfl

theorem cell23_3461140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 10].length) (baseStart_3461140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461140 prefixEnd_3461140 := by exact prefixLift 3461140
  have htrace : WordTrace (prefixWord ++ tailWord_3461140) baseStart_3461140 baseEnd_3461140 := by
    simpa [prefixWord, tailWord_3461140, baseEnd_3461140] using wordTrace_append hprefix tailTrace_3461140
  have hstable : (prefixWord ++ tailWord_3461140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461140).length < 2 ^ (prefixWord ++ tailWord_3461140).sum := by decide
  have hdescent : baseEnd_3461140 < baseStart_3461140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461196 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 9]
def baseStart_3461196 : Nat := 118140960795 + 3461196 * 2 ^ 59
def prefixEnd_3461196 : Nat := 4983230072969 + 3 ^ 40 * 3461196 * 2
def baseEnd_3461196 : Nat := 197473020824371698714695

theorem tailTrace_3461196 : CollatzResearch.WordTrace tailWord_3461196 prefixEnd_3461196 197473020824371698714695 := by
  unfold tailWord_3461196
  simp only [CollatzResearch.WordTrace]
  refine ⟨63120094584342746030013721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84160126112456994706684961 63120094584342746030013721)
  ·
    refine ⟨47340070938257059522510291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63120094584342746030013721 47340070938257059522510291)
    ·
      refine ⟨71010106407385589283765437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47340070938257059522510291 71010106407385589283765437)
      ·
        refine ⟨26628789902769595981412039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71010106407385589283765437 26628789902769595981412039)
        ·
          refine ⟨39943184854154393972118059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26628789902769595981412039 39943184854154393972118059)
          ·
            refine ⟨59914777281231590958177089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39943184854154393972118059 59914777281231590958177089)
            ·
              refine ⟨44936082960923693218632817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59914777281231590958177089 44936082960923693218632817)
              ·
                refine ⟨33702062220692769913974613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44936082960923693218632817 33702062220692769913974613)
                ·
                  refine ⟨197473020824371698714695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33702062220692769913974613 197473020824371698714695)
                  ·
                    rfl

theorem cell23_3461196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 9].length) (baseStart_3461196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461196 prefixEnd_3461196 := by exact prefixLift 3461196
  have htrace : WordTrace (prefixWord ++ tailWord_3461196) baseStart_3461196 baseEnd_3461196 := by
    simpa [prefixWord, tailWord_3461196, baseEnd_3461196] using wordTrace_append hprefix tailTrace_3461196
  have hstable : (prefixWord ++ tailWord_3461196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461196).length < 2 ^ (prefixWord ++ tailWord_3461196).sum := by decide
  have hdescent : baseEnd_3461196 < baseStart_3461196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461218 : List Nat := [3, 3, 2, 2, 3, 1, 2, 1, 2, 1, 3]
def baseStart_3461218 : Nat := 118140960795 + 3461218 * 2 ^ 59
def prefixEnd_3461218 : Nat := 4983230072969 + 3 ^ 40 * 3461218 * 2
def baseEnd_3461218 : Nat := 1777268483993744202357155

theorem tailTrace_3461218 : CollatzResearch.WordTrace tailWord_3461218 prefixEnd_3461218 1777268483993744202357155 := by
  unfold tailWord_3461218
  simp only [CollatzResearch.WordTrace]
  refine ⟨31560247893651447454332077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84160661049737193211552205 31560247893651447454332077)
  ·
    refine ⟨11835092960119292795374529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31560247893651447454332077 11835092960119292795374529)
    ·
      refine ⟨8876319720089469596530897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11835092960119292795374529 8876319720089469596530897)
      ·
        refine ⟨6657239790067102197398173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8876319720089469596530897 6657239790067102197398173)
        ·
          refine ⟨2496464921275163324024315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6657239790067102197398173 2496464921275163324024315)
          ·
            refine ⟨3744697381912744986036473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2496464921275163324024315 3744697381912744986036473)
            ·
              refine ⟨2808523036434558739527355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3744697381912744986036473 2808523036434558739527355)
              ·
                refine ⟨4212784554651838109291033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2808523036434558739527355 4212784554651838109291033)
                ·
                  refine ⟨3159588415988878581968275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4212784554651838109291033 3159588415988878581968275)
                  ·
                    refine ⟨4739382623983317872952413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3159588415988878581968275 4739382623983317872952413)
                    ·
                      refine ⟨1777268483993744202357155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4739382623983317872952413 1777268483993744202357155)
                      ·
                        rfl

theorem cell23_3461218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_3461218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461218 prefixEnd_3461218 := by exact prefixLift 3461218
  have htrace : WordTrace (prefixWord ++ tailWord_3461218) baseStart_3461218 baseEnd_3461218 := by
    simpa [prefixWord, tailWord_3461218, baseEnd_3461218] using wordTrace_append hprefix tailTrace_3461218
  have hstable : (prefixWord ++ tailWord_3461218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461218).length < 2 ^ (prefixWord ++ tailWord_3461218).sum := by decide
  have hdescent : baseEnd_3461218 < baseStart_3461218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461223 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 1, 5, 3]
def baseStart_3461223 : Nat := 118140960795 + 3461223 * 2 ^ 59
def prefixEnd_3461223 : Nat := 4983230072969 + 3 ^ 40 * 3461223 * 2
def baseEnd_3461223 : Nat := 1777271051397016682794631

theorem tailTrace_3461223 : CollatzResearch.WordTrace tailWord_3461223 prefixEnd_3461223 1777271051397016682794631 := by
  unfold tailWord_3461223
  simp only [CollatzResearch.WordTrace]
  refine ⟨126241173939587675671260323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84160782626391783780840215 126241173939587675671260323)
  ·
    refine ⟨189361760909381513506890485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126241173939587675671260323 189361760909381513506890485)
    ·
      refine ⟨17752665085254516891270983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189361760909381513506890485 17752665085254516891270983)
      ·
        refine ⟨26628997627881775336906475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17752665085254516891270983 26628997627881775336906475)
        ·
          refine ⟨39943496441822663005359713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26628997627881775336906475 39943496441822663005359713)
          ·
            refine ⟨29957622331366997254019785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39943496441822663005359713 29957622331366997254019785)
            ·
              refine ⟨22468216748525247940514839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29957622331366997254019785 22468216748525247940514839)
              ·
                refine ⟨33702325122787871910772259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22468216748525247940514839 33702325122787871910772259)
                ·
                  refine ⟨50553487684181807866158389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33702325122787871910772259 50553487684181807866158389)
                  ·
                    refine ⟨4739389470392044487452349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50553487684181807866158389 4739389470392044487452349)
                    ·
                      refine ⟨1777271051397016682794631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4739389470392044487452349 1777271051397016682794631)
                      ·
                        rfl

theorem cell23_3461223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_3461223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461223 prefixEnd_3461223 := by exact prefixLift 3461223
  have htrace : WordTrace (prefixWord ++ tailWord_3461223) baseStart_3461223 baseEnd_3461223 := by
    simpa [prefixWord, tailWord_3461223, baseEnd_3461223] using wordTrace_append hprefix tailTrace_3461223
  have hstable : (prefixWord ++ tailWord_3461223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461223).length < 2 ^ (prefixWord ++ tailWord_3461223).sum := by decide
  have hdescent : baseEnd_3461223 < baseStart_3461223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461253 : List Nat := [1, 3, 1, 1, 5, 1, 1, 2, 1, 2, 5]
def baseStart_3461253 : Nat := 118140960795 + 3461253 * 2 ^ 59
def prefixEnd_3461253 : Nat := 4983230072969 + 3 ^ 40 * 3461253 * 2
def baseEnd_3461253 : Nat := 1777286455816651565419493

theorem tailTrace_3461253 : CollatzResearch.WordTrace tailWord_3461253 prefixEnd_3461253 1777286455816651565419493 := by
  unfold tailWord_3461253
  simp only [CollatzResearch.WordTrace]
  refine ⟨126242268129478990794852413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84161512086319327196568275 126242268129478990794852413)
  ·
    refine ⟨47340850548554621548069655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126242268129478990794852413 47340850548554621548069655)
    ·
      refine ⟨71011275822831932322104483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47340850548554621548069655 71011275822831932322104483)
      ·
        refine ⟨106516913734247898483156725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71011275822831932322104483 106516913734247898483156725)
        ·
          refine ⟨9985960662585740482795943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106516913734247898483156725 9985960662585740482795943)
          ·
            refine ⟨14978940993878610724193915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9985960662585740482795943 14978940993878610724193915)
            ·
              refine ⟨22468411490817916086290873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14978940993878610724193915 22468411490817916086290873)
              ·
                refine ⟨16851308618113437064718155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22468411490817916086290873 16851308618113437064718155)
                ·
                  refine ⟨25276962927170155597077233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16851308618113437064718155 25276962927170155597077233)
                  ·
                    refine ⟨18957722195377616697807925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25276962927170155597077233 18957722195377616697807925)
                    ·
                      refine ⟨1777286455816651565419493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18957722195377616697807925 1777286455816651565419493)
                      ·
                        rfl

theorem cell23_3461253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_3461253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461253 prefixEnd_3461253 := by exact prefixLift 3461253
  have htrace : WordTrace (prefixWord ++ tailWord_3461253) baseStart_3461253 baseEnd_3461253 := by
    simpa [prefixWord, tailWord_3461253, baseEnd_3461253] using wordTrace_append hprefix tailTrace_3461253
  have hstable : (prefixWord ++ tailWord_3461253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461253).length < 2 ^ (prefixWord ++ tailWord_3461253).sum := by decide
  have hdescent : baseEnd_3461253 < baseStart_3461253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461273 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 7, 4]
def baseStart_3461273 : Nat := 118140960795 + 3461273 * 2 ^ 59
def prefixEnd_3461273 : Nat := 4983230072969 + 3 ^ 40 * 3461273 * 2
def baseEnd_3461273 : Nat := 592432241809913829056467

theorem tailTrace_3461273 : CollatzResearch.WordTrace tailWord_3461273 prefixEnd_3461273 592432241809913829056467 := by
  unfold tailWord_3461273
  simp only [CollatzResearch.WordTrace]
  refine ⟨126242997589406534210580473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84161998392937689473720315 126242997589406534210580473)
  ·
    refine ⟨94682248192054900657935355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126242997589406534210580473 94682248192054900657935355)
    ·
      refine ⟨142023372288082350986903033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94682248192054900657935355 142023372288082350986903033)
      ·
        refine ⟨106517529216061763240177275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142023372288082350986903033 106517529216061763240177275)
        ·
          refine ⟨159776293824092644860265913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106517529216061763240177275 159776293824092644860265913)
          ·
            refine ⟨119832220368069483645199435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159776293824092644860265913 119832220368069483645199435)
            ·
              refine ⟨179748330552104225467799153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119832220368069483645199435 179748330552104225467799153)
              ·
                refine ⟨134811247914078169100849365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179748330552104225467799153 134811247914078169100849365)
                ·
                  refine ⟨3159638622986207088301157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 134811247914078169100849365 3159638622986207088301157)
                  ·
                    refine ⟨592432241809913829056467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3159638622986207088301157 592432241809913829056467)
                    ·
                      rfl

theorem cell23_3461273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7, 4].length) (baseStart_3461273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461273 prefixEnd_3461273 := by exact prefixLift 3461273
  have htrace : WordTrace (prefixWord ++ tailWord_3461273) baseStart_3461273 baseEnd_3461273 := by
    simpa [prefixWord, tailWord_3461273, baseEnd_3461273] using wordTrace_append hprefix tailTrace_3461273
  have hstable : (prefixWord ++ tailWord_3461273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461273).length < 2 ^ (prefixWord ++ tailWord_3461273).sum := by decide
  have hdescent : baseEnd_3461273 < baseStart_3461273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461280 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 1, 6, 2]
def baseStart_3461280 : Nat := 118140960795 + 3461280 * 2 ^ 59
def prefixEnd_3461280 : Nat := 4983230072969 + 3 ^ 40 * 3461280 * 2
def baseEnd_3461280 : Nat := 1777300319794322959781869

theorem tailTrace_3461280 : CollatzResearch.WordTrace tailWord_3461280 prefixEnd_3461280 1777300319794322959781869 := by
  unfold tailWord_3461280
  simp only [CollatzResearch.WordTrace]
  refine ⟨63121626450190587203042647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84162168600254116270723529 63121626450190587203042647)
  ·
    refine ⟨94682439675285880804563971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63121626450190587203042647 94682439675285880804563971)
    ·
      refine ⟨142023659512928821206845957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94682439675285880804563971 142023659512928821206845957)
      ·
        refine ⟨26629436158674153976283617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142023659512928821206845957 26629436158674153976283617)
        ·
          refine ⟨19972077119005615482212713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26629436158674153976283617 19972077119005615482212713)
          ·
            refine ⟨14979057839254211611659535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19972077119005615482212713 14979057839254211611659535)
            ·
              refine ⟨22468586758881317417489303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14979057839254211611659535 22468586758881317417489303)
              ·
                refine ⟨33702880138321976126233955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22468586758881317417489303 33702880138321976126233955)
                ·
                  refine ⟨50554320207482964189350933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33702880138321976126233955 50554320207482964189350933)
                  ·
                    refine ⟨2369733759725763946375825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 50554320207482964189350933 2369733759725763946375825)
                    ·
                      refine ⟨1777300319794322959781869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2369733759725763946375825 1777300319794322959781869)
                      ·
                        rfl

theorem cell23_3461280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_3461280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461280 prefixEnd_3461280 := by exact prefixLift 3461280
  have htrace : WordTrace (prefixWord ++ tailWord_3461280) baseStart_3461280 baseEnd_3461280 := by
    simpa [prefixWord, tailWord_3461280, baseEnd_3461280] using wordTrace_append hprefix tailTrace_3461280
  have hstable : (prefixWord ++ tailWord_3461280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461280).length < 2 ^ (prefixWord ++ tailWord_3461280).sum := by decide
  have hdescent : baseEnd_3461280 < baseStart_3461280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461307 : List Nat := [1, 1, 1, 1, 1, 2, 8, 3, 1, 4]
def baseStart_3461307 : Nat := 118140960795 + 3461307 * 2 ^ 59
def prefixEnd_3461307 : Nat := 4983230072969 + 3 ^ 40 * 3461307 * 2
def baseEnd_3461307 : Nat := 592438061257331451381415

theorem tailTrace_3461307 : CollatzResearch.WordTrace tailWord_3461307 prefixEnd_3461307 592438061257331451381415 := by
  unfold tailWord_3461307
  simp only [CollatzResearch.WordTrace]
  refine ⟨126244237671283358017318175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84162825114188905344878783 126244237671283358017318175)
  ·
    refine ⟨189366356506925037025977263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126244237671283358017318175 189366356506925037025977263)
    ·
      refine ⟨284049534760387555538965895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189366356506925037025977263 284049534760387555538965895)
      ·
        refine ⟨426074302140581333308448843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284049534760387555538965895 426074302140581333308448843)
        ·
          refine ⟨639111453210871999962673265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426074302140581333308448843 639111453210871999962673265)
          ·
            refine ⟨479333589908153999972004949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 639111453210871999962673265 479333589908153999972004949)
            ·
              refine ⟨5617190506736179687171933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 479333589908153999972004949 5617190506736179687171933)
              ·
                refine ⟨2106446440026067382689475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5617190506736179687171933 2106446440026067382689475)
                ·
                  refine ⟨3159669660039101074034213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2106446440026067382689475 3159669660039101074034213)
                  ·
                    refine ⟨592438061257331451381415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3159669660039101074034213 592438061257331451381415)
                    ·
                      rfl

theorem cell23_3461307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3, 1, 4].length) (baseStart_3461307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461307 prefixEnd_3461307 := by exact prefixLift 3461307
  have htrace : WordTrace (prefixWord ++ tailWord_3461307) baseStart_3461307 baseEnd_3461307 := by
    simpa [prefixWord, tailWord_3461307, baseEnd_3461307] using wordTrace_append hprefix tailTrace_3461307
  have hstable : (prefixWord ++ tailWord_3461307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461307).length < 2 ^ (prefixWord ++ tailWord_3461307).sum := by decide
  have hdescent : baseEnd_3461307 < baseStart_3461307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461324 : List Nat := [2, 2, 1, 6, 1, 1, 2, 1, 3, 4]
def baseStart_3461324 : Nat := 118140960795 + 3461324 * 2 ^ 59
def prefixEnd_3461324 : Nat := 4983230072969 + 3 ^ 40 * 3461324 * 2
def baseEnd_3461324 : Nat := 592440970981040262543889

theorem tailTrace_3461324 : CollatzResearch.WordTrace tailWord_3461324 prefixEnd_3461324 592440970981040262543889 := by
  unfold tailWord_3461324
  simp only [CollatzResearch.WordTrace]
  refine ⟨63122428856110884960343513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84163238474814513280458017 63122428856110884960343513)
  ·
    refine ⟨47341821642083163720257635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63122428856110884960343513 47341821642083163720257635)
    ·
      refine ⟨71012732463124745580386453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47341821642083163720257635 71012732463124745580386453)
      ·
        refine ⟨3328721834208972449080615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 71012732463124745580386453 3328721834208972449080615)
        ·
          refine ⟨4993082751313458673620923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3328721834208972449080615 4993082751313458673620923)
          ·
            refine ⟨7489624126970188010431385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4993082751313458673620923 7489624126970188010431385)
            ·
              refine ⟨5617218095227641007823539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7489624126970188010431385 5617218095227641007823539)
              ·
                refine ⟨8425827142841461511735309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5617218095227641007823539 8425827142841461511735309)
                ·
                  refine ⟨3159685178565548066900741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8425827142841461511735309 3159685178565548066900741)
                  ·
                    refine ⟨592440970981040262543889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3159685178565548066900741 592440970981040262543889)
                    ·
                      rfl

theorem cell23_3461324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 3, 4].length) (baseStart_3461324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461324 prefixEnd_3461324 := by exact prefixLift 3461324
  have htrace : WordTrace (prefixWord ++ tailWord_3461324) baseStart_3461324 baseEnd_3461324 := by
    simpa [prefixWord, tailWord_3461324, baseEnd_3461324] using wordTrace_append hprefix tailTrace_3461324
  have hstable : (prefixWord ++ tailWord_3461324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461324).length < 2 ^ (prefixWord ++ tailWord_3461324).sum := by decide
  have hdescent : baseEnd_3461324 < baseStart_3461324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461363 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 3, 6]
def baseStart_3461363 : Nat := 118140960795 + 3461363 * 2 ^ 59
def prefixEnd_3461363 : Nat := 4983230072969 + 3 ^ 40 * 3461363 * 2
def baseEnd_3461363 : Nat := 592447646229548711681329

theorem tailTrace_3461363 : CollatzResearch.WordTrace tailWord_3461363 prefixEnd_3461363 592447646229548711681329 := by
  unfold tailWord_3461363
  simp only [CollatzResearch.WordTrace]
  refine ⟨126246280159080479581356743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84164186772720319720904495 126246280159080479581356743)
  ·
    refine ⟨189369420238620719372035115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126246280159080479581356743 189369420238620719372035115)
    ·
      refine ⟨284054130357931079058052673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189369420238620719372035115 284054130357931079058052673)
      ·
        refine ⟨213040597768448309293539505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284054130357931079058052673 213040597768448309293539505)
        ·
          refine ⟨159780448326336231970154629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213040597768448309293539505 159780448326336231970154629)
          ·
            refine ⟨29958834061188043494403993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159780448326336231970154629 29958834061188043494403993)
            ·
              refine ⟨22469125545891032620802995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29958834061188043494403993 22469125545891032620802995)
              ·
                refine ⟨33703688318836548931204493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22469125545891032620802995 33703688318836548931204493)
                ·
                  refine ⟨12638883119563705849201685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33703688318836548931204493 12638883119563705849201685)
                  ·
                    refine ⟨592447646229548711681329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12638883119563705849201685 592447646229548711681329)
                    ·
                      rfl

theorem cell23_3461363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 6].length) (baseStart_3461363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461363 prefixEnd_3461363 := by exact prefixLift 3461363
  have htrace : WordTrace (prefixWord ++ tailWord_3461363) baseStart_3461363 baseEnd_3461363 := by
    simpa [prefixWord, tailWord_3461363, baseEnd_3461363] using wordTrace_append hprefix tailTrace_3461363
  have hstable : (prefixWord ++ tailWord_3461363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461363).length < 2 ^ (prefixWord ++ tailWord_3461363).sum := by decide
  have hdescent : baseEnd_3461363 < baseStart_3461363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461374 : List Nat := [4, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2]
def baseStart_3461374 : Nat := 118140960795 + 3461374 * 2 ^ 59
def prefixEnd_3461374 : Nat := 4983230072969 + 3 ^ 40 * 3461374 * 2
def baseEnd_3461374 : Nat := 1777348586975845592006437

theorem tailTrace_3461374 : CollatzResearch.WordTrace tailWord_3461374 prefixEnd_3461374 1777348586975845592006437 := by
  unfold tailWord_3461374
  simp only [CollatzResearch.WordTrace]
  refine ⟨15780835170255078557500897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84164454241360418973338117 15780835170255078557500897)
  ·
    refine ⟨11835626377691308918125673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15780835170255078557500897 11835626377691308918125673)
    ·
      refine ⟨8876719783268481688594255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11835626377691308918125673 8876719783268481688594255)
      ·
        refine ⟨13315079674902722532891383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8876719783268481688594255 13315079674902722532891383)
        ·
          refine ⟨19972619512354083799337075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13315079674902722532891383 19972619512354083799337075)
          ·
            refine ⟨29958929268531125699005613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19972619512354083799337075 29958929268531125699005613)
            ·
              refine ⟨11234598475699172137127105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29958929268531125699005613 11234598475699172137127105)
              ·
                refine ⟨8425948856774379102845329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11234598475699172137127105 8425948856774379102845329)
                ·
                  refine ⟨6319461642580784327133997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8425948856774379102845329 6319461642580784327133997)
                  ·
                    refine ⟨2369798115967794122675249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6319461642580784327133997 2369798115967794122675249)
                    ·
                      refine ⟨1777348586975845592006437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2369798115967794122675249 1777348586975845592006437)
                      ·
                        rfl

theorem cell23_3461374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_3461374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461374 prefixEnd_3461374 := by exact prefixLift 3461374
  have htrace : WordTrace (prefixWord ++ tailWord_3461374) baseStart_3461374 baseEnd_3461374 := by
    simpa [prefixWord, tailWord_3461374, baseEnd_3461374] using wordTrace_append hprefix tailTrace_3461374
  have hstable : (prefixWord ++ tailWord_3461374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461374).length < 2 ^ (prefixWord ++ tailWord_3461374).sum := by decide
  have hdescent : baseEnd_3461374 < baseStart_3461374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461390 : List Nat := [4, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5]
def baseStart_3461390 : Nat := 118140960795 + 3461390 * 2 ^ 59
def prefixEnd_3461390 : Nat := 4983230072969 + 3 ^ 40 * 3461390 * 2
def baseEnd_3461390 : Nat := 1777356802666317529406363

theorem tailTrace_3461390 : CollatzResearch.WordTrace tailWord_3461390 prefixEnd_3461390 1777356802666317529406363 := by
  unfold tailWord_3461390
  simp only [CollatzResearch.WordTrace]
  refine ⟨15780908116247832899073703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84164843286655108795059749 15780908116247832899073703)
  ·
    refine ⟨23671362174371749348610555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15780908116247832899073703 23671362174371749348610555)
    ·
      refine ⟨35507043261557624022915833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23671362174371749348610555 35507043261557624022915833)
      ·
        refine ⟨26630282446168218017186875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35507043261557624022915833 26630282446168218017186875)
        ·
          refine ⟨39945423669252327025780313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26630282446168218017186875 39945423669252327025780313)
          ·
            refine ⟨29959067751939245269335235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39945423669252327025780313 29959067751939245269335235)
            ·
              refine ⟨44938601627908867904002853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29959067751939245269335235 44938601627908867904002853)
              ·
                refine ⟨8425987805232912732000535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44938601627908867904002853 8425987805232912732000535)
                ·
                  refine ⟨12638981707849369098000803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8425987805232912732000535 12638981707849369098000803)
                  ·
                    refine ⟨18958472561774053647001205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12638981707849369098000803 18958472561774053647001205)
                    ·
                      refine ⟨1777356802666317529406363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18958472561774053647001205 1777356802666317529406363)
                      ·
                        rfl

theorem cell23_3461390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_3461390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461390 prefixEnd_3461390 := by exact prefixLift 3461390
  have htrace : WordTrace (prefixWord ++ tailWord_3461390) baseStart_3461390 baseEnd_3461390 := by
    simpa [prefixWord, tailWord_3461390, baseEnd_3461390] using wordTrace_append hprefix tailTrace_3461390
  have hstable : (prefixWord ++ tailWord_3461390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461390).length < 2 ^ (prefixWord ++ tailWord_3461390).sum := by decide
  have hdescent : baseEnd_3461390 < baseStart_3461390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461393 : List Nat := [1, 2, 2, 1, 1, 5, 1, 10]
def baseStart_3461393 : Nat := 118140960795 + 3461393 * 2 ^ 59
def prefixEnd_3461393 : Nat := 4983230072969 + 3 ^ 40 * 3461393 * 2
def baseEnd_3461393 : Nat := 65828086781788185839587

theorem tailTrace_3461393 : CollatzResearch.WordTrace tailWord_3461393 prefixEnd_3461393 65828086781788185839587 := by
  unfold tailWord_3461393
  simp only [CollatzResearch.WordTrace]
  refine ⟨126247374348971794704948833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84164916232647863136632555 126247374348971794704948833)
  ·
    refine ⟨94685530761728846028711625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126247374348971794704948833 94685530761728846028711625)
    ·
      refine ⟨71014148071296634521533719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94685530761728846028711625 71014148071296634521533719)
      ·
        refine ⟨106521222106944951782300579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71014148071296634521533719 106521222106944951782300579)
        ·
          refine ⟨159781833160417427673450869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106521222106944951782300579 159781833160417427673450869)
          ·
            refine ⟨14979546858789133844386019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 159781833160417427673450869 14979546858789133844386019)
            ·
              refine ⟨22469320288183700766579029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14979546858789133844386019 22469320288183700766579029)
              ·
                refine ⟨65828086781788185839587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22469320288183700766579029 65828086781788185839587)
                ·
                  rfl

theorem cell23_3461393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 10].length) (baseStart_3461393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461393 prefixEnd_3461393 := by exact prefixLift 3461393
  have htrace : WordTrace (prefixWord ++ tailWord_3461393) baseStart_3461393 baseEnd_3461393 := by
    simpa [prefixWord, tailWord_3461393, baseEnd_3461393] using wordTrace_append hprefix tailTrace_3461393
  have hstable : (prefixWord ++ tailWord_3461393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461393).length < 2 ^ (prefixWord ++ tailWord_3461393).sum := by decide
  have hdescent : baseEnd_3461393 < baseStart_3461393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461400 : List Nat := [2, 1, 2, 3, 1, 2, 2, 3, 1, 2, 4]
def baseStart_3461400 : Nat := 118140960795 + 3461400 * 2 ^ 59
def prefixEnd_3461400 : Nat := 4983230072969 + 3 ^ 40 * 3461400 * 2
def baseEnd_3461400 : Nat := 1777361937472862490281317

theorem tailTrace_3461400 : CollatzResearch.WordTrace tailWord_3461400 prefixEnd_3461400 1777361937472862490281317 := by
  unfold tailWord_3461400
  simp only [CollatzResearch.WordTrace]
  refine ⟨63123814829973217450226827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84165086439964289933635769 63123814829973217450226827)
  ·
    refine ⟨94685722244959826175340241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63123814829973217450226827 94685722244959826175340241)
    ·
      refine ⟨71014291683719869631505181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94685722244959826175340241 71014291683719869631505181)
      ·
        refine ⟨26630359381394951111814443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71014291683719869631505181 26630359381394951111814443)
        ·
          refine ⟨39945539072092426667721665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26630359381394951111814443 39945539072092426667721665)
          ·
            refine ⟨29959154304069320000791249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39945539072092426667721665 29959154304069320000791249)
            ·
              refine ⟨22469365728051990000593437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29959154304069320000791249 22469365728051990000593437)
              ·
                refine ⟨8426012148019496250222539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22469365728051990000593437 8426012148019496250222539)
                ·
                  refine ⟨12639018222029244375333809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8426012148019496250222539 12639018222029244375333809)
                  ·
                    refine ⟨9479263666521933281500357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12639018222029244375333809 9479263666521933281500357)
                    ·
                      refine ⟨1777361937472862490281317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9479263666521933281500357 1777361937472862490281317)
                      ·
                        rfl

theorem cell23_3461400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_3461400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461400 prefixEnd_3461400 := by exact prefixLift 3461400
  have htrace : WordTrace (prefixWord ++ tailWord_3461400) baseStart_3461400 baseEnd_3461400 := by
    simpa [prefixWord, tailWord_3461400, baseEnd_3461400] using wordTrace_append hprefix tailTrace_3461400
  have hstable : (prefixWord ++ tailWord_3461400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461400).length < 2 ^ (prefixWord ++ tailWord_3461400).sum := by decide
  have hdescent : baseEnd_3461400 < baseStart_3461400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461407 : List Nat := [1, 1, 2, 4, 3, 2, 1, 1, 3, 2, 3]
def baseStart_3461407 : Nat := 118140960795 + 3461407 * 2 ^ 59
def prefixEnd_3461407 : Nat := 4983230072969 + 3 ^ 40 * 3461407 * 2
def baseEnd_3461407 : Nat := 1777365531837443962893785

theorem tailTrace_3461407 : CollatzResearch.WordTrace tailWord_3461407 prefixEnd_3461407 1777365531837443962893785 := by
  unfold tailWord_3461407
  simp only [CollatzResearch.WordTrace]
  refine ⟨126247884970921075095958475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84165256647280716730638983 126247884970921075095958475)
  ·
    refine ⟨189371827456381612643937713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126247884970921075095958475 189371827456381612643937713)
    ·
      refine ⟨142028870592286209482953285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189371827456381612643937713 142028870592286209482953285)
      ·
        refine ⟨26630413236053664278053741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142028870592286209482953285 26630413236053664278053741)
        ·
          refine ⟨9986404963520124104270153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26630413236053664278053741 9986404963520124104270153)
          ·
            refine ⟨7489803722640093078202615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9986404963520124104270153 7489803722640093078202615)
            ·
              refine ⟨11234705583960139617303923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7489803722640093078202615 11234705583960139617303923)
              ·
                refine ⟨16852058375940209425955885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11234705583960139617303923 16852058375940209425955885)
                ·
                  refine ⟨6319521890977578534733457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16852058375940209425955885 6319521890977578534733457)
                  ·
                    refine ⟨4739641418233183901050093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6319521890977578534733457 4739641418233183901050093)
                    ·
                      refine ⟨1777365531837443962893785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4739641418233183901050093 1777365531837443962893785)
                      ·
                        rfl

theorem cell23_3461407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_3461407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461407 prefixEnd_3461407 := by exact prefixLift 3461407
  have htrace : WordTrace (prefixWord ++ tailWord_3461407) baseStart_3461407 baseEnd_3461407 := by
    simpa [prefixWord, tailWord_3461407, baseEnd_3461407] using wordTrace_append hprefix tailTrace_3461407
  have hstable : (prefixWord ++ tailWord_3461407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461407).length < 2 ^ (prefixWord ++ tailWord_3461407).sum := by decide
  have hdescent : baseEnd_3461407 < baseStart_3461407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461410 : List Nat := [3, 3, 1, 1, 3, 1, 2, 9]
def baseStart_3461410 : Nat := 118140960795 + 3461410 * 2 ^ 59
def prefixEnd_3461410 : Nat := 4983230072969 + 3 ^ 40 * 3461410 * 2
def baseEnd_3461410 : Nat := 65828410084422498190973

theorem tailTrace_3461410 : CollatzResearch.WordTrace tailWord_3461410 prefixEnd_3461410 65828410084422498190973 := by
  unfold tailWord_3461410
  simp only [CollatzResearch.WordTrace]
  refine ⟨31561998597477551652079421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84165329593273471072211789 31561998597477551652079421)
  ·
    refine ⟨11835749474054081869529783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31561998597477551652079421 11835749474054081869529783)
    ·
      refine ⟨17753624211081122804294675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11835749474054081869529783 17753624211081122804294675)
      ·
        refine ⟨26630436316621684206442013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17753624211081122804294675 26630436316621684206442013)
        ·
          refine ⟨9986413618733131577415755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26630436316621684206442013 9986413618733131577415755)
          ·
            refine ⟨14979620428099697366123633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9986413618733131577415755 14979620428099697366123633)
            ·
              refine ⟨11234715321074773024592725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14979620428099697366123633 11234715321074773024592725)
              ·
                refine ⟨65828410084422498190973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11234715321074773024592725 65828410084422498190973)
                ·
                  rfl

theorem cell23_3461410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 9].length) (baseStart_3461410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461410 prefixEnd_3461410 := by exact prefixLift 3461410
  have htrace : WordTrace (prefixWord ++ tailWord_3461410) baseStart_3461410 baseEnd_3461410 := by
    simpa [prefixWord, tailWord_3461410, baseEnd_3461410] using wordTrace_append hprefix tailTrace_3461410
  have hstable : (prefixWord ++ tailWord_3461410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461410).length < 2 ^ (prefixWord ++ tailWord_3461410).sum := by decide
  have hdescent : baseEnd_3461410 < baseStart_3461410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461420 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 3]
def baseStart_3461420 : Nat := 118140960795 + 3461420 * 2 ^ 59
def prefixEnd_3461420 : Nat := 4983230072969 + 3 ^ 40 * 3461420 * 2
def baseEnd_3461420 : Nat := 1777372207085952412031225

theorem tailTrace_3461420 : CollatzResearch.WordTrace tailWord_3461420 prefixEnd_3461420 1777372207085952412031225 := by
  unfold tailWord_3461420
  simp only [CollatzResearch.WordTrace]
  refine ⟨63124179559936989158090857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84165572746582652210787809 63124179559936989158090857)
  ·
    refine ⟨47343134669952741868568143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63124179559936989158090857 47343134669952741868568143)
    ·
      refine ⟨71014702004929112802852215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47343134669952741868568143 71014702004929112802852215)
      ·
        refine ⟨106522053007393669204278323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71014702004929112802852215 106522053007393669204278323)
        ·
          refine ⟨159783079511090503806417485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106522053007393669204278323 159783079511090503806417485)
          ·
            refine ⟨59918654816658938927406557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159783079511090503806417485 59918654816658938927406557)
            ·
              refine ⟨22469495556247102097777459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59918654816658938927406557 22469495556247102097777459)
              ·
                refine ⟨33704243334370653146666189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22469495556247102097777459 33704243334370653146666189)
                ·
                  refine ⟨12639091250388994929999821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33704243334370653146666189 12639091250388994929999821)
                  ·
                    refine ⟨4739659218895873098749933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12639091250388994929999821 4739659218895873098749933)
                    ·
                      refine ⟨1777372207085952412031225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4739659218895873098749933 1777372207085952412031225)
                      ·
                        rfl

theorem cell23_3461420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 3].length) (baseStart_3461420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461420 prefixEnd_3461420 := by exact prefixLift 3461420
  have htrace : WordTrace (prefixWord ++ tailWord_3461420) baseStart_3461420 baseEnd_3461420 := by
    simpa [prefixWord, tailWord_3461420, baseEnd_3461420] using wordTrace_append hprefix tailTrace_3461420
  have hstable : (prefixWord ++ tailWord_3461420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461420).length < 2 ^ (prefixWord ++ tailWord_3461420).sum := by decide
  have hdescent : baseEnd_3461420 < baseStart_3461420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461438 : List Nat := [4, 2, 1, 2, 1, 3, 1, 4, 1, 2, 2]
def baseStart_3461438 : Nat := 118140960795 + 3461438 * 2 ^ 59
def prefixEnd_3461438 : Nat := 4983230072969 + 3 ^ 40 * 3461438 * 2
def baseEnd_3461438 : Nat := 1777381449737733341606143

theorem tailTrace_3461438 : CollatzResearch.WordTrace tailWord_3461438 prefixEnd_3461438 1777381449737733341606143 := by
  unfold tailWord_3461438
  simp only [CollatzResearch.WordTrace]
  refine ⟨15781126954226095923792121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84166010422539178260224645 15781126954226095923792121)
  ·
    refine ⟨11835845215669571942844091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15781126954226095923792121 11835845215669571942844091)
    ·
      refine ⟨17753767823504357914266137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11835845215669571942844091 17753767823504357914266137)
      ·
        refine ⟨13315325867628268435699603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17753767823504357914266137 13315325867628268435699603)
        ·
          refine ⟨19972988801442402653549405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13315325867628268435699603 19972988801442402653549405)
          ·
            refine ⟨7489870800540900995081027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19972988801442402653549405 7489870800540900995081027)
            ·
              refine ⟨11234806200811351492621541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7489870800540900995081027 11234806200811351492621541)
              ·
                refine ⟨2106526162652128404866539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11234806200811351492621541 2106526162652128404866539)
                ·
                  refine ⟨3159789243978192607299809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2106526162652128404866539 3159789243978192607299809)
                  ·
                    refine ⟨2369841932983644455474857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3159789243978192607299809 2369841932983644455474857)
                    ·
                      refine ⟨1777381449737733341606143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2369841932983644455474857 1777381449737733341606143)
                      ·
                        rfl

theorem cell23_3461438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_3461438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461438 prefixEnd_3461438 := by exact prefixLift 3461438
  have htrace : WordTrace (prefixWord ++ tailWord_3461438) baseStart_3461438 baseEnd_3461438 := by
    simpa [prefixWord, tailWord_3461438, baseEnd_3461438] using wordTrace_append hprefix tailTrace_3461438
  have hstable : (prefixWord ++ tailWord_3461438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461438).length < 2 ^ (prefixWord ++ tailWord_3461438).sum := by decide
  have hdescent : baseEnd_3461438 < baseStart_3461438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461444 : List Nat := [2, 3, 4, 1, 2, 2, 1, 8]
def baseStart_3461444 : Nat := 118140960795 + 3461444 * 2 ^ 59
def prefixEnd_3461444 : Nat := 4983230072969 + 3 ^ 40 * 3461444 * 2
def baseEnd_3461444 : Nat := 65829056689691122893745

theorem tailTrace_3461444 : CollatzResearch.WordTrace tailWord_3461444 prefixEnd_3461444 65829056689691122893745 := by
  unfold tailWord_3461444
  simp only [CollatzResearch.WordTrace]
  refine ⟨63124617235893515207527693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84166156314524686943370257 63124617235893515207527693)
  ·
    refine ⟨23671731463460068202822885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63124617235893515207527693 23671731463460068202822885)
    ·
      refine ⟨4438449649398762788029291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23671731463460068202822885 4438449649398762788029291)
      ·
        refine ⟨6657674474098144182043937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4438449649398762788029291 6657674474098144182043937)
        ·
          refine ⟨4993255855573608136532953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6657674474098144182043937 4993255855573608136532953)
          ·
            refine ⟨3744941891680206102399715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4993255855573608136532953 3744941891680206102399715)
            ·
              refine ⟨5617412837520309153599573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3744941891680206102399715 5617412837520309153599573)
              ·
                refine ⟨65829056689691122893745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5617412837520309153599573 65829056689691122893745)
                ·
                  rfl

theorem cell23_3461444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 8].length) (baseStart_3461444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461444 prefixEnd_3461444 := by exact prefixLift 3461444
  have htrace : WordTrace (prefixWord ++ tailWord_3461444) baseStart_3461444 baseEnd_3461444 := by
    simpa [prefixWord, tailWord_3461444, baseEnd_3461444] using wordTrace_append hprefix tailTrace_3461444
  have hstable : (prefixWord ++ tailWord_3461444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461444).length < 2 ^ (prefixWord ++ tailWord_3461444).sum := by decide
  have hdescent : baseEnd_3461444 < baseStart_3461444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461447 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 5, 3, 2]
def baseStart_3461447 : Nat := 118140960795 + 3461447 * 2 ^ 59
def prefixEnd_3461447 : Nat := 4983230072969 + 3 ^ 40 * 3461447 * 2
def baseEnd_3461447 : Nat := 1777386071063623806393601

theorem tailTrace_3461447 : CollatzResearch.WordTrace tailWord_3461447 prefixEnd_3461447 1777386071063623806393601 := by
  unfold tailWord_3461447
  simp only [CollatzResearch.WordTrace]
  refine ⟨126249343890776161927414595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84166229260517441284943063 126249343890776161927414595)
  ·
    refine ⟨189374015836164242891121893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126249343890776161927414595 189374015836164242891121893)
    ·
      refine ⟨35507627969280795542085355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189374015836164242891121893 35507627969280795542085355)
      ·
        refine ⟨53261441953921193313128033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35507627969280795542085355 53261441953921193313128033)
        ·
          refine ⟨39946081465440894984846025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53261441953921193313128033 39946081465440894984846025)
          ·
            refine ⟨29959561099080671238634519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39946081465440894984846025 29959561099080671238634519)
            ·
              refine ⟨44939341648621006857951779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29959561099080671238634519 44939341648621006857951779)
              ·
                refine ⟨67409012472931510286927669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44939341648621006857951779 67409012472931510286927669)
                ·
                  refine ⟨6319594919337329089399469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67409012472931510286927669 6319594919337329089399469)
                  ·
                    refine ⟨2369848094751498408524801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6319594919337329089399469 2369848094751498408524801)
                    ·
                      refine ⟨1777386071063623806393601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2369848094751498408524801 1777386071063623806393601)
                      ·
                        rfl

theorem cell23_3461447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 3, 2].length) (baseStart_3461447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461447 prefixEnd_3461447 := by exact prefixLift 3461447
  have htrace : WordTrace (prefixWord ++ tailWord_3461447) baseStart_3461447 baseEnd_3461447 := by
    simpa [prefixWord, tailWord_3461447, baseEnd_3461447] using wordTrace_append hprefix tailTrace_3461447
  have hstable : (prefixWord ++ tailWord_3461447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461447).length < 2 ^ (prefixWord ++ tailWord_3461447).sum := by decide
  have hdescent : baseEnd_3461447 < baseStart_3461447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461577 : List Nat := [1, 2, 1, 1, 2, 1, 4, 4, 3, 4]
def baseStart_3461577 : Nat := 118140960795 + 3461577 * 2 ^ 59
def prefixEnd_3461577 : Nat := 4983230072969 + 3 ^ 40 * 3461577 * 2
def baseEnd_3461577 : Nat := 592484274516236099256001

theorem tailTrace_3461577 : CollatzResearch.WordTrace tailWord_3461577 prefixEnd_3461577 592484274516236099256001 := by
  unfold tailWord_3461577
  simp only [CollatzResearch.WordTrace]
  refine ⟨126254085380305194129646985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84169390253536796086431323 126254085380305194129646985)
  ·
    refine ⟨94690564035228895597235239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126254085380305194129646985 94690564035228895597235239)
    ·
      refine ⟨142035846052843343395852859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94690564035228895597235239 142035846052843343395852859)
      ·
        refine ⟨213053769079265015093779289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142035846052843343395852859 213053769079265015093779289)
        ·
          refine ⟨159790326809448761320334467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213053769079265015093779289 159790326809448761320334467)
          ·
            refine ⟨239685490214173141980501701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159790326809448761320334467 239685490214173141980501701)
            ·
              refine ⟨44941029415157464121344069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239685490214173141980501701 44941029415157464121344069)
              ·
                refine ⟨8426443015342024522752013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44941029415157464121344069 8426443015342024522752013)
                ·
                  refine ⟨3159916130753259196032005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8426443015342024522752013 3159916130753259196032005)
                  ·
                    refine ⟨592484274516236099256001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3159916130753259196032005 592484274516236099256001)
                    ·
                      rfl

theorem cell23_3461577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3, 4].length) (baseStart_3461577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461577 prefixEnd_3461577 := by exact prefixLift 3461577
  have htrace : WordTrace (prefixWord ++ tailWord_3461577) baseStart_3461577 baseEnd_3461577 := by
    simpa [prefixWord, tailWord_3461577, baseEnd_3461577] using wordTrace_append hprefix tailTrace_3461577
  have hstable : (prefixWord ++ tailWord_3461577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461577).length < 2 ^ (prefixWord ++ tailWord_3461577).sum := by decide
  have hdescent : baseEnd_3461577 < baseStart_3461577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461597 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_3461597 : Nat := 118140960795 + 3461597 * 2 ^ 59
def prefixEnd_3461597 : Nat := 4983230072969 + 3 ^ 40 * 3461597 * 2
def baseEnd_3461597 : Nat := 1777463093161798219517911

theorem tailTrace_3461597 : CollatzResearch.WordTrace tailWord_3461597 prefixEnd_3461597 1777463093161798219517911 := by
  unfold tailWord_3461597
  simp only [CollatzResearch.WordTrace]
  refine ⟨126254814840232737545375045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84169876560155158363583363 126254814840232737545375045)
  ·
    refine ⟨23672777782543638289757821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126254814840232737545375045 23672777782543638289757821)
    ·
      refine ⟨8877291668453864358659183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23672777782543638289757821 8877291668453864358659183)
      ·
        refine ⟨13315937502680796537988775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8877291668453864358659183 13315937502680796537988775)
        ·
          refine ⟨19973906254021194806983163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13315937502680796537988775 19973906254021194806983163)
          ·
            refine ⟨29960859381031792210474745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19973906254021194806983163 29960859381031792210474745)
            ·
              refine ⟨22470644535773844157856059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29960859381031792210474745 22470644535773844157856059)
              ·
                refine ⟨33705966803660766236784089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22470644535773844157856059 33705966803660766236784089)
                ·
                  refine ⟨25279475102745574677588067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33705966803660766236784089 25279475102745574677588067)
                  ·
                    refine ⟨37919212654118362016382101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25279475102745574677588067 37919212654118362016382101)
                    ·
                      refine ⟨1777463093161798219517911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37919212654118362016382101 1777463093161798219517911)
                      ·
                        rfl

theorem cell23_3461597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_3461597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461597 prefixEnd_3461597 := by exact prefixLift 3461597
  have htrace : WordTrace (prefixWord ++ tailWord_3461597) baseStart_3461597 baseEnd_3461597 := by
    simpa [prefixWord, tailWord_3461597, baseEnd_3461597] using wordTrace_append hprefix tailTrace_3461597
  have hstable : (prefixWord ++ tailWord_3461597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461597).length < 2 ^ (prefixWord ++ tailWord_3461597).sum := by decide
  have hdescent : baseEnd_3461597 < baseStart_3461597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461602 : List Nat := [3, 3, 3, 2, 2, 1, 2, 2, 5]
def baseStart_3461602 : Nat := 118140960795 + 3461602 * 2 ^ 59
def prefixEnd_3461602 : Nat := 4983230072969 + 3 ^ 40 * 3461602 * 2
def baseEnd_3461602 : Nat := 197496184507230077772821

theorem tailTrace_3461602 : CollatzResearch.WordTrace tailWord_3461602 prefixEnd_3461602 197496184507230077772821 := by
  unfold tailWord_3461602
  simp only [CollatzResearch.WordTrace]
  refine ⟨31563749301303655849826765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84169998136809748932871373 31563749301303655849826765)
  ·
    refine ⟨11836405987988870943685037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31563749301303655849826765 11836405987988870943685037)
    ·
      refine ⟨4438652245495826603881889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11836405987988870943685037 4438652245495826603881889)
      ·
        refine ⟨3328989184121869952911417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4438652245495826603881889 3328989184121869952911417)
        ·
          refine ⟨2496741888091402464683563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3328989184121869952911417 2496741888091402464683563)
          ·
            refine ⟨3745112832137103697025345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2496741888091402464683563 3745112832137103697025345)
            ·
              refine ⟨2808834624102827772769009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3745112832137103697025345 2808834624102827772769009)
              ·
                refine ⟨2106625968077120829576757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2808834624102827772769009 2106625968077120829576757)
                ·
                  refine ⟨197496184507230077772821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2106625968077120829576757 197496184507230077772821)
                  ·
                    rfl

theorem cell23_3461602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_3461602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461602 prefixEnd_3461602 := by exact prefixLift 3461602
  have htrace : WordTrace (prefixWord ++ tailWord_3461602) baseStart_3461602 baseEnd_3461602 := by
    simpa [prefixWord, tailWord_3461602, baseEnd_3461602] using wordTrace_append hprefix tailTrace_3461602
  have hstable : (prefixWord ++ tailWord_3461602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461602).length < 2 ^ (prefixWord ++ tailWord_3461602).sum := by decide
  have hdescent : baseEnd_3461602 < baseStart_3461602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461637 : List Nat := [1, 3, 1, 1, 2, 2, 4, 1, 3, 5]
def baseStart_3461637 : Nat := 118140960795 + 3461637 * 2 ^ 59
def prefixEnd_3461637 : Nat := 4983230072969 + 3 ^ 40 * 3461637 * 2
def baseEnd_3461637 : Nat := 592494544129326021005909

theorem tailTrace_3461637 : CollatzResearch.WordTrace tailWord_3461637 prefixEnd_3461637 592494544129326021005909 := by
  unfold tailWord_3461637
  simp only [CollatzResearch.WordTrace]
  refine ⟨126256273760087824376831165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84170849173391882917887443 126256273760087824376831165)
  ·
    refine ⟨47346102660032934141311687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126256273760087824376831165 47346102660032934141311687)
    ·
      refine ⟨71019153990049401211967531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47346102660032934141311687 71019153990049401211967531)
      ·
        refine ⟨106528730985074101817951297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71019153990049401211967531 106528730985074101817951297)
        ·
          refine ⟨79896548238805576363463473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106528730985074101817951297 79896548238805576363463473)
          ·
            refine ⟨59922411179104182272597605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79896548238805576363463473 59922411179104182272597605)
            ·
              refine ⟨11235452096082034176112051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59922411179104182272597605 11235452096082034176112051)
              ·
                refine ⟨16853178144123051264168077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11235452096082034176112051 16853178144123051264168077)
                ·
                  refine ⟨6319941804046144224063029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16853178144123051264168077 6319941804046144224063029)
                  ·
                    refine ⟨592494544129326021005909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6319941804046144224063029 592494544129326021005909)
                    ·
                      rfl

theorem cell23_3461637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 5].length) (baseStart_3461637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461637 prefixEnd_3461637 := by exact prefixLift 3461637
  have htrace : WordTrace (prefixWord ++ tailWord_3461637) baseStart_3461637 baseEnd_3461637 := by
    simpa [prefixWord, tailWord_3461637, baseEnd_3461637] using wordTrace_append hprefix tailTrace_3461637
  have hstable : (prefixWord ++ tailWord_3461637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461637).length < 2 ^ (prefixWord ++ tailWord_3461637).sum := by decide
  have hdescent : baseEnd_3461637 < baseStart_3461637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461645 : List Nat := [1, 7, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_3461645 : Nat := 118140960795 + 3461645 * 2 ^ 59
def prefixEnd_3461645 : Nat := 4983230072969 + 3 ^ 40 * 3461645 * 2
def baseEnd_3461645 : Nat := 592495913411071343905897

theorem tailTrace_3461645 : CollatzResearch.WordTrace tailWord_3461645 prefixEnd_3461645 592495913411071343905897 := by
  unfold tailWord_3461645
  simp only [CollatzResearch.WordTrace]
  refine ⟨126256565544058841743122389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84171043696039227828748259 126256565544058841743122389)
  ·
    refine ⟨2959138254938879103354431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 126256565544058841743122389 2959138254938879103354431)
    ·
      refine ⟨4438707382408318655031647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2959138254938879103354431 4438707382408318655031647)
      ·
        refine ⟨6658061073612477982547471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4438707382408318655031647 6658061073612477982547471)
        ·
          refine ⟨9987091610418716973821207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6658061073612477982547471 9987091610418716973821207)
          ·
            refine ⟨14980637415628075460731811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9987091610418716973821207 14980637415628075460731811)
            ·
              refine ⟨22470956123442113191097717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14980637415628075460731811 22470956123442113191097717)
              ·
                refine ⟨2106652136572698111665411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22470956123442113191097717 2106652136572698111665411)
                ·
                  refine ⟨3159978204859047167498117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2106652136572698111665411 3159978204859047167498117)
                  ·
                    refine ⟨592495913411071343905897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3159978204859047167498117 592495913411071343905897)
                    ·
                      rfl

theorem cell23_3461645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_3461645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461645 prefixEnd_3461645 := by exact prefixLift 3461645
  have htrace : WordTrace (prefixWord ++ tailWord_3461645) baseStart_3461645 baseEnd_3461645 := by
    simpa [prefixWord, tailWord_3461645, baseEnd_3461645] using wordTrace_append hprefix tailTrace_3461645
  have hstable : (prefixWord ++ tailWord_3461645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461645).length < 2 ^ (prefixWord ++ tailWord_3461645).sum := by decide
  have hdescent : baseEnd_3461645 < baseStart_3461645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461687 : List Nat := [1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 6]
def baseStart_3461687 : Nat := 118140960795 + 3461687 * 2 ^ 59
def prefixEnd_3461687 : Nat := 4983230072969 + 3 ^ 40 * 3461687 * 2
def baseEnd_3461687 : Nat := 1777509306420702867392497

theorem tailTrace_3461687 : CollatzResearch.WordTrace tailWord_3461687 prefixEnd_3461687 1777509306420702867392497 := by
  unfold tailWord_3461687
  simp only [CollatzResearch.WordTrace]
  refine ⟨126258097409906682916151315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84172064939937788610767543 126258097409906682916151315)
  ·
    refine ⟨189387146114860024374226973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126258097409906682916151315 189387146114860024374226973)
    ·
      refine ⟨71020179793072509140335115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189387146114860024374226973 71020179793072509140335115)
      ·
        refine ⟨106530269689608763710502673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71020179793072509140335115 106530269689608763710502673)
        ·
          refine ⟨79897702267206572782877005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106530269689608763710502673 79897702267206572782877005)
          ·
            refine ⟨29961638350202464793578877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79897702267206572782877005 29961638350202464793578877)
            ·
              refine ⟨11235614381325924297592079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29961638350202464793578877 11235614381325924297592079)
              ·
                refine ⟨16853421571988886446388119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11235614381325924297592079 16853421571988886446388119)
                ·
                  refine ⟨25280132357983329669582179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16853421571988886446388119 25280132357983329669582179)
                  ·
                    refine ⟨37920198536974994504373269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25280132357983329669582179 37920198536974994504373269)
                    ·
                      refine ⟨1777509306420702867392497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37920198536974994504373269 1777509306420702867392497)
                      ·
                        rfl

theorem cell23_3461687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_3461687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461687 prefixEnd_3461687 := by exact prefixLift 3461687
  have htrace : WordTrace (prefixWord ++ tailWord_3461687) baseStart_3461687 baseEnd_3461687 := by
    simpa [prefixWord, tailWord_3461687, baseEnd_3461687] using wordTrace_append hprefix tailTrace_3461687
  have hstable : (prefixWord ++ tailWord_3461687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461687).length < 2 ^ (prefixWord ++ tailWord_3461687).sum := by decide
  have hdescent : baseEnd_3461687 < baseStart_3461687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461702 : List Nat := [6, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3]
def baseStart_3461702 : Nat := 118140960795 + 3461702 * 2 ^ 59
def prefixEnd_3461702 : Nat := 4983230072969 + 3 ^ 40 * 3461702 * 2
def baseEnd_3461702 : Nat := 1777517008630520308704929

theorem tailTrace_3461702 : CollatzResearch.WordTrace tailWord_3461702 prefixEnd_3461702 1777517008630520308704929 := by
  unfold tailWord_3461702
  simp only [CollatzResearch.WordTrace]
  refine ⟨3945582640776635639935855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84172429669901560318631573 3945582640776635639935855)
  ·
    refine ⟨5918373961164953459903783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3945582640776635639935855 5918373961164953459903783)
    ·
      refine ⟨8877560941747430189855675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5918373961164953459903783 8877560941747430189855675)
      ·
        refine ⟨13316341412621145284783513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8877560941747430189855675 13316341412621145284783513)
        ·
          refine ⟨9987256059465858963587635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13316341412621145284783513 9987256059465858963587635)
          ·
            refine ⟨14980884089198788445381453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9987256059465858963587635 14980884089198788445381453)
            ·
              refine ⟨5617831533449545667018045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14980884089198788445381453 5617831533449545667018045)
              ·
                refine ⟨2106686825043579625131767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5617831533449545667018045 2106686825043579625131767)
                ·
                  refine ⟨3160030237565369437697651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2106686825043579625131767 3160030237565369437697651)
                  ·
                    refine ⟨4740045356348054156546477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3160030237565369437697651 4740045356348054156546477)
                    ·
                      refine ⟨1777517008630520308704929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4740045356348054156546477 1777517008630520308704929)
                      ·
                        rfl

theorem cell23_3461702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_3461702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461702 prefixEnd_3461702 := by exact prefixLift 3461702
  have htrace : WordTrace (prefixWord ++ tailWord_3461702) baseStart_3461702 baseEnd_3461702 := by
    simpa [prefixWord, tailWord_3461702, baseEnd_3461702] using wordTrace_append hprefix tailTrace_3461702
  have hstable : (prefixWord ++ tailWord_3461702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461702).length < 2 ^ (prefixWord ++ tailWord_3461702).sum := by decide
  have hdescent : baseEnd_3461702 < baseStart_3461702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461747 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 4]
def baseStart_3461747 : Nat := 118140960795 + 3461747 * 2 ^ 59
def prefixEnd_3461747 : Nat := 4983230072969 + 3 ^ 40 * 3461747 * 2
def baseEnd_3461747 : Nat := 1777540115259972632642221

theorem tailTrace_3461747 : CollatzResearch.WordTrace tailWord_3461747 prefixEnd_3461747 1777540115259972632642221 := by
  unfold tailWord_3461747
  simp only [CollatzResearch.WordTrace]
  refine ⟨126260285789689313163335495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84173523859792875442223663 126260285789689313163335495)
  ·
    refine ⟨189390428684533969745003243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126260285789689313163335495 189390428684533969745003243)
    ·
      refine ⟨284085643026800954617504865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189390428684533969745003243 284085643026800954617504865)
      ·
        refine ⟨213064232270100715963128649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284085643026800954617504865 213064232270100715963128649)
        ·
          refine ⟨159798174202575536972346487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213064232270100715963128649 159798174202575536972346487)
          ·
            refine ⟨239697261303863305458519731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159798174202575536972346487 239697261303863305458519731)
            ·
              refine ⟨359545891955794958187779597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239697261303863305458519731 359545891955794958187779597)
              ·
                refine ⟨134829709483423109320417349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 359545891955794958187779597 134829709483423109320417349)
                ·
                  refine ⟨25280570528141832997578253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134829709483423109320417349 25280570528141832997578253)
                  ·
                    refine ⟨9480213948053187374091845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25280570528141832997578253 9480213948053187374091845)
                    ·
                      refine ⟨1777540115259972632642221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9480213948053187374091845 1777540115259972632642221)
                      ·
                        rfl

theorem cell23_3461747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 4].length) (baseStart_3461747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461747 prefixEnd_3461747 := by exact prefixLift 3461747
  have htrace : WordTrace (prefixWord ++ tailWord_3461747) baseStart_3461747 baseEnd_3461747 := by
    simpa [prefixWord, tailWord_3461747, baseEnd_3461747] using wordTrace_append hprefix tailTrace_3461747
  have hstable : (prefixWord ++ tailWord_3461747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461747).length < 2 ^ (prefixWord ++ tailWord_3461747).sum := by decide
  have hdescent : baseEnd_3461747 < baseStart_3461747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461762 : List Nat := [3, 4, 3, 1, 1, 2, 1, 1, 1, 1, 5]
def baseStart_3461762 : Nat := 118140960795 + 3461762 * 2 ^ 59
def prefixEnd_3461762 : Nat := 4983230072969 + 3 ^ 40 * 3461762 * 2
def baseEnd_3461762 : Nat := 1777547817469790073954653

theorem tailTrace_3461762 : CollatzResearch.WordTrace tailWord_3461762 prefixEnd_3461762 1777547817469790073954653 := by
  unfold tailWord_3461762
  simp only [CollatzResearch.WordTrace]
  refine ⟨31565208221158742681282885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84173888589756647150087693 31565208221158742681282885)
  ·
    refine ⟨5918476541467264252740541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31565208221158742681282885 5918476541467264252740541)
    ·
      refine ⟨2219428703050224094777703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5918476541467264252740541 2219428703050224094777703)
      ·
        refine ⟨3329143054575336142166555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2219428703050224094777703 3329143054575336142166555)
        ·
          refine ⟨4993714581863004213249833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3329143054575336142166555 4993714581863004213249833)
          ·
            refine ⟨3745285936397253159937375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4993714581863004213249833 3745285936397253159937375)
            ·
              refine ⟨5617928904595879739906063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3745285936397253159937375 5617928904595879739906063)
              ·
                refine ⟨8426893356893819609859095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5617928904595879739906063 8426893356893819609859095)
                ·
                  refine ⟨12640340035340729414788643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8426893356893819609859095 12640340035340729414788643)
                  ·
                    refine ⟨18960510053011094122182965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12640340035340729414788643 18960510053011094122182965)
                    ·
                      refine ⟨1777547817469790073954653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18960510053011094122182965 1777547817469790073954653)
                      ·
                        rfl

theorem cell23_3461762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_3461762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461762 prefixEnd_3461762 := by exact prefixLift 3461762
  have htrace : WordTrace (prefixWord ++ tailWord_3461762) baseStart_3461762 baseEnd_3461762 := by
    simpa [prefixWord, tailWord_3461762, baseEnd_3461762] using wordTrace_append hprefix tailTrace_3461762
  have hstable : (prefixWord ++ tailWord_3461762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461762).length < 2 ^ (prefixWord ++ tailWord_3461762).sum := by decide
  have hdescent : baseEnd_3461762 < baseStart_3461762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461774 : List Nat := [4, 1, 1, 3, 1, 1, 2, 2, 2, 6]
def baseStart_3461774 : Nat := 118140960795 + 3461774 * 2 ^ 59
def prefixEnd_3461774 : Nat := 4983230072969 + 3 ^ 40 * 3461774 * 2
def baseEnd_3461774 : Nat := 592517993079214675668199

theorem tailTrace_3461774 : CollatzResearch.WordTrace tailWord_3461774 prefixEnd_3461774 592517993079214675668199 := by
  unfold tailWord_3461774
  simp only [CollatzResearch.WordTrace]
  refine ⟨15782658820073937096821047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84174180373727664516378917 15782658820073937096821047)
  ·
    refine ⟨23673988230110905645231571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15782658820073937096821047 23673988230110905645231571)
    ·
      refine ⟨35510982345166358467847357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23673988230110905645231571 35510982345166358467847357)
      ·
        refine ⟨13316618379437384425442759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35510982345166358467847357 13316618379437384425442759)
        ·
          refine ⟨19974927569156076638164139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13316618379437384425442759 19974927569156076638164139)
          ·
            refine ⟨29962391353734114957246209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19974927569156076638164139 29962391353734114957246209)
            ·
              refine ⟨22471793515300586217934657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29962391353734114957246209 22471793515300586217934657)
              ·
                refine ⟨16853845136475439663450993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22471793515300586217934657 16853845136475439663450993)
                ·
                  refine ⟨12640383852356579747588245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16853845136475439663450993 12640383852356579747588245)
                  ·
                    refine ⟨592517993079214675668199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12640383852356579747588245 592517993079214675668199)
                    ·
                      rfl

theorem cell23_3461774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_3461774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461774 prefixEnd_3461774 := by exact prefixLift 3461774
  have htrace : WordTrace (prefixWord ++ tailWord_3461774) baseStart_3461774 baseEnd_3461774 := by
    simpa [prefixWord, tailWord_3461774, baseEnd_3461774] using wordTrace_append hprefix tailTrace_3461774
  have hstable : (prefixWord ++ tailWord_3461774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461774).length < 2 ^ (prefixWord ++ tailWord_3461774).sum := by decide
  have hdescent : baseEnd_3461774 < baseStart_3461774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461784 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 1, 6, 3]
def baseStart_3461784 : Nat := 118140960795 + 3461784 * 2 ^ 59
def prefixEnd_3461784 : Nat := 4983230072969 + 3 ^ 40 * 3461784 * 2
def baseEnd_3461784 : Nat := 1777559114044188987879551

theorem tailTrace_3461784 : CollatzResearch.WordTrace tailWord_3461784 prefixEnd_3461784 1777559114044188987879551 := by
  unfold tailWord_3461784
  simp only [CollatzResearch.WordTrace]
  refine ⟨63130817645277634241216203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84174423527036845654954937 63130817645277634241216203)
  ·
    refine ⟨94696226467916451361824305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63130817645277634241216203 94696226467916451361824305)
    ·
      refine ⟨71022169850937338521368229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94696226467916451361824305 71022169850937338521368229)
      ·
        refine ⟨13316656847050750972756543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71022169850937338521368229 13316656847050750972756543)
        ·
          refine ⟨19974985270576126459134815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13316656847050750972756543 19974985270576126459134815)
          ·
            refine ⟨29962477905864189688702223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19974985270576126459134815 29962477905864189688702223)
            ·
              refine ⟨44943716858796284533053335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29962477905864189688702223 44943716858796284533053335)
              ·
                refine ⟨67415575288194426799580003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44943716858796284533053335 67415575288194426799580003)
                ·
                  refine ⟨101123362932291640199370005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67415575288194426799580003 101123362932291640199370005)
                  ·
                    refine ⟨4740157637451170634345469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101123362932291640199370005 4740157637451170634345469)
                    ·
                      refine ⟨1777559114044188987879551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4740157637451170634345469 1777559114044188987879551)
                      ·
                        rfl

theorem cell23_3461784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_3461784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461784 prefixEnd_3461784 := by exact prefixLift 3461784
  have htrace : WordTrace (prefixWord ++ tailWord_3461784) baseStart_3461784 baseEnd_3461784 := by
    simpa [prefixWord, tailWord_3461784, baseEnd_3461784] using wordTrace_append hprefix tailTrace_3461784
  have hstable : (prefixWord ++ tailWord_3461784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461784).length < 2 ^ (prefixWord ++ tailWord_3461784).sum := by decide
  have hdescent : baseEnd_3461784 < baseStart_3461784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461821 : List Nat := [1, 4, 1, 2, 1, 3, 1, 5, 5]
def baseStart_3461821 : Nat := 118140960795 + 3461821 * 2 ^ 59
def prefixEnd_3461821 : Nat := 4983230072969 + 3 ^ 40 * 3461821 * 2
def baseEnd_3461821 : Nat := 197508679203156149235209

theorem tailTrace_3461821 : CollatzResearch.WordTrace tailWord_3461821 prefixEnd_3461821 197508679203156149235209 := by
  unfold tailWord_3461821
  simp only [CollatzResearch.WordTrace]
  refine ⟨126262984791421223801529317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84175323194280815867686211 126262984791421223801529317)
  ·
    refine ⟨23674309648391479462786747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126262984791421223801529317 23674309648391479462786747)
    ·
      refine ⟨35511464472587219194180121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23674309648391479462786747 35511464472587219194180121)
      ·
        refine ⟨26633598354440414395635091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35511464472587219194180121 26633598354440414395635091)
        ·
          refine ⟨39950397531660621593452637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26633598354440414395635091 39950397531660621593452637)
          ·
            refine ⟨14981399074372733097544739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39950397531660621593452637 14981399074372733097544739)
            ·
              refine ⟨22472098611559099646317109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14981399074372733097544739 22472098611559099646317109)
              ·
                refine ⟨2106759244833665591842229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22472098611559099646317109 2106759244833665591842229)
                ·
                  refine ⟨197508679203156149235209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2106759244833665591842229 197508679203156149235209)
                  ·
                    rfl

theorem cell23_3461821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5, 5].length) (baseStart_3461821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461821 prefixEnd_3461821 := by exact prefixLift 3461821
  have htrace : WordTrace (prefixWord ++ tailWord_3461821) baseStart_3461821 baseEnd_3461821 := by
    simpa [prefixWord, tailWord_3461821, baseEnd_3461821] using wordTrace_append hprefix tailTrace_3461821
  have hstable : (prefixWord ++ tailWord_3461821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461821).length < 2 ^ (prefixWord ++ tailWord_3461821).sum := by decide
  have hdescent : baseEnd_3461821 < baseStart_3461821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461949 : List Nat := [1, 4, 1, 4, 2, 2, 2, 2, 1, 4]
def baseStart_3461949 : Nat := 118140960795 + 3461949 * 2 ^ 59
def prefixEnd_3461949 : Nat := 4983230072969 + 3 ^ 40 * 3461949 * 2
def baseEnd_3461949 : Nat := 592547946117393614105431

theorem tailTrace_3461949 : CollatzResearch.WordTrace tailWord_3461949 prefixEnd_3461949 592547946117393614105431 := by
  unfold tailWord_3461949
  simp only [CollatzResearch.WordTrace]
  refine ⟨126267653334957501662188901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84178435556638334441459267 126267653334957501662188901)
  ·
    refine ⟨23675185000304531561660419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126267653334957501662188901 23675185000304531561660419)
    ·
      refine ⟨35512777500456797342490629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23675185000304531561660419 35512777500456797342490629)
      ·
        refine ⟨6658645781335649501716993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35512777500456797342490629 6658645781335649501716993)
        ·
          refine ⟨4993984336001737126287745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6658645781335649501716993 4993984336001737126287745)
          ·
            refine ⟨3745488252001302844715809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4993984336001737126287745 3745488252001302844715809)
            ·
              refine ⟨2809116189000977133536857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3745488252001302844715809 2809116189000977133536857)
              ·
                refine ⟨2106837141750732850152643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2809116189000977133536857 2106837141750732850152643)
                ·
                  refine ⟨3160255712626099275228965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2106837141750732850152643 3160255712626099275228965)
                  ·
                    refine ⟨592547946117393614105431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3160255712626099275228965 592547946117393614105431)
                    ·
                      rfl

theorem cell23_3461949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_3461949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461949 prefixEnd_3461949 := by exact prefixLift 3461949
  have htrace : WordTrace (prefixWord ++ tailWord_3461949) baseStart_3461949 baseEnd_3461949 := by
    simpa [prefixWord, tailWord_3461949, baseEnd_3461949] using wordTrace_append hprefix tailTrace_3461949
  have hstable : (prefixWord ++ tailWord_3461949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461949).length < 2 ^ (prefixWord ++ tailWord_3461949).sum := by decide
  have hdescent : baseEnd_3461949 < baseStart_3461949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461955 : List Nat := [1, 1, 1, 3, 1, 4, 3, 4, 1, 1, 3]
def baseStart_3461955 : Nat := 118140960795 + 3461955 * 2 ^ 59
def prefixEnd_3461955 : Nat := 4983230072969 + 3 ^ 40 * 3461955 * 2
def baseEnd_3461955 : Nat := 1777646919236107818841265

theorem tailTrace_3461955 : CollatzResearch.WordTrace tailWord_3461955 prefixEnd_3461955 1777646919236107818841265 := by
  unfold tailWord_3461955
  simp only [CollatzResearch.WordTrace]
  refine ⟨126267872172935764686907319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84178581448623843124604879 126267872172935764686907319)
  ·
    refine ⟨189401808259403647030360979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126267872172935764686907319 189401808259403647030360979)
    ·
      refine ⟨284102712389105470545541469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189401808259403647030360979 284102712389105470545541469)
      ·
        refine ⟨106538517145914551454578051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284102712389105470545541469 106538517145914551454578051)
        ·
          refine ⟨159807775718871827181867077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106538517145914551454578051 159807775718871827181867077)
          ·
            refine ⟨29963957947288467596600077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159807775718871827181867077 29963957947288467596600077)
            ·
              refine ⟨11236484230233175348725029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29963957947288467596600077 11236484230233175348725029)
              ·
                refine ⟨2106840793168720377885943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11236484230233175348725029 2106840793168720377885943)
                ·
                  refine ⟨3160261189753080566828915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2106840793168720377885943 3160261189753080566828915)
                  ·
                    refine ⟨4740391784629620850243373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3160261189753080566828915 4740391784629620850243373)
                    ·
                      refine ⟨1777646919236107818841265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4740391784629620850243373 1777646919236107818841265)
                      ·
                        rfl

theorem cell23_3461955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4, 1, 1, 3].length) (baseStart_3461955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461955 prefixEnd_3461955 := by exact prefixLift 3461955
  have htrace : WordTrace (prefixWord ++ tailWord_3461955) baseStart_3461955 baseEnd_3461955 := by
    simpa [prefixWord, tailWord_3461955, baseEnd_3461955] using wordTrace_append hprefix tailTrace_3461955
  have hstable : (prefixWord ++ tailWord_3461955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461955).length < 2 ^ (prefixWord ++ tailWord_3461955).sum := by decide
  have hdescent : baseEnd_3461955 < baseStart_3461955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3461961 : List Nat := [1, 2, 1, 1, 2, 5, 1, 2, 3, 1, 4]
def baseStart_3461961 : Nat := 118140960795 + 3461961 * 2 ^ 59
def prefixEnd_3461961 : Nat := 4983230072969 + 3 ^ 40 * 3461961 * 2
def baseEnd_3461961 : Nat := 1777650000120034795366237

theorem tailTrace_3461961 : CollatzResearch.WordTrace tailWord_3461961 prefixEnd_3461961 1777650000120034795366237 := by
  unfold tailWord_3461961
  simp only [CollatzResearch.WordTrace]
  refine ⟨126268091010914027711625737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84178727340609351807750491 126268091010914027711625737)
  ·
    refine ⟨94701068258185520783719303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126268091010914027711625737 94701068258185520783719303)
    ·
      refine ⟨142051602387278281175578955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94701068258185520783719303 142051602387278281175578955)
      ·
        refine ⟨213077403580917421763368433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142051602387278281175578955 213077403580917421763368433)
        ·
          refine ⟨159808052685688066322526325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213077403580917421763368433 159808052685688066322526325)
          ·
            refine ⟨14982004939283256217736843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 159808052685688066322526325 14982004939283256217736843)
            ·
              refine ⟨22473007408924884326605265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14982004939283256217736843 22473007408924884326605265)
              ·
                refine ⟨16854755556693663244953949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22473007408924884326605265 16854755556693663244953949)
                ·
                  refine ⟨6320533333760123716857731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16854755556693663244953949 6320533333760123716857731)
                  ·
                    refine ⟨9480800000640185575286597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6320533333760123716857731 9480800000640185575286597)
                    ·
                      refine ⟨1777650000120034795366237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9480800000640185575286597 1777650000120034795366237)
                      ·
                        rfl

theorem cell23_3461961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 1, 4].length) (baseStart_3461961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3461961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3461961 prefixEnd_3461961 := by exact prefixLift 3461961
  have htrace : WordTrace (prefixWord ++ tailWord_3461961) baseStart_3461961 baseEnd_3461961 := by
    simpa [prefixWord, tailWord_3461961, baseEnd_3461961] using wordTrace_append hprefix tailTrace_3461961
  have hstable : (prefixWord ++ tailWord_3461961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3461961).length < 2 ^ (prefixWord ++ tailWord_3461961).sum := by decide
  have hdescent : baseEnd_3461961 < baseStart_3461961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3461961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462005 : List Nat := [1, 3, 4, 1, 1, 2, 3, 2, 2, 4]
def baseStart_3462005 : Nat := 118140960795 + 3462005 * 2 ^ 59
def prefixEnd_3462005 : Nat := 4983230072969 + 3 ^ 40 * 3462005 * 2
def baseEnd_3462005 : Nat := 592557531089610874405345

theorem tailTrace_3462005 : CollatzResearch.WordTrace tailWord_3462005 prefixEnd_3462005 592557531089610874405345 := by
  unfold tailWord_3462005
  simp only [CollatzResearch.WordTrace]
  refine ⟨126269695822754623226227469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84179797215169748817484979 126269695822754623226227469)
  ·
    refine ⟨47351135933532983709835301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126269695822754623226227469 47351135933532983709835301)
    ·
      refine ⟨8878337987537434445594119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47351135933532983709835301 8878337987537434445594119)
      ·
        refine ⟨13317506981306151668391179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8878337987537434445594119 13317506981306151668391179)
        ·
          refine ⟨19976260471959227502586769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13317506981306151668391179 19976260471959227502586769)
          ·
            refine ⟨14982195353969420626940077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19976260471959227502586769 14982195353969420626940077)
            ·
              refine ⟨5618323257738532735102529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14982195353969420626940077 5618323257738532735102529)
              ·
                refine ⟨4213742443303899551326897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5618323257738532735102529 4213742443303899551326897)
                ·
                  refine ⟨3160306832477924663495173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4213742443303899551326897 3160306832477924663495173)
                  ·
                    refine ⟨592557531089610874405345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3160306832477924663495173 592557531089610874405345)
                    ·
                      rfl

theorem cell23_3462005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_3462005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462005 prefixEnd_3462005 := by exact prefixLift 3462005
  have htrace : WordTrace (prefixWord ++ tailWord_3462005) baseStart_3462005 baseEnd_3462005 := by
    simpa [prefixWord, tailWord_3462005, baseEnd_3462005] using wordTrace_append hprefix tailTrace_3462005
  have hstable : (prefixWord ++ tailWord_3462005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462005).length < 2 ^ (prefixWord ++ tailWord_3462005).sum := by decide
  have hdescent : baseEnd_3462005 < baseStart_3462005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462011 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 3, 3, 3]
def baseStart_3462011 : Nat := 118140960795 + 3462011 * 2 ^ 59
def prefixEnd_3462011 : Nat := 4983230072969 + 3 ^ 40 * 3462011 * 2
def baseEnd_3462011 : Nat := 1777675674152759599741007

theorem tailTrace_3462011 : CollatzResearch.WordTrace tailWord_3462011 prefixEnd_3462011 1777675674152759599741007 := by
  unfold tailWord_3462011
  simp only [CollatzResearch.WordTrace]
  refine ⟨126269914660732886250945887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84179943107155257500630591 126269914660732886250945887)
  ·
    refine ⟨189404871991099329376418831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126269914660732886250945887 189404871991099329376418831)
    ·
      refine ⟨284107307986648994064628247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189404871991099329376418831 284107307986648994064628247)
      ·
        refine ⟨426160961979973491096942371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284107307986648994064628247 426160961979973491096942371)
        ·
          refine ⟨639241442969960236645413557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426160961979973491096942371 639241442969960236645413557)
          ·
            refine ⟨59928885278433772185507521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 639241442969960236645413557 59928885278433772185507521)
            ·
              refine ⟨44946663958825329139130641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59928885278433772185507521 44946663958825329139130641)
              ·
                refine ⟨33709997969118996854347981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44946663958825329139130641 33709997969118996854347981)
                ·
                  refine ⟨12641249238419623820380493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33709997969118996854347981 12641249238419623820380493)
                  ·
                    refine ⟨4740468464407358932642685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12641249238419623820380493 4740468464407358932642685)
                    ·
                      refine ⟨1777675674152759599741007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4740468464407358932642685 1777675674152759599741007)
                      ·
                        rfl

theorem cell23_3462011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3, 3].length) (baseStart_3462011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462011 prefixEnd_3462011 := by exact prefixLift 3462011
  have htrace : WordTrace (prefixWord ++ tailWord_3462011) baseStart_3462011 baseEnd_3462011 := by
    simpa [prefixWord, tailWord_3462011, baseEnd_3462011] using wordTrace_append hprefix tailTrace_3462011
  have hstable : (prefixWord ++ tailWord_3462011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462011).length < 2 ^ (prefixWord ++ tailWord_3462011).sum := by decide
  have hdescent : baseEnd_3462011 < baseStart_3462011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462028 : List Nat := [2, 2, 1, 2, 1, 2, 5, 1, 1, 3, 3]
def baseStart_3462028 : Nat := 118140960795 + 3462028 * 2 ^ 59
def prefixEnd_3462028 : Nat := 4983230072969 + 3 ^ 40 * 3462028 * 2
def baseEnd_3462028 : Nat := 1777684403323886033228429

theorem tailTrace_3462028 : CollatzResearch.WordTrace tailWord_3462028 prefixEnd_3462028 1777684403323886033228429 := by
  unfold tailWord_3462028
  simp only [CollatzResearch.WordTrace]
  refine ⟨63135267350835649077157369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84180356467780865436209825 63135267350835649077157369)
  ·
    refine ⟨47351450513126736807868027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63135267350835649077157369 47351450513126736807868027)
    ·
      refine ⟨71027175769690105211802041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47351450513126736807868027 71027175769690105211802041)
      ·
        refine ⟨53270381827267578908851531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71027175769690105211802041 53270381827267578908851531)
        ·
          refine ⟨79905572740901368363277297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53270381827267578908851531 79905572740901368363277297)
          ·
            refine ⟨59929179555676026272457973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79905572740901368363277297 59929179555676026272457973)
            ·
              refine ⟨5618360583344627463042935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59929179555676026272457973 5618360583344627463042935)
              ·
                refine ⟨8427540875016941194564403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5618360583344627463042935 8427540875016941194564403)
                ·
                  refine ⟨12641311312525411791846605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8427540875016941194564403 12641311312525411791846605)
                  ·
                    refine ⟨4740491742197029421942477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12641311312525411791846605 4740491742197029421942477)
                    ·
                      refine ⟨1777684403323886033228429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4740491742197029421942477 1777684403323886033228429)
                      ·
                        rfl

theorem cell23_3462028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_3462028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462028 prefixEnd_3462028 := by exact prefixLift 3462028
  have htrace : WordTrace (prefixWord ++ tailWord_3462028) baseStart_3462028 baseEnd_3462028 := by
    simpa [prefixWord, tailWord_3462028, baseEnd_3462028] using wordTrace_append hprefix tailTrace_3462028
  have hstable : (prefixWord ++ tailWord_3462028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462028).length < 2 ^ (prefixWord ++ tailWord_3462028).sum := by decide
  have hdescent : baseEnd_3462028 < baseStart_3462028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462102 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2]
def baseStart_3462102 : Nat := 118140960795 + 3462102 * 2 ^ 59
def prefixEnd_3462102 : Nat := 4983230072969 + 3 ^ 40 * 3462102 * 2
def baseEnd_3462102 : Nat := 1777722400892318743703089

theorem tailTrace_3462102 : CollatzResearch.WordTrace tailWord_3462102 prefixEnd_3462102 1777722400892318743703089 := by
  unfold tailWord_3462102
  simp only [CollatzResearch.WordTrace]
  refine ⟨7892077106462700549531785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84182155802268805861672373 7892077106462700549531785)
  ·
    refine ⟨5919057829847025412148839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7892077106462700549531785 5919057829847025412148839)
    ·
      refine ⟨8878586744770538118223259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5919057829847025412148839 8878586744770538118223259)
      ·
        refine ⟨13317880117155807177334889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8878586744770538118223259 13317880117155807177334889)
        ·
          refine ⟨9988410087866855383001167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13317880117155807177334889 9988410087866855383001167)
          ·
            refine ⟨14982615131800283074501751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9988410087866855383001167 14982615131800283074501751)
            ·
              refine ⟨22473922697700424611752627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14982615131800283074501751 22473922697700424611752627)
              ·
                refine ⟨33710884046550636917628941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22473922697700424611752627 33710884046550636917628941)
                ·
                  refine ⟨12641581517456488844110853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33710884046550636917628941 12641581517456488844110853)
                  ·
                    refine ⟨2370296534523091658270785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12641581517456488844110853 2370296534523091658270785)
                    ·
                      refine ⟨1777722400892318743703089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2370296534523091658270785 1777722400892318743703089)
                      ·
                        rfl

theorem cell23_3462102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_3462102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462102 prefixEnd_3462102 := by exact prefixLift 3462102
  have htrace : WordTrace (prefixWord ++ tailWord_3462102) baseStart_3462102 baseEnd_3462102 := by
    simpa [prefixWord, tailWord_3462102, baseEnd_3462102] using wordTrace_append hprefix tailTrace_3462102
  have hstable : (prefixWord ++ tailWord_3462102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462102).length < 2 ^ (prefixWord ++ tailWord_3462102).sum := by decide
  have hdescent : baseEnd_3462102 < baseStart_3462102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462119 : List Nat := [1, 1, 5, 2, 2, 2, 2, 2, 2, 2, 2]
def baseStart_3462119 : Nat := 118140960795 + 3462119 * 2 ^ 59
def prefixEnd_3462119 : Nat := 4983230072969 + 3 ^ 40 * 3462119 * 2
def baseEnd_3462119 : Nat := 1777731130063445177190511

theorem tailTrace_3462119 : CollatzResearch.WordTrace tailWord_3462119 prefixEnd_3462119 1777731130063445177190511 := by
  unfold tailWord_3462119
  simp only [CollatzResearch.WordTrace]
  refine ⟨126273853744341620695877411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84182569162894413797251607 126273853744341620695877411)
  ·
    refine ⟨189410780616512431043816117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126273853744341620695877411 189410780616512431043816117)
    ·
      refine ⟨17757260682798040410357761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189410780616512431043816117 17757260682798040410357761)
      ·
        refine ⟨13317945512098530307768321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17757260682798040410357761 13317945512098530307768321)
        ·
          refine ⟨9988459134073897730826241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13317945512098530307768321 9988459134073897730826241)
          ·
            refine ⟨7491344350555423298119681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9988459134073897730826241 7491344350555423298119681)
            ·
              refine ⟨5618508262916567473589761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7491344350555423298119681 5618508262916567473589761)
              ·
                refine ⟨4213881197187425605192321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5618508262916567473589761 4213881197187425605192321)
                ·
                  refine ⟨3160410897890569203894241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4213881197187425605192321 3160410897890569203894241)
                  ·
                    refine ⟨2370308173417926902920681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3160410897890569203894241 2370308173417926902920681)
                    ·
                      refine ⟨1777731130063445177190511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2370308173417926902920681 1777731130063445177190511)
                      ·
                        rfl

theorem cell23_3462119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_3462119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462119 prefixEnd_3462119 := by exact prefixLift 3462119
  have htrace : WordTrace (prefixWord ++ tailWord_3462119) baseStart_3462119 baseEnd_3462119 := by
    simpa [prefixWord, tailWord_3462119, baseEnd_3462119] using wordTrace_append hprefix tailTrace_3462119
  have hstable : (prefixWord ++ tailWord_3462119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462119).length < 2 ^ (prefixWord ++ tailWord_3462119).sum := by decide
  have hdescent : baseEnd_3462119 < baseStart_3462119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462155 : List Nat := [1, 1, 1, 1, 6, 4, 1, 1, 2, 5]
def baseStart_3462155 : Nat := 118140960795 + 3462155 * 2 ^ 59
def prefixEnd_3462155 : Nat := 4983230072969 + 3 ^ 40 * 3462155 * 2
def baseEnd_3462155 : Nat := 592583205122335678780115

theorem tailTrace_3462155 : CollatzResearch.WordTrace tailWord_3462155 prefixEnd_3462155 592583205122335678780115 := by
  unfold tailWord_3462155
  simp only [CollatzResearch.WordTrace]
  refine ⟨126275166772211198844187919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84183444514807465896125279 126275166772211198844187919)
  ·
    refine ⟨189412750158316798266281879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126275166772211198844187919 189412750158316798266281879)
    ·
      refine ⟨284119125237475197399422819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189412750158316798266281879 284119125237475197399422819)
      ·
        refine ⟨426178687856212796099134229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284119125237475197399422819 426178687856212796099134229)
        ·
          refine ⟨19977125993259974817146917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 426178687856212796099134229 19977125993259974817146917)
          ·
            refine ⟨3745711123736245278215047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19977125993259974817146917 3745711123736245278215047)
            ·
              refine ⟨5618566685604367917322571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3745711123736245278215047 5618566685604367917322571)
              ·
                refine ⟨8427850028406551875983857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5618566685604367917322571 8427850028406551875983857)
                ·
                  refine ⟨6320887521304913906987893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8427850028406551875983857 6320887521304913906987893)
                  ·
                    refine ⟨592583205122335678780115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6320887521304913906987893 592583205122335678780115)
                    ·
                      rfl

theorem cell23_3462155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 5].length) (baseStart_3462155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462155 prefixEnd_3462155 := by exact prefixLift 3462155
  have htrace : WordTrace (prefixWord ++ tailWord_3462155) baseStart_3462155 baseEnd_3462155 := by
    simpa [prefixWord, tailWord_3462155, baseEnd_3462155] using wordTrace_append hprefix tailTrace_3462155
  have hstable : (prefixWord ++ tailWord_3462155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462155).length < 2 ^ (prefixWord ++ tailWord_3462155).sum := by decide
  have hdescent : baseEnd_3462155 < baseStart_3462155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462175 : List Nat := [1, 1, 2, 4, 1, 3, 1, 2, 2, 4, 2]
def baseStart_3462175 : Nat := 118140960795 + 3462175 * 2 ^ 59
def prefixEnd_3462175 : Nat := 4983230072969 + 3 ^ 40 * 3462175 * 2
def baseEnd_3462175 : Nat := 1777759884980096958090253

theorem tailTrace_3462175 : CollatzResearch.WordTrace tailWord_3462175 prefixEnd_3462175 1777759884980096958090253 := by
  unfold tailWord_3462175
  simp only [CollatzResearch.WordTrace]
  refine ⟨126275896232138742259915979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84183930821425828173277319 126275896232138742259915979)
  ·
    refine ⟨189413844348208113389873969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126275896232138742259915979 189413844348208113389873969)
    ·
      refine ⟨142060383261156085042405477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189413844348208113389873969 142060383261156085042405477)
      ·
        refine ⟨26636321861466765945451027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142060383261156085042405477 26636321861466765945451027)
        ·
          refine ⟨39954482792200148918176541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26636321861466765945451027 39954482792200148918176541)
          ·
            refine ⟨14982931047075055844316203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39954482792200148918176541 14982931047075055844316203)
            ·
              refine ⟨22474396570612583766474305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14982931047075055844316203 22474396570612583766474305)
              ·
                refine ⟨16855797427959437824855729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22474396570612583766474305 16855797427959437824855729)
                ·
                  refine ⟨12641848070969578368641797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16855797427959437824855729 12641848070969578368641797)
                  ·
                    refine ⟨2370346513306795944120337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12641848070969578368641797 2370346513306795944120337)
                    ·
                      refine ⟨1777759884980096958090253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2370346513306795944120337 1777759884980096958090253)
                      ·
                        rfl

theorem cell23_3462175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_3462175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462175 prefixEnd_3462175 := by exact prefixLift 3462175
  have htrace : WordTrace (prefixWord ++ tailWord_3462175) baseStart_3462175 baseEnd_3462175 := by
    simpa [prefixWord, tailWord_3462175, baseEnd_3462175] using wordTrace_append hprefix tailTrace_3462175
  have hstable : (prefixWord ++ tailWord_3462175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462175).length < 2 ^ (prefixWord ++ tailWord_3462175).sum := by decide
  have hdescent : baseEnd_3462175 < baseStart_3462175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462191 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 9]
def baseStart_3462191 : Nat := 118140960795 + 3462191 * 2 ^ 59
def prefixEnd_3462191 : Nat := 4983230072969 + 3 ^ 40 * 3462191 * 2
def baseEnd_3462191 : Nat := 1777768100670568895490179

theorem tailTrace_3462191 : CollatzResearch.WordTrace tailWord_3462191 prefixEnd_3462191 1777768100670568895490179 := by
  unfold tailWord_3462191
  simp only [CollatzResearch.WordTrace]
  refine ⟨126276479800080776992498427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84184319866720517994998951 126276479800080776992498427)
  ·
    refine ⟨189414719700121165488747641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126276479800080776992498427 189414719700121165488747641)
    ·
      refine ⟨142061039775090874116560731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189414719700121165488747641 142061039775090874116560731)
      ·
        refine ⟨213091559662636311174841097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142061039775090874116560731 213091559662636311174841097)
        ·
          refine ⟨159818669746977233381130823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213091559662636311174841097 159818669746977233381130823)
          ·
            refine ⟨239728004620465850071696235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159818669746977233381130823 239728004620465850071696235)
            ·
              refine ⟨359592006930698775107544353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239728004620465850071696235 359592006930698775107544353)
              ·
                refine ⟨269694005198024081330658265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359592006930698775107544353 269694005198024081330658265)
                ·
                  refine ⟨202270503898518060997993699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 269694005198024081330658265 202270503898518060997993699)
                  ·
                    refine ⟨303405755847777091496990549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 202270503898518060997993699 303405755847777091496990549)
                    ·
                      refine ⟨1777768100670568895490179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 303405755847777091496990549 1777768100670568895490179)
                      ·
                        rfl

theorem cell23_3462191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 9].length) (baseStart_3462191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462191 prefixEnd_3462191 := by exact prefixLift 3462191
  have htrace : WordTrace (prefixWord ++ tailWord_3462191) baseStart_3462191 baseEnd_3462191 := by
    simpa [prefixWord, tailWord_3462191, baseEnd_3462191] using wordTrace_append hprefix tailTrace_3462191
  have hstable : (prefixWord ++ tailWord_3462191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462191).length < 2 ^ (prefixWord ++ tailWord_3462191).sum := by decide
  have hdescent : baseEnd_3462191 < baseStart_3462191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462208 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 3]
def baseStart_3462208 : Nat := 118140960795 + 3462208 * 2 ^ 59
def prefixEnd_3462208 : Nat := 4983230072969 + 3 ^ 40 * 3462208 * 2
def baseEnd_3462208 : Nat := 1777776829841695328977601

theorem tailTrace_3462208 : CollatzResearch.WordTrace tailWord_3462208 prefixEnd_3462208 1777776829841695328977601 := by
  unfold tailWord_3462208
  simp only [CollatzResearch.WordTrace]
  refine ⟨63138549920509594447933639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84184733227346125930578185 63138549920509594447933639)
  ·
    refine ⟨94707824880764391671900459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63138549920509594447933639 94707824880764391671900459)
    ·
      refine ⟨142061737321146587507850689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94707824880764391671900459 142061737321146587507850689)
      ·
        refine ⟨106546302990859940630888017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142061737321146587507850689 106546302990859940630888017)
        ·
          refine ⟨79909727243144955473166013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106546302990859940630888017 79909727243144955473166013)
          ·
            refine ⟨29966147716179358302437255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79909727243144955473166013 29966147716179358302437255)
            ·
              refine ⟨44949221574269037453655883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29966147716179358302437255 44949221574269037453655883)
              ·
                refine ⟨67423832361403556180483825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44949221574269037453655883 67423832361403556180483825)
                ·
                  refine ⟨50567874271052667135362869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67423832361403556180483825 50567874271052667135362869)
                  ·
                    refine ⟨4740738212911187543940269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50567874271052667135362869 4740738212911187543940269)
                    ·
                      refine ⟨1777776829841695328977601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4740738212911187543940269 1777776829841695328977601)
                      ·
                        rfl

theorem cell23_3462208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 3].length) (baseStart_3462208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462208 prefixEnd_3462208 := by exact prefixLift 3462208
  have htrace : WordTrace (prefixWord ++ tailWord_3462208) baseStart_3462208 baseEnd_3462208 := by
    simpa [prefixWord, tailWord_3462208, baseEnd_3462208] using wordTrace_append hprefix tailTrace_3462208
  have hstable : (prefixWord ++ tailWord_3462208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462208).length < 2 ^ (prefixWord ++ tailWord_3462208).sum := by decide
  have hdescent : baseEnd_3462208 < baseStart_3462208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462225 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 5, 1, 3]
def baseStart_3462225 : Nat := 118140960795 + 3462225 * 2 ^ 59
def prefixEnd_3462225 : Nat := 4983230072969 + 3 ^ 40 * 3462225 * 2
def baseEnd_3462225 : Nat := 1777785559012821762465023

theorem tailTrace_3462225 : CollatzResearch.WordTrace tailWord_3462225 prefixEnd_3462225 1777785559012821762465023 := by
  unfold tailWord_3462225
  simp only [CollatzResearch.WordTrace]
  refine ⟨126277719881957600799236129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84185146587971733866157419 126277719881957600799236129)
  ·
    refine ⟨94708289911468200599427097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126277719881957600799236129 94708289911468200599427097)
    ·
      refine ⟨71031217433601150449570323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94708289911468200599427097 71031217433601150449570323)
      ·
        refine ⟨106546826150401725674355485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71031217433601150449570323 106546826150401725674355485)
        ·
          refine ⟨39955059806400647127883307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106546826150401725674355485 39955059806400647127883307)
          ·
            refine ⟨59932589709600970691824961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39955059806400647127883307 59932589709600970691824961)
            ·
              refine ⟨44949442282200728018868721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59932589709600970691824961 44949442282200728018868721)
              ·
                refine ⟨33712081711650546014151541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44949442282200728018868721 33712081711650546014151541)
                ·
                  refine ⟨3160507660467238688826707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33712081711650546014151541 3160507660467238688826707)
                  ·
                    refine ⟨4740761490700858033240061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3160507660467238688826707 4740761490700858033240061)
                    ·
                      refine ⟨1777785559012821762465023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4740761490700858033240061 1777785559012821762465023)
                      ·
                        rfl

theorem cell23_3462225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5, 1, 3].length) (baseStart_3462225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462225 prefixEnd_3462225 := by exact prefixLift 3462225
  have htrace : WordTrace (prefixWord ++ tailWord_3462225) baseStart_3462225 baseEnd_3462225 := by
    simpa [prefixWord, tailWord_3462225, baseEnd_3462225] using wordTrace_append hprefix tailTrace_3462225
  have hstable : (prefixWord ++ tailWord_3462225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462225).length < 2 ^ (prefixWord ++ tailWord_3462225).sum := by decide
  have hdescent : baseEnd_3462225 < baseStart_3462225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462332 : List Nat := [2, 2, 2, 3, 2, 1, 2, 2, 1, 3, 3]
def baseStart_3462332 : Nat := 118140960795 + 3462332 * 2 ^ 59
def prefixEnd_3462332 : Nat := 4983230072969 + 3 ^ 40 * 3462332 * 2
def baseEnd_3462332 : Nat := 1777840501442852843827031

theorem tailTrace_3462332 : CollatzResearch.WordTrace tailWord_3462332 prefixEnd_3462332 1777840501442852843827031 := by
  unfold tailWord_3462332
  simp only [CollatzResearch.WordTrace]
  refine ⟨63140811246284979036690625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84187748328379972048920833 63140811246284979036690625)
  ·
    refine ⟨47355608434713734277517969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63140811246284979036690625 47355608434713734277517969)
    ·
      refine ⟨35516706326035300708138477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47355608434713734277517969 35516706326035300708138477)
      ·
        refine ⟨13318764872263237765551929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35516706326035300708138477 13318764872263237765551929)
        ·
          refine ⟨9989073654197428324163947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13318764872263237765551929 9989073654197428324163947)
          ·
            refine ⟨14983610481296142486245921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9989073654197428324163947 14983610481296142486245921)
            ·
              refine ⟨11237707860972106864684441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14983610481296142486245921 11237707860972106864684441)
              ·
                refine ⟨8428280895729080148513331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11237707860972106864684441 8428280895729080148513331)
                ·
                  refine ⟨12642421343593620222769997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8428280895729080148513331 12642421343593620222769997)
                  ·
                    refine ⟨4740908003847607583538749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12642421343593620222769997 4740908003847607583538749)
                    ·
                      refine ⟨1777840501442852843827031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4740908003847607583538749 1777840501442852843827031)
                      ·
                        rfl

theorem cell23_3462332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_3462332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462332 prefixEnd_3462332 := by exact prefixLift 3462332
  have htrace : WordTrace (prefixWord ++ tailWord_3462332) baseStart_3462332 baseEnd_3462332 := by
    simpa [prefixWord, tailWord_3462332, baseEnd_3462332] using wordTrace_append hprefix tailTrace_3462332
  have hstable : (prefixWord ++ tailWord_3462332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462332).length < 2 ^ (prefixWord ++ tailWord_3462332).sum := by decide
  have hdescent : baseEnd_3462332 < baseStart_3462332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462336 : List Nat := [2, 1, 1, 2, 6, 2, 2, 1, 1, 2, 3]
def baseStart_3462336 : Nat := 118140960795 + 3462336 * 2 ^ 59
def prefixEnd_3462336 : Nat := 4983230072969 + 3 ^ 40 * 3462336 * 2
def baseEnd_3462336 : Nat := 1777842555365470828177013

theorem tailTrace_3462336 : CollatzResearch.WordTrace tailWord_3462336 prefixEnd_3462336 1777842555365470828177013 := by
  unfold tailWord_3462336
  simp only [CollatzResearch.WordTrace]
  refine ⟨63140884192277733378263431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84187845589703644504351241 63140884192277733378263431)
  ·
    refine ⟨94711326288416600067395147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63140884192277733378263431 94711326288416600067395147)
    ·
      refine ⟨142066989432624900101092721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94711326288416600067395147 142066989432624900101092721)
      ·
        refine ⟨106550242074468675075819541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142066989432624900101092721 106550242074468675075819541)
        ·
          refine ⟨4994542597240719144179041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 106550242074468675075819541 4994542597240719144179041)
          ·
            refine ⟨3745906947930539358134281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4994542597240719144179041 3745906947930539358134281)
            ·
              refine ⟨2809430210947904518600711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3745906947930539358134281 2809430210947904518600711)
              ·
                refine ⟨4214145316421856777901067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2809430210947904518600711 4214145316421856777901067)
                ·
                  refine ⟨6321217974632785166851601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4214145316421856777901067 6321217974632785166851601)
                  ·
                    refine ⟨4740913480974588875138701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6321217974632785166851601 4740913480974588875138701)
                    ·
                      refine ⟨1777842555365470828177013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4740913480974588875138701 1777842555365470828177013)
                      ·
                        rfl

theorem cell23_3462336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 1, 2, 3].length) (baseStart_3462336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462336 prefixEnd_3462336 := by exact prefixLift 3462336
  have htrace : WordTrace (prefixWord ++ tailWord_3462336) baseStart_3462336 baseEnd_3462336 := by
    simpa [prefixWord, tailWord_3462336, baseEnd_3462336] using wordTrace_append hprefix tailTrace_3462336
  have hstable : (prefixWord ++ tailWord_3462336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462336).length < 2 ^ (prefixWord ++ tailWord_3462336).sum := by decide
  have hdescent : baseEnd_3462336 < baseStart_3462336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462412 : List Nat := [2, 2, 1, 2, 2, 5, 1, 1, 7]
def baseStart_3462412 : Nat := 118140960795 + 3462412 * 2 ^ 59
def prefixEnd_3462412 : Nat := 4983230072969 + 3 ^ 40 * 3462412 * 2
def baseEnd_3462412 : Nat := 197542397766134725647407

theorem tailTrace_3462412 : CollatzResearch.WordTrace tailWord_3462412 prefixEnd_3462412 197542397766134725647407 := by
  unfold tailWord_3462412
  simp only [CollatzResearch.WordTrace]
  refine ⟨63142270166140065868146745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84189693554853421157528993 63142270166140065868146745)
  ·
    refine ⟨47356702624605049401110059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63142270166140065868146745 47356702624605049401110059)
    ·
      refine ⟨71035053936907574101665089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47356702624605049401110059 71035053936907574101665089)
      ·
        refine ⟨53276290452680680576248817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71035053936907574101665089 53276290452680680576248817)
        ·
          refine ⟨39957217839510510432186613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53276290452680680576248817 39957217839510510432186613)
          ·
            refine ⟨3745989172454110353017495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39957217839510510432186613 3745989172454110353017495)
            ·
              refine ⟨5618983758681165529526243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3745989172454110353017495 5618983758681165529526243)
              ·
                refine ⟨8428475638021748294289365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5618983758681165529526243 8428475638021748294289365)
                ·
                  refine ⟨197542397766134725647407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8428475638021748294289365 197542397766134725647407)
                  ·
                    rfl

theorem cell23_3462412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 7].length) (baseStart_3462412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462412 prefixEnd_3462412 := by exact prefixLift 3462412
  have htrace : WordTrace (prefixWord ++ tailWord_3462412) baseStart_3462412 baseEnd_3462412 := by
    simpa [prefixWord, tailWord_3462412, baseEnd_3462412] using wordTrace_append hprefix tailTrace_3462412
  have hstable : (prefixWord ++ tailWord_3462412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462412).length < 2 ^ (prefixWord ++ tailWord_3462412).sum := by decide
  have hdescent : baseEnd_3462412 < baseStart_3462412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462452 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_3462452 : Nat := 118140960795 + 3462452 * 2 ^ 59
def prefixEnd_3462452 : Nat := 4983230072969 + 3 ^ 40 * 3462452 * 2
def baseEnd_3462452 : Nat := 1777902119121392374326479

theorem tailTrace_3462452 : CollatzResearch.WordTrace tailWord_3462452 prefixEnd_3462452 1777902119121392374326479 := by
  unfold tailWord_3462452
  simp only [CollatzResearch.WordTrace]
  refine ⟨63142999626067609283874805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84190666168090145711833073 63142999626067609283874805)
  ·
    refine ⟨5919656214943838370363263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63142999626067609283874805 5919656214943838370363263)
    ·
      refine ⟨8879484322415757555544895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5919656214943838370363263 8879484322415757555544895)
      ·
        refine ⟨13319226483623636333317343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8879484322415757555544895 13319226483623636333317343)
        ·
          refine ⟨19978839725435454499976015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13319226483623636333317343 19978839725435454499976015)
          ·
            refine ⟨29968259588153181749964023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19978839725435454499976015 29968259588153181749964023)
            ·
              refine ⟨44952389382229772624946035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29968259588153181749964023 44952389382229772624946035)
              ·
                refine ⟨67428584073344658937419053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44952389382229772624946035 67428584073344658937419053)
                ·
                  refine ⟨25285719027504247101532145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67428584073344658937419053 25285719027504247101532145)
                  ·
                    refine ⟨18964289270628185326149109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25285719027504247101532145 18964289270628185326149109)
                    ·
                      refine ⟨1777902119121392374326479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18964289270628185326149109 1777902119121392374326479)
                      ·
                        rfl

theorem cell23_3462452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_3462452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462452 prefixEnd_3462452 := by exact prefixLift 3462452
  have htrace : WordTrace (prefixWord ++ tailWord_3462452) baseStart_3462452 baseEnd_3462452 := by
    simpa [prefixWord, tailWord_3462452, baseEnd_3462452] using wordTrace_append hprefix tailTrace_3462452
  have hstable : (prefixWord ++ tailWord_3462452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462452).length < 2 ^ (prefixWord ++ tailWord_3462452).sum := by decide
  have hdescent : baseEnd_3462452 < baseStart_3462452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462472 : List Nat := [2, 1, 3, 1, 1, 2, 1, 5, 3, 4]
def baseStart_3462472 : Nat := 118140960795 + 3462472 * 2 ^ 59
def prefixEnd_3462472 : Nat := 4983230072969 + 3 ^ 40 * 3462472 * 2
def baseEnd_3462472 : Nat := 592637462911494098692129

theorem tailTrace_3462472 : CollatzResearch.WordTrace tailWord_3462472 prefixEnd_3462472 592637462911494098692129 := by
  unfold tailWord_3462472
  simp only [CollatzResearch.WordTrace]
  refine ⟨63143364356031380991738835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84191152474708507988985113 63143364356031380991738835)
  ·
    refine ⟨94715046534047071487608253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63143364356031380991738835 94715046534047071487608253)
    ·
      refine ⟨35518142450267651807853095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94715046534047071487608253 35518142450267651807853095)
      ·
        refine ⟨53277213675401477711779643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35518142450267651807853095 53277213675401477711779643)
        ·
          refine ⟨79915820513102216567669465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53277213675401477711779643 79915820513102216567669465)
          ·
            refine ⟨59936865384826662425752099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79915820513102216567669465 59936865384826662425752099)
            ·
              refine ⟨89905298077239993638628149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59936865384826662425752099 89905298077239993638628149)
              ·
                refine ⟨8428621694741249403621389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89905298077239993638628149 8428621694741249403621389)
                ·
                  refine ⟨3160733135527968526358021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8428621694741249403621389 3160733135527968526358021)
                  ·
                    refine ⟨592637462911494098692129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3160733135527968526358021 592637462911494098692129)
                    ·
                      rfl

theorem cell23_3462472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_3462472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462472 prefixEnd_3462472 := by exact prefixLift 3462472
  have htrace : WordTrace (prefixWord ++ tailWord_3462472) baseStart_3462472 baseEnd_3462472 := by
    simpa [prefixWord, tailWord_3462472, baseEnd_3462472] using wordTrace_append hprefix tailTrace_3462472
  have hstable : (prefixWord ++ tailWord_3462472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462472).length < 2 ^ (prefixWord ++ tailWord_3462472).sum := by decide
  have hdescent : baseEnd_3462472 < baseStart_3462472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462482 : List Nat := [3, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3]
def baseStart_3462482 : Nat := 118140960795 + 3462482 * 2 ^ 59
def prefixEnd_3462482 : Nat := 4983230072969 + 3 ^ 40 * 3462482 * 2
def baseEnd_3462482 : Nat := 1777917523541027256951341

theorem tailTrace_3462482 : CollatzResearch.WordTrace tailWord_3462482 prefixEnd_3462482 1777917523541027256951341 := by
  unfold tailWord_3462482
  simp only [CollatzResearch.WordTrace]
  refine ⟨31571773360506633422835425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84191395628017689127561133 31571773360506633422835425)
  ·
    refine ⟨23678830020379975067126569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31571773360506633422835425 23678830020379975067126569)
    ·
      refine ⟨17759122515284981300344927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23678830020379975067126569 17759122515284981300344927)
      ·
        refine ⟨26638683772927471950517391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17759122515284981300344927 26638683772927471950517391)
        ·
          refine ⟨39958025659391207925776087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26638683772927471950517391 39958025659391207925776087)
          ·
            refine ⟨59937038489086811888664131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39958025659391207925776087 59937038489086811888664131)
            ·
              refine ⟨89905557733630217832996197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59937038489086811888664131 89905557733630217832996197)
              ·
                refine ⟨16857292075055665843686787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89905557733630217832996197 16857292075055665843686787)
                ·
                  refine ⟨25285938112583498765530181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16857292075055665843686787 25285938112583498765530181)
                  ·
                    refine ⟨4741113396109406018536909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25285938112583498765530181 4741113396109406018536909)
                    ·
                      refine ⟨1777917523541027256951341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4741113396109406018536909 1777917523541027256951341)
                      ·
                        rfl

theorem cell23_3462482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_3462482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462482 prefixEnd_3462482 := by exact prefixLift 3462482
  have htrace : WordTrace (prefixWord ++ tailWord_3462482) baseStart_3462482 baseEnd_3462482 := by
    simpa [prefixWord, tailWord_3462482, baseEnd_3462482] using wordTrace_append hprefix tailTrace_3462482
  have hstable : (prefixWord ++ tailWord_3462482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462482).length < 2 ^ (prefixWord ++ tailWord_3462482).sum := by decide
  have hdescent : baseEnd_3462482 < baseStart_3462482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462499 : List Nat := [1, 1, 1, 5, 2, 2, 3, 1, 2, 2, 3]
def baseStart_3462499 : Nat := 118140960795 + 3462499 * 2 ^ 59
def prefixEnd_3462499 : Nat := 4983230072969 + 3 ^ 40 * 3462499 * 2
def baseEnd_3462499 : Nat := 1777926252712153690438763

theorem tailTrace_3462499 : CollatzResearch.WordTrace tailWord_3462499 prefixEnd_3462499 1777926252712153690438763 := by
  unfold tailWord_3462499
  simp only [CollatzResearch.WordTrace]
  refine ⟨126287713482964945594710551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84191808988643297063140367 126287713482964945594710551)
  ·
    refine ⟨189431570224447418392065827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126287713482964945594710551 189431570224447418392065827)
    ·
      refine ⟨284147355336671127588098741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189431570224447418392065827 284147355336671127588098741)
      ·
        refine ⟨26638814562812918211384257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 284147355336671127588098741 26638814562812918211384257)
        ·
          refine ⟨19979110922109688658538193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26638814562812918211384257 19979110922109688658538193)
          ·
            refine ⟨14984333191582266493903645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19979110922109688658538193 14984333191582266493903645)
            ·
              refine ⟨5619124946843349935213867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14984333191582266493903645 5619124946843349935213867)
              ·
                refine ⟨8428687420265024902820801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5619124946843349935213867 8428687420265024902820801)
                ·
                  refine ⟨6321515565198768677115601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8428687420265024902820801 6321515565198768677115601)
                  ·
                    refine ⟨4741136673899076507836701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6321515565198768677115601 4741136673899076507836701)
                    ·
                      refine ⟨1777926252712153690438763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4741136673899076507836701 1777926252712153690438763)
                      ·
                        rfl

theorem cell23_3462499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_3462499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462499 prefixEnd_3462499 := by exact prefixLift 3462499
  have htrace : WordTrace (prefixWord ++ tailWord_3462499) baseStart_3462499 baseEnd_3462499 := by
    simpa [prefixWord, tailWord_3462499, baseEnd_3462499] using wordTrace_append hprefix tailTrace_3462499
  have hstable : (prefixWord ++ tailWord_3462499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462499).length < 2 ^ (prefixWord ++ tailWord_3462499).sum := by decide
  have hdescent : baseEnd_3462499 < baseStart_3462499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462572 : List Nat := [2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 5]
def baseStart_3462572 : Nat := 118140960795 + 3462572 * 2 ^ 59
def prefixEnd_3462572 : Nat := 4983230072969 + 3 ^ 40 * 3462572 * 2
def baseEnd_3462572 : Nat := 1777963736799931904825927

theorem tailTrace_3462572 : CollatzResearch.WordTrace tailWord_3462572 prefixEnd_3462572 1777963736799931904825927 := by
  unfold tailWord_3462572
  simp only [CollatzResearch.WordTrace]
  refine ⟨63145188005850239531058985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84193584007800319374745313 63145188005850239531058985)
  ·
    refine ⟨47358891004387679648294239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63145188005850239531058985 47358891004387679648294239)
    ·
      refine ⟨71038336506581519472441359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47358891004387679648294239 71038336506581519472441359)
      ·
        refine ⟨106557504759872279208662039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71038336506581519472441359 106557504759872279208662039)
        ·
          refine ⟨159836257139808418812993059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106557504759872279208662039 159836257139808418812993059)
          ·
            refine ⟨239754385709712628219489589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159836257139808418812993059 239754385709712628219489589)
            ·
              refine ⟨22476973660285558895577149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 239754385709712628219489589 22476973660285558895577149)
              ·
                refine ⟨8428865122607084585841431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22476973660285558895577149 8428865122607084585841431)
                ·
                  refine ⟨12643297683910626878762147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8428865122607084585841431 12643297683910626878762147)
                  ·
                    refine ⟨18964946525865940318143221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12643297683910626878762147 18964946525865940318143221)
                    ·
                      refine ⟨1777963736799931904825927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18964946525865940318143221 1777963736799931904825927)
                      ·
                        rfl

theorem cell23_3462572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_3462572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462572 prefixEnd_3462572 := by exact prefixLift 3462572
  have htrace : WordTrace (prefixWord ++ tailWord_3462572) baseStart_3462572 baseEnd_3462572 := by
    simpa [prefixWord, tailWord_3462572, baseEnd_3462572] using wordTrace_append hprefix tailTrace_3462572
  have hstable : (prefixWord ++ tailWord_3462572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462572).length < 2 ^ (prefixWord ++ tailWord_3462572).sum := by decide
  have hdescent : baseEnd_3462572 < baseStart_3462572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462573 : List Nat := [1, 5, 2, 2, 1, 2, 1, 2, 2, 3, 2]
def baseStart_3462573 : Nat := 118140960795 + 3462573 * 2 ^ 59
def prefixEnd_3462573 : Nat := 4983230072969 + 3 ^ 40 * 3462573 * 2
def baseEnd_3462573 : Nat := 1777964250280586400913423

theorem tailTrace_3462573 : CollatzResearch.WordTrace tailWord_3462573 prefixEnd_3462573 1777964250280586400913423 := by
  unfold tailWord_3462573
  simp only [CollatzResearch.WordTrace]
  refine ⟨126290412484696856232904373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84193608323131237488602915 126290412484696856232904373)
  ·
    refine ⟨11839726170440330271834785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126290412484696856232904373 11839726170440330271834785)
    ·
      refine ⟨8879794627830247703876089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11839726170440330271834785 8879794627830247703876089)
      ·
        refine ⟨6659845970872685777907067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8879794627830247703876089 6659845970872685777907067)
        ·
          refine ⟨9989768956309028666860601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6659845970872685777907067 9989768956309028666860601)
          ·
            refine ⟨7492326717231771500145451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9989768956309028666860601 7492326717231771500145451)
            ·
              refine ⟨11238490075847657250218177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7492326717231771500145451 11238490075847657250218177)
              ·
                refine ⟨8428867556885742937663633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11238490075847657250218177 8428867556885742937663633)
                ·
                  refine ⟨6321650667664307203247725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8428867556885742937663633 6321650667664307203247725)
                  ·
                    refine ⟨2370619000374115201217897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6321650667664307203247725 2370619000374115201217897)
                    ·
                      refine ⟨1777964250280586400913423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2370619000374115201217897 1777964250280586400913423)
                      ·
                        rfl

theorem cell23_3462573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_3462573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462573 prefixEnd_3462573 := by exact prefixLift 3462573
  have htrace : WordTrace (prefixWord ++ tailWord_3462573) baseStart_3462573 baseEnd_3462573 := by
    simpa [prefixWord, tailWord_3462573, baseEnd_3462573] using wordTrace_append hprefix tailTrace_3462573
  have hstable : (prefixWord ++ tailWord_3462573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462573).length < 2 ^ (prefixWord ++ tailWord_3462573).sum := by decide
  have hdescent : baseEnd_3462573 < baseStart_3462573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462589 : List Nat := [1, 4, 1, 2, 2, 1, 2, 2, 3, 2, 3]
def baseStart_3462589 : Nat := 118140960795 + 3462589 * 2 ^ 59
def prefixEnd_3462589 : Nat := 4983230072969 + 3 ^ 40 * 3462589 * 2
def baseEnd_3462589 : Nat := 1777972465971058338313349

theorem tailTrace_3462589 : CollatzResearch.WordTrace tailWord_3462589 prefixEnd_3462589 1777972465971058338313349 := by
  unfold tailWord_3462589
  simp only [CollatzResearch.WordTrace]
  refine ⟨126290996052638890965486821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84193997368425927310324547 126290996052638890965486821)
  ·
    refine ⟨23679561759869792056028779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126290996052638890965486821 23679561759869792056028779)
    ·
      refine ⟨35519342639804688084043169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23679561759869792056028779 35519342639804688084043169)
      ·
        refine ⟨26639506979853516063032377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35519342639804688084043169 26639506979853516063032377)
        ·
          refine ⟨19979630234890137047274283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26639506979853516063032377 19979630234890137047274283)
          ·
            refine ⟨29969445352335205570911425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19979630234890137047274283 29969445352335205570911425)
            ·
              refine ⟨22477084014251404178183569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29969445352335205570911425 22477084014251404178183569)
              ·
                refine ⟨16857813010688553133637677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22477084014251404178183569 16857813010688553133637677)
                ·
                  refine ⟨6321679879008207425114129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16857813010688553133637677 6321679879008207425114129)
                  ·
                    refine ⟨4741259909256155568835597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6321679879008207425114129 4741259909256155568835597)
                    ·
                      refine ⟨1777972465971058338313349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4741259909256155568835597 1777972465971058338313349)
                      ·
                        rfl

theorem cell23_3462589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_3462589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462589 prefixEnd_3462589 := by exact prefixLift 3462589
  have htrace : WordTrace (prefixWord ++ tailWord_3462589) baseStart_3462589 baseEnd_3462589 := by
    simpa [prefixWord, tailWord_3462589, baseEnd_3462589] using wordTrace_append hprefix tailTrace_3462589
  have hstable : (prefixWord ++ tailWord_3462589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462589).length < 2 ^ (prefixWord ++ tailWord_3462589).sum := by decide
  have hdescent : baseEnd_3462589 < baseStart_3462589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462606 : List Nat := [4, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3]
def baseStart_3462606 : Nat := 118140960795 + 3462606 * 2 ^ 59
def prefixEnd_3462606 : Nat := 4983230072969 + 3 ^ 40 * 3462606 * 2
def baseEnd_3462606 : Nat := 1777981195142184771800771

theorem tailTrace_3462606 : CollatzResearch.WordTrace tailWord_3462606 prefixEnd_3462606 1777981195142184771800771 := by
  unfold tailWord_3462606
  simp only [CollatzResearch.WordTrace]
  refine ⟨15786452011697162858606959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84194410729051535245903781 15786452011697162858606959)
  ·
    refine ⟨23679678017545744287910439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15786452011697162858606959 23679678017545744287910439)
    ·
      refine ⟨35519517026318616431865659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23679678017545744287910439 35519517026318616431865659)
      ·
        refine ⟨53279275539477924647798489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35519517026318616431865659 53279275539477924647798489)
        ·
          refine ⟨39959456654608443485848867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53279275539477924647798489 39959456654608443485848867)
          ·
            refine ⟨59939184981912665228773301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39959456654608443485848867 59939184981912665228773301)
            ·
              refine ⟨5619298592054312365197497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59939184981912665228773301 5619298592054312365197497)
              ·
                refine ⟨4214473944040734273898123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5619298592054312365197497 4214473944040734273898123)
                ·
                  refine ⟨6321710916061101410847185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4214473944040734273898123 6321710916061101410847185)
                  ·
                    refine ⟨4741283187045826058135389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6321710916061101410847185 4741283187045826058135389)
                    ·
                      refine ⟨1777981195142184771800771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4741283187045826058135389 1777981195142184771800771)
                      ·
                        rfl

theorem cell23_3462606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_3462606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462606 prefixEnd_3462606 := by exact prefixLift 3462606
  have htrace : WordTrace (prefixWord ++ tailWord_3462606) baseStart_3462606 baseEnd_3462606 := by
    simpa [prefixWord, tailWord_3462606, baseEnd_3462606] using wordTrace_append hprefix tailTrace_3462606
  have hstable : (prefixWord ++ tailWord_3462606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462606).length < 2 ^ (prefixWord ++ tailWord_3462606).sum := by decide
  have hdescent : baseEnd_3462606 < baseStart_3462606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462637 : List Nat := [1, 5, 1, 3, 2, 1, 1, 4, 1, 2, 2]
def baseStart_3462637 : Nat := 118140960795 + 3462637 * 2 ^ 59
def prefixEnd_3462637 : Nat := 4983230072969 + 3 ^ 40 * 3462637 * 2
def baseEnd_3462637 : Nat := 1777997113042474150513129

theorem tailTrace_3462637 : CollatzResearch.WordTrace tailWord_3462637 prefixEnd_3462637 1777997113042474150513129 := by
  unfold tailWord_3462637
  simp only [CollatzResearch.WordTrace]
  refine ⟨126292746756464995163234165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84195164504309996775489443 126292746756464995163234165)
  ·
    refine ⟨11839945008418593296553203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126292746756464995163234165 11839945008418593296553203)
    ·
      refine ⟨17759917512627889944829805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11839945008418593296553203 17759917512627889944829805)
      ·
        refine ⟨6659969067235458729311177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17759917512627889944829805 6659969067235458729311177)
        ·
          refine ⟨4994976800426594046983383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6659969067235458729311177 4994976800426594046983383)
          ·
            refine ⟨7492465200639891070475075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4994976800426594046983383 7492465200639891070475075)
            ·
              refine ⟨11238697800959836605712613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7492465200639891070475075 11238697800959836605712613)
              ·
                refine ⟨2107255837679969363571115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11238697800959836605712613 2107255837679969363571115)
                ·
                  refine ⟨3160883756519954045356673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2107255837679969363571115 3160883756519954045356673)
                  ·
                    refine ⟨2370662817389965534017505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3160883756519954045356673 2370662817389965534017505)
                    ·
                      refine ⟨1777997113042474150513129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2370662817389965534017505 1777997113042474150513129)
                      ·
                        rfl

theorem cell23_3462637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_3462637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462637 prefixEnd_3462637 := by exact prefixLift 3462637
  have htrace : WordTrace (prefixWord ++ tailWord_3462637) baseStart_3462637 baseEnd_3462637 := by
    simpa [prefixWord, tailWord_3462637, baseEnd_3462637] using wordTrace_append hprefix tailTrace_3462637
  have hstable : (prefixWord ++ tailWord_3462637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462637).length < 2 ^ (prefixWord ++ tailWord_3462637).sum := by decide
  have hdescent : baseEnd_3462637 < baseStart_3462637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462652 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 1, 8]
def baseStart_3462652 : Nat := 118140960795 + 3462652 * 2 ^ 59
def prefixEnd_3462652 : Nat := 4983230072969 + 3 ^ 40 * 3462652 * 2
def baseEnd_3462652 : Nat := 592668271750763863941853

theorem tailTrace_3462652 : CollatzResearch.WordTrace tailWord_3462652 prefixEnd_3462652 592668271750763863941853 := by
  unfold tailWord_3462652
  simp only [CollatzResearch.WordTrace]
  refine ⟨63146646925705326362515105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84195529234273768483353473 63146646925705326362515105)
  ·
    refine ⟨47359985194278994771886329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63146646925705326362515105 47359985194278994771886329)
    ·
      refine ⟨35519988895709246078914747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47359985194278994771886329 35519988895709246078914747)
      ·
        refine ⟨53279983343563869118372121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35519988895709246078914747 53279983343563869118372121)
        ·
          refine ⟨39959987507672901838779091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53279983343563869118372121 39959987507672901838779091)
          ·
            refine ⟨59939981261509352758168637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39959987507672901838779091 59939981261509352758168637)
            ·
              refine ⟨22477492973066007284313239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59939981261509352758168637 22477492973066007284313239)
              ·
                refine ⟨33716239459599010926469859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22477492973066007284313239 33716239459599010926469859)
                ·
                  refine ⟨50574359189398516389704789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33716239459599010926469859 50574359189398516389704789)
                  ·
                    refine ⟨592668271750763863941853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50574359189398516389704789 592668271750763863941853)
                    ·
                      rfl

theorem cell23_3462652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_3462652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462652 prefixEnd_3462652 := by exact prefixLift 3462652
  have htrace : WordTrace (prefixWord ++ tailWord_3462652) baseStart_3462652 baseEnd_3462652 := by
    simpa [prefixWord, tailWord_3462652, baseEnd_3462652] using wordTrace_append hprefix tailTrace_3462652
  have hstable : (prefixWord ++ tailWord_3462652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462652).length < 2 ^ (prefixWord ++ tailWord_3462652).sum := by decide
  have hdescent : baseEnd_3462652 < baseStart_3462652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462682 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 11]
def baseStart_3462682 : Nat := 118140960795 + 3462682 * 2 ^ 59
def prefixEnd_3462682 : Nat := 4983230072969 + 3 ^ 40 * 3462682 * 2
def baseEnd_3462682 : Nat := 197557802185769608272269

theorem tailTrace_3462682 : CollatzResearch.WordTrace tailWord_3462682 prefixEnd_3462682 197557802185769608272269 := by
  unfold tailWord_3462682
  simp only [CollatzResearch.WordTrace]
  refine ⟨31573597010325491962155575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84196258694201311899081533 31573597010325491962155575)
  ·
    refine ⟨47360395515488237943233363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31573597010325491962155575 47360395515488237943233363)
    ·
      refine ⟨71040593273232356914850045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47360395515488237943233363 71040593273232356914850045)
      ·
        refine ⟨26640222477462133843068767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71040593273232356914850045 26640222477462133843068767)
        ·
          refine ⟨39960333716193200764603151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26640222477462133843068767 39960333716193200764603151)
          ·
            refine ⟨59940500574289801146904727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39960333716193200764603151 59940500574289801146904727)
            ·
              refine ⟨89910750861434701720357091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59940500574289801146904727 89910750861434701720357091)
              ·
                refine ⟨134866126292152052580535637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89910750861434701720357091 134866126292152052580535637)
                ·
                  refine ⟨197557802185769608272269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 134866126292152052580535637 197557802185769608272269)
                  ·
                    rfl

theorem cell23_3462682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 11].length) (baseStart_3462682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462682 prefixEnd_3462682 := by exact prefixLift 3462682
  have htrace : WordTrace (prefixWord ++ tailWord_3462682) baseStart_3462682 baseEnd_3462682 := by
    simpa [prefixWord, tailWord_3462682, baseEnd_3462682] using wordTrace_append hprefix tailTrace_3462682
  have hstable : (prefixWord ++ tailWord_3462682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462682).length < 2 ^ (prefixWord ++ tailWord_3462682).sum := by decide
  have hdescent : baseEnd_3462682 < baseStart_3462682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462689 : List Nat := [1, 2, 3, 2, 2, 2, 1, 2, 2, 2, 4]
def baseStart_3462689 : Nat := 118140960795 + 3462689 * 2 ^ 59
def prefixEnd_3462689 : Nat := 4983230072969 + 3 ^ 40 * 3462689 * 2
def baseEnd_3462689 : Nat := 1778023814036507947062889

theorem tailTrace_3462689 : CollatzResearch.WordTrace tailWord_3462689 prefixEnd_3462689 1778023814036507947062889 := by
  unfold tailWord_3462689
  simp only [CollatzResearch.WordTrace]
  refine ⟨126294643352276608044127121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84196428901517738696084747 126294643352276608044127121)
  ·
    refine ⟨94720982514207456033095341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126294643352276608044127121 94720982514207456033095341)
    ·
      refine ⟨35520368442827796012410753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94720982514207456033095341 35520368442827796012410753)
      ·
        refine ⟨26640276332120847009308065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35520368442827796012410753 26640276332120847009308065)
        ·
          refine ⟨19980207249090635256981049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26640276332120847009308065 19980207249090635256981049)
          ·
            refine ⟨14985155436817976442735787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19980207249090635256981049 14985155436817976442735787)
            ·
              refine ⟨22477733155226964664103681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14985155436817976442735787 22477733155226964664103681)
              ·
                refine ⟨16858299866420223498077761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22477733155226964664103681 16858299866420223498077761)
                ·
                  refine ⟨12643724899815167623558321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16858299866420223498077761 12643724899815167623558321)
                  ·
                    refine ⟨9482793674861375717668741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12643724899815167623558321 9482793674861375717668741)
                    ·
                      refine ⟨1778023814036507947062889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9482793674861375717668741 1778023814036507947062889)
                      ·
                        rfl

theorem cell23_3462689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_3462689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462689 prefixEnd_3462689 := by exact prefixLift 3462689
  have htrace : WordTrace (prefixWord ++ tailWord_3462689) baseStart_3462689 baseEnd_3462689 := by
    simpa [prefixWord, tailWord_3462689, baseEnd_3462689] using wordTrace_append hprefix tailTrace_3462689
  have hstable : (prefixWord ++ tailWord_3462689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462689).length < 2 ^ (prefixWord ++ tailWord_3462689).sum := by decide
  have hdescent : baseEnd_3462689 < baseStart_3462689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462769 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 3, 4, 3]
def baseStart_3462769 : Nat := 118140960795 + 3462769 * 2 ^ 59
def prefixEnd_3462769 : Nat := 4983230072969 + 3 ^ 40 * 3462769 * 2
def baseEnd_3462769 : Nat := 1778064892488867634062521

theorem tailTrace_3462769 : CollatzResearch.WordTrace tailWord_3462769 prefixEnd_3462769 1778064892488867634062521 := by
  unfold tailWord_3462769
  simp only [CollatzResearch.WordTrace]
  refine ⟨126297561191986781707039361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84198374127991187804692907 126297561191986781707039361)
  ·
    refine ⟨94723170893990086280279521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126297561191986781707039361 94723170893990086280279521)
    ·
      refine ⟨71042378170492564710209641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94723170893990086280279521 71042378170492564710209641)
      ·
        refine ⟨53281783627869423532657231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71042378170492564710209641 53281783627869423532657231)
        ·
          refine ⟨79922675441804135298985847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53281783627869423532657231 79922675441804135298985847)
          ·
            refine ⟨119884013162706202948478771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79922675441804135298985847 119884013162706202948478771)
            ·
              refine ⟨179826019744059304422718157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119884013162706202948478771 179826019744059304422718157)
              ·
                refine ⟨67434757404022239158519309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179826019744059304422718157 67434757404022239158519309)
                ·
                  refine ⟨25288034026508339684444741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67434757404022239158519309 25288034026508339684444741)
                  ·
                    refine ⟨4741506379970313690833389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25288034026508339684444741 4741506379970313690833389)
                    ·
                      refine ⟨1778064892488867634062521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4741506379970313690833389 1778064892488867634062521)
                      ·
                        rfl

theorem cell23_3462769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_3462769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462769 prefixEnd_3462769 := by exact prefixLift 3462769
  have htrace : WordTrace (prefixWord ++ tailWord_3462769) baseStart_3462769 baseEnd_3462769 := by
    simpa [prefixWord, tailWord_3462769, baseEnd_3462769] using wordTrace_append hprefix tailTrace_3462769
  have hstable : (prefixWord ++ tailWord_3462769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462769).length < 2 ^ (prefixWord ++ tailWord_3462769).sum := by decide
  have hdescent : baseEnd_3462769 < baseStart_3462769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462819 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 5, 5]
def baseStart_3462819 : Nat := 118140960795 + 3462819 * 2 ^ 59
def prefixEnd_3462819 : Nat := 4983230072969 + 3 ^ 40 * 3462819 * 2
def baseEnd_3462819 : Nat := 592696855507197479479097

theorem tailTrace_3462819 : CollatzResearch.WordTrace tailWord_3462819 prefixEnd_3462819 592696855507197479479097 := by
  unfold tailWord_3462819
  simp only [CollatzResearch.WordTrace]
  refine ⟨126299384841805640246359511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84199589894537093497573007 126299384841805640246359511)
  ·
    refine ⟨189449077262708460369539267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126299384841805640246359511 189449077262708460369539267)
    ·
      refine ⟨284173615894062690554308901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189449077262708460369539267 284173615894062690554308901)
      ·
        refine ⟨53282552980136754478932919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 284173615894062690554308901 53282552980136754478932919)
        ·
          refine ⟨79923829470205131718399379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53282552980136754478932919 79923829470205131718399379)
          ·
            refine ⟨119885744205307697577599069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79923829470205131718399379 119885744205307697577599069)
            ·
              refine ⟨44957154076990386591599651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119885744205307697577599069 44957154076990386591599651)
              ·
                refine ⟨67435731115485579887399477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44957154076990386591599651 67435731115485579887399477)
                ·
                  refine ⟨6322099792076773114443701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67435731115485579887399477 6322099792076773114443701)
                  ·
                    refine ⟨592696855507197479479097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6322099792076773114443701 592696855507197479479097)
                    ·
                      rfl

theorem cell23_3462819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 5].length) (baseStart_3462819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462819 prefixEnd_3462819 := by exact prefixLift 3462819
  have htrace : WordTrace (prefixWord ++ tailWord_3462819) baseStart_3462819 baseEnd_3462819 := by
    simpa [prefixWord, tailWord_3462819, baseEnd_3462819] using wordTrace_append hprefix tailTrace_3462819
  have hstable : (prefixWord ++ tailWord_3462819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462819).length < 2 ^ (prefixWord ++ tailWord_3462819).sum := by decide
  have hdescent : baseEnd_3462819 < baseStart_3462819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462837 : List Nat := [1, 3, 3, 3, 3, 1, 1, 1, 2, 2, 3]
def baseStart_3462837 : Nat := 118140960795 + 3462837 * 2 ^ 59
def prefixEnd_3462837 : Nat := 4983230072969 + 3 ^ 40 * 3462837 * 2
def baseEnd_3462837 : Nat := 1778099809173373368012209

theorem tailTrace_3462837 : CollatzResearch.WordTrace tailWord_3462837 prefixEnd_3462837 1778099809173373368012209 := by
  unfold tailWord_3462837
  simp only [CollatzResearch.WordTrace]
  refine ⟨126300041355740429320514765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84200027570493619547009843 126300041355740429320514765)
  ·
    refine ⟨47362515508402660995193037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126300041355740429320514765 47362515508402660995193037)
    ·
      refine ⟨17760943315650997873197389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47362515508402660995193037 17760943315650997873197389)
      ·
        refine ⟨6660353743369124202449021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17760943315650997873197389 6660353743369124202449021)
        ·
          refine ⟨2497632653763421575918383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6660353743369124202449021 2497632653763421575918383)
          ·
            refine ⟨3746448980645132363877575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2497632653763421575918383 3746448980645132363877575)
            ·
              refine ⟨5619673470967698545816363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3746448980645132363877575 5619673470967698545816363)
              ·
                refine ⟨8429510206451547818724545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5619673470967698545816363 8429510206451547818724545)
                ·
                  refine ⟨6322132654838660864043409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8429510206451547818724545 6322132654838660864043409)
                  ·
                    refine ⟨4741599491128995648032557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6322132654838660864043409 4741599491128995648032557)
                    ·
                      refine ⟨1778099809173373368012209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4741599491128995648032557 1778099809173373368012209)
                      ·
                        rfl

theorem cell23_3462837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_3462837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462837 prefixEnd_3462837 := by exact prefixLift 3462837
  have htrace : WordTrace (prefixWord ++ tailWord_3462837) baseStart_3462837 baseEnd_3462837 := by
    simpa [prefixWord, tailWord_3462837, baseEnd_3462837] using wordTrace_append hprefix tailTrace_3462837
  have hstable : (prefixWord ++ tailWord_3462837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462837).length < 2 ^ (prefixWord ++ tailWord_3462837).sum := by decide
  have hdescent : baseEnd_3462837 < baseStart_3462837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462859 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 5]
def baseStart_3462859 : Nat := 118140960795 + 3462859 * 2 ^ 59
def prefixEnd_3462859 : Nat := 4983230072969 + 3 ^ 40 * 3462859 * 2
def baseEnd_3462859 : Nat := 1778111105747772281937107

theorem tailTrace_3462859 : CollatzResearch.WordTrace tailWord_3462859 prefixEnd_3462859 1778111105747772281937107 := by
  unfold tailWord_3462859
  simp only [CollatzResearch.WordTrace]
  refine ⟨126300843761660727077815631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84200562507773818051877087 126300843761660727077815631)
  ·
    refine ⟨189451265642491090616723447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126300843761660727077815631 189451265642491090616723447)
    ·
      refine ⟨284176898463736635925085171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189451265642491090616723447 284176898463736635925085171)
      ·
        refine ⟨426265347695604953887627757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284176898463736635925085171 426265347695604953887627757)
        ·
          refine ⟨159849505385851857707860409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 426265347695604953887627757 159849505385851857707860409)
          ·
            refine ⟨119887129039388893280895307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159849505385851857707860409 119887129039388893280895307)
            ·
              refine ⟨179830693559083339921342961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119887129039388893280895307 179830693559083339921342961)
              ·
                refine ⟨134873020169312504941007221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179830693559083339921342961 134873020169312504941007221)
                ·
                  refine ⟨12644345640873047338219427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134873020169312504941007221 12644345640873047338219427)
                  ·
                    refine ⟨18966518461309571007329141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12644345640873047338219427 18966518461309571007329141)
                    ·
                      refine ⟨1778111105747772281937107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18966518461309571007329141 1778111105747772281937107)
                      ·
                        rfl

theorem cell23_3462859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 5].length) (baseStart_3462859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462859 prefixEnd_3462859 := by exact prefixLift 3462859
  have htrace : WordTrace (prefixWord ++ tailWord_3462859) baseStart_3462859 baseEnd_3462859 := by
    simpa [prefixWord, tailWord_3462859, baseEnd_3462859] using wordTrace_append hprefix tailTrace_3462859
  have hstable : (prefixWord ++ tailWord_3462859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462859).length < 2 ^ (prefixWord ++ tailWord_3462859).sum := by decide
  have hdescent : baseEnd_3462859 < baseStart_3462859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462879 : List Nat := [1, 1, 2, 3, 2, 2, 2, 10]
def baseStart_3462879 : Nat := 118140960795 + 3462879 * 2 ^ 59
def prefixEnd_3462879 : Nat := 4983230072969 + 3 ^ 40 * 3462879 * 2
def baseEnd_3462879 : Nat := 65856347235587489025445

theorem tailTrace_3462879 : CollatzResearch.WordTrace tailWord_3462879 prefixEnd_3462879 65856347235587489025445 := by
  unfold tailWord_3462879
  simp only [CollatzResearch.WordTrace]
  refine ⟨126301573221588270493543691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84201048814392180329029127 126301573221588270493543691)
  ·
    refine ⟨189452359832382405740315537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126301573221588270493543691 189452359832382405740315537)
    ·
      refine ⟨142089269874286804305236653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189452359832382405740315537 142089269874286804305236653)
      ·
        refine ⟨53283476202857551614463745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142089269874286804305236653 53283476202857551614463745)
        ·
          refine ⟨39962607152143163710847809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53283476202857551614463745 39962607152143163710847809)
          ·
            refine ⟨29971955364107372783135857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39962607152143163710847809 29971955364107372783135857)
            ·
              refine ⟨22478966523080529587351893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29971955364107372783135857 22478966523080529587351893)
              ·
                refine ⟨65856347235587489025445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22478966523080529587351893 65856347235587489025445)
                ·
                  rfl

theorem cell23_3462879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 10].length) (baseStart_3462879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462879 prefixEnd_3462879 := by exact prefixLift 3462879
  have htrace : WordTrace (prefixWord ++ tailWord_3462879) baseStart_3462879 baseEnd_3462879 := by
    simpa [prefixWord, tailWord_3462879, baseEnd_3462879] using wordTrace_append hprefix tailTrace_3462879
  have hstable : (prefixWord ++ tailWord_3462879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462879).length < 2 ^ (prefixWord ++ tailWord_3462879).sum := by decide
  have hdescent : baseEnd_3462879 < baseStart_3462879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462890 : List Nat := [3, 1, 3, 1, 1, 1, 4, 2, 3, 2, 2]
def baseStart_3462890 : Nat := 118140960795 + 3462890 * 2 ^ 59
def prefixEnd_3462890 : Nat := 4983230072969 + 3 ^ 40 * 3462890 * 2
def baseEnd_3462890 : Nat := 1778127023648061660649465

theorem tailTrace_3462890 : CollatzResearch.WordTrace tailWord_3462890 prefixEnd_3462890 1778127023648061660649465 := by
  unfold tailWord_3462890
  simp only [CollatzResearch.WordTrace]
  refine ⟨31575493606137104843048531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84201316283032279581462749 31575493606137104843048531)
  ·
    refine ⟨47363240409205657264572797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31575493606137104843048531 47363240409205657264572797)
    ·
      refine ⟨17761215153452121474214799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47363240409205657264572797 17761215153452121474214799)
      ·
        refine ⟨26641822730178182211322199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17761215153452121474214799 26641822730178182211322199)
        ·
          refine ⟨39962734095267273316983299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26641822730178182211322199 39962734095267273316983299)
          ·
            refine ⟨59944101142900909975474949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39962734095267273316983299 59944101142900909975474949)
            ·
              refine ⟨11239518964293920620401553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59944101142900909975474949 11239518964293920620401553)
              ·
                refine ⟨8429639223220440465301165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11239518964293920620401553 8429639223220440465301165)
                ·
                  refine ⟨3161114708707665174487937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8429639223220440465301165 3161114708707665174487937)
                  ·
                    refine ⟨2370836031530748880865953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3161114708707665174487937 2370836031530748880865953)
                    ·
                      refine ⟨1778127023648061660649465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2370836031530748880865953 1778127023648061660649465)
                      ·
                        rfl

theorem cell23_3462890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_3462890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462890 prefixEnd_3462890 := by exact prefixLift 3462890
  have htrace : WordTrace (prefixWord ++ tailWord_3462890) baseStart_3462890 baseEnd_3462890 := by
    simpa [prefixWord, tailWord_3462890, baseEnd_3462890] using wordTrace_append hprefix tailTrace_3462890
  have hstable : (prefixWord ++ tailWord_3462890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462890).length < 2 ^ (prefixWord ++ tailWord_3462890).sum := by decide
  have hdescent : baseEnd_3462890 < baseStart_3462890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462906 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3]
def baseStart_3462906 : Nat := 118140960795 + 3462906 * 2 ^ 59
def prefixEnd_3462906 : Nat := 4983230072969 + 3 ^ 40 * 3462906 * 2
def baseEnd_3462906 : Nat := 1778135239338533598049391

theorem tailTrace_3462906 : CollatzResearch.WordTrace tailWord_3462906 prefixEnd_3462906 1778135239338533598049391 := by
  unfold tailWord_3462906
  simp only [CollatzResearch.WordTrace]
  refine ⟨31575639498122613526194143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84201705328326969403184381 31575639498122613526194143)
  ·
    refine ⟨47363459247183920289291215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31575639498122613526194143 47363459247183920289291215)
    ·
      refine ⟨71045188870775880433936823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47363459247183920289291215 71045188870775880433936823)
      ·
        refine ⟨106567783306163820650905235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71045188870775880433936823 106567783306163820650905235)
        ·
          refine ⟨159851674959245730976357853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106567783306163820650905235 159851674959245730976357853)
          ·
            refine ⟨59944378109717149116134195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159851674959245730976357853 59944378109717149116134195)
            ·
              refine ⟨89916567164575723674201293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59944378109717149116134195 89916567164575723674201293)
              ·
                refine ⟨33718712686715896377825485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89916567164575723674201293 33718712686715896377825485)
                ·
                  refine ⟨12644517257518461141684557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33718712686715896377825485 12644517257518461141684557)
                  ·
                    refine ⟨4741693971569422928131709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12644517257518461141684557 4741693971569422928131709)
                    ·
                      refine ⟨1778135239338533598049391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4741693971569422928131709 1778135239338533598049391)
                      ·
                        rfl

theorem cell23_3462906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3].length) (baseStart_3462906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462906 prefixEnd_3462906 := by exact prefixLift 3462906
  have htrace : WordTrace (prefixWord ++ tailWord_3462906) baseStart_3462906 baseEnd_3462906 := by
    simpa [prefixWord, tailWord_3462906, baseEnd_3462906] using wordTrace_append hprefix tailTrace_3462906
  have hstable : (prefixWord ++ tailWord_3462906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462906).length < 2 ^ (prefixWord ++ tailWord_3462906).sum := by decide
  have hdescent : baseEnd_3462906 < baseStart_3462906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462910 : List Nat := [4, 2, 2, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_3462910 : Nat := 118140960795 + 3462910 * 2 ^ 59
def prefixEnd_3462910 : Nat := 4983230072969 + 3 ^ 40 * 3462910 * 2
def baseEnd_3462910 : Nat := 1778137293261151582399373

theorem tailTrace_3462910 : CollatzResearch.WordTrace tailWord_3462910 prefixEnd_3462910 1778137293261151582399373 := by
  unfold tailWord_3462910
  simp only [CollatzResearch.WordTrace]
  refine ⟨15787837985559495348490273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84201802589650641858614789 15787837985559495348490273)
  ·
    refine ⟨11840878489169621511367705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15787837985559495348490273 11840878489169621511367705)
    ·
      refine ⟨8880658866877216133525779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11840878489169621511367705 8880658866877216133525779)
      ·
        refine ⟨13320988300315824200288669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8880658866877216133525779 13320988300315824200288669)
        ·
          refine ⟨4995370612618434075108251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13320988300315824200288669 4995370612618434075108251)
          ·
            refine ⟨7493055918927651112662377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4995370612618434075108251 7493055918927651112662377)
            ·
              refine ⟨5619791939195738334496783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7493055918927651112662377 5619791939195738334496783)
              ·
                refine ⟨8429687908793607501745175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5619791939195738334496783 8429687908793607501745175)
                ·
                  refine ⟨12644531863190411252617763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8429687908793607501745175 12644531863190411252617763)
                  ·
                    refine ⟨18966797794785616878926645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12644531863190411252617763 18966797794785616878926645)
                    ·
                      refine ⟨1778137293261151582399373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18966797794785616878926645 1778137293261151582399373)
                      ·
                        rfl

theorem cell23_3462910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_3462910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462910 prefixEnd_3462910 := by exact prefixLift 3462910
  have htrace : WordTrace (prefixWord ++ tailWord_3462910) baseStart_3462910 baseEnd_3462910 := by
    simpa [prefixWord, tailWord_3462910, baseEnd_3462910] using wordTrace_append hprefix tailTrace_3462910
  have hstable : (prefixWord ++ tailWord_3462910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462910).length < 2 ^ (prefixWord ++ tailWord_3462910).sum := by decide
  have hdescent : baseEnd_3462910 < baseStart_3462910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462923 : List Nat := [1, 1, 1, 1, 5, 1, 4, 1, 4, 1, 3]
def baseStart_3462923 : Nat := 118140960795 + 3462923 * 2 ^ 59
def prefixEnd_3462923 : Nat := 4983230072969 + 3 ^ 40 * 3462923 * 2
def baseEnd_3462923 : Nat := 1778143968509660031536813

theorem tailTrace_3462923 : CollatzResearch.WordTrace tailWord_3462923 prefixEnd_3462923 1778143968509660031536813 := by
  unfold tailWord_3462923
  simp only [CollatzResearch.WordTrace]
  refine ⟨126303178033428866008145423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84202118688952577338763615 126303178033428866008145423)
  ·
    refine ⟨189454767050143299012218135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126303178033428866008145423 189454767050143299012218135)
    ·
      refine ⟨284182150575214948518327203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189454767050143299012218135 284182150575214948518327203)
      ·
        refine ⟨426273225862822422777490805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284182150575214948518327203 426273225862822422777490805)
        ·
          refine ⟨39963114924639602135389763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 426273225862822422777490805 39963114924639602135389763)
          ·
            refine ⟨59944672386959403203084645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39963114924639602135389763 59944672386959403203084645)
            ·
              refine ⟨11239626072554888100578371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59944672386959403203084645 11239626072554888100578371)
              ·
                refine ⟨16859439108832332150867557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11239626072554888100578371 16859439108832332150867557)
                ·
                  refine ⟨3161144832906062278287667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16859439108832332150867557 3161144832906062278287667)
                  ·
                    refine ⟨4741717249359093417431501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3161144832906062278287667 4741717249359093417431501)
                    ·
                      refine ⟨1778143968509660031536813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4741717249359093417431501 1778143968509660031536813)
                      ·
                        rfl

theorem cell23_3462923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4, 1, 3].length) (baseStart_3462923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462923 prefixEnd_3462923 := by exact prefixLift 3462923
  have htrace : WordTrace (prefixWord ++ tailWord_3462923) baseStart_3462923 baseEnd_3462923 := by
    simpa [prefixWord, tailWord_3462923, baseEnd_3462923] using wordTrace_append hprefix tailTrace_3462923
  have hstable : (prefixWord ++ tailWord_3462923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462923).length < 2 ^ (prefixWord ++ tailWord_3462923).sum := by decide
  have hdescent : baseEnd_3462923 < baseStart_3462923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462940 : List Nat := [2, 2, 3, 1, 1, 2, 3, 3, 2, 1, 3]
def baseStart_3462940 : Nat := 118140960795 + 3462940 * 2 ^ 59
def prefixEnd_3462940 : Nat := 4983230072969 + 3 ^ 40 * 3462940 * 2
def baseEnd_3462940 : Nat := 1778152697680786465024235

theorem tailTrace_3462940 : CollatzResearch.WordTrace tailWord_3462940 prefixEnd_3462940 1778152697680786465024235 := by
  unfold tailWord_3462940
  simp only [CollatzResearch.WordTrace]
  refine ⟨63151899037183638955757137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84202532049578185274342849 63151899037183638955757137)
  ·
    refine ⟨47363924277887729216817853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63151899037183638955757137 47363924277887729216817853)
    ·
      refine ⟨17761471604207898456306695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47363924277887729216817853 17761471604207898456306695)
      ·
        refine ⟨26642207406311847684460043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17761471604207898456306695 26642207406311847684460043)
        ·
          refine ⟨39963311109467771526690065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26642207406311847684460043 39963311109467771526690065)
          ·
            refine ⟨29972483332100828645017549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39963311109467771526690065 29972483332100828645017549)
            ·
              refine ⟨11239681249537810741881581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29972483332100828645017549 11239681249537810741881581)
              ·
                refine ⟨4214880468576679028205593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11239681249537810741881581 4214880468576679028205593)
                ·
                  refine ⟨3161160351432509271154195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4214880468576679028205593 3161160351432509271154195)
                  ·
                    refine ⟨4741740527148763906731293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3161160351432509271154195 4741740527148763906731293)
                    ·
                      refine ⟨1778152697680786465024235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4741740527148763906731293 1778152697680786465024235)
                      ·
                        rfl

theorem cell23_3462940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_3462940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462940 prefixEnd_3462940 := by exact prefixLift 3462940
  have htrace : WordTrace (prefixWord ++ tailWord_3462940) baseStart_3462940 baseEnd_3462940 := by
    simpa [prefixWord, tailWord_3462940, baseEnd_3462940] using wordTrace_append hprefix tailTrace_3462940
  have hstable : (prefixWord ++ tailWord_3462940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462940).length < 2 ^ (prefixWord ++ tailWord_3462940).sum := by decide
  have hdescent : baseEnd_3462940 < baseStart_3462940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462986 : List Nat := [3, 1, 2, 1, 1, 1, 4, 3, 7]
def baseStart_3462986 : Nat := 118140960795 + 3462986 * 2 ^ 59
def prefixEnd_3462986 : Nat := 4983230072969 + 3 ^ 40 * 3462986 * 2
def baseEnd_3462986 : Nat := 197575146421210365005447

theorem tailTrace_3462986 : CollatzResearch.WordTrace tailWord_3462986 prefixEnd_3462986 197575146421210365005447 := by
  unfold tailWord_3462986
  simp only [CollatzResearch.WordTrace]
  refine ⟨31576368958050156941922203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84203650554800418511792541 31576368958050156941922203)
  ·
    refine ⟨47364553437075235412883305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31576368958050156941922203 47364553437075235412883305)
    ·
      refine ⟨35523415077806426559662479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47364553437075235412883305 35523415077806426559662479)
      ·
        refine ⟨53285122616709639839493719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35523415077806426559662479 53285122616709639839493719)
        ·
          refine ⟨79927683925064459759240579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53285122616709639839493719 79927683925064459759240579)
          ·
            refine ⟨119891525887596689638860869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79927683925064459759240579 119891525887596689638860869)
            ·
              refine ⟨22479661103924379307286413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119891525887596689638860869 22479661103924379307286413)
              ·
                refine ⟨8429872913971642240232405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22479661103924379307286413 8429872913971642240232405)
                ·
                  refine ⟨197575146421210365005447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8429872913971642240232405 197575146421210365005447)
                  ·
                    rfl

theorem cell23_3462986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 7].length) (baseStart_3462986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462986 prefixEnd_3462986 := by exact prefixLift 3462986
  have htrace : WordTrace (prefixWord ++ tailWord_3462986) baseStart_3462986 baseEnd_3462986 := by
    simpa [prefixWord, tailWord_3462986, baseEnd_3462986] using wordTrace_append hprefix tailTrace_3462986
  have hstable : (prefixWord ++ tailWord_3462986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462986).length < 2 ^ (prefixWord ++ tailWord_3462986).sum := by decide
  have hdescent : baseEnd_3462986 < baseStart_3462986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462993 : List Nat := [1, 2, 2, 1, 5, 2, 1, 1, 2, 2, 4]
def baseStart_3462993 : Nat := 118140960795 + 3462993 * 2 ^ 59
def prefixEnd_3462993 : Nat := 4983230072969 + 3 ^ 40 * 3462993 * 2
def baseEnd_3462993 : Nat := 1778179912155474757661491

theorem tailTrace_3462993 : CollatzResearch.WordTrace tailWord_3462993 prefixEnd_3462993 1778179912155474757661491 := by
  unfold tailWord_3462993
  simp only [CollatzResearch.WordTrace]
  refine ⟨126305731143175267963193633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84203820762116845308795755 126305731143175267963193633)
  ·
    refine ⟨94729298357381450972395225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126305731143175267963193633 94729298357381450972395225)
    ·
      refine ⟨71046973768036088229296419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94729298357381450972395225 71046973768036088229296419)
      ·
        refine ⟨106570460652054132343944629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71046973768036088229296419 106570460652054132343944629)
        ·
          refine ⟨9990980686130074907244809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106570460652054132343944629 9990980686130074907244809)
          ·
            refine ⟨7493235514597556180433607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9990980686130074907244809 7493235514597556180433607)
            ·
              refine ⟨11239853271896334270650411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7493235514597556180433607 11239853271896334270650411)
              ·
                refine ⟨16859779907844501405975617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11239853271896334270650411 16859779907844501405975617)
                ·
                  refine ⟨12644834930883376054481713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16859779907844501405975617 12644834930883376054481713)
                  ·
                    refine ⟨9483626198162532040861285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12644834930883376054481713 9483626198162532040861285)
                    ·
                      refine ⟨1778179912155474757661491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9483626198162532040861285 1778179912155474757661491)
                      ·
                        rfl

theorem cell23_3462993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_3462993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462993 prefixEnd_3462993 := by exact prefixLift 3462993
  have htrace : WordTrace (prefixWord ++ tailWord_3462993) baseStart_3462993 baseEnd_3462993 := by
    simpa [prefixWord, tailWord_3462993, baseEnd_3462993] using wordTrace_append hprefix tailTrace_3462993
  have hstable : (prefixWord ++ tailWord_3462993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462993).length < 2 ^ (prefixWord ++ tailWord_3462993).sum := by decide
  have hdescent : baseEnd_3462993 < baseStart_3462993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3462997 : List Nat := [1, 3, 2, 2, 2, 2, 2, 3, 2, 2, 2]
def baseStart_3462997 : Nat := 118140960795 + 3462997 * 2 ^ 59
def prefixEnd_3462997 : Nat := 4983230072969 + 3 ^ 40 * 3462997 * 2
def baseEnd_3462997 : Nat := 1778181966078092742011473

theorem tailTrace_3462997 : CollatzResearch.WordTrace tailWord_3462997 prefixEnd_3462997 1778181966078092742011473 := by
  unfold tailWord_3462997
  simp only [CollatzResearch.WordTrace]
  refine ⟨126305877035160776646339245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84203918023440517764226163 126305877035160776646339245)
  ·
    refine ⟨47364703888185291242377217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126305877035160776646339245 47364703888185291242377217)
    ·
      refine ⟨35523527916138968431782913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47364703888185291242377217 35523527916138968431782913)
      ·
        refine ⟨26642645937104226323837185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35523527916138968431782913 26642645937104226323837185)
        ·
          refine ⟨19981984452828169742877889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26642645937104226323837185 19981984452828169742877889)
          ·
            refine ⟨14986488339621127307158417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19981984452828169742877889 14986488339621127307158417)
            ·
              refine ⟨11239866254715845480368813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14986488339621127307158417 11239866254715845480368813)
              ·
                refine ⟨4214949845518442055138305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11239866254715845480368813 4214949845518442055138305)
                ·
                  refine ⟨3161212384138831541353729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4214949845518442055138305 3161212384138831541353729)
                  ·
                    refine ⟨2370909288104123656015297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3161212384138831541353729 2370909288104123656015297)
                    ·
                      refine ⟨1778181966078092742011473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2370909288104123656015297 1778181966078092742011473)
                      ·
                        rfl

theorem cell23_3462997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_3462997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3462997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3462997 prefixEnd_3462997 := by exact prefixLift 3462997
  have htrace : WordTrace (prefixWord ++ tailWord_3462997) baseStart_3462997 baseEnd_3462997 := by
    simpa [prefixWord, tailWord_3462997, baseEnd_3462997] using wordTrace_append hprefix tailTrace_3462997
  have hstable : (prefixWord ++ tailWord_3462997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3462997).length < 2 ^ (prefixWord ++ tailWord_3462997).sum := by decide
  have hdescent : baseEnd_3462997 < baseStart_3462997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3462997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463018 : List Nat := [3, 1, 3, 4, 2, 1, 2, 1, 1, 3, 2]
def baseStart_3463018 : Nat := 118140960795 + 3463018 * 2 ^ 59
def prefixEnd_3463018 : Nat := 4983230072969 + 3 ^ 40 * 3463018 * 2
def baseEnd_3463018 : Nat := 1778192749171837159848877

theorem tailTrace_3463018 : CollatzResearch.WordTrace tailWord_3463018 prefixEnd_3463018 1778192749171837159848877 := by
  unfold tailWord_3463018
  simp only [CollatzResearch.WordTrace]
  refine ⟨31576660742021174308213427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84204428645389798155235805 31576660742021174308213427)
  ·
    refine ⟨47364991113031761462320141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31576660742021174308213427 47364991113031761462320141)
    ·
      refine ⟨17761871667386910548370053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47364991113031761462320141 17761871667386910548370053)
      ·
        refine ⟨3330350937635045727819385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17761871667386910548370053 3330350937635045727819385)
        ·
          refine ⟨2497763203226284295864539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3330350937635045727819385 2497763203226284295864539)
          ·
            refine ⟨3746644804839426443796809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2497763203226284295864539 3746644804839426443796809)
            ·
              refine ⟨2809983603629569832847607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3746644804839426443796809 2809983603629569832847607)
              ·
                refine ⟨4214975405444354749271411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2809983603629569832847607 4214975405444354749271411)
                ·
                  refine ⟨6322463108166532123907117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4214975405444354749271411 6322463108166532123907117)
                  ·
                    refine ⟨2370923665562449546465169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6322463108166532123907117 2370923665562449546465169)
                    ·
                      refine ⟨1778192749171837159848877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2370923665562449546465169 1778192749171837159848877)
                      ·
                        rfl

theorem cell23_3463018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_3463018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463018 prefixEnd_3463018 := by exact prefixLift 3463018
  have htrace : WordTrace (prefixWord ++ tailWord_3463018) baseStart_3463018 baseEnd_3463018 := by
    simpa [prefixWord, tailWord_3463018, baseEnd_3463018] using wordTrace_append hprefix tailTrace_3463018
  have hstable : (prefixWord ++ tailWord_3463018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463018).length < 2 ^ (prefixWord ++ tailWord_3463018).sum := by decide
  have hdescent : baseEnd_3463018 < baseStart_3463018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463020 : List Nat := [2, 2, 1, 1, 4, 3, 2, 3, 5]
def baseStart_3463020 : Nat := 118140960795 + 3463020 * 2 ^ 59
def prefixEnd_3463020 : Nat := 4983230072969 + 3 ^ 40 * 3463020 * 2
def baseEnd_3463020 : Nat := 197577086237016239113763

theorem tailTrace_3463020 : CollatzResearch.WordTrace tailWord_3463020 prefixEnd_3463020 197577086237016239113763 := by
  unfold tailWord_3463020
  simp only [CollatzResearch.WordTrace]
  refine ⟨63153357957038725787213257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84204477276051634382951009 63153357957038725787213257)
  ·
    refine ⟨47365018467779044340409943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63153357957038725787213257 47365018467779044340409943)
    ·
      refine ⟨71047527701668566510614915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47365018467779044340409943 71047527701668566510614915)
      ·
        refine ⟨106571291552502849765922373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71047527701668566510614915 106571291552502849765922373)
        ·
          refine ⟨19982117166094284331110445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106571291552502849765922373 19982117166094284331110445)
          ·
            refine ⟨7493293937285356624166417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19982117166094284331110445 7493293937285356624166417)
            ·
              refine ⟨5619970452964017468124813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7493293937285356624166417 5619970452964017468124813)
              ·
                refine ⟨2107488919861506550546805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5619970452964017468124813 2107488919861506550546805)
                ·
                  refine ⟨197577086237016239113763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2107488919861506550546805 197577086237016239113763)
                  ·
                    rfl

theorem cell23_3463020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3, 5].length) (baseStart_3463020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463020 prefixEnd_3463020 := by exact prefixLift 3463020
  have htrace : WordTrace (prefixWord ++ tailWord_3463020) baseStart_3463020 baseEnd_3463020 := by
    simpa [prefixWord, tailWord_3463020, baseEnd_3463020] using wordTrace_append hprefix tailTrace_3463020
  have hstable : (prefixWord ++ tailWord_3463020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463020).length < 2 ^ (prefixWord ++ tailWord_3463020).sum := by decide
  have hdescent : baseEnd_3463020 < baseStart_3463020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463093 : List Nat := [1, 3, 3, 2, 1, 2, 2, 1, 8]
def baseStart_3463093 : Nat := 118140960795 + 3463093 * 2 ^ 59
def prefixEnd_3463093 : Nat := 4983230072969 + 3 ^ 40 * 3463093 * 2
def baseEnd_3463093 : Nat := 197581251135658262934559

theorem tailTrace_3463093 : CollatzResearch.WordTrace tailWord_3463093 prefixEnd_3463093 197581251135658262934559 := by
  unfold tailWord_3463093
  simp only [CollatzResearch.WordTrace]
  refine ⟨126309378442812985041833933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84206252295208656694555955 126309378442812985041833933)
  ·
    refine ⟨47366016916054869390687725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126309378442812985041833933 47366016916054869390687725)
    ·
      refine ⟨17762256343520576021507897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47366016916054869390687725 17762256343520576021507897)
      ·
        refine ⟨13321692257640432016130923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17762256343520576021507897 13321692257640432016130923)
        ·
          refine ⟨19982538386460648024196385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13321692257640432016130923 19982538386460648024196385)
          ·
            refine ⟨14986903789845486018147289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19982538386460648024196385 14986903789845486018147289)
            ·
              refine ⟨11240177842384114513610467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14986903789845486018147289 11240177842384114513610467)
              ·
                refine ⟨16860266763576171770415701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11240177842384114513610467 16860266763576171770415701)
                ·
                  refine ⟨197581251135658262934559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16860266763576171770415701 197581251135658262934559)
                  ·
                    rfl

theorem cell23_3463093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 8].length) (baseStart_3463093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463093 prefixEnd_3463093 := by exact prefixLift 3463093
  have htrace : WordTrace (prefixWord ++ tailWord_3463093) baseStart_3463093 baseEnd_3463093 := by
    simpa [prefixWord, tailWord_3463093, baseEnd_3463093] using wordTrace_append hprefix tailTrace_3463093
  have hstable : (prefixWord ++ tailWord_3463093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463093).length < 2 ^ (prefixWord ++ tailWord_3463093).sum := by decide
  have hdescent : baseEnd_3463093 < baseStart_3463093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463120 : List Nat := [2, 1, 1, 1, 1, 2, 4, 4, 3, 1, 3]
def baseStart_3463120 : Nat := 118140960795 + 3463120 * 2 ^ 59
def prefixEnd_3463120 : Nat := 4983230072969 + 3 ^ 40 * 3463120 * 2
def baseEnd_3463120 : Nat := 1778245124198595760773407

theorem tailTrace_3463120 : CollatzResearch.WordTrace tailWord_3463120 prefixEnd_3463120 1778245124198595760773407 := by
  unfold tailWord_3463120
  simp only [CollatzResearch.WordTrace]
  refine ⟨63155181606857584326533407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84206908809143445768711209 63155181606857584326533407)
  ·
    refine ⟨94732772410286376489800111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63155181606857584326533407 94732772410286376489800111)
    ·
      refine ⟨142099158615429564734700167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94732772410286376489800111 142099158615429564734700167)
      ·
        refine ⟨213148737923144347102050251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142099158615429564734700167 213148737923144347102050251)
        ·
          refine ⟨319723106884716520653075377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213148737923144347102050251 319723106884716520653075377)
          ·
            refine ⟨239792330163537390489806533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319723106884716520653075377 239792330163537390489806533)
            ·
              refine ⟨44961061905663260716838725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239792330163537390489806533 44961061905663260716838725)
              ·
                refine ⟨8430199107311861384407261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44961061905663260716838725 8430199107311861384407261)
                ·
                  refine ⟨3161324665241948019152723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8430199107311861384407261 3161324665241948019152723)
                  ·
                    refine ⟨4741986997862922028729085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3161324665241948019152723 4741986997862922028729085)
                    ·
                      refine ⟨1778245124198595760773407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4741986997862922028729085 1778245124198595760773407)
                      ·
                        rfl

theorem cell23_3463120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 3, 1, 3].length) (baseStart_3463120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463120 prefixEnd_3463120 := by exact prefixLift 3463120
  have htrace : WordTrace (prefixWord ++ tailWord_3463120) baseStart_3463120 baseEnd_3463120 := by
    simpa [prefixWord, tailWord_3463120, baseEnd_3463120] using wordTrace_append hprefix tailTrace_3463120
  have hstable : (prefixWord ++ tailWord_3463120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463120).length < 2 ^ (prefixWord ++ tailWord_3463120).sum := by decide
  have hdescent : baseEnd_3463120 < baseStart_3463120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463163 : List Nat := [1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 5]
def baseStart_3463163 : Nat := 118140960795 + 3463163 * 2 ^ 59
def prefixEnd_3463163 : Nat := 4983230072969 + 3 ^ 40 * 3463163 * 2
def baseEnd_3463163 : Nat := 1778267203866739092535709

theorem tailTrace_3463163 : CollatzResearch.WordTrace tailWord_3463163 prefixEnd_3463163 1778267203866739092535709 := by
  unfold tailWord_3463163
  simp only [CollatzResearch.WordTrace]
  refine ⟨126311931552559386996882143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84207954368372924664588095 126311931552559386996882143)
  ·
    refine ⟨189467897328839080495323215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126311931552559386996882143 189467897328839080495323215)
    ·
      refine ⟨284201845993258620742984823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189467897328839080495323215 284201845993258620742984823)
      ·
        refine ⟨426302768989887931114477235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284201845993258620742984823 426302768989887931114477235)
        ·
          refine ⟨639454153484831896671715853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426302768989887931114477235 639454153484831896671715853)
          ·
            refine ⟨239795307556811961251893445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 639454153484831896671715853 239795307556811961251893445)
            ·
              refine ⟨44961620166902242734730021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239795307556811961251893445 44961620166902242734730021)
              ·
                refine ⟨8430303781294170512761879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44961620166902242734730021 8430303781294170512761879)
                ·
                  refine ⟨12645455671941255769142819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8430303781294170512761879 12645455671941255769142819)
                  ·
                    refine ⟨18968183507911883653714229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12645455671941255769142819 18968183507911883653714229)
                    ·
                      refine ⟨1778267203866739092535709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18968183507911883653714229 1778267203866739092535709)
                      ·
                        rfl

theorem cell23_3463163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 5].length) (baseStart_3463163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463163 prefixEnd_3463163 := by exact prefixLift 3463163
  have htrace : WordTrace (prefixWord ++ tailWord_3463163) baseStart_3463163 baseEnd_3463163 := by
    simpa [prefixWord, tailWord_3463163, baseEnd_3463163] using wordTrace_append hprefix tailTrace_3463163
  have hstable : (prefixWord ++ tailWord_3463163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463163).length < 2 ^ (prefixWord ++ tailWord_3463163).sum := by decide
  have hdescent : baseEnd_3463163 < baseStart_3463163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463180 : List Nat := [2, 2, 1, 2, 3, 1, 1, 3, 3, 2, 3]
def baseStart_3463180 : Nat := 118140960795 + 3463180 * 2 ^ 59
def prefixEnd_3463180 : Nat := 4983230072969 + 3 ^ 40 * 3463180 * 2
def baseEnd_3463180 : Nat := 1778275933037865526023131

theorem tailTrace_3463180 : CollatzResearch.WordTrace tailWord_3463180 prefixEnd_3463180 1778275933037865526023131 := by
  unfold tailWord_3463180
  simp only [CollatzResearch.WordTrace]
  refine ⟨63156275796748899450125497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84208367728998532600167329 63156275796748899450125497)
  ·
    refine ⟨47367206847561674587594123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63156275796748899450125497 47367206847561674587594123)
    ·
      refine ⟨71050810271342511881391185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47367206847561674587594123 71050810271342511881391185)
      ·
        refine ⟨53288107703506883911043389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71050810271342511881391185 53288107703506883911043389)
        ·
          refine ⟨19983040388815081466641271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53288107703506883911043389 19983040388815081466641271)
          ·
            refine ⟨29974560583222622199961907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19983040388815081466641271 29974560583222622199961907)
            ·
              refine ⟨44961840874833933299942861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29974560583222622199961907 44961840874833933299942861)
              ·
                refine ⟨16860690328062724987478573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44961840874833933299942861 16860690328062724987478573)
                ·
                  refine ⟨6322758873023521870304465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16860690328062724987478573 6322758873023521870304465)
                  ·
                    refine ⟨4742069154767641402728349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6322758873023521870304465 4742069154767641402728349)
                    ·
                      refine ⟨1778275933037865526023131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4742069154767641402728349 1778275933037865526023131)
                      ·
                        rfl

theorem cell23_3463180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_3463180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463180 prefixEnd_3463180 := by exact prefixLift 3463180
  have htrace : WordTrace (prefixWord ++ tailWord_3463180) baseStart_3463180 baseEnd_3463180 := by
    simpa [prefixWord, tailWord_3463180, baseEnd_3463180] using wordTrace_append hprefix tailTrace_3463180
  have hstable : (prefixWord ++ tailWord_3463180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463180).length < 2 ^ (prefixWord ++ tailWord_3463180).sum := by decide
  have hdescent : baseEnd_3463180 < baseStart_3463180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463191 : List Nat := [1, 1, 3, 5, 3, 1, 2, 1, 1, 5]
def baseStart_3463191 : Nat := 118140960795 + 3463191 * 2 ^ 59
def prefixEnd_3463191 : Nat := 4983230072969 + 3 ^ 40 * 3463191 * 2
def baseEnd_3463191 : Nat := 592760527108354994328527

theorem tailTrace_3463191 : CollatzResearch.WordTrace tailWord_3463191 prefixEnd_3463191 592760527108354994328527 := by
  unfold tailWord_3463191
  simp only [CollatzResearch.WordTrace]
  refine ⟨126312952796457947778901427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84208635197638631852600951 126312952796457947778901427)
  ·
    refine ⟨189469429194686921668352141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126312952796457947778901427 189469429194686921668352141)
    ·
      refine ⟨71051035948007595625632053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189469429194686921668352141 71051035948007595625632053)
      ·
        refine ⟨6661034620125712089903005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71051035948007595625632053 6661034620125712089903005)
        ·
          refine ⟨2497887982547142033713627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6661034620125712089903005 2497887982547142033713627)
          ·
            refine ⟨3746831973820713050570441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2497887982547142033713627 3746831973820713050570441)
            ·
              refine ⟨2810123980365534787927831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3746831973820713050570441 2810123980365534787927831)
              ·
                refine ⟨4215185970548302181891747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2810123980365534787927831 4215185970548302181891747)
                ·
                  refine ⟨6322778955822453272837621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4215185970548302181891747 6322778955822453272837621)
                  ·
                    refine ⟨592760527108354994328527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6322778955822453272837621 592760527108354994328527)
                    ·
                      rfl

theorem cell23_3463191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 1, 5].length) (baseStart_3463191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463191 prefixEnd_3463191 := by exact prefixLift 3463191
  have htrace : WordTrace (prefixWord ++ tailWord_3463191) baseStart_3463191 baseEnd_3463191 := by
    simpa [prefixWord, tailWord_3463191, baseEnd_3463191] using wordTrace_append hprefix tailTrace_3463191
  have hstable : (prefixWord ++ tailWord_3463191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463191).length < 2 ^ (prefixWord ++ tailWord_3463191).sum := by decide
  have hdescent : baseEnd_3463191 < baseStart_3463191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463194 : List Nat := [3, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4]
def baseStart_3463194 : Nat := 118140960795 + 3463194 * 2 ^ 59
def prefixEnd_3463194 : Nat := 4983230072969 + 3 ^ 40 * 3463194 * 2
def baseEnd_3463194 : Nat := 1778283121767028471248067

theorem tailTrace_3463194 : CollatzResearch.WordTrace tailWord_3463194 prefixEnd_3463194 1778283121767028471248067 := by
  unfold tailWord_3463194
  simp only [CollatzResearch.WordTrace]
  refine ⟨31578265553861769822815159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84208708143631386194173757 31578265553861769822815159)
  ·
    refine ⟨47367398330792654734222739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31578265553861769822815159 47367398330792654734222739)
    ·
      refine ⟨71051097496188982101334109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47367398330792654734222739 71051097496188982101334109)
      ·
        refine ⟨26644161561070868288000291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71051097496188982101334109 26644161561070868288000291)
        ·
          refine ⟨39966242341606302432000437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26644161561070868288000291 39966242341606302432000437)
          ·
            refine ⟨3746835219525590853000041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39966242341606302432000437 3746835219525590853000041)
            ·
              refine ⟨2810126414644193139750031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3746835219525590853000041 2810126414644193139750031)
              ·
                refine ⟨4215189621966289709625047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2810126414644193139750031 4215189621966289709625047)
                ·
                  refine ⟨6322784432949434564437571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4215189621966289709625047 6322784432949434564437571)
                  ·
                    refine ⟨9484176649424151846656357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6322784432949434564437571 9484176649424151846656357)
                    ·
                      refine ⟨1778283121767028471248067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9484176649424151846656357 1778283121767028471248067)
                      ·
                        rfl

theorem cell23_3463194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_3463194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463194 prefixEnd_3463194 := by exact prefixLift 3463194
  have htrace : WordTrace (prefixWord ++ tailWord_3463194) baseStart_3463194 baseEnd_3463194 := by
    simpa [prefixWord, tailWord_3463194, baseEnd_3463194] using wordTrace_append hprefix tailTrace_3463194
  have hstable : (prefixWord ++ tailWord_3463194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463194).length < 2 ^ (prefixWord ++ tailWord_3463194).sum := by decide
  have hdescent : baseEnd_3463194 < baseStart_3463194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463224 : List Nat := [2, 1, 2, 1, 7, 1, 1, 1, 1, 2, 4]
def baseStart_3463224 : Nat := 118140960795 + 3463224 * 2 ^ 59
def prefixEnd_3463224 : Nat := 4983230072969 + 3 ^ 40 * 3463224 * 2
def baseEnd_3463224 : Nat := 1778298526186663353872929

theorem tailTrace_3463224 : CollatzResearch.WordTrace tailWord_3463224 prefixEnd_3463224 1778298526186663353872929 := by
  unfold tailWord_3463224
  simp only [CollatzResearch.WordTrace]
  refine ⟨63157078202669197207426363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84209437603558929609901817 63157078202669197207426363)
  ·
    refine ⟨94735617304003795811139545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63157078202669197207426363 94735617304003795811139545)
    ·
      refine ⟨71051712978002846858354659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94735617304003795811139545 71051712978002846858354659)
      ·
        refine ⟨106577569467004270287531989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71051712978002846858354659 106577569467004270287531989)
        ·
          refine ⟨2497911784382912584864031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 106577569467004270287531989 2497911784382912584864031)
          ·
            refine ⟨3746867676574368877296047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2497911784382912584864031 3746867676574368877296047)
            ·
              refine ⟨5620301514861553315944071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3746867676574368877296047 5620301514861553315944071)
              ·
                refine ⟨8430452272292329973916107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5620301514861553315944071 8430452272292329973916107)
                ·
                  refine ⟨12645678408438494960874161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8430452272292329973916107 12645678408438494960874161)
                  ·
                    refine ⟨9484258806328871220655621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12645678408438494960874161 9484258806328871220655621)
                    ·
                      refine ⟨1778298526186663353872929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9484258806328871220655621 1778298526186663353872929)
                      ·
                        rfl

theorem cell23_3463224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 1, 2, 4].length) (baseStart_3463224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463224 prefixEnd_3463224 := by exact prefixLift 3463224
  have htrace : WordTrace (prefixWord ++ tailWord_3463224) baseStart_3463224 baseEnd_3463224 := by
    simpa [prefixWord, tailWord_3463224, baseEnd_3463224] using wordTrace_append hprefix tailTrace_3463224
  have hstable : (prefixWord ++ tailWord_3463224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463224).length < 2 ^ (prefixWord ++ tailWord_3463224).sum := by decide
  have hdescent : baseEnd_3463224 < baseStart_3463224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463262 : List Nat := [4, 4, 1, 1, 3, 1, 1, 1, 3, 2, 2]
def baseStart_3463262 : Nat := 118140960795 + 3463262 * 2 ^ 59
def prefixEnd_3463262 : Nat := 4983230072969 + 3 ^ 40 * 3463262 * 2
def baseEnd_3463262 : Nat := 1778318038451534205197755

theorem tailTrace_3463262 : CollatzResearch.WordTrace tailWord_3463262 prefixEnd_3463262 1778318038451534205197755 := by
  unfold tailWord_3463262
  simp only [CollatzResearch.WordTrace]
  refine ⟨15789442797400090863092005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84210361586133817936490693 15789442797400090863092005)
  ·
    refine ⟨2960520524512517036829751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15789442797400090863092005 2960520524512517036829751)
    ·
      refine ⟨4440780786768775555244627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2960520524512517036829751 4440780786768775555244627)
      ·
        refine ⟨6661171180153163332866941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4440780786768775555244627 6661171180153163332866941)
        ·
          refine ⟨2497939192557436249825103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6661171180153163332866941 2497939192557436249825103)
          ·
            refine ⟨3746908788836154374737655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2497939192557436249825103 3746908788836154374737655)
            ·
              refine ⟨5620363183254231562106483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3746908788836154374737655 5620363183254231562106483)
              ·
                refine ⟨8430544774881347343159725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5620363183254231562106483 8430544774881347343159725)
                ·
                  refine ⟨3161454290580505253684897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8430544774881347343159725 3161454290580505253684897)
                  ·
                    refine ⟨2371090717935378940263673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3161454290580505253684897 2371090717935378940263673)
                    ·
                      refine ⟨1778318038451534205197755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2371090717935378940263673 1778318038451534205197755)
                      ·
                        rfl

theorem cell23_3463262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_3463262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463262 prefixEnd_3463262 := by exact prefixLift 3463262
  have htrace : WordTrace (prefixWord ++ tailWord_3463262) baseStart_3463262 baseEnd_3463262 := by
    simpa [prefixWord, tailWord_3463262, baseEnd_3463262] using wordTrace_append hprefix tailTrace_3463262
  have hstable : (prefixWord ++ tailWord_3463262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463262).length < 2 ^ (prefixWord ++ tailWord_3463262).sum := by decide
  have hdescent : baseEnd_3463262 < baseStart_3463262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463263 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 6]
def baseStart_3463263 : Nat := 118140960795 + 3463263 * 2 ^ 59
def prefixEnd_3463263 : Nat := 4983230072969 + 3 ^ 40 * 3463263 * 2
def baseEnd_3463263 : Nat := 1778318551932188701285249

theorem tailTrace_3463263 : CollatzResearch.WordTrace tailWord_3463263 prefixEnd_3463263 1778318551932188701285249 := by
  unfold tailWord_3463263
  simp only [CollatzResearch.WordTrace]
  refine ⟨126315578852197104075522443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84210385901464736050348295 126315578852197104075522443)
  ·
    refine ⟨189473368278295656113283665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126315578852197104075522443 189473368278295656113283665)
    ·
      refine ⟨142105026208721742084962749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189473368278295656113283665 142105026208721742084962749)
      ·
        refine ⟨53289384828270653281861031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142105026208721742084962749 53289384828270653281861031)
        ·
          refine ⟨79934077242405979922791547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53289384828270653281861031 79934077242405979922791547)
          ·
            refine ⟨119901115863608969884187321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79934077242405979922791547 119901115863608969884187321)
            ·
              refine ⟨89925836897706727413140491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119901115863608969884187321 89925836897706727413140491)
              ·
                refine ⟨134888755346560091119710737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89925836897706727413140491 134888755346560091119710737)
                ·
                  refine ⟨101166566509920068339783053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134888755346560091119710737 101166566509920068339783053)
                  ·
                    refine ⟨37937462441220025627418645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101166566509920068339783053 37937462441220025627418645)
                    ·
                      refine ⟨1778318551932188701285249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37937462441220025627418645 1778318551932188701285249)
                      ·
                        rfl

theorem cell23_3463263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_3463263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463263 prefixEnd_3463263 := by exact prefixLift 3463263
  have htrace : WordTrace (prefixWord ++ tailWord_3463263) baseStart_3463263 baseEnd_3463263 := by
    simpa [prefixWord, tailWord_3463263, baseEnd_3463263] using wordTrace_append hprefix tailTrace_3463263
  have hstable : (prefixWord ++ tailWord_3463263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463263).length < 2 ^ (prefixWord ++ tailWord_3463263).sum := by decide
  have hdescent : baseEnd_3463263 < baseStart_3463263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463357 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 3, 6, 2]
def baseStart_3463357 : Nat := 118140960795 + 3463357 * 2 ^ 59
def prefixEnd_3463357 : Nat := 4983230072969 + 3 ^ 40 * 3463357 * 2
def baseEnd_3463357 : Nat := 1778366819113711333509817

theorem tailTrace_3463357 : CollatzResearch.WordTrace tailWord_3463357 prefixEnd_3463357 1778366819113711333509817 := by
  unfold tailWord_3463357
  simp only [CollatzResearch.WordTrace]
  refine ⟨126319007313856558129444325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84212671542571038752962883 126319007313856558129444325)
  ·
    refine ⟨23684813871348104649270811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126319007313856558129444325 23684813871348104649270811)
    ·
      refine ⟨35527220807022156973906217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23684813871348104649270811 35527220807022156973906217)
      ·
        refine ⟨26645415605266617730429663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35527220807022156973906217 26645415605266617730429663)
        ·
          refine ⟨39968123407899926595644495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26645415605266617730429663 39968123407899926595644495)
          ·
            refine ⟨59952185111849889893466743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39968123407899926595644495 59952185111849889893466743)
            ·
              refine ⟨89928277667774834840200115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59952185111849889893466743 89928277667774834840200115)
              ·
                refine ⟨134892416501662252260300173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89928277667774834840200115 134892416501662252260300173)
                ·
                  refine ⟨50584656188123344597612565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134892416501662252260300173 50584656188123344597612565)
                  ·
                    refine ⟨2371155758818281778013089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 50584656188123344597612565 2371155758818281778013089)
                    ·
                      refine ⟨1778366819113711333509817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2371155758818281778013089 1778366819113711333509817)
                      ·
                        rfl

theorem cell23_3463357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_3463357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463357 prefixEnd_3463357 := by exact prefixLift 3463357
  have htrace : WordTrace (prefixWord ++ tailWord_3463357) baseStart_3463357 baseEnd_3463357 := by
    simpa [prefixWord, tailWord_3463357, baseEnd_3463357] using wordTrace_append hprefix tailTrace_3463357
  have hstable : (prefixWord ++ tailWord_3463357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463357).length < 2 ^ (prefixWord ++ tailWord_3463357).sum := by decide
  have hdescent : baseEnd_3463357 < baseStart_3463357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463370 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 1, 3, 6]
def baseStart_3463370 : Nat := 118140960795 + 3463370 * 2 ^ 59
def prefixEnd_3463370 : Nat := 4983230072969 + 3 ^ 40 * 3463370 * 2
def baseEnd_3463370 : Nat := 1778373494362219782647257

theorem tailTrace_3463370 : CollatzResearch.WordTrace tailWord_3463370 prefixEnd_3463370 1778373494362219782647257 := by
  unfold tailWord_3463370
  simp only [CollatzResearch.WordTrace]
  refine ⟨31579870365702365337416891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84212987641872974233111709 31579870365702365337416891)
  ·
    refine ⟨47369805548553548006125337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31579870365702365337416891 47369805548553548006125337)
    ·
      refine ⟨35527354161415161004594003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47369805548553548006125337 35527354161415161004594003)
      ·
        refine ⟨53291031242122741506891005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35527354161415161004594003 53291031242122741506891005)
        ·
          refine ⟨19984136715796028065084127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53291031242122741506891005 19984136715796028065084127)
          ·
            refine ⟨29976205073694042097626191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19984136715796028065084127 29976205073694042097626191)
            ·
              refine ⟨44964307610541063146439287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29976205073694042097626191 44964307610541063146439287)
              ·
                refine ⟨67446461415811594719658931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44964307610541063146439287 67446461415811594719658931)
                ·
                  refine ⟨101169692123717392079488397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67446461415811594719658931 101169692123717392079488397)
                  ·
                    refine ⟨37938634546394022029808149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101169692123717392079488397 37938634546394022029808149)
                    ·
                      refine ⟨1778373494362219782647257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37938634546394022029808149 1778373494362219782647257)
                      ·
                        rfl

theorem cell23_3463370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_3463370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463370 prefixEnd_3463370 := by exact prefixLift 3463370
  have htrace : WordTrace (prefixWord ++ tailWord_3463370) baseStart_3463370 baseEnd_3463370 := by
    simpa [prefixWord, tailWord_3463370, baseEnd_3463370] using wordTrace_append hprefix tailTrace_3463370
  have hstable : (prefixWord ++ tailWord_3463370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463370).length < 2 ^ (prefixWord ++ tailWord_3463370).sum := by decide
  have hdescent : baseEnd_3463370 < baseStart_3463370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463374 : List Nat := [4, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2]
def baseStart_3463374 : Nat := 118140960795 + 3463374 * 2 ^ 59
def prefixEnd_3463374 : Nat := 4983230072969 + 3 ^ 40 * 3463374 * 2
def baseEnd_3463374 : Nat := 1778375548284837766997239

theorem tailTrace_3463374 : CollatzResearch.WordTrace tailWord_3463374 prefixEnd_3463374 1778375548284837766997239 := by
  unfold tailWord_3463374
  simp only [CollatzResearch.WordTrace]
  refine ⟨15789953419349371254101647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84213084903196646688542117 15789953419349371254101647)
  ·
    refine ⟨23684930129024056881152471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15789953419349371254101647 23684930129024056881152471)
    ·
      refine ⟨35527395193536085321728707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23684930129024056881152471 35527395193536085321728707)
      ·
        refine ⟨53291092790304127982593061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35527395193536085321728707 53291092790304127982593061)
        ·
          refine ⟨9992079898182023996736199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53291092790304127982593061 9992079898182023996736199)
          ·
            refine ⟨14988119847273035995104299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9992079898182023996736199 14988119847273035995104299)
            ·
              refine ⟨22482179770909553992656449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14988119847273035995104299 22482179770909553992656449)
              ·
                refine ⟨16861634828182165494492337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22482179770909553992656449 16861634828182165494492337)
                ·
                  refine ⟨12646226121136624120869253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16861634828182165494492337 12646226121136624120869253)
                  ·
                    refine ⟨2371167397713117022662985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12646226121136624120869253 2371167397713117022662985)
                    ·
                      refine ⟨1778375548284837766997239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2371167397713117022662985 1778375548284837766997239)
                      ·
                        rfl

theorem cell23_3463374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2].length) (baseStart_3463374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463374 prefixEnd_3463374 := by exact prefixLift 3463374
  have htrace : WordTrace (prefixWord ++ tailWord_3463374) baseStart_3463374 baseEnd_3463374 := by
    simpa [prefixWord, tailWord_3463374, baseEnd_3463374] using wordTrace_append hprefix tailTrace_3463374
  have hstable : (prefixWord ++ tailWord_3463374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463374).length < 2 ^ (prefixWord ++ tailWord_3463374).sum := by decide
  have hdescent : baseEnd_3463374 < baseStart_3463374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463377 : List Nat := [1, 2, 2, 1, 2, 2, 2, 4, 2, 2, 3]
def baseStart_3463377 : Nat := 118140960795 + 3463377 * 2 ^ 59
def prefixEnd_3463377 : Nat := 4983230072969 + 3 ^ 40 * 3463377 * 2
def baseEnd_3463377 : Nat := 1778377088726801255259725

theorem tailTrace_3463377 : CollatzResearch.WordTrace tailWord_3463377 prefixEnd_3463377 1778377088726801255259725 := by
  unfold tailWord_3463377
  simp only [CollatzResearch.WordTrace]
  refine ⟨126319736773784101545172385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84213157849189401030114923 126319736773784101545172385)
  ·
    refine ⟨94739802580338076158879289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126319736773784101545172385 94739802580338076158879289)
    ·
      refine ⟨71054851935253557119159467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94739802580338076158879289 71054851935253557119159467)
      ·
        refine ⟨106582277902880335678739201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71054851935253557119159467 106582277902880335678739201)
        ·
          refine ⟨79936708427160251759054401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106582277902880335678739201 79936708427160251759054401)
          ·
            refine ⟨59952531320370188819290801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79936708427160251759054401 59952531320370188819290801)
            ·
              refine ⟨44964398490277641614468101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59952531320370188819290801 44964398490277641614468101)
              ·
                refine ⟨8430824716927057802712769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44964398490277641614468101 8430824716927057802712769)
                ·
                  refine ⟨6323118537695293352034577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8430824716927057802712769 6323118537695293352034577)
                  ·
                    refine ⟨4742338903271470014025933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6323118537695293352034577 4742338903271470014025933)
                    ·
                      refine ⟨1778377088726801255259725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4742338903271470014025933 1778377088726801255259725)
                      ·
                        rfl

theorem cell23_3463377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 2, 3].length) (baseStart_3463377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463377 prefixEnd_3463377 := by exact prefixLift 3463377
  have htrace : WordTrace (prefixWord ++ tailWord_3463377) baseStart_3463377 baseEnd_3463377 := by
    simpa [prefixWord, tailWord_3463377, baseEnd_3463377] using wordTrace_append hprefix tailTrace_3463377
  have hstable : (prefixWord ++ tailWord_3463377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463377).length < 2 ^ (prefixWord ++ tailWord_3463377).sum := by decide
  have hdescent : baseEnd_3463377 < baseStart_3463377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463384 : List Nat := [2, 1, 2, 2, 4, 2, 2, 1, 3, 4]
def baseStart_3463384 : Nat := 118140960795 + 3463384 * 2 ^ 59
def prefixEnd_3463384 : Nat := 4983230072969 + 3 ^ 40 * 3463384 * 2
def baseEnd_3463384 : Nat := 592793561030460909290731

theorem tailTrace_3463384 : CollatzResearch.WordTrace tailWord_3463384 prefixEnd_3463384 592793561030460909290731 := by
  unfold tailWord_3463384
  simp only [CollatzResearch.WordTrace]
  refine ⟨63159996042379370870338603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84213328056505827827118137 63159996042379370870338603)
  ·
    refine ⟨94739994063569056305507905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63159996042379370870338603 94739994063569056305507905)
    ·
      refine ⟨71054995547676792229130929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94739994063569056305507905 71054995547676792229130929)
      ·
        refine ⟨53291246660757594171848197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71054995547676792229130929 53291246660757594171848197)
        ·
          refine ⟨9992108748892048907221537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53291246660757594171848197 9992108748892048907221537)
          ·
            refine ⟨7494081561669036680416153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9992108748892048907221537 7494081561669036680416153)
            ·
              refine ⟨5620561171251777510312115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7494081561669036680416153 5620561171251777510312115)
              ·
                refine ⟨8430841756877666265468173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5620561171251777510312115 8430841756877666265468173)
                ·
                  refine ⟨3161565658829124849550565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8430841756877666265468173 3161565658829124849550565)
                  ·
                    refine ⟨592793561030460909290731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3161565658829124849550565 592793561030460909290731)
                    ·
                      rfl

theorem cell23_3463384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 3, 4].length) (baseStart_3463384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463384 prefixEnd_3463384 := by exact prefixLift 3463384
  have htrace : WordTrace (prefixWord ++ tailWord_3463384) baseStart_3463384 baseEnd_3463384 := by
    simpa [prefixWord, tailWord_3463384, baseEnd_3463384] using wordTrace_append hprefix tailTrace_3463384
  have hstable : (prefixWord ++ tailWord_3463384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463384).length < 2 ^ (prefixWord ++ tailWord_3463384).sum := by decide
  have hdescent : baseEnd_3463384 < baseStart_3463384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463427 : List Nat := [1, 1, 1, 3, 2, 3, 1, 5, 1, 5]
def baseStart_3463427 : Nat := 118140960795 + 3463427 * 2 ^ 59
def prefixEnd_3463427 : Nat := 4983230072969 + 3 ^ 40 * 3463427 * 2
def baseEnd_3463427 : Nat := 592800920919842019878165

theorem tailTrace_3463427 : CollatzResearch.WordTrace tailWord_3463427 prefixEnd_3463427 592800920919842019878165 := by
  unfold tailWord_3463427
  simp only [CollatzResearch.WordTrace]
  refine ⟨126321560423602960084492535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84214373615735306722995023 126321560423602960084492535)
  ·
    refine ⟨189482340635404440126738803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126321560423602960084492535 189482340635404440126738803)
    ·
      refine ⟨284223510953106660190108205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189482340635404440126738803 284223510953106660190108205)
      ·
        refine ⟨106583816607414997571290577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284223510953106660190108205 106583816607414997571290577)
        ·
          refine ⟨79937862455561248178467933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106583816607414997571290577 79937862455561248178467933)
          ·
            refine ⟨29976698420835468066925475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79937862455561248178467933 29976698420835468066925475)
            ·
              refine ⟨44965047631253202100388213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29976698420835468066925475 44965047631253202100388213)
              ·
                refine ⟨4215473215429987696911395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44965047631253202100388213 4215473215429987696911395)
                ·
                  refine ⟨6323209823144981545367093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4215473215429987696911395 6323209823144981545367093)
                  ·
                    refine ⟨592800920919842019878165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6323209823144981545367093 592800920919842019878165)
                    ·
                      rfl

theorem cell23_3463427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 5].length) (baseStart_3463427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463427 prefixEnd_3463427 := by exact prefixLift 3463427
  have htrace : WordTrace (prefixWord ++ tailWord_3463427) baseStart_3463427 baseEnd_3463427 := by
    simpa [prefixWord, tailWord_3463427, baseEnd_3463427] using wordTrace_append hprefix tailTrace_3463427
  have hstable : (prefixWord ++ tailWord_3463427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463427).length < 2 ^ (prefixWord ++ tailWord_3463427).sum := by decide
  have hdescent : baseEnd_3463427 < baseStart_3463427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463434 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2]
def baseStart_3463434 : Nat := 118140960795 + 3463434 * 2 ^ 59
def prefixEnd_3463434 : Nat := 4983230072969 + 3 ^ 40 * 3463434 * 2
def baseEnd_3463434 : Nat := 1778406357124107532246963

theorem tailTrace_3463434 : CollatzResearch.WordTrace tailWord_3463434 prefixEnd_3463434 1778406357124107532246963 := by
  unfold tailWord_3463434
  simp only [CollatzResearch.WordTrace]
  refine ⟨31580453933644400069999339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84214543823051733519998237 31580453933644400069999339)
  ·
    refine ⟨47370680900466600104999009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31580453933644400069999339 47370680900466600104999009)
    ·
      refine ⟨35528010675349950078749257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47370680900466600104999009 35528010675349950078749257)
      ·
        refine ⟨26646008006512462559061943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35528010675349950078749257 26646008006512462559061943)
        ·
          refine ⟨39969012009768693838592915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26646008006512462559061943 39969012009768693838592915)
          ·
            refine ⟨59953518014653040757889373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39969012009768693838592915 59953518014653040757889373)
            ·
              refine ⟨22482569255494890284208515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59953518014653040757889373 22482569255494890284208515)
              ·
                refine ⟨33723853883242335426312773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22482569255494890284208515 33723853883242335426312773)
                ·
                  refine ⟨6323222603107937892433645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33723853883242335426312773 6323222603107937892433645)
                  ·
                    refine ⟨2371208476165476709662617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6323222603107937892433645 2371208476165476709662617)
                    ·
                      refine ⟨1778406357124107532246963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2371208476165476709662617 1778406357124107532246963)
                      ·
                        rfl

theorem cell23_3463434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_3463434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463434 prefixEnd_3463434 := by exact prefixLift 3463434
  have htrace : WordTrace (prefixWord ++ tailWord_3463434) baseStart_3463434 baseEnd_3463434 := by
    simpa [prefixWord, tailWord_3463434, baseEnd_3463434] using wordTrace_append hprefix tailTrace_3463434
  have hstable : (prefixWord ++ tailWord_3463434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463434).length < 2 ^ (prefixWord ++ tailWord_3463434).sum := by decide
  have hdescent : baseEnd_3463434 < baseStart_3463434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463441 : List Nat := [1, 2, 2, 1, 1, 7, 1, 1, 3, 1, 3]
def baseStart_3463441 : Nat := 118140960795 + 3463441 * 2 ^ 59
def prefixEnd_3463441 : Nat := 4983230072969 + 3 ^ 40 * 3463441 * 2
def baseEnd_3463441 : Nat := 1778409951488689004859431

theorem tailTrace_3463441 : CollatzResearch.WordTrace tailWord_3463441 prefixEnd_3463441 1778409951488689004859431 := by
  unfold tailWord_3463441
  simp only [CollatzResearch.WordTrace]
  refine ⟨126322071045552240475502177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84214714030368160317001451 126322071045552240475502177)
  ·
    refine ⟨94741553284164180356626633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126322071045552240475502177 94741553284164180356626633)
    ·
      refine ⟨71056164963123135267469975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94741553284164180356626633 71056164963123135267469975)
      ·
        refine ⟨106584247444684702901204963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71056164963123135267469975 106584247444684702901204963)
        ·
          refine ⟨159876371167027054351807445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106584247444684702901204963 159876371167027054351807445)
          ·
            refine ⟨3747102449227196586370487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 159876371167027054351807445 3747102449227196586370487)
            ·
              refine ⟨5620653673840794879555731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3747102449227196586370487 5620653673840794879555731)
              ·
                refine ⟨8430980510761192319333597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5620653673840794879555731 8430980510761192319333597)
                ·
                  refine ⟨3161617691535447119750099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8430980510761192319333597 3161617691535447119750099)
                  ·
                    refine ⟨4742426537303170679625149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3161617691535447119750099 4742426537303170679625149)
                    ·
                      refine ⟨1778409951488689004859431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4742426537303170679625149 1778409951488689004859431)
                      ·
                        rfl

theorem cell23_3463441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3, 1, 3].length) (baseStart_3463441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463441 prefixEnd_3463441 := by exact prefixLift 3463441
  have htrace : WordTrace (prefixWord ++ tailWord_3463441) baseStart_3463441 baseEnd_3463441 := by
    simpa [prefixWord, tailWord_3463441, baseEnd_3463441] using wordTrace_append hprefix tailTrace_3463441
  have hstable : (prefixWord ++ tailWord_3463441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463441).length < 2 ^ (prefixWord ++ tailWord_3463441).sum := by decide
  have hdescent : baseEnd_3463441 < baseStart_3463441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463461 : List Nat := [1, 3, 1, 2, 5, 2, 1, 2, 1, 5]
def baseStart_3463461 : Nat := 118140960795 + 3463461 * 2 ^ 59
def prefixEnd_3463461 : Nat := 4983230072969 + 3 ^ 40 * 3463461 * 2
def baseEnd_3463461 : Nat := 592806740367259642203113

theorem tailTrace_3463461 : CollatzResearch.WordTrace tailWord_3463461 prefixEnd_3463461 592806740367259642203113 := by
  unfold tailWord_3463461
  simp only [CollatzResearch.WordTrace]
  refine ⟨126322800505479783891230237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84215200336986522594153491 126322800505479783891230237)
  ·
    refine ⟨47371050189554918959211339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126322800505479783891230237 47371050189554918959211339)
    ·
      refine ⟨71056575284332378438817009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47371050189554918959211339 71056575284332378438817009)
      ·
        refine ⟨53292431463249283829112757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71056575284332378438817009 53292431463249283829112757)
        ·
          refine ⟨4996165449679620358979321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53292431463249283829112757 4996165449679620358979321)
          ·
            refine ⟨3747124087259715269234491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4996165449679620358979321 3747124087259715269234491)
            ·
              refine ⟨5620686130889572903851737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3747124087259715269234491 5620686130889572903851737)
              ·
                refine ⟨4215514598167179677888803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5620686130889572903851737 4215514598167179677888803)
                ·
                  refine ⟨6323271897250769516833205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4215514598167179677888803 6323271897250769516833205)
                  ·
                    refine ⟨592806740367259642203113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6323271897250769516833205 592806740367259642203113)
                    ·
                      rfl

theorem cell23_3463461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 5].length) (baseStart_3463461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463461 prefixEnd_3463461 := by exact prefixLift 3463461
  have htrace : WordTrace (prefixWord ++ tailWord_3463461) baseStart_3463461 baseEnd_3463461 := by
    simpa [prefixWord, tailWord_3463461, baseEnd_3463461] using wordTrace_append hprefix tailTrace_3463461
  have hstable : (prefixWord ++ tailWord_3463461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463461).length < 2 ^ (prefixWord ++ tailWord_3463461).sum := by decide
  have hdescent : baseEnd_3463461 < baseStart_3463461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463474 : List Nat := [3, 2, 1, 1, 5, 1, 1, 2, 1, 6]
def baseStart_3463474 : Nat := 118140960795 + 3463474 * 2 ^ 59
def prefixEnd_3463474 : Nat := 4983230072969 + 3 ^ 40 * 3463474 * 2
def baseEnd_3463474 : Nat := 592808965450095791915593

theorem tailTrace_3463474 : CollatzResearch.WordTrace tailWord_3463474 prefixEnd_3463474 592808965450095791915593 := by
  unfold tailWord_3463474
  simp only [CollatzResearch.WordTrace]
  refine ⟨31580818663608171777863369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84215516436288458074302317 31580818663608171777863369)
  ·
    refine ⟨23685613997706128833397527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31580818663608171777863369 23685613997706128833397527)
    ·
      refine ⟨35528420996559193250096291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23685613997706128833397527 35528420996559193250096291)
      ·
        refine ⟨53292631494838789875144437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35528420996559193250096291 53292631494838789875144437)
        ·
          refine ⟨4996184202641136550794791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53292631494838789875144437 4996184202641136550794791)
          ·
            refine ⟨7494276303961704826192187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4996184202641136550794791 7494276303961704826192187)
            ·
              refine ⟨11241414455942557239288281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7494276303961704826192187 11241414455942557239288281)
              ·
                refine ⟨8431060841956917929466211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11241414455942557239288281 8431060841956917929466211)
                ·
                  refine ⟨12646591262935376894199317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8431060841956917929466211 12646591262935376894199317)
                  ·
                    refine ⟨592808965450095791915593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12646591262935376894199317 592808965450095791915593)
                    ·
                      rfl

theorem cell23_3463474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_3463474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463474 prefixEnd_3463474 := by exact prefixLift 3463474
  have htrace : WordTrace (prefixWord ++ tailWord_3463474) baseStart_3463474 baseEnd_3463474 := by
    simpa [prefixWord, tailWord_3463474, baseEnd_3463474] using wordTrace_append hprefix tailTrace_3463474
  have hstable : (prefixWord ++ tailWord_3463474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463474).length < 2 ^ (prefixWord ++ tailWord_3463474).sum := by decide
  have hdescent : baseEnd_3463474 < baseStart_3463474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463497 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 5, 3, 3]
def baseStart_3463497 : Nat := 118140960795 + 3463497 * 2 ^ 59
def prefixEnd_3463497 : Nat := 4983230072969 + 3 ^ 40 * 3463497 * 2
def baseEnd_3463497 : Nat := 1778438706405340785759173

theorem tailTrace_3463497 : CollatzResearch.WordTrace tailWord_3463497 prefixEnd_3463497 1778438706405340785759173 := by
  unfold tailWord_3463497
  simp only [CollatzResearch.WordTrace]
  refine ⟨126324113533349362039540745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84216075688899574693027163 126324113533349362039540745)
  ·
    refine ⟨94743085150012021529655559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126324113533349362039540745 94743085150012021529655559)
    ·
      refine ⟨142114627725018032294483339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94743085150012021529655559 142114627725018032294483339)
      ·
        refine ⟨213171941587527048441725009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142114627725018032294483339 213171941587527048441725009)
        ·
          refine ⟨159878956190645286331293757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213171941587527048441725009 159878956190645286331293757)
          ·
            refine ⟨59954608571491982374235159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159878956190645286331293757 59954608571491982374235159)
            ·
              refine ⟨89931912857237973561352739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59954608571491982374235159 89931912857237973561352739)
              ·
                refine ⟨134897869285856960342029109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89931912857237973561352739 134897869285856960342029109)
                ·
                  refine ⟨12646675245549090032065229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134897869285856960342029109 12646675245549090032065229)
                  ·
                    refine ⟨4742503217080908762024461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12646675245549090032065229 4742503217080908762024461)
                    ·
                      refine ⟨1778438706405340785759173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4742503217080908762024461 1778438706405340785759173)
                      ·
                        rfl

theorem cell23_3463497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 3, 3].length) (baseStart_3463497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463497 prefixEnd_3463497 := by exact prefixLift 3463497
  have htrace : WordTrace (prefixWord ++ tailWord_3463497) baseStart_3463497 baseEnd_3463497 := by
    simpa [prefixWord, tailWord_3463497, baseEnd_3463497] using wordTrace_append hprefix tailTrace_3463497
  have hstable : (prefixWord ++ tailWord_3463497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463497).length < 2 ^ (prefixWord ++ tailWord_3463497).sum := by decide
  have hdescent : baseEnd_3463497 < baseStart_3463497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463514 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3]
def baseStart_3463514 : Nat := 118140960795 + 3463514 * 2 ^ 59
def prefixEnd_3463514 : Nat := 4983230072969 + 3 ^ 40 * 3463514 * 2
def baseEnd_3463514 : Nat := 1778447435576467219246595

theorem tailTrace_3463514 : CollatzResearch.WordTrace tailWord_3463514 prefixEnd_3463514 1778447435576467219246595 := by
  unfold tailWord_3463514
  simp only [CollatzResearch.WordTrace]
  refine ⟨31581183393571943485727399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84216489049525182628606397 31581183393571943485727399)
  ·
    refine ⟨47371775090357915228591099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31581183393571943485727399 47371775090357915228591099)
    ·
      refine ⟨71057662635536872842886649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47371775090357915228591099 71057662635536872842886649)
      ·
        refine ⟨53293246976652654632164987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71057662635536872842886649 53293246976652654632164987)
        ·
          refine ⟨79939870464978981948247481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53293246976652654632164987 79939870464978981948247481)
          ·
            refine ⟨59954902848734236461185611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79939870464978981948247481 59954902848734236461185611)
            ·
              refine ⟨89932354273101354691778417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59954902848734236461185611 89932354273101354691778417)
              ·
                refine ⟨67449265704826016018833813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89932354273101354691778417 67449265704826016018833813)
                ·
                  refine ⟨3161684329913719500882835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67449265704826016018833813 3161684329913719500882835)
                  ·
                    refine ⟨4742526494870579251324253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3161684329913719500882835 4742526494870579251324253)
                    ·
                      refine ⟨1778447435576467219246595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4742526494870579251324253 1778447435576467219246595)
                      ·
                        rfl

theorem cell23_3463514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_3463514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463514 prefixEnd_3463514 := by exact prefixLift 3463514
  have htrace : WordTrace (prefixWord ++ tailWord_3463514) baseStart_3463514 baseEnd_3463514 := by
    simpa [prefixWord, tailWord_3463514, baseEnd_3463514] using wordTrace_append hprefix tailTrace_3463514
  have hstable : (prefixWord ++ tailWord_3463514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463514).length < 2 ^ (prefixWord ++ tailWord_3463514).sum := by decide
  have hdescent : baseEnd_3463514 < baseStart_3463514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463542 : List Nat := [5, 1, 1, 4, 2, 1, 1, 2, 2, 4]
def baseStart_3463542 : Nat := 118140960795 + 3463542 * 2 ^ 59
def prefixEnd_3463542 : Nat := 4983230072969 + 3 ^ 40 * 3463542 * 2
def baseEnd_3463542 : Nat := 592820604344931036565489

theorem tailTrace_3463542 : CollatzResearch.WordTrace tailWord_3463542 prefixEnd_3463542 592820604344931036565489 := by
  unfold tailWord_3463542
  simp only [CollatzResearch.WordTrace]
  refine ⟨7895359676136645920308055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84217169878790889816619253 7895359676136645920308055)
  ·
    refine ⟨11843039514204968880462083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7895359676136645920308055 11843039514204968880462083)
    ·
      refine ⟨17764559271307453320693125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11843039514204968880462083 17764559271307453320693125)
      ·
        refine ⟨3330854863370147497629961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17764559271307453320693125 3330854863370147497629961)
        ·
          refine ⟨2498141147527610623222471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3330854863370147497629961 2498141147527610623222471)
          ·
            refine ⟨3747211721291415934833707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2498141147527610623222471 3747211721291415934833707)
            ·
              refine ⟨5620817581937123902250561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3747211721291415934833707 5620817581937123902250561)
              ·
                refine ⟨4215613186452842926687921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5620817581937123902250561 4215613186452842926687921)
                ·
                  refine ⟨3161709889839632195015941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4215613186452842926687921 3161709889839632195015941)
                  ·
                    refine ⟨592820604344931036565489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3161709889839632195015941 592820604344931036565489)
                    ·
                      rfl

theorem cell23_3463542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_3463542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463542 prefixEnd_3463542 := by exact prefixLift 3463542
  have htrace : WordTrace (prefixWord ++ tailWord_3463542) baseStart_3463542 baseEnd_3463542 := by
    simpa [prefixWord, tailWord_3463542, baseEnd_3463542] using wordTrace_append hprefix tailTrace_3463542
  have hstable : (prefixWord ++ tailWord_3463542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463542).length < 2 ^ (prefixWord ++ tailWord_3463542).sum := by decide
  have hdescent : baseEnd_3463542 < baseStart_3463542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463547 : List Nat := [1, 1, 1, 1, 1, 7, 1, 2, 2, 6]
def baseStart_3463547 : Nat := 118140960795 + 3463547 * 2 ^ 59
def prefixEnd_3463547 : Nat := 4983230072969 + 3 ^ 40 * 3463547 * 2
def baseEnd_3463547 : Nat := 592821460146021863377981

theorem tailTrace_3463547 : CollatzResearch.WordTrace tailWord_3463547 prefixEnd_3463547 592821460146021863377981 := by
  unfold tailWord_3463547
  simp only [CollatzResearch.WordTrace]
  refine ⟨126325937183168220578860895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84217291455445480385907263 126325937183168220578860895)
  ·
    refine ⟨189488905774752330868291343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126325937183168220578860895 189488905774752330868291343)
    ·
      refine ⟨284233358662128496302437015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189488905774752330868291343 284233358662128496302437015)
      ·
        refine ⟨426350037993192744453655523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284233358662128496302437015 426350037993192744453655523)
        ·
          refine ⟨639525056989789116680483285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426350037993192744453655523 639525056989789116680483285)
          ·
            refine ⟨14988868523198182422198827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 639525056989789116680483285 14988868523198182422198827)
            ·
              refine ⟨22483302784797273633298241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14988868523198182422198827 22483302784797273633298241)
              ·
                refine ⟨16862477088597955224973681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22483302784797273633298241 16862477088597955224973681)
                ·
                  refine ⟨12646857816448466418730261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16862477088597955224973681 12646857816448466418730261)
                  ·
                    refine ⟨592821460146021863377981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12646857816448466418730261 592821460146021863377981)
                    ·
                      rfl

theorem cell23_3463547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 6].length) (baseStart_3463547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463547 prefixEnd_3463547 := by exact prefixLift 3463547
  have htrace : WordTrace (prefixWord ++ tailWord_3463547) baseStart_3463547 baseEnd_3463547 := by
    simpa [prefixWord, tailWord_3463547, baseEnd_3463547] using wordTrace_append hprefix tailTrace_3463547
  have hstable : (prefixWord ++ tailWord_3463547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463547).length < 2 ^ (prefixWord ++ tailWord_3463547).sum := by decide
  have hdescent : baseEnd_3463547 < baseStart_3463547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463557 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 4, 1, 5]
def baseStart_3463557 : Nat := 118140960795 + 3463557 * 2 ^ 59
def prefixEnd_3463557 : Nat := 4983230072969 + 3 ^ 40 * 3463557 * 2
def baseEnd_3463557 : Nat := 1778469515244610551008897

theorem tailTrace_3463557 : CollatzResearch.WordTrace tailWord_3463557 prefixEnd_3463557 1778469515244610551008897 := by
  unfold tailWord_3463557
  simp only [CollatzResearch.WordTrace]
  refine ⟨126326301913131992286724925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84217534608754661524483283 126326301913131992286724925)
  ·
    refine ⟨47372363217424497107521847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126326301913131992286724925 47372363217424497107521847)
    ·
      refine ⟨71058544826136745661282771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47372363217424497107521847 71058544826136745661282771)
      ·
        refine ⟨106587817239205118491924157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71058544826136745661282771 106587817239205118491924157)
        ·
          refine ⟨39970431464701919434471559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106587817239205118491924157 39970431464701919434471559)
          ·
            refine ⟨59955647197052879151707339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39970431464701919434471559 59955647197052879151707339)
            ·
              refine ⟨89933470795579318727561009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59955647197052879151707339 89933470795579318727561009)
              ·
                refine ⟨67450103096684489045670757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89933470795579318727561009 67450103096684489045670757)
                ·
                  refine ⟨12646894330628341696063267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67450103096684489045670757 12646894330628341696063267)
                  ·
                    refine ⟨18970341495942512544094901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12646894330628341696063267 18970341495942512544094901)
                    ·
                      refine ⟨1778469515244610551008897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18970341495942512544094901 1778469515244610551008897)
                      ·
                        rfl

theorem cell23_3463557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_3463557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463557 prefixEnd_3463557 := by exact prefixLift 3463557
  have htrace : WordTrace (prefixWord ++ tailWord_3463557) baseStart_3463557 baseEnd_3463557 := by
    simpa [prefixWord, tailWord_3463557, baseEnd_3463557] using wordTrace_append hprefix tailTrace_3463557
  have hstable : (prefixWord ++ tailWord_3463557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463557).length < 2 ^ (prefixWord ++ tailWord_3463557).sum := by decide
  have hdescent : baseEnd_3463557 < baseStart_3463557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463577 : List Nat := [1, 2, 1, 2, 1, 4, 1, 4, 7]
def baseStart_3463577 : Nat := 118140960795 + 3463577 * 2 ^ 59
def prefixEnd_3463577 : Nat := 4983230072969 + 3 ^ 40 * 3463577 * 2
def baseEnd_3463577 : Nat := 197608864984188941417645

theorem tailTrace_3463577 : CollatzResearch.WordTrace tailWord_3463577 prefixEnd_3463577 197608864984188941417645 := by
  unfold tailWord_3463577
  simp only [CollatzResearch.WordTrace]
  refine ⟨126327031373059535702452985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84218020915373023801635323 126327031373059535702452985)
  ·
    refine ⟨94745273529794651776839739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126327031373059535702452985 94745273529794651776839739)
    ·
      refine ⟨142117910294691977665259609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94745273529794651776839739 142117910294691977665259609)
      ·
        refine ⟨106588432721018983248944707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142117910294691977665259609 106588432721018983248944707)
        ·
          refine ⟨159882649081528474873417061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106588432721018983248944707 159882649081528474873417061)
          ·
            refine ⟨29977996702786589038765699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159882649081528474873417061 29977996702786589038765699)
            ·
              refine ⟨44966995054179883558148549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29977996702786589038765699 44966995054179883558148549)
              ·
                refine ⟨8431311572658728167152853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44966995054179883558148549 8431311572658728167152853)
                ·
                  refine ⟨197608864984188941417645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8431311572658728167152853 197608864984188941417645)
                  ·
                    rfl

theorem cell23_3463577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 7].length) (baseStart_3463577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463577 prefixEnd_3463577 := by exact prefixLift 3463577
  have htrace : WordTrace (prefixWord ++ tailWord_3463577) baseStart_3463577 baseEnd_3463577 := by
    simpa [prefixWord, tailWord_3463577, baseEnd_3463577] using wordTrace_append hprefix tailTrace_3463577
  have hstable : (prefixWord ++ tailWord_3463577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463577).length < 2 ^ (prefixWord ++ tailWord_3463577).sum := by decide
  have hdescent : baseEnd_3463577 < baseStart_3463577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463711 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 7, 1, 3]
def baseStart_3463711 : Nat := 118140960795 + 3463711 * 2 ^ 59
def prefixEnd_3463711 : Nat := 4983230072969 + 3 ^ 40 * 3463711 * 2
def baseEnd_3463711 : Nat := 1778548591265402948483189

theorem tailTrace_3463711 : CollatzResearch.WordTrace tailWord_3463711 prefixEnd_3463711 1778548591265402948483189 := by
  unfold tailWord_3463711
  simp only [CollatzResearch.WordTrace]
  refine ⟨126331918754574076587830987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84221279169716051058553991 126331918754574076587830987)
  ·
    refine ⟨189497878131861114881746481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126331918754574076587830987 189497878131861114881746481)
    ·
      refine ⟨142123408598895836161309861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189497878131861114881746481 142123408598895836161309861)
      ·
        refine ⟨26648139112292969280245599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142123408598895836161309861 26648139112292969280245599)
        ·
          refine ⟨39972208668439453920368399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26648139112292969280245599 39972208668439453920368399)
          ·
            refine ⟨59958313002659180880552599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39972208668439453920368399 59958313002659180880552599)
            ·
              refine ⟨89937469503988771320828899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59958313002659180880552599 89937469503988771320828899)
              ·
                refine ⟨134906204255983156981243349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89937469503988771320828899 134906204255983156981243349)
                ·
                  refine ⟨3161864162249605241747891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 134906204255983156981243349 3161864162249605241747891)
                  ·
                    refine ⟨4742796243374407862621837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3161864162249605241747891 4742796243374407862621837)
                    ·
                      refine ⟨1778548591265402948483189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4742796243374407862621837 1778548591265402948483189)
                      ·
                        rfl

theorem cell23_3463711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_3463711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463711 prefixEnd_3463711 := by exact prefixLift 3463711
  have htrace : WordTrace (prefixWord ++ tailWord_3463711) baseStart_3463711 baseEnd_3463711 := by
    simpa [prefixWord, tailWord_3463711, baseEnd_3463711] using wordTrace_append hprefix tailTrace_3463711
  have hstable : (prefixWord ++ tailWord_3463711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463711).length < 2 ^ (prefixWord ++ tailWord_3463711).sum := by decide
  have hdescent : baseEnd_3463711 < baseStart_3463711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463761 : List Nat := [1, 2, 2, 1, 3, 3, 1, 2, 4, 4]
def baseStart_3463761 : Nat := 118140960795 + 3463761 * 2 ^ 59
def prefixEnd_3463761 : Nat := 4983230072969 + 3 ^ 40 * 3463761 * 2
def baseEnd_3463761 : Nat := 592858088432709250952653

theorem tailTrace_3463761 : CollatzResearch.WordTrace tailWord_3463761 prefixEnd_3463761 592858088432709250952653 := by
  unfold tailWord_3463761
  simp only [CollatzResearch.WordTrace]
  refine ⟨126333742404392935127151137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84222494936261956751434091 126333742404392935127151137)
  ·
    refine ⟨94750306803294701345363353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126333742404392935127151137 94750306803294701345363353)
    ·
      refine ⟨71062730102471026009022515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94750306803294701345363353 71062730102471026009022515)
      ·
        refine ⟨106594095153706539013533773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71062730102471026009022515 106594095153706539013533773)
        ·
          refine ⟨39972785682639952130075165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106594095153706539013533773 39972785682639952130075165)
          ·
            refine ⟨14989794630989982048778187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39972785682639952130075165 14989794630989982048778187)
            ·
              refine ⟨22484691946484973073167281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14989794630989982048778187 22484691946484973073167281)
              ·
                refine ⟨16863518959863729804875461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22484691946484973073167281 16863518959863729804875461)
                ·
                  refine ⟨3161909804974449338414149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16863518959863729804875461 3161909804974449338414149)
                  ·
                    refine ⟨592858088432709250952653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3161909804974449338414149 592858088432709250952653)
                    ·
                      rfl

theorem cell23_3463761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4, 4].length) (baseStart_3463761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463761 prefixEnd_3463761 := by exact prefixLift 3463761
  have htrace : WordTrace (prefixWord ++ tailWord_3463761) baseStart_3463761 baseEnd_3463761 := by
    simpa [prefixWord, tailWord_3463761, baseEnd_3463761] using wordTrace_append hprefix tailTrace_3463761
  have hstable : (prefixWord ++ tailWord_3463761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463761).length < 2 ^ (prefixWord ++ tailWord_3463761).sum := by decide
  have hdescent : baseEnd_3463761 < baseStart_3463761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463768 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 5, 2, 2]
def baseStart_3463768 : Nat := 118140960795 + 3463768 * 2 ^ 59
def prefixEnd_3463768 : Nat := 4983230072969 + 3 ^ 40 * 3463768 * 2
def baseEnd_3463768 : Nat := 1778577859662709225470427

theorem tailTrace_3463768 : CollatzResearch.WordTrace tailWord_3463768 prefixEnd_3463768 1778577859662709225470427 := by
  unfold tailWord_3463768
  simp only [CollatzResearch.WordTrace]
  refine ⟨63166998857683787661327979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84222665143578383548437305 63166998857683787661327979)
  ·
    refine ⟨94750498286525681491991969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63166998857683787661327979 94750498286525681491991969)
    ·
      refine ⟨71062873714894261118993977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94750498286525681491991969 71062873714894261118993977)
      ·
        refine ⟨53297155286170695839245483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71062873714894261118993977 53297155286170695839245483)
        ·
          refine ⟨79945732929256043758868225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53297155286170695839245483 79945732929256043758868225)
          ·
            refine ⟨59959299696942032819151169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79945732929256043758868225 59959299696942032819151169)
            ·
              refine ⟨44969474772706524614363377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59959299696942032819151169 44969474772706524614363377)
              ·
                refine ⟨33727106079529893460772533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44969474772706524614363377 33727106079529893460772533)
                ·
                  refine ⟨3161916194955927511947425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33727106079529893460772533 3161916194955927511947425)
                  ·
                    refine ⟨2371437146216945633960569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3161916194955927511947425 2371437146216945633960569)
                    ·
                      refine ⟨1778577859662709225470427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2371437146216945633960569 1778577859662709225470427)
                      ·
                        rfl

theorem cell23_3463768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 5, 2, 2].length) (baseStart_3463768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463768 prefixEnd_3463768 := by exact prefixLift 3463768
  have htrace : WordTrace (prefixWord ++ tailWord_3463768) baseStart_3463768 baseEnd_3463768 := by
    simpa [prefixWord, tailWord_3463768, baseEnd_3463768] using wordTrace_append hprefix tailTrace_3463768
  have hstable : (prefixWord ++ tailWord_3463768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463768).length < 2 ^ (prefixWord ++ tailWord_3463768).sum := by decide
  have hdescent : baseEnd_3463768 < baseStart_3463768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463836 : List Nat := [2, 2, 3, 2, 2, 3, 2, 2, 1, 2, 2]
def baseStart_3463836 : Nat := 118140960795 + 3463836 * 2 ^ 59
def prefixEnd_3463836 : Nat := 4983230072969 + 3 ^ 40 * 3463836 * 2
def baseEnd_3463836 : Nat := 1778612776347214959420115

theorem tailTrace_3463836 : CollatzResearch.WordTrace tailWord_3463836 prefixEnd_3463836 1778612776347214959420115 := by
  unfold tailWord_3463836
  simp only [CollatzResearch.WordTrace]
  refine ⟨63168238939560611468065681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84224318586080815290754241 63168238939560611468065681)
  ·
    refine ⟨47376179204670458601049261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63168238939560611468065681 47376179204670458601049261)
    ·
      refine ⟨17766067201751421975393473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47376179204670458601049261 17766067201751421975393473)
      ·
        refine ⟨13324550401313566481545105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17766067201751421975393473 13324550401313566481545105)
        ·
          refine ⟨9993412800985174861158829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13324550401313566481545105 9993412800985174861158829)
          ·
            refine ⟨3747529800369440572934561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9993412800985174861158829 3747529800369440572934561)
            ·
              refine ⟨2810647350277080429700921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3747529800369440572934561 2810647350277080429700921)
              ·
                refine ⟨2107985512707810322275691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2810647350277080429700921 2107985512707810322275691)
                ·
                  refine ⟨3161978269061715483413537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2107985512707810322275691 3161978269061715483413537)
                  ·
                    refine ⟨2371483701796286612560153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3161978269061715483413537 2371483701796286612560153)
                    ·
                      refine ⟨1778612776347214959420115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2371483701796286612560153 1778612776347214959420115)
                      ·
                        rfl

theorem cell23_3463836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_3463836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463836 prefixEnd_3463836 := by exact prefixLift 3463836
  have htrace : WordTrace (prefixWord ++ tailWord_3463836) baseStart_3463836 baseEnd_3463836 := by
    simpa [prefixWord, tailWord_3463836, baseEnd_3463836] using wordTrace_append hprefix tailTrace_3463836
  have hstable : (prefixWord ++ tailWord_3463836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463836).length < 2 ^ (prefixWord ++ tailWord_3463836).sum := by decide
  have hdescent : baseEnd_3463836 < baseStart_3463836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463898 : List Nat := [3, 1, 1, 2, 2, 2, 1, 6, 5]
def baseStart_3463898 : Nat := 118140960795 + 3463898 * 2 ^ 59
def prefixEnd_3463898 : Nat := 4983230072969 + 3 ^ 40 * 3463898 * 2
def baseEnd_3463898 : Nat := 197627179127532635204981

theorem tailTrace_3463898 : CollatzResearch.WordTrace tailWord_3463898 prefixEnd_3463898 197627179127532635204981 := by
  unfold tailWord_3463898
  simp only [CollatzResearch.WordTrace]
  refine ⟨31584684801224151881222087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84225826136597738349925565 31584684801224151881222087)
  ·
    refine ⟨47377027201836227821833131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31584684801224151881222087 47377027201836227821833131)
    ·
      refine ⟨71065540802754341732749697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47377027201836227821833131 71065540802754341732749697)
      ·
        refine ⟨53299155602065756299562273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71065540802754341732749697 53299155602065756299562273)
        ·
          refine ⟨39974366701549317224671705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53299155602065756299562273 39974366701549317224671705)
          ·
            refine ⟨29980775026161987918503779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39974366701549317224671705 29980775026161987918503779)
            ·
              refine ⟨44971162539242981877755669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29980775026161987918503779 44971162539242981877755669)
              ·
                refine ⟨2108023244027014775519797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44971162539242981877755669 2108023244027014775519797)
                ·
                  refine ⟨197627179127532635204981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2108023244027014775519797 197627179127532635204981)
                  ·
                    rfl

theorem cell23_3463898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6, 5].length) (baseStart_3463898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463898 prefixEnd_3463898 := by exact prefixLift 3463898
  have htrace : WordTrace (prefixWord ++ tailWord_3463898) baseStart_3463898 baseEnd_3463898 := by
    simpa [prefixWord, tailWord_3463898, baseEnd_3463898] using wordTrace_append hprefix tailTrace_3463898
  have hstable : (prefixWord ++ tailWord_3463898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463898).length < 2 ^ (prefixWord ++ tailWord_3463898).sum := by decide
  have hdescent : baseEnd_3463898 < baseStart_3463898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463908 : List Nat := [2, 3, 1, 1, 1, 4, 2, 1, 2, 3, 3]
def baseStart_3463908 : Nat := 118140960795 + 3463908 * 2 ^ 59
def prefixEnd_3463908 : Nat := 4983230072969 + 3 ^ 40 * 3463908 * 2
def baseEnd_3463908 : Nat := 1778649746954338677719783

theorem tailTrace_3463908 : CollatzResearch.WordTrace tailWord_3463908 prefixEnd_3463908 1778649746954338677719783 := by
  unfold tailWord_3463908
  simp only [CollatzResearch.WordTrace]
  refine ⟨63169551967430189616376189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84226069289906919488501585 63169551967430189616376189)
  ·
    refine ⟨23688581987786321106141071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63169551967430189616376189 23688581987786321106141071)
    ·
      refine ⟨35532872981679481659211607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23688581987786321106141071 35532872981679481659211607)
      ·
        refine ⟨53299309472519222488817411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35532872981679481659211607 53299309472519222488817411)
        ·
          refine ⟨79948964208778833733226117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53299309472519222488817411 79948964208778833733226117)
          ·
            refine ⟨14990430789146031324979897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79948964208778833733226117 14990430789146031324979897)
            ·
              refine ⟨11242823091859523493734923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14990430789146031324979897 11242823091859523493734923)
              ·
                refine ⟨16864234637789285240602385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11242823091859523493734923 16864234637789285240602385)
                ·
                  refine ⟨12648175978341963930451789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16864234637789285240602385 12648175978341963930451789)
                  ·
                    refine ⟨4743065991878236473919421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12648175978341963930451789 4743065991878236473919421)
                    ·
                      refine ⟨1778649746954338677719783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4743065991878236473919421 1778649746954338677719783)
                      ·
                        rfl

theorem cell23_3463908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_3463908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463908 prefixEnd_3463908 := by exact prefixLift 3463908
  have htrace : WordTrace (prefixWord ++ tailWord_3463908) baseStart_3463908 baseEnd_3463908 := by
    simpa [prefixWord, tailWord_3463908, baseEnd_3463908] using wordTrace_append hprefix tailTrace_3463908
  have hstable : (prefixWord ++ tailWord_3463908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463908).length < 2 ^ (prefixWord ++ tailWord_3463908).sum := by decide
  have hdescent : baseEnd_3463908 < baseStart_3463908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463909 : List Nat := [1, 3, 1, 4, 1, 3, 3, 1, 2, 2, 2]
def baseStart_3463909 : Nat := 118140960795 + 3463909 * 2 ^ 59
def prefixEnd_3463909 : Nat := 4983230072969 + 3 ^ 40 * 3463909 * 2
def baseEnd_3463909 : Nat := 1778650260434993173807279

theorem tailTrace_3463909 : CollatzResearch.WordTrace tailWord_3463909 prefixEnd_3463909 1778650260434993173807279 := by
  unfold tailWord_3463909
  simp only [CollatzResearch.WordTrace]
  refine ⟨126339140407856756403538781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84226093605237837602359187 126339140407856756403538781)
  ·
    refine ⟨47377177652946283651327043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126339140407856756403538781 47377177652946283651327043)
    ·
      refine ⟨71065766479419425476990565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47377177652946283651327043 71065766479419425476990565)
      ·
        refine ⟨13324831214891142276935731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71065766479419425476990565 13324831214891142276935731)
        ·
          refine ⟨19987246822336713415403597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13324831214891142276935731 19987246822336713415403597)
          ·
            refine ⟨7495217558376267530776349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19987246822336713415403597 7495217558376267530776349)
            ·
              refine ⟨2810706584391100324041131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7495217558376267530776349 2810706584391100324041131)
              ·
                refine ⟨4216059876586650486061697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2810706584391100324041131 4216059876586650486061697)
                ·
                  refine ⟨3162044907439987864546273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4216059876586650486061697 3162044907439987864546273)
                  ·
                    refine ⟨2371533680579990898409705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3162044907439987864546273 2371533680579990898409705)
                    ·
                      refine ⟨1778650260434993173807279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2371533680579990898409705 1778650260434993173807279)
                      ·
                        rfl

theorem cell23_3463909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_3463909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463909 prefixEnd_3463909 := by exact prefixLift 3463909
  have htrace : WordTrace (prefixWord ++ tailWord_3463909) baseStart_3463909 baseEnd_3463909 := by
    simpa [prefixWord, tailWord_3463909, baseEnd_3463909] using wordTrace_append hprefix tailTrace_3463909
  have hstable : (prefixWord ++ tailWord_3463909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463909).length < 2 ^ (prefixWord ++ tailWord_3463909).sum := by decide
  have hdescent : baseEnd_3463909 < baseStart_3463909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463961 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 2, 4, 4]
def baseStart_3463961 : Nat := 118140960795 + 3463961 * 2 ^ 59
def prefixEnd_3463961 : Nat := 4983230072969 + 3 ^ 40 * 3463961 * 2
def baseEnd_3463961 : Nat := 1778676961429026970357039

theorem tailTrace_3463961 : CollatzResearch.WordTrace tailWord_3463961 prefixEnd_3463961 1778676961429026970357039 := by
  unfold tailWord_3463961
  simp only [CollatzResearch.WordTrace]
  refine ⟨126341037003668369284431737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84227358002445579522954491 126341037003668369284431737)
  ·
    refine ⟨94755777752751276963323803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126341037003668369284431737 94755777752751276963323803)
    ·
      refine ⟨142133666629126915444985705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94755777752751276963323803 142133666629126915444985705)
      ·
        refine ⟨106600249971845186583739279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142133666629126915444985705 106600249971845186583739279)
        ·
          refine ⟨159900374957767779875608919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106600249971845186583739279 159900374957767779875608919)
          ·
            refine ⟨239850562436651669813413379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159900374957767779875608919 239850562436651669813413379)
            ·
              refine ⟨359775843654977504720120069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239850562436651669813413379 359775843654977504720120069)
              ·
                refine ⟨67457970685308282135022513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 359775843654977504720120069 67457970685308282135022513)
                ·
                  refine ⟨50593478013981211601266885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67457970685308282135022513 50593478013981211601266885)
                  ·
                    refine ⟨9486277127621477175237541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50593478013981211601266885 9486277127621477175237541)
                    ·
                      refine ⟨1778676961429026970357039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9486277127621477175237541 1778676961429026970357039)
                      ·
                        rfl

theorem cell23_3463961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_3463961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463961 prefixEnd_3463961 := by exact prefixLift 3463961
  have htrace : WordTrace (prefixWord ++ tailWord_3463961) baseStart_3463961 baseEnd_3463961 := by
    simpa [prefixWord, tailWord_3463961, baseEnd_3463961] using wordTrace_append hprefix tailTrace_3463961
  have hstable : (prefixWord ++ tailWord_3463961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463961).length < 2 ^ (prefixWord ++ tailWord_3463961).sum := by decide
  have hdescent : baseEnd_3463961 < baseStart_3463961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463982 : List Nat := [4, 1, 3, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_3463982 : Nat := 118140960795 + 3463982 * 2 ^ 59
def prefixEnd_3463982 : Nat := 4983230072969 + 3 ^ 40 * 3463982 * 2
def baseEnd_3463982 : Nat := 1778687744522771388194443

theorem tailTrace_3463982 : CollatzResearch.WordTrace tailWord_3463982 prefixEnd_3463982 1778687744522771388194443 := by
  unfold tailWord_3463982
  simp only [CollatzResearch.WordTrace]
  refine ⟨15792725367074036233868275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84227868624394859913964133 15792725367074036233868275)
  ·
    refine ⟨23689088050611054350802413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15792725367074036233868275 23689088050611054350802413)
    ·
      refine ⟨8883408018979145381550905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23689088050611054350802413 8883408018979145381550905)
      ·
        refine ⟨6662556014234359036163179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8883408018979145381550905 6662556014234359036163179)
        ·
          refine ⟨9993834021351538554244769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6662556014234359036163179 9993834021351538554244769)
          ·
            refine ⟨7495375516013653915683577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9993834021351538554244769 7495375516013653915683577)
            ·
              refine ⟨5621531637010240436762683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7495375516013653915683577 5621531637010240436762683)
              ·
                refine ⟨8432297455515360655144025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5621531637010240436762683 8432297455515360655144025)
                ·
                  refine ⟨6324223091636520491358019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8432297455515360655144025 6324223091636520491358019)
                  ·
                    refine ⟨9486334637454780737037029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6324223091636520491358019 9486334637454780737037029)
                    ·
                      refine ⟨1778687744522771388194443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9486334637454780737037029 1778687744522771388194443)
                      ·
                        rfl

theorem cell23_3463982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_3463982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463982 prefixEnd_3463982 := by exact prefixLift 3463982
  have htrace : WordTrace (prefixWord ++ tailWord_3463982) baseStart_3463982 baseEnd_3463982 := by
    simpa [prefixWord, tailWord_3463982, baseEnd_3463982] using wordTrace_append hprefix tailTrace_3463982
  have hstable : (prefixWord ++ tailWord_3463982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463982).length < 2 ^ (prefixWord ++ tailWord_3463982).sum := by decide
  have hdescent : baseEnd_3463982 < baseStart_3463982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3463985 : List Nat := [1, 2, 2, 3, 2, 1, 4, 1, 2, 2, 3]
def baseStart_3463985 : Nat := 118140960795 + 3463985 * 2 ^ 59
def prefixEnd_3463985 : Nat := 4983230072969 + 3 ^ 40 * 3463985 * 2
def baseEnd_3463985 : Nat := 1778689284964734876456929

theorem tailTrace_3463985 : CollatzResearch.WordTrace tailWord_3463985 prefixEnd_3463985 1778689284964734876456929 := by
  unfold tailWord_3463985
  simp only [CollatzResearch.WordTrace]
  refine ⟨126341912355581421383305409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84227941570387614255536939 126341912355581421383305409)
  ·
    refine ⟨94756434266686066037479057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126341912355581421383305409 94756434266686066037479057)
    ·
      refine ⟨71067325700014549528109293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94756434266686066037479057 71067325700014549528109293)
      ·
        refine ⟨26650247137505456073040985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71067325700014549528109293 26650247137505456073040985)
        ·
          refine ⟨19987685353129092054780739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26650247137505456073040985 19987685353129092054780739)
          ·
            refine ⟨29981528029693638082171109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19987685353129092054780739 29981528029693638082171109)
            ·
              refine ⟨5621536505567557140407083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29981528029693638082171109 5621536505567557140407083)
              ·
                refine ⟨8432304758351335710610625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5621536505567557140407083 8432304758351335710610625)
                ·
                  refine ⟨6324228568763501782957969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8432304758351335710610625 6324228568763501782957969)
                  ·
                    refine ⟨4743171426572626337218477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6324228568763501782957969 4743171426572626337218477)
                    ·
                      refine ⟨1778689284964734876456929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4743171426572626337218477 1778689284964734876456929)
                      ·
                        rfl

theorem cell23_3463985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_3463985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3463985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3463985 prefixEnd_3463985 := by exact prefixLift 3463985
  have htrace : WordTrace (prefixWord ++ tailWord_3463985) baseStart_3463985 baseEnd_3463985 := by
    simpa [prefixWord, tailWord_3463985, baseEnd_3463985] using wordTrace_append hprefix tailTrace_3463985
  have hstable : (prefixWord ++ tailWord_3463985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3463985).length < 2 ^ (prefixWord ++ tailWord_3463985).sum := by decide
  have hdescent : baseEnd_3463985 < baseStart_3463985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3463985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464009 : List Nat := [1, 2, 1, 1, 2, 7, 2, 2, 1, 4]
def baseStart_3464009 : Nat := 118140960795 + 3464009 * 2 ^ 59
def prefixEnd_3464009 : Nat := 4983230072969 + 3 ^ 40 * 3464009 * 2
def baseEnd_3464009 : Nat := 592900536166814260852273

theorem tailTrace_3464009 : CollatzResearch.WordTrace tailWord_3464009 prefixEnd_3464009 592900536166814260852273 := by
  unfold tailWord_3464009
  simp only [CollatzResearch.WordTrace]
  refine ⟨126342787707494473482179081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84228525138329648988119387 126342787707494473482179081)
  ·
    refine ⟨94757090780620855111634311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126342787707494473482179081 94757090780620855111634311)
    ·
      refine ⟨142135636170931282667451467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94757090780620855111634311 142135636170931282667451467)
      ·
        refine ⟨213203454256396924001177201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142135636170931282667451467 213203454256396924001177201)
        ·
          refine ⟨159902590692297693000882901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213203454256396924001177201 159902590692297693000882901)
          ·
            refine ⟨3747716969350727179708193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 159902590692297693000882901 3747716969350727179708193)
            ·
              refine ⟨2810787727013045384781145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3747716969350727179708193 2810787727013045384781145)
              ·
                refine ⟨2108090795259784038585859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2810787727013045384781145 2108090795259784038585859)
                ·
                  refine ⟨3162136192889676057878789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2108090795259784038585859 3162136192889676057878789)
                  ·
                    refine ⟨592900536166814260852273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3162136192889676057878789 592900536166814260852273)
                    ·
                      rfl

theorem cell23_3464009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2, 1, 4].length) (baseStart_3464009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464009 prefixEnd_3464009 := by exact prefixLift 3464009
  have htrace : WordTrace (prefixWord ++ tailWord_3464009) baseStart_3464009 baseEnd_3464009 := by
    simpa [prefixWord, tailWord_3464009, baseEnd_3464009] using wordTrace_append hprefix tailTrace_3464009
  have hstable : (prefixWord ++ tailWord_3464009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464009).length < 2 ^ (prefixWord ++ tailWord_3464009).sum := by decide
  have hdescent : baseEnd_3464009 < baseStart_3464009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464011 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 5]
def baseStart_3464011 : Nat := 118140960795 + 3464011 * 2 ^ 59
def prefixEnd_3464011 : Nat := 4983230072969 + 3 ^ 40 * 3464011 * 2
def baseEnd_3464011 : Nat := 1778702635461751774731809

theorem tailTrace_3464011 : CollatzResearch.WordTrace tailWord_3464011 prefixEnd_3464011 1778702635461751774731809 := by
  unfold tailWord_3464011
  simp only [CollatzResearch.WordTrace]
  refine ⟨126342860653487227823751887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84228573768991485215834591 126342860653487227823751887)
  ·
    refine ⟨189514290980230841735627831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126342860653487227823751887 189514290980230841735627831)
    ·
      refine ⟨284271436470346262603441747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189514290980230841735627831 284271436470346262603441747)
      ·
        refine ⟨426407154705519393905162621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284271436470346262603441747 426407154705519393905162621)
        ·
          refine ⟨159902683014569772714435983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 426407154705519393905162621 159902683014569772714435983)
          ·
            refine ⟨239854024521854659071653975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159902683014569772714435983 239854024521854659071653975)
            ·
              refine ⟨359781036782781988607480963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239854024521854659071653975 359781036782781988607480963)
              ·
                refine ⟨539671555174172982911221445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359781036782781988607480963 539671555174172982911221445)
                ·
                  refine ⟨101188416595157434295854021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 539671555174172982911221445 101188416595157434295854021)
                  ·
                    refine ⟨18972828111592018930472629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101188416595157434295854021 18972828111592018930472629)
                    ·
                      refine ⟨1778702635461751774731809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18972828111592018930472629 1778702635461751774731809)
                      ·
                        rfl

theorem cell23_3464011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 5].length) (baseStart_3464011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464011 prefixEnd_3464011 := by exact prefixLift 3464011
  have htrace : WordTrace (prefixWord ++ tailWord_3464011) baseStart_3464011 baseEnd_3464011 := by
    simpa [prefixWord, tailWord_3464011, baseEnd_3464011] using wordTrace_append hprefix tailTrace_3464011
  have hstable : (prefixWord ++ tailWord_3464011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464011).length < 2 ^ (prefixWord ++ tailWord_3464011).sum := by decide
  have hdescent : baseEnd_3464011 < baseStart_3464011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464018 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 5, 5]
def baseStart_3464018 : Nat := 118140960795 + 3464018 * 2 ^ 59
def prefixEnd_3464018 : Nat := 4983230072969 + 3 ^ 40 * 3464018 * 2
def baseEnd_3464018 : Nat := 592902076608777749114759

theorem tailTrace_3464018 : CollatzResearch.WordTrace tailWord_3464018 prefixEnd_3464018 592902076608777749114759 := by
  unfold tailWord_3464018
  simp only [CollatzResearch.WordTrace]
  refine ⟨31585778991115467004814177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84228743976307912012837805 31585778991115467004814177)
  ·
    refine ⟨23689334243336600253610633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31585778991115467004814177 23689334243336600253610633)
    ·
      refine ⟨17767000682502450190207975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23689334243336600253610633 17767000682502450190207975)
      ·
        refine ⟨26650501023753675285311963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17767000682502450190207975 26650501023753675285311963)
        ·
          refine ⟨39975751535630512927967945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26650501023753675285311963 39975751535630512927967945)
          ·
            refine ⟨29981813651722884695975959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39975751535630512927967945 29981813651722884695975959)
            ·
              refine ⟨44972720477584327043963939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29981813651722884695975959 44972720477584327043963939)
              ·
                refine ⟨67459080716376490565945909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44972720477584327043963939 67459080716376490565945909)
                ·
                  refine ⟨6324288817160295990557429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67459080716376490565945909 6324288817160295990557429)
                  ·
                    refine ⟨592902076608777749114759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6324288817160295990557429 592902076608777749114759)
                    ·
                      rfl

theorem cell23_3464018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_3464018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464018 prefixEnd_3464018 := by exact prefixLift 3464018
  have htrace : WordTrace (prefixWord ++ tailWord_3464018) baseStart_3464018 baseEnd_3464018 := by
    simpa [prefixWord, tailWord_3464018, baseEnd_3464018] using wordTrace_append hprefix tailTrace_3464018
  have hstable : (prefixWord ++ tailWord_3464018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464018).length < 2 ^ (prefixWord ++ tailWord_3464018).sum := by decide
  have hdescent : baseEnd_3464018 < baseStart_3464018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464048 : List Nat := [2, 1, 1, 1, 4, 1, 4, 2, 1, 6]
def baseStart_3464048 : Nat := 118140960795 + 3464048 * 2 ^ 59
def prefixEnd_3464048 : Nat := 4983230072969 + 3 ^ 40 * 3464048 * 2
def baseEnd_3464048 : Nat := 592907211415322709989713

theorem tailTrace_3464048 : CollatzResearch.WordTrace tailWord_3464048 prefixEnd_3464048 592907211415322709989713 := by
  unfold tailWord_3464048
  simp only [CollatzResearch.WordTrace]
  refine ⟨63172105077176591571424399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84229473436235455428565865 63172105077176591571424399)
  ·
    refine ⟨94758157615764887357136599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63172105077176591571424399 94758157615764887357136599)
    ·
      refine ⟨142137236423647331035704899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94758157615764887357136599 142137236423647331035704899)
      ·
        refine ⟨213205854635470996553557349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142137236423647331035704899 213205854635470996553557349)
        ·
          refine ⟨39976097744150811853792003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213205854635470996553557349 39976097744150811853792003)
          ·
            refine ⟨59964146616226217780688005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39976097744150811853792003 59964146616226217780688005)
            ·
              refine ⟨11243277490542415833879001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59964146616226217780688005 11243277490542415833879001)
              ·
                refine ⟨8432458117906811875409251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11243277490542415833879001 8432458117906811875409251)
                ·
                  refine ⟨12648687176860217813113877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8432458117906811875409251 12648687176860217813113877)
                  ·
                    refine ⟨592907211415322709989713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12648687176860217813113877 592907211415322709989713)
                    ·
                      rfl

theorem cell23_3464048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 1, 6].length) (baseStart_3464048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464048 prefixEnd_3464048 := by exact prefixLift 3464048
  have htrace : WordTrace (prefixWord ++ tailWord_3464048) baseStart_3464048 baseEnd_3464048 := by
    simpa [prefixWord, tailWord_3464048, baseEnd_3464048] using wordTrace_append hprefix tailTrace_3464048
  have hstable : (prefixWord ++ tailWord_3464048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464048).length < 2 ^ (prefixWord ++ tailWord_3464048).sum := by decide
  have hdescent : baseEnd_3464048 < baseStart_3464048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464049 : List Nat := [1, 2, 2, 2, 1, 5, 2, 3, 1, 1, 3]
def baseStart_3464049 : Nat := 118140960795 + 3464049 * 2 ^ 59
def prefixEnd_3464049 : Nat := 4983230072969 + 3 ^ 40 * 3464049 * 2
def baseEnd_3464049 : Nat := 1778722147726622626056635

theorem tailTrace_3464049 : CollatzResearch.WordTrace tailWord_3464049 prefixEnd_3464049 1778722147726622626056635 := by
  unfold tailWord_3464049
  simp only [CollatzResearch.WordTrace]
  refine ⟨126344246627349560313635201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84229497751566373542423467 126344246627349560313635201)
  ·
    refine ⟨94758184970512170235226401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126344246627349560313635201 94758184970512170235226401)
    ·
      refine ⟨71068638727884127676419801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94758184970512170235226401 71068638727884127676419801)
      ·
        refine ⟨53301479045913095757314851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71068638727884127676419801 53301479045913095757314851)
        ·
          refine ⟨79952218568869643635972277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53301479045913095757314851 79952218568869643635972277)
          ·
            refine ⟨7495520490831529090872401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79952218568869643635972277 7495520490831529090872401)
            ·
              refine ⟨5621640368123646818154301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7495520490831529090872401 5621640368123646818154301)
              ·
                refine ⟨2108115138046367556807863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5621640368123646818154301 2108115138046367556807863)
                ·
                  refine ⟨3162172707069551335211795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2108115138046367556807863 3162172707069551335211795)
                  ·
                    refine ⟨4743259060604327002817693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3162172707069551335211795 4743259060604327002817693)
                    ·
                      refine ⟨1778722147726622626056635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4743259060604327002817693 1778722147726622626056635)
                      ·
                        rfl

theorem cell23_3464049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3, 1, 1, 3].length) (baseStart_3464049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464049 prefixEnd_3464049 := by exact prefixLift 3464049
  have htrace : WordTrace (prefixWord ++ tailWord_3464049) baseStart_3464049 baseEnd_3464049 := by
    simpa [prefixWord, tailWord_3464049, baseEnd_3464049] using wordTrace_append hprefix tailTrace_3464049
  have hstable : (prefixWord ++ tailWord_3464049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464049).length < 2 ^ (prefixWord ++ tailWord_3464049).sum := by decide
  have hdescent : baseEnd_3464049 < baseStart_3464049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464058 : List Nat := [3, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5]
def baseStart_3464058 : Nat := 118140960795 + 3464058 * 2 ^ 59
def prefixEnd_3464058 : Nat := 4983230072969 + 3 ^ 40 * 3464058 * 2
def baseEnd_3464058 : Nat := 1778726769052513090844093

theorem tailTrace_3464058 : CollatzResearch.WordTrace tailWord_3464058 prefixEnd_3464058 1778726769052513090844093 := by
  unfold tailWord_3464058
  simp only [CollatzResearch.WordTrace]
  refine ⟨31586143721079238712678207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84229716589544636567141885 31586143721079238712678207)
  ·
    refine ⟨47379215581618858069017311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31586143721079238712678207 47379215581618858069017311)
    ·
      refine ⟨71068823372428287103525967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47379215581618858069017311 71068823372428287103525967)
      ·
        refine ⟨106603235058642430655288951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71068823372428287103525967 106603235058642430655288951)
        ·
          refine ⟨159904852587963645982933427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106603235058642430655288951 159904852587963645982933427)
          ·
            refine ⟨239857278881945468974400141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159904852587963645982933427 239857278881945468974400141)
            ·
              refine ⟨89946479580729550865400053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239857278881945468974400141 89946479580729550865400053)
              ·
                refine ⟨8432482460693395393631255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89946479580729550865400053 8432482460693395393631255)
                ·
                  refine ⟨12648723691040093090446883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8432482460693395393631255 12648723691040093090446883)
                  ·
                    refine ⟨18973085536560139635670325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12648723691040093090446883 18973085536560139635670325)
                    ·
                      refine ⟨1778726769052513090844093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18973085536560139635670325 1778726769052513090844093)
                      ·
                        rfl

theorem cell23_3464058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_3464058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464058 prefixEnd_3464058 := by exact prefixLift 3464058
  have htrace : WordTrace (prefixWord ++ tailWord_3464058) baseStart_3464058 baseEnd_3464058 := by
    simpa [prefixWord, tailWord_3464058, baseEnd_3464058] using wordTrace_append hprefix tailTrace_3464058
  have hstable : (prefixWord ++ tailWord_3464058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464058).length < 2 ^ (prefixWord ++ tailWord_3464058).sum := by decide
  have hdescent : baseEnd_3464058 < baseStart_3464058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464068 : List Nat := [2, 3, 2, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_3464068 : Nat := 118140960795 + 3464068 * 2 ^ 59
def prefixEnd_3464068 : Nat := 4983230072969 + 3 ^ 40 * 3464068 * 2
def baseEnd_3464068 : Nat := 1778731903859058051719047

theorem tailTrace_3464068 : CollatzResearch.WordTrace tailWord_3464068 prefixEnd_3464068 1778731903859058051719047 := by
  unfold tailWord_3464068
  simp only [CollatzResearch.WordTrace]
  refine ⟨63172469807140363279288429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84229959742853817705717905 63172469807140363279288429)
  ·
    refine ⟨23689676177677636229733161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63172469807140363279288429 23689676177677636229733161)
    ·
      refine ⟨17767257133258227172299871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23689676177677636229733161 17767257133258227172299871)
      ·
        refine ⟨26650885699887340758449807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17767257133258227172299871 26650885699887340758449807)
        ·
          refine ⟨39976328549831011137674711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26650885699887340758449807 39976328549831011137674711)
          ·
            refine ⟨59964492824746516706512067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39976328549831011137674711 59964492824746516706512067)
            ·
              refine ⟨89946739237119775059768101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59964492824746516706512067 89946739237119775059768101)
              ·
                refine ⟨16865013606959957823706519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89946739237119775059768101 16865013606959957823706519)
                ·
                  refine ⟨25297520410439936735559779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16865013606959957823706519 25297520410439936735559779)
                  ·
                    refine ⟨37946280615659905103339669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25297520410439936735559779 37946280615659905103339669)
                    ·
                      refine ⟨1778731903859058051719047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37946280615659905103339669 1778731903859058051719047)
                      ·
                        rfl

theorem cell23_3464068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_3464068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464068 prefixEnd_3464068 := by exact prefixLift 3464068
  have htrace : WordTrace (prefixWord ++ tailWord_3464068) baseStart_3464068 baseEnd_3464068 := by
    simpa [prefixWord, tailWord_3464068, baseEnd_3464068] using wordTrace_append hprefix tailTrace_3464068
  have hstable : (prefixWord ++ tailWord_3464068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464068).length < 2 ^ (prefixWord ++ tailWord_3464068).sum := by decide
  have hdescent : baseEnd_3464068 < baseStart_3464068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464085 : List Nat := [1, 3, 2, 1, 1, 4, 3, 1, 1, 2, 4]
def baseStart_3464085 : Nat := 118140960795 + 3464085 * 2 ^ 59
def prefixEnd_3464085 : Nat := 4983230072969 + 3 ^ 40 * 3464085 * 2
def baseEnd_3464085 : Nat := 1778740633030184485206469

theorem tailTrace_3464085 : CollatzResearch.WordTrace tailWord_3464085 prefixEnd_3464085 1778740633030184485206469 := by
  unfold tailWord_3464085
  simp only [CollatzResearch.WordTrace]
  refine ⟨126345559655219138461945709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84230373103479425641297139 126345559655219138461945709)
  ·
    refine ⟨47379584870707176923229641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126345559655219138461945709 47379584870707176923229641)
    ·
      refine ⟨35534688653030382692422231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47379584870707176923229641 35534688653030382692422231)
      ·
        refine ⟨53302032979545574038633347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35534688653030382692422231 53302032979545574038633347)
        ·
          refine ⟨79953049469318361057950021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53302032979545574038633347 79953049469318361057950021)
          ·
            refine ⟨14991196775497192698365629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79953049469318361057950021 14991196775497192698365629)
            ·
              refine ⟨5621698790811447261887111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14991196775497192698365629 5621698790811447261887111)
              ·
                refine ⟨8432548186217170892830667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5621698790811447261887111 8432548186217170892830667)
                ·
                  refine ⟨12648822279325756339246001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8432548186217170892830667 12648822279325756339246001)
                  ·
                    refine ⟨9486616709494317254434501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12648822279325756339246001 9486616709494317254434501)
                    ·
                      refine ⟨1778740633030184485206469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9486616709494317254434501 1778740633030184485206469)
                      ·
                        rfl

theorem cell23_3464085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_3464085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464085 prefixEnd_3464085 := by exact prefixLift 3464085
  have htrace : WordTrace (prefixWord ++ tailWord_3464085) baseStart_3464085 baseEnd_3464085 := by
    simpa [prefixWord, tailWord_3464085, baseEnd_3464085] using wordTrace_append hprefix tailTrace_3464085
  have hstable : (prefixWord ++ tailWord_3464085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464085).length < 2 ^ (prefixWord ++ tailWord_3464085).sum := by decide
  have hdescent : baseEnd_3464085 < baseStart_3464085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464086 : List Nat := [5, 3, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_3464086 : Nat := 118140960795 + 3464086 * 2 ^ 59
def prefixEnd_3464086 : Nat := 4983230072969 + 3 ^ 40 * 3464086 * 2
def baseEnd_3464086 : Nat := 592913715503612993764655

theorem tailTrace_3464086 : CollatzResearch.WordTrace tailWord_3464086 prefixEnd_3464086 592913715503612993764655 := by
  unfold tailWord_3464086
  simp only [CollatzResearch.WordTrace]
  refine ⟨7896599758013469727045757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84230397418810343755154741 7896599758013469727045757)
  ·
    refine ⟨2961224909255051147642159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7896599758013469727045757 2961224909255051147642159)
    ·
      refine ⟨4441837363882576721463239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2961224909255051147642159 4441837363882576721463239)
      ·
        refine ⟨6662756045823865082194859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4441837363882576721463239 6662756045823865082194859)
        ·
          refine ⟨9994134068735797623292289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6662756045823865082194859 9994134068735797623292289)
          ·
            refine ⟨7495600551551848217469217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9994134068735797623292289 7495600551551848217469217)
            ·
              refine ⟨5621700413663886163101913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7495600551551848217469217 5621700413663886163101913)
              ·
                refine ⟨4216275310247914622326435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5621700413663886163101913 4216275310247914622326435)
                ·
                  refine ⟨6324412965371871933489653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4216275310247914622326435 6324412965371871933489653)
                  ·
                    refine ⟨592913715503612993764655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6324412965371871933489653 592913715503612993764655)
                    ·
                      rfl

theorem cell23_3464086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_3464086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464086 prefixEnd_3464086 := by exact prefixLift 3464086
  have htrace : WordTrace (prefixWord ++ tailWord_3464086) baseStart_3464086 baseEnd_3464086 := by
    simpa [prefixWord, tailWord_3464086, baseEnd_3464086] using wordTrace_append hprefix tailTrace_3464086
  have hstable : (prefixWord ++ tailWord_3464086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464086).length < 2 ^ (prefixWord ++ tailWord_3464086).sum := by decide
  have hdescent : baseEnd_3464086 < baseStart_3464086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464095 : List Nat := [1, 1, 2, 5, 2, 1, 4, 7]
def baseStart_3464095 : Nat := 118140960795 + 3464095 * 2 ^ 59
def prefixEnd_3464095 : Nat := 4983230072969 + 3 ^ 40 * 3464095 * 2
def baseEnd_3464095 : Nat := 65879472882841831336349

theorem tailTrace_3464095 : CollatzResearch.WordTrace tailWord_3464095 prefixEnd_3464095 65879472882841831336349 := by
  unfold tailWord_3464095
  simp only [CollatzResearch.WordTrace]
  refine ⟨126345924385182910169809739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84230616256788606779873159 126345924385182910169809739)
  ·
    refine ⟨189518886577774365254714609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126345924385182910169809739 189518886577774365254714609)
    ·
      refine ⟨142139164933330773941035957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189518886577774365254714609 142139164933330773941035957)
      ·
        refine ⟨13325546712499760056972121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142139164933330773941035957 13325546712499760056972121)
        ·
          refine ⟨9994160034374820042729091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13325546712499760056972121 9994160034374820042729091)
          ·
            refine ⟨14991240051562230064093637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9994160034374820042729091 14991240051562230064093637)
            ·
              refine ⟨2810857509667918137017557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14991240051562230064093637 2810857509667918137017557)
              ·
                refine ⟨65879472882841831336349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2810857509667918137017557 65879472882841831336349)
                ·
                  rfl

theorem cell23_3464095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 7].length) (baseStart_3464095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464095 prefixEnd_3464095 := by exact prefixLift 3464095
  have htrace : WordTrace (prefixWord ++ tailWord_3464095) baseStart_3464095 baseEnd_3464095 := by
    simpa [prefixWord, tailWord_3464095, baseEnd_3464095] using wordTrace_append hprefix tailTrace_3464095
  have hstable : (prefixWord ++ tailWord_3464095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464095).length < 2 ^ (prefixWord ++ tailWord_3464095).sum := by decide
  have hdescent : baseEnd_3464095 < baseStart_3464095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464105 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 6, 1, 3]
def baseStart_3464105 : Nat := 118140960795 + 3464105 * 2 ^ 59
def prefixEnd_3464105 : Nat := 4983230072969 + 3 ^ 40 * 3464105 * 2
def baseEnd_3464105 : Nat := 1778750902643274406956377

theorem tailTrace_3464105 : CollatzResearch.WordTrace tailWord_3464105 prefixEnd_3464105 1778750902643274406956377 := by
  unfold tailWord_3464105
  simp only [CollatzResearch.WordTrace]
  refine ⟨126346289115146681877673769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84230859410097787918449179 126346289115146681877673769)
  ·
    refine ⟨94759716836360011408255327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126346289115146681877673769 94759716836360011408255327)
    ·
      refine ⟨142139575254540017112382991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94759716836360011408255327 142139575254540017112382991)
      ·
        refine ⟨213209362881810025668574487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142139575254540017112382991 213209362881810025668574487)
        ·
          refine ⟨319814044322715038502861731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213209362881810025668574487 319814044322715038502861731)
          ·
            refine ⟨479721066484072557754292597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319814044322715038502861731 479721066484072557754292597)
            ·
              refine ⟨44973849982881802289464931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 479721066484072557754292597 44973849982881802289464931)
              ·
                refine ⟨67460774974322703434197397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44973849982881802289464931 67460774974322703434197397)
                ·
                  refine ⟨3162223826921376723478003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67460774974322703434197397 3162223826921376723478003)
                  ·
                    refine ⟨4743335740382065085217005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3162223826921376723478003 4743335740382065085217005)
                    ·
                      refine ⟨1778750902643274406956377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4743335740382065085217005 1778750902643274406956377)
                      ·
                        rfl

theorem cell23_3464105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6, 1, 3].length) (baseStart_3464105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464105 prefixEnd_3464105 := by exact prefixLift 3464105
  have htrace : WordTrace (prefixWord ++ tailWord_3464105) baseStart_3464105 baseEnd_3464105 := by
    simpa [prefixWord, tailWord_3464105, baseEnd_3464105] using wordTrace_append hprefix tailTrace_3464105
  have hstable : (prefixWord ++ tailWord_3464105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464105).length < 2 ^ (prefixWord ++ tailWord_3464105).sum := by decide
  have hdescent : baseEnd_3464105 < baseStart_3464105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464109 : List Nat := [1, 5, 2, 3, 1, 1, 2, 1, 1, 1, 5]
def baseStart_3464109 : Nat := 118140960795 + 3464109 * 2 ^ 59
def prefixEnd_3464109 : Nat := 4983230072969 + 3 ^ 40 * 3464109 * 2
def baseEnd_3464109 : Nat := 1778752956565892391306359

theorem tailTrace_3464109 : CollatzResearch.WordTrace tailWord_3464109 prefixEnd_3464109 1778752956565892391306359 := by
  unfold tailWord_3464109
  simp only [CollatzResearch.WordTrace]
  refine ⟨126346435007132190560819381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84230956671421460373879587 126346435007132190560819381)
  ·
    refine ⟨11844978281918642865076817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126346435007132190560819381 11844978281918642865076817)
    ·
      refine ⟨8883733711438982148807613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11844978281918642865076817 8883733711438982148807613)
      ·
        refine ⟨3331400141789618305802855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8883733711438982148807613 3331400141789618305802855)
        ·
          refine ⟨4997100212684427458704283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3331400141789618305802855 4997100212684427458704283)
          ·
            refine ⟨7495650319026641188056425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4997100212684427458704283 7495650319026641188056425)
            ·
              refine ⟨5621737739269980891042319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7495650319026641188056425 5621737739269980891042319)
              ·
                refine ⟨8432606608904971336563479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5621737739269980891042319 8432606608904971336563479)
                ·
                  refine ⟨12648909913357457004845219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8432606608904971336563479 12648909913357457004845219)
                  ·
                    refine ⟨18973364870036185507267829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12648909913357457004845219 18973364870036185507267829)
                    ·
                      refine ⟨1778752956565892391306359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18973364870036185507267829 1778752956565892391306359)
                      ·
                        rfl

theorem cell23_3464109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_3464109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464109 prefixEnd_3464109 := by exact prefixLift 3464109
  have htrace : WordTrace (prefixWord ++ tailWord_3464109) baseStart_3464109 baseEnd_3464109 := by
    simpa [prefixWord, tailWord_3464109, baseEnd_3464109] using wordTrace_append hprefix tailTrace_3464109
  have hstable : (prefixWord ++ tailWord_3464109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464109).length < 2 ^ (prefixWord ++ tailWord_3464109).sum := by decide
  have hdescent : baseEnd_3464109 < baseStart_3464109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464122 : List Nat := [3, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3]
def baseStart_3464122 : Nat := 118140960795 + 3464122 * 2 ^ 59
def prefixEnd_3464122 : Nat := 4983230072969 + 3 ^ 40 * 3464122 * 2
def baseEnd_3464122 : Nat := 1778759631814400840443799

theorem tailTrace_3464122 : CollatzResearch.WordTrace tailWord_3464122 prefixEnd_3464122 1778759631814400840443799 := by
  unfold tailWord_3464122
  simp only [CollatzResearch.WordTrace]
  refine ⟨31586727289021273445260655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84231272770723395854028413 31586727289021273445260655)
  ·
    refine ⟨47380090933531910167890983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31586727289021273445260655 47380090933531910167890983)
    ·
      refine ⟨71070136400297865251836475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47380090933531910167890983 71070136400297865251836475)
      ·
        refine ⟨106605204600446797877754713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71070136400297865251836475 106605204600446797877754713)
        ·
          refine ⟨79953903450335098408316035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106605204600446797877754713 79953903450335098408316035)
          ·
            refine ⟨119930855175502647612474053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79953903450335098408316035 119930855175502647612474053)
            ·
              refine ⟨22487035345406746427338885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119930855175502647612474053 22487035345406746427338885)
              ·
                refine ⟨4216319127263764955126041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22487035345406746427338885 4216319127263764955126041)
                ·
                  refine ⟨3162239345447823716344531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4216319127263764955126041 3162239345447823716344531)
                  ·
                    refine ⟨4743359018171735574516797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3162239345447823716344531 4743359018171735574516797)
                    ·
                      refine ⟨1778759631814400840443799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4743359018171735574516797 1778759631814400840443799)
                      ·
                        rfl

theorem cell23_3464122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3].length) (baseStart_3464122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464122 prefixEnd_3464122 := by exact prefixLift 3464122
  have htrace : WordTrace (prefixWord ++ tailWord_3464122) baseStart_3464122 baseEnd_3464122 := by
    simpa [prefixWord, tailWord_3464122, baseEnd_3464122] using wordTrace_append hprefix tailTrace_3464122
  have hstable : (prefixWord ++ tailWord_3464122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464122).length < 2 ^ (prefixWord ++ tailWord_3464122).sum := by decide
  have hdescent : baseEnd_3464122 < baseStart_3464122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464138 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 1, 8]
def baseStart_3464138 : Nat := 118140960795 + 3464138 * 2 ^ 59
def prefixEnd_3464138 : Nat := 4983230072969 + 3 ^ 40 * 3464138 * 2
def baseEnd_3464138 : Nat := 592922615834957592614575

theorem tailTrace_3464138 : CollatzResearch.WordTrace tailWord_3464138 prefixEnd_3464138 592922615834957592614575 := by
  unfold tailWord_3464138
  simp only [CollatzResearch.WordTrace]
  refine ⟨31586873181006782128406267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84231661816018085675750045 31586873181006782128406267)
  ·
    refine ⟨47380309771510173192609401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31586873181006782128406267 47380309771510173192609401)
    ·
      refine ⟨35535232328632629894457051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47380309771510173192609401 35535232328632629894457051)
      ·
        refine ⟨53302848492948944841685577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35535232328632629894457051 53302848492948944841685577)
        ·
          refine ⟨39977136369711708631264183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53302848492948944841685577 39977136369711708631264183)
          ·
            refine ⟨59965704554567562946896275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39977136369711708631264183 59965704554567562946896275)
            ·
              refine ⟨89948556831851344420344413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59965704554567562946896275 89948556831851344420344413)
              ·
                refine ⟨33730708811944254157629155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89948556831851344420344413 33730708811944254157629155)
                ·
                  refine ⟨50596063217916381236443733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33730708811944254157629155 50596063217916381236443733)
                  ·
                    refine ⟨592922615834957592614575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50596063217916381236443733 592922615834957592614575)
                    ·
                      rfl

theorem cell23_3464138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_3464138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464138 prefixEnd_3464138 := by exact prefixLift 3464138
  have htrace : WordTrace (prefixWord ++ tailWord_3464138) baseStart_3464138 baseEnd_3464138 := by
    simpa [prefixWord, tailWord_3464138, baseEnd_3464138] using wordTrace_append hprefix tailTrace_3464138
  have hstable : (prefixWord ++ tailWord_3464138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464138).length < 2 ^ (prefixWord ++ tailWord_3464138).sum := by decide
  have hdescent : baseEnd_3464138 < baseStart_3464138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464139 : List Nat := [1, 1, 1, 1, 3, 5, 4, 1, 2, 1, 3]
def baseStart_3464139 : Nat := 118140960795 + 3464139 * 2 ^ 59
def prefixEnd_3464139 : Nat := 4983230072969 + 3 ^ 40 * 3464139 * 2
def baseEnd_3464139 : Nat := 1778768360985527273931221

theorem tailTrace_3464139 : CollatzResearch.WordTrace tailWord_3464139 prefixEnd_3464139 1778768360985527273931221 := by
  unfold tailWord_3464139
  simp only [CollatzResearch.WordTrace]
  refine ⟨126347529197023505684411471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84231686131349003789607647 126347529197023505684411471)
  ·
    refine ⟨189521293795535258526617207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126347529197023505684411471 189521293795535258526617207)
    ·
      refine ⟨284281940693302887789925811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189521293795535258526617207 284281940693302887789925811)
      ·
        refine ⟨426422911039954331684888717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284281940693302887789925811 426422911039954331684888717)
        ·
          refine ⟨159908591639982874381833269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 426422911039954331684888717 159908591639982874381833269)
          ·
            refine ⟨14991430466248394473296869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 159908591639982874381833269 14991430466248394473296869)
            ·
              refine ⟨2810893212421573963743163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14991430466248394473296869 2810893212421573963743163)
              ·
                refine ⟨4216339818632360945614745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2810893212421573963743163 4216339818632360945614745)
                ·
                  refine ⟨3162254863974270709211059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4216339818632360945614745 3162254863974270709211059)
                  ·
                    refine ⟨4743382295961406063816589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3162254863974270709211059 4743382295961406063816589)
                    ·
                      refine ⟨1778768360985527273931221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4743382295961406063816589 1778768360985527273931221)
                      ·
                        rfl

theorem cell23_3464139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 2, 1, 3].length) (baseStart_3464139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464139 prefixEnd_3464139 := by exact prefixLift 3464139
  have htrace : WordTrace (prefixWord ++ tailWord_3464139) baseStart_3464139 baseEnd_3464139 := by
    simpa [prefixWord, tailWord_3464139, baseEnd_3464139] using wordTrace_append hprefix tailTrace_3464139
  have hstable : (prefixWord ++ tailWord_3464139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464139).length < 2 ^ (prefixWord ++ tailWord_3464139).sum := by decide
  have hdescent : baseEnd_3464139 < baseStart_3464139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464149 : List Nat := [1, 3, 2, 3, 3, 1, 1, 1, 3, 3, 2]
def baseStart_3464149 : Nat := 118140960795 + 3464149 * 2 ^ 59
def prefixEnd_3464149 : Nat := 4983230072969 + 3 ^ 40 * 3464149 * 2
def baseEnd_3464149 : Nat := 1778773495792072234806175

theorem tailTrace_3464149 : CollatzResearch.WordTrace tailWord_3464149 prefixEnd_3464149 1778773495792072234806175 := by
  unfold tailWord_3464149
  simp only [CollatzResearch.WordTrace]
  refine ⟨126347893926987277392275501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84231929284658184928183667 126347893926987277392275501)
  ·
    refine ⟨47380460222620229022103313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126347893926987277392275501 47380460222620229022103313)
    ·
      refine ⟨35535345166965171766577485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47380460222620229022103313 35535345166965171766577485)
      ·
        refine ⟨13325754437611939412466557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35535345166965171766577485 13325754437611939412466557)
        ·
          refine ⟨4997157914104477279674959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13325754437611939412466557 4997157914104477279674959)
          ·
            refine ⟨7495736871156715919512439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4997157914104477279674959 7495736871156715919512439)
            ·
              refine ⟨11243605306735073879268659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7495736871156715919512439 11243605306735073879268659)
              ·
                refine ⟨16865407960102610818902989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11243605306735073879268659 16865407960102610818902989)
                ·
                  refine ⟨6324527985038479057088621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16865407960102610818902989 6324527985038479057088621)
                  ·
                    refine ⟨2371697994389429646408233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6324527985038479057088621 2371697994389429646408233)
                    ·
                      refine ⟨1778773495792072234806175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2371697994389429646408233 1778773495792072234806175)
                      ·
                        rfl

theorem cell23_3464149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_3464149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464149 prefixEnd_3464149 := by exact prefixLift 3464149
  have htrace : WordTrace (prefixWord ++ tailWord_3464149) baseStart_3464149 baseEnd_3464149 := by
    simpa [prefixWord, tailWord_3464149, baseEnd_3464149] using wordTrace_append hprefix tailTrace_3464149
  have hstable : (prefixWord ++ tailWord_3464149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464149).length < 2 ^ (prefixWord ++ tailWord_3464149).sum := by decide
  have hdescent : baseEnd_3464149 < baseStart_3464149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464182 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3]
def baseStart_3464182 : Nat := 118140960795 + 3464182 * 2 ^ 59
def prefixEnd_3464182 : Nat := 4983230072969 + 3 ^ 40 * 3464182 * 2
def baseEnd_3464182 : Nat := 1778790440653670605693523

theorem tailTrace_3464182 : CollatzResearch.WordTrace tailWord_3464182 prefixEnd_3464182 1778790440653670605693523 := by
  unfold tailWord_3464182
  simp only [CollatzResearch.WordTrace]
  refine ⟨7896818595991732751764175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84232731690578482685484533 7896818595991732751764175)
  ·
    refine ⟨11845227893987599127646263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7896818595991732751764175 11845227893987599127646263)
    ·
      refine ⟨17767841840981398691469395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11845227893987599127646263 17767841840981398691469395)
      ·
        refine ⟨26651762761472098037204093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17767841840981398691469395 26651762761472098037204093)
        ·
          refine ⟨9994411035552036763951535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26651762761472098037204093 9994411035552036763951535)
          ·
            refine ⟨14991616553328055145927303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9994411035552036763951535 14991616553328055145927303)
            ·
              refine ⟨22487424829992082718890955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14991616553328055145927303 22487424829992082718890955)
              ·
                refine ⟨33731137244988124078336433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22487424829992082718890955 33731137244988124078336433)
                ·
                  refine ⟨25298352933741093058752325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33731137244988124078336433 25298352933741093058752325)
                  ·
                    refine ⟨4743441175076454948516061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25298352933741093058752325 4743441175076454948516061)
                    ·
                      refine ⟨1778790440653670605693523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4743441175076454948516061 1778790440653670605693523)
                      ·
                        rfl

theorem cell23_3464182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_3464182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464182 prefixEnd_3464182 := by exact prefixLift 3464182
  have htrace : WordTrace (prefixWord ++ tailWord_3464182) baseStart_3464182 baseEnd_3464182 := by
    simpa [prefixWord, tailWord_3464182, baseEnd_3464182] using wordTrace_append hprefix tailTrace_3464182
  have hstable : (prefixWord ++ tailWord_3464182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464182).length < 2 ^ (prefixWord ++ tailWord_3464182).sum := by decide
  have hdescent : baseEnd_3464182 < baseStart_3464182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464235 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 4]
def baseStart_3464235 : Nat := 118140960795 + 3464235 * 2 ^ 59
def prefixEnd_3464235 : Nat := 4983230072969 + 3 ^ 40 * 3464235 * 2
def baseEnd_3464235 : Nat := 1778817655128358898330779

theorem tailTrace_3464235 : CollatzResearch.WordTrace tailWord_3464235 prefixEnd_3464235 1778817655128358898330779 := by
  unfold tailWord_3464235
  simp only [CollatzResearch.WordTrace]
  refine ⟨126351030604675714079906159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84234020403117142719937439 126351030604675714079906159)
  ·
    refine ⟨189526545907013571119859239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126351030604675714079906159 189526545907013571119859239)
    ·
      refine ⟨284289818860520356679788859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189526545907013571119859239 284289818860520356679788859)
      ·
        refine ⟨426434728290780535019683289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284289818860520356679788859 426434728290780535019683289)
        ·
          refine ⟨319826046218085401264762467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426434728290780535019683289 319826046218085401264762467)
          ·
            refine ⟨479739069327128101897143701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319826046218085401264762467 479739069327128101897143701)
            ·
              refine ⟨22487768874709129776428611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 479739069327128101897143701 22487768874709129776428611)
              ·
                refine ⟨33731653312063694664642917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22487768874709129776428611 33731653312063694664642917)
                ·
                  refine ⟨6324684996011942749620547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33731653312063694664642917 6324684996011942749620547)
                  ·
                    refine ⟨9487027494017914124430821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6324684996011942749620547 9487027494017914124430821)
                    ·
                      refine ⟨1778817655128358898330779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9487027494017914124430821 1778817655128358898330779)
                      ·
                        rfl

theorem cell23_3464235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 4].length) (baseStart_3464235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464235 prefixEnd_3464235 := by exact prefixLift 3464235
  have htrace : WordTrace (prefixWord ++ tailWord_3464235) baseStart_3464235 baseEnd_3464235 := by
    simpa [prefixWord, tailWord_3464235, baseEnd_3464235] using wordTrace_append hprefix tailTrace_3464235
  have hstable : (prefixWord ++ tailWord_3464235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464235).length < 2 ^ (prefixWord ++ tailWord_3464235).sum := by decide
  have hdescent : baseEnd_3464235 < baseStart_3464235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464286 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_3464286 : Nat := 118140960795 + 3464286 * 2 ^ 59
def prefixEnd_3464286 : Nat := 4983230072969 + 3 ^ 40 * 3464286 * 2
def baseEnd_3464286 : Nat := 1778843842641738198793045

theorem tailTrace_3464286 : CollatzResearch.WordTrace tailWord_3464286 prefixEnd_3464286 1778843842641738198793045 := by
  unfold tailWord_3464286
  simp only [CollatzResearch.WordTrace]
  refine ⟨15794111340936368723751589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84235260484993966526675141 15794111340936368723751589)
  ·
    refine ⟨2961395876425569135703423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15794111340936368723751589 2961395876425569135703423)
    ·
      refine ⟨4442093814638353703555135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2961395876425569135703423 4442093814638353703555135)
      ·
        refine ⟨6663140721957530555332703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4442093814638353703555135 6663140721957530555332703)
        ·
          refine ⟨9994711082936295832999055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6663140721957530555332703 9994711082936295832999055)
          ·
            refine ⟨14992066624404443749498583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9994711082936295832999055 14992066624404443749498583)
            ·
              refine ⟨22488099936606665624247875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14992066624404443749498583 22488099936606665624247875)
              ·
                refine ⟨33732149904909998436371813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22488099936606665624247875 33732149904909998436371813)
                ·
                  refine ⟨6324778107170624706819715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33732149904909998436371813 6324778107170624706819715)
                  ·
                    refine ⟨9487167160755937060229573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6324778107170624706819715 9487167160755937060229573)
                    ·
                      refine ⟨1778843842641738198793045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9487167160755937060229573 1778843842641738198793045)
                      ·
                        rfl

theorem cell23_3464286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_3464286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464286 prefixEnd_3464286 := by exact prefixLift 3464286
  have htrace : WordTrace (prefixWord ++ tailWord_3464286) baseStart_3464286 baseEnd_3464286 := by
    simpa [prefixWord, tailWord_3464286, baseEnd_3464286] using wordTrace_append hprefix tailTrace_3464286
  have hstable : (prefixWord ++ tailWord_3464286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464286).length < 2 ^ (prefixWord ++ tailWord_3464286).sum := by decide
  have hdescent : baseEnd_3464286 < baseStart_3464286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464312 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 3, 5, 2]
def baseStart_3464312 : Nat := 118140960795 + 3464312 * 2 ^ 59
def prefixEnd_3464312 : Nat := 4983230072969 + 3 ^ 40 * 3464312 * 2
def baseEnd_3464312 : Nat := 1778857193138755097067925

theorem tailTrace_3464312 : CollatzResearch.WordTrace tailWord_3464312 prefixEnd_3464312 1778857193138755097067925 := by
  unfold tailWord_3464312
  simp only [CollatzResearch.WordTrace]
  refine ⟨63176919512698378115229595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84235892683597837486972793 63176919512698378115229595)
  ·
    refine ⟨94765379269047567172844393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63176919512698378115229595 94765379269047567172844393)
    ·
      refine ⟨71074034451785675379633295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94765379269047567172844393 71074034451785675379633295)
      ·
        refine ⟨106611051677678513069449943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71074034451785675379633295 106611051677678513069449943)
        ·
          refine ⟨159916577516517769604174915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106611051677678513069449943 159916577516517769604174915)
          ·
            refine ⟨239874866274776654406262373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159916577516517769604174915 239874866274776654406262373)
            ·
              refine ⟨44976537426520622701174195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239874866274776654406262373 44976537426520622701174195)
              ·
                refine ⟨67464806139780934051761293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44976537426520622701174195 67464806139780934051761293)
                ·
                  refine ⟨25299302302417850269410485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67464806139780934051761293 25299302302417850269410485)
                  ·
                    refine ⟨2371809590851673462757233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25299302302417850269410485 2371809590851673462757233)
                    ·
                      refine ⟨1778857193138755097067925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2371809590851673462757233 1778857193138755097067925)
                      ·
                        rfl

theorem cell23_3464312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 3, 5, 2].length) (baseStart_3464312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464312 prefixEnd_3464312 := by exact prefixLift 3464312
  have htrace : WordTrace (prefixWord ++ tailWord_3464312) baseStart_3464312 baseEnd_3464312 := by
    simpa [prefixWord, tailWord_3464312, baseEnd_3464312] using wordTrace_append hprefix tailTrace_3464312
  have hstable : (prefixWord ++ tailWord_3464312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464312).length < 2 ^ (prefixWord ++ tailWord_3464312).sum := by decide
  have hdescent : baseEnd_3464312 < baseStart_3464312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464329 : List Nat := [1, 2, 1, 1, 4, 3, 1, 3, 2, 3, 2]
def baseStart_3464329 : Nat := 118140960795 + 3464329 * 2 ^ 59
def prefixEnd_3464329 : Nat := 4983230072969 + 3 ^ 40 * 3464329 * 2
def baseEnd_3464329 : Nat := 1778865922309881530555347

theorem tailTrace_3464329 : CollatzResearch.WordTrace tailWord_3464329 prefixEnd_3464329 1778865922309881530555347 := by
  unfold tailWord_3464329
  simp only [CollatzResearch.WordTrace]
  refine ⟨126354459066335168133828041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84236306044223445422552027 126354459066335168133828041)
  ·
    refine ⟨94765844299751376100371031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126354459066335168133828041 94765844299751376100371031)
    ·
      refine ⟨142148766449627064150556547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94765844299751376100371031 142148766449627064150556547)
      ·
        refine ⟨213223149674440596225834821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142148766449627064150556547 213223149674440596225834821)
        ·
          refine ⟨39979340563957611792344029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213223149674440596225834821 39979340563957611792344029)
          ·
            refine ⟨14992252711484104422129011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39979340563957611792344029 14992252711484104422129011)
            ·
              refine ⟨22488379067226156633193517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14992252711484104422129011 22488379067226156633193517)
              ·
                refine ⟨8433142150209808737447569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22488379067226156633193517 8433142150209808737447569)
                ·
                  refine ⟨6324856612657356553085677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8433142150209808737447569 6324856612657356553085677)
                  ·
                    refine ⟨2371821229746508707407129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6324856612657356553085677 2371821229746508707407129)
                    ·
                      refine ⟨1778865922309881530555347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2371821229746508707407129 1778865922309881530555347)
                      ·
                        rfl

theorem cell23_3464329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 3, 2].length) (baseStart_3464329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464329 prefixEnd_3464329 := by exact prefixLift 3464329
  have htrace : WordTrace (prefixWord ++ tailWord_3464329) baseStart_3464329 baseEnd_3464329 := by
    simpa [prefixWord, tailWord_3464329, baseEnd_3464329] using wordTrace_append hprefix tailTrace_3464329
  have hstable : (prefixWord ++ tailWord_3464329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464329).length < 2 ^ (prefixWord ++ tailWord_3464329).sum := by decide
  have hdescent : baseEnd_3464329 < baseStart_3464329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464346 : List Nat := [3, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2]
def baseStart_3464346 : Nat := 118140960795 + 3464346 * 2 ^ 59
def prefixEnd_3464346 : Nat := 4983230072969 + 3 ^ 40 * 3464346 * 2
def baseEnd_3464346 : Nat := 1778874651481007964042769

theorem tailTrace_3464346 : CollatzResearch.WordTrace tailWord_3464346 prefixEnd_3464346 1778874651481007964042769 := by
  unfold tailWord_3464346
  simp only [CollatzResearch.WordTrace]
  refine ⟨31588769776818395009299223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84236719404849053358131261 31588769776818395009299223)
  ·
    refine ⟨47383154665227592513948835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31588769776818395009299223 47383154665227592513948835)
    ·
      refine ⟨71074731997841388770923253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47383154665227592513948835 71074731997841388770923253)
      ·
        refine ⟨6663256124797630197274055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71074731997841388770923253 6663256124797630197274055)
        ·
          refine ⟨9994884187196445295911083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6663256124797630197274055 9994884187196445295911083)
          ·
            refine ⟨14992326280794667943866625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9994884187196445295911083 14992326280794667943866625)
            ·
              refine ⟨11244244710596000957899969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14992326280794667943866625 11244244710596000957899969)
              ·
                refine ⟨8433183532947000718424977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11244244710596000957899969 8433183532947000718424977)
                ·
                  refine ⟨6324887649710250538818733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8433183532947000718424977 6324887649710250538818733)
                  ·
                    refine ⟨2371832868641343952057025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6324887649710250538818733 2371832868641343952057025)
                    ·
                      refine ⟨1778874651481007964042769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2371832868641343952057025 1778874651481007964042769)
                      ·
                        rfl

theorem cell23_3464346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_3464346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464346 prefixEnd_3464346 := by exact prefixLift 3464346
  have htrace : WordTrace (prefixWord ++ tailWord_3464346) baseStart_3464346 baseEnd_3464346 := by
    simpa [prefixWord, tailWord_3464346, baseEnd_3464346] using wordTrace_append hprefix tailTrace_3464346
  have hstable : (prefixWord ++ tailWord_3464346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464346).length < 2 ^ (prefixWord ++ tailWord_3464346).sum := by decide
  have hdescent : baseEnd_3464346 < baseStart_3464346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464355 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 6]
def baseStart_3464355 : Nat := 118140960795 + 3464355 * 2 ^ 59
def prefixEnd_3464355 : Nat := 4983230072969 + 3 ^ 40 * 3464355 * 2
def baseEnd_3464355 : Nat := 1778879272806898428830227

theorem tailTrace_3464355 : CollatzResearch.WordTrace tailWord_3464355 prefixEnd_3464355 1778879272806898428830227 := by
  unfold tailWord_3464355
  simp only [CollatzResearch.WordTrace]
  refine ⟨126355407364240974574274519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84236938242827316382849679 126355407364240974574274519)
  ·
    refine ⟨189533111046361461861411779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126355407364240974574274519 189533111046361461861411779)
    ·
      refine ⟨284299666569542192792117669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189533111046361461861411779 284299666569542192792117669)
      ·
        refine ⟨53306187481789161148522063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 284299666569542192792117669 53306187481789161148522063)
        ·
          refine ⟨79959281222683741722783095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53306187481789161148522063 79959281222683741722783095)
          ·
            refine ⟨119938921834025612584174643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79959281222683741722783095 119938921834025612584174643)
            ·
              refine ⟨179908382751038418876261965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119938921834025612584174643 179908382751038418876261965)
              ·
                refine ⟨67465643531639407078598237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179908382751038418876261965 67465643531639407078598237)
                ·
                  refine ⟨25299616324364777654474339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67465643531639407078598237 25299616324364777654474339)
                  ·
                    refine ⟨37949424486547166481711509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25299616324364777654474339 37949424486547166481711509)
                    ·
                      refine ⟨1778879272806898428830227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37949424486547166481711509 1778879272806898428830227)
                      ·
                        rfl

theorem cell23_3464355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_3464355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464355 prefixEnd_3464355 := by exact prefixLift 3464355
  have htrace : WordTrace (prefixWord ++ tailWord_3464355) baseStart_3464355 baseEnd_3464355 := by
    simpa [prefixWord, tailWord_3464355, baseEnd_3464355] using wordTrace_append hprefix tailTrace_3464355
  have hstable : (prefixWord ++ tailWord_3464355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464355).length < 2 ^ (prefixWord ++ tailWord_3464355).sum := by decide
  have hdescent : baseEnd_3464355 < baseStart_3464355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464359 : List Nat := [1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_3464359 : Nat := 118140960795 + 3464359 * 2 ^ 59
def prefixEnd_3464359 : Nat := 4983230072969 + 3 ^ 40 * 3464359 * 2
def baseEnd_3464359 : Nat := 1778881326729516413180209

theorem tailTrace_3464359 : CollatzResearch.WordTrace tailWord_3464359 prefixEnd_3464359 1778881326729516413180209 := by
  unfold tailWord_3464359
  simp only [CollatzResearch.WordTrace]
  refine ⟨126355553256226483257420131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84237035504150988838280087 126355553256226483257420131)
  ·
    refine ⟨189533329884339724886130197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126355553256226483257420131 189533329884339724886130197)
    ·
      refine ⟨8884374838328424604037353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 189533329884339724886130197 8884374838328424604037353)
      ·
        refine ⟨6663281128746318453028015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8884374838328424604037353 6663281128746318453028015)
        ·
          refine ⟨9994921693119477679542023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6663281128746318453028015 9994921693119477679542023)
          ·
            refine ⟨14992382539679216519313035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9994921693119477679542023 14992382539679216519313035)
            ·
              refine ⟨22488573809518824778969553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14992382539679216519313035 22488573809518824778969553)
              ·
                refine ⟨16866430357139118584227165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22488573809518824778969553 16866430357139118584227165)
                ·
                  refine ⟨6324911383927169469085187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16866430357139118584227165 6324911383927169469085187)
                  ·
                    refine ⟨9487367075890754203627781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6324911383927169469085187 9487367075890754203627781)
                    ·
                      refine ⟨1778881326729516413180209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9487367075890754203627781 1778881326729516413180209)
                      ·
                        rfl

theorem cell23_3464359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_3464359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464359 prefixEnd_3464359 := by exact prefixLift 3464359
  have htrace : WordTrace (prefixWord ++ tailWord_3464359) baseStart_3464359 baseEnd_3464359 := by
    simpa [prefixWord, tailWord_3464359, baseEnd_3464359] using wordTrace_append hprefix tailTrace_3464359
  have hstable : (prefixWord ++ tailWord_3464359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464359).length < 2 ^ (prefixWord ++ tailWord_3464359).sum := by decide
  have hdescent : baseEnd_3464359 < baseStart_3464359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464369 : List Nat := [1, 2, 2, 5, 1, 2, 2, 1, 1, 6]
def baseStart_3464369 : Nat := 118140960795 + 3464369 * 2 ^ 59
def prefixEnd_3464369 : Nat := 4983230072969 + 3 ^ 40 * 3464369 * 2
def baseEnd_3464369 : Nat := 592962153845353791351721

theorem tailTrace_3464369 : CollatzResearch.WordTrace tailWord_3464369 prefixEnd_3464369 592962153845353791351721 := by
  unfold tailWord_3464369
  simp only [CollatzResearch.WordTrace]
  refine ⟨126355917986190254965284161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84237278657460169976856107 126355917986190254965284161)
  ·
    refine ⟨94766938489642691223963121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126355917986190254965284161 94766938489642691223963121)
    ·
      refine ⟨71075203867232018417972341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94766938489642691223963121 71075203867232018417972341)
      ·
        refine ⟨6663300362553001726684907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71075203867232018417972341 6663300362553001726684907)
        ·
          refine ⟨9994950543829502590027361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6663300362553001726684907 9994950543829502590027361)
          ·
            refine ⟨7496212907872126942520521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9994950543829502590027361 7496212907872126942520521)
            ·
              refine ⟨5622159680904095206890391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7496212907872126942520521 5622159680904095206890391)
              ·
                refine ⟨8433239521356142810335587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5622159680904095206890391 8433239521356142810335587)
                ·
                  refine ⟨12649859282034214215503381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8433239521356142810335587 12649859282034214215503381)
                  ·
                    refine ⟨592962153845353791351721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12649859282034214215503381 592962153845353791351721)
                    ·
                      rfl

theorem cell23_3464369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 6].length) (baseStart_3464369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464369 prefixEnd_3464369 := by exact prefixLift 3464369
  have htrace : WordTrace (prefixWord ++ tailWord_3464369) baseStart_3464369 baseEnd_3464369 := by
    simpa [prefixWord, tailWord_3464369, baseEnd_3464369] using wordTrace_append hprefix tailTrace_3464369
  have hstable : (prefixWord ++ tailWord_3464369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464369).length < 2 ^ (prefixWord ++ tailWord_3464369).sum := by decide
  have hdescent : baseEnd_3464369 < baseStart_3464369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464390 : List Nat := [6, 1, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_3464390 : Nat := 118140960795 + 3464390 * 2 ^ 59
def prefixEnd_3464390 : Nat := 4983230072969 + 3 ^ 40 * 3464390 * 2
def baseEnd_3464390 : Nat := 592965748209935263964189

theorem tailTrace_3464390 : CollatzResearch.WordTrace tailWord_3464390 prefixEnd_3464390 592965748209935263964189 := by
  unfold tailWord_3464390
  simp only [CollatzResearch.WordTrace]
  refine ⟨3948646372472317985993707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84237789279409450367865749 3948646372472317985993707)
  ·
    refine ⟨5922969558708476978990561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3948646372472317985993707 5922969558708476978990561)
    ·
      refine ⟨4442227169031357734242921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5922969558708476978990561 4442227169031357734242921)
      ·
        refine ⟨3331670376773518300682191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4442227169031357734242921 3331670376773518300682191)
        ·
          refine ⟨4997505565160277451023287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3331670376773518300682191 4997505565160277451023287)
          ·
            refine ⟨7496258347740416176534931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4997505565160277451023287 7496258347740416176534931)
            ·
              refine ⟨11244387521610624264802397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7496258347740416176534931 11244387521610624264802397)
              ·
                refine ⟨4216645320603984099300899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11244387521610624264802397 4216645320603984099300899)
                ·
                  refine ⟨6324967980905976148951349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4216645320603984099300899 6324967980905976148951349)
                  ·
                    refine ⟨592965748209935263964189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6324967980905976148951349 592965748209935263964189)
                    ·
                      rfl

theorem cell23_3464390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_3464390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464390 prefixEnd_3464390 := by exact prefixLift 3464390
  have htrace : WordTrace (prefixWord ++ tailWord_3464390) baseStart_3464390 baseEnd_3464390 := by
    simpa [prefixWord, tailWord_3464390, baseEnd_3464390] using wordTrace_append hprefix tailTrace_3464390
  have hstable : (prefixWord ++ tailWord_3464390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464390).length < 2 ^ (prefixWord ++ tailWord_3464390).sum := by decide
  have hdescent : baseEnd_3464390 < baseStart_3464390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464395 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 1, 9]
def baseStart_3464395 : Nat := 118140960795 + 3464395 * 2 ^ 59
def prefixEnd_3464395 : Nat := 4983230072969 + 3 ^ 40 * 3464395 * 2
def baseEnd_3464395 : Nat := 592966604011026090776681

theorem tailTrace_3464395 : CollatzResearch.WordTrace tailWord_3464395 prefixEnd_3464395 592966604011026090776681 := by
  unfold tailWord_3464395
  simp only [CollatzResearch.WordTrace]
  refine ⟨126356866284096061405730639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84237910856064040937153759 126356866284096061405730639)
  ·
    refine ⟨189535299426144092108595959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126356866284096061405730639 189535299426144092108595959)
    ·
      refine ⟨284302949139216138162893939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189535299426144092108595959 284302949139216138162893939)
      ·
        refine ⟨426454423708824207244340909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284302949139216138162893939 426454423708824207244340909)
        ·
          refine ⟨159920408890809077716627841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 426454423708824207244340909 159920408890809077716627841)
          ·
            refine ⟨119940306668106808287470881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159920408890809077716627841 119940306668106808287470881)
            ·
              refine ⟨89955230001080106215603161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119940306668106808287470881 89955230001080106215603161)
              ·
                refine ⟨67466422500810079661702371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89955230001080106215603161 67466422500810079661702371)
                ·
                  refine ⟨101199633751215119492553557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67466422500810079661702371 101199633751215119492553557)
                  ·
                    refine ⟨592966604011026090776681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 101199633751215119492553557 592966604011026090776681)
                    ·
                      rfl

theorem cell23_3464395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 9].length) (baseStart_3464395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464395 prefixEnd_3464395 := by exact prefixLift 3464395
  have htrace : WordTrace (prefixWord ++ tailWord_3464395) baseStart_3464395 baseEnd_3464395 := by
    simpa [prefixWord, tailWord_3464395, baseEnd_3464395] using wordTrace_append hprefix tailTrace_3464395
  have hstable : (prefixWord ++ tailWord_3464395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464395).length < 2 ^ (prefixWord ++ tailWord_3464395).sum := by decide
  have hdescent : baseEnd_3464395 < baseStart_3464395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464423 : List Nat := [1, 1, 5, 3, 3, 1, 1, 1, 1, 2, 4]
def baseStart_3464423 : Nat := 118140960795 + 3464423 * 2 ^ 59
def prefixEnd_3464423 : Nat := 4983230072969 + 3 ^ 40 * 3464423 * 2
def baseEnd_3464423 : Nat := 1778914189491404162779915

theorem tailTrace_3464423 : CollatzResearch.WordTrace tailWord_3464423 prefixEnd_3464423 1778914189491404162779915 := by
  unfold tailWord_3464423
  simp only [CollatzResearch.WordTrace]
  refine ⟨126357887527994622187749923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84238591685329748125166615 126357887527994622187749923)
  ·
    refine ⟨189536831291991933281624885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126357887527994622187749923 189536831291991933281624885)
    ·
      refine ⟨17769077933624243745152333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189536831291991933281624885 17769077933624243745152333)
      ·
        refine ⟨6663404225109091404432125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17769077933624243745152333 6663404225109091404432125)
        ·
          refine ⟨2498776584415909276662047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6663404225109091404432125 2498776584415909276662047)
          ·
            refine ⟨3748164876623863914993071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2498776584415909276662047 3748164876623863914993071)
            ·
              refine ⟨5622247314935795872489607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3748164876623863914993071 5622247314935795872489607)
              ·
                refine ⟨8433370972403693808734411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5622247314935795872489607 8433370972403693808734411)
                ·
                  refine ⟨12650056458605540713101617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8433370972403693808734411 12650056458605540713101617)
                  ·
                    refine ⟨9487542343954155534826213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12650056458605540713101617 9487542343954155534826213)
                    ·
                      refine ⟨1778914189491404162779915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9487542343954155534826213 1778914189491404162779915)
                      ·
                        rfl

theorem cell23_3464423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_3464423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464423 prefixEnd_3464423 := by exact prefixLift 3464423
  have htrace : WordTrace (prefixWord ++ tailWord_3464423) baseStart_3464423 baseEnd_3464423 := by
    simpa [prefixWord, tailWord_3464423, baseEnd_3464423] using wordTrace_append hprefix tailTrace_3464423
  have hstable : (prefixWord ++ tailWord_3464423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464423).length < 2 ^ (prefixWord ++ tailWord_3464423).sum := by decide
  have hdescent : baseEnd_3464423 < baseStart_3464423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464426 : List Nat := [3, 1, 3, 1, 1, 5, 1, 1, 1, 3, 3]
def baseStart_3464426 : Nat := 118140960795 + 3464426 * 2 ^ 59
def prefixEnd_3464426 : Nat := 4983230072969 + 3 ^ 40 * 3464426 * 2
def baseEnd_3464426 : Nat := 1778915729933367651042401

theorem tailTrace_3464426 : CollatzResearch.WordTrace tailWord_3464426 prefixEnd_3464426 1778915729933367651042401 := by
  unfold tailWord_3464426
  simp only [CollatzResearch.WordTrace]
  refine ⟨31589499236745938425027283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84238664631322502466739421 31589499236745938425027283)
  ·
    refine ⟨47384248855118907637540925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31589499236745938425027283 47384248855118907637540925)
    ·
      refine ⟨17769093320669590364077847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47384248855118907637540925 17769093320669590364077847)
      ·
        refine ⟨26653639981004385546116771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17769093320669590364077847 26653639981004385546116771)
        ·
          refine ⟨39980459971506578319175157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26653639981004385546116771 39980459971506578319175157)
          ·
            refine ⟨3748168122328741717422671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39980459971506578319175157 3748168122328741717422671)
            ·
              refine ⟨5622252183493112576134007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3748168122328741717422671 5622252183493112576134007)
              ·
                refine ⟨8433378275239668864201011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5622252183493112576134007 8433378275239668864201011)
                ·
                  refine ⟨12650067412859503296301517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8433378275239668864201011 12650067412859503296301517)
                  ·
                    refine ⟨4743775279822313736113069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12650067412859503296301517 4743775279822313736113069)
                    ·
                      refine ⟨1778915729933367651042401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4743775279822313736113069 1778915729933367651042401)
                      ·
                        rfl

theorem cell23_3464426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_3464426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464426 prefixEnd_3464426 := by exact prefixLift 3464426
  have htrace : WordTrace (prefixWord ++ tailWord_3464426) baseStart_3464426 baseEnd_3464426 := by
    simpa [prefixWord, tailWord_3464426, baseEnd_3464426] using wordTrace_append hprefix tailTrace_3464426
  have hstable : (prefixWord ++ tailWord_3464426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464426).length < 2 ^ (prefixWord ++ tailWord_3464426).sum := by decide
  have hdescent : baseEnd_3464426 < baseStart_3464426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464483 : List Nat := [1, 1, 1, 4, 2, 4, 1, 3, 2, 2, 2]
def baseStart_3464483 : Nat := 118140960795 + 3464483 * 2 ^ 59
def prefixEnd_3464483 : Nat := 4983230072969 + 3 ^ 40 * 3464483 * 2
def baseEnd_3464483 : Nat := 1778944998330673928029639

theorem tailTrace_3464483 : CollatzResearch.WordTrace tailWord_3464483 prefixEnd_3464483 1778944998330673928029639 := by
  unfold tailWord_3464483
  simp only [CollatzResearch.WordTrace]
  refine ⟨126360075907777252434934103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84240050605184834956622735 126360075907777252434934103)
  ·
    refine ⟨189540113861665878652401155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126360075907777252434934103 189540113861665878652401155)
    ·
      refine ⟨284310170792498817978601733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189540113861665878652401155 284310170792498817978601733)
      ·
        refine ⟨53308157023593528370987825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 284310170792498817978601733 53308157023593528370987825)
        ·
          refine ⟨39981117767695146278240869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53308157023593528370987825 39981117767695146278240869)
          ·
            refine ⟨7496459581442839927170163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39981117767695146278240869 7496459581442839927170163)
            ·
              refine ⟨11244689372164259890755245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7496459581442839927170163 11244689372164259890755245)
              ·
                refine ⟨4216758514561597459033217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11244689372164259890755245 4216758514561597459033217)
                ·
                  refine ⟨3162568885921198094274913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4216758514561597459033217 3162568885921198094274913)
                  ·
                    refine ⟨2371926664440898570706185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3162568885921198094274913 2371926664440898570706185)
                    ·
                      refine ⟨1778944998330673928029639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2371926664440898570706185 1778944998330673928029639)
                      ·
                        rfl

theorem cell23_3464483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2, 2, 2].length) (baseStart_3464483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464483 prefixEnd_3464483 := by exact prefixLift 3464483
  have htrace : WordTrace (prefixWord ++ tailWord_3464483) baseStart_3464483 baseEnd_3464483 := by
    simpa [prefixWord, tailWord_3464483, baseEnd_3464483] using wordTrace_append hprefix tailTrace_3464483
  have hstable : (prefixWord ++ tailWord_3464483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464483).length < 2 ^ (prefixWord ++ tailWord_3464483).sum := by decide
  have hdescent : baseEnd_3464483 < baseStart_3464483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464512 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 5]
def baseStart_3464512 : Nat := 118140960795 + 3464512 * 2 ^ 59
def prefixEnd_3464512 : Nat := 4983230072969 + 3 ^ 40 * 3464512 * 2
def baseEnd_3464512 : Nat := 1778959889269654314567005

theorem tailTrace_3464512 : CollatzResearch.WordTrace tailWord_3464512 prefixEnd_3464512 1778959889269654314567005 := by
  unfold tailWord_3464512
  simp only [CollatzResearch.WordTrace]
  refine ⟨63180566812336095193869895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84240755749781460258493193 63180566812336095193869895)
  ·
    refine ⟨94770850218504142790804843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63180566812336095193869895 94770850218504142790804843)
    ·
      refine ⟨142156275327756214186207265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94770850218504142790804843 142156275327756214186207265)
      ·
        refine ⟨106617206495817160639655449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142156275327756214186207265 106617206495817160639655449)
        ·
          refine ⟨79962904871862870479741587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106617206495817160639655449 79962904871862870479741587)
          ·
            refine ⟨119944357307794305719612381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79962904871862870479741587 119944357307794305719612381)
            ·
              refine ⟨44979133990422864644854643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119944357307794305719612381 44979133990422864644854643)
              ·
                refine ⟨67468700985634296967281965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44979133990422864644854643 67468700985634296967281965)
                ·
                  refine ⟨25300762869612861362730737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67468700985634296967281965 25300762869612861362730737)
                  ·
                    refine ⟨18975572152209646022048053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25300762869612861362730737 18975572152209646022048053)
                    ·
                      refine ⟨1778959889269654314567005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18975572152209646022048053 1778959889269654314567005)
                      ·
                        rfl

theorem cell23_3464512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_3464512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464512 prefixEnd_3464512 := by exact prefixLift 3464512
  have htrace : WordTrace (prefixWord ++ tailWord_3464512) baseStart_3464512 baseEnd_3464512 := by
    simpa [prefixWord, tailWord_3464512, baseEnd_3464512] using wordTrace_append hprefix tailTrace_3464512
  have hstable : (prefixWord ++ tailWord_3464512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464512).length < 2 ^ (prefixWord ++ tailWord_3464512).sum := by decide
  have hdescent : baseEnd_3464512 < baseStart_3464512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464519 : List Nat := [1, 1, 4, 1, 2, 3, 2, 2, 2, 5]
def baseStart_3464519 : Nat := 118140960795 + 3464519 * 2 ^ 59
def prefixEnd_3464519 : Nat := 4983230072969 + 3 ^ 40 * 3464519 * 2
def baseEnd_3464519 : Nat := 592987827878078595726491

theorem tailTrace_3464519 : CollatzResearch.WordTrace tailWord_3464519 prefixEnd_3464519 592987827878078595726491 := by
  unfold tailWord_3464519
  simp only [CollatzResearch.WordTrace]
  refine ⟨126361388935646830583244611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84240925957097887055496407 126361388935646830583244611)
  ·
    refine ⟨189542083403470245874866917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126361388935646830583244611 189542083403470245874866917)
    ·
      refine ⟨35539140638150671101537547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189542083403470245874866917 35539140638150671101537547)
      ·
        refine ⟨53308710957226006652306321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35539140638150671101537547 53308710957226006652306321)
        ·
          refine ⟨39981533217919504989229741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53308710957226006652306321 39981533217919504989229741)
          ·
            refine ⟨14993074956719814370961153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39981533217919504989229741 14993074956719814370961153)
            ·
              refine ⟨11244806217539860778220865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14993074956719814370961153 11244806217539860778220865)
              ·
                refine ⟨8433604663154895583665649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11244806217539860778220865 8433604663154895583665649)
                ·
                  refine ⟨6325203497366171687749237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8433604663154895583665649 6325203497366171687749237)
                  ·
                    refine ⟨592987827878078595726491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6325203497366171687749237 592987827878078595726491)
                    ·
                      rfl

theorem cell23_3464519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_3464519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464519 prefixEnd_3464519 := by exact prefixLift 3464519
  have htrace : WordTrace (prefixWord ++ tailWord_3464519) baseStart_3464519 baseEnd_3464519 := by
    simpa [prefixWord, tailWord_3464519, baseEnd_3464519] using wordTrace_append hprefix tailTrace_3464519
  have hstable : (prefixWord ++ tailWord_3464519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464519).length < 2 ^ (prefixWord ++ tailWord_3464519).sum := by decide
  have hdescent : baseEnd_3464519 < baseStart_3464519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464534 : List Nat := [5, 2, 3, 1, 1, 1, 2, 1, 1, 4, 2]
def baseStart_3464534 : Nat := 118140960795 + 3464534 * 2 ^ 59
def prefixEnd_3464534 : Nat := 4983230072969 + 3 ^ 40 * 3464534 * 2
def baseEnd_3464534 : Nat := 1778971185844053228491905

theorem tailTrace_3464534 : CollatzResearch.WordTrace tailWord_3464534 prefixEnd_3464534 1778971185844053228491905 := by
  unfold tailWord_3464534
  simp only [CollatzResearch.WordTrace]
  refine ⟨7897621001912030509065041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84241290687061658763360437 7897621001912030509065041)
  ·
    refine ⟨5923215751434022881798781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7897621001912030509065041 5923215751434022881798781)
    ·
      refine ⟨2221205906787758580674543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5923215751434022881798781 2221205906787758580674543)
      ·
        refine ⟨3331808860181637871011815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2221205906787758580674543 3331808860181637871011815)
        ·
          refine ⟨4997713290272456806517723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3331808860181637871011815 4997713290272456806517723)
          ·
            refine ⟨7496569935408685209776585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4997713290272456806517723 7496569935408685209776585)
            ·
              refine ⟨5622427451556513907332439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7496569935408685209776585 5622427451556513907332439)
              ·
                refine ⟨8433641177334770860998659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5622427451556513907332439 8433641177334770860998659)
                ·
                  refine ⟨12650461766002156291497989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8433641177334770860998659 12650461766002156291497989)
                  ·
                    refine ⟨2371961581125404304655873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12650461766002156291497989 2371961581125404304655873)
                    ·
                      refine ⟨1778971185844053228491905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2371961581125404304655873 1778971185844053228491905)
                      ·
                        rfl

theorem cell23_3464534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_3464534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464534 prefixEnd_3464534 := by exact prefixLift 3464534
  have htrace : WordTrace (prefixWord ++ tailWord_3464534) baseStart_3464534 baseEnd_3464534 := by
    simpa [prefixWord, tailWord_3464534, baseEnd_3464534] using wordTrace_append hprefix tailTrace_3464534
  have hstable : (prefixWord ++ tailWord_3464534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464534).length < 2 ^ (prefixWord ++ tailWord_3464534).sum := by decide
  have hdescent : baseEnd_3464534 < baseStart_3464534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464556 : List Nat := [2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 4]
def baseStart_3464556 : Nat := 118140960795 + 3464556 * 2 ^ 59
def prefixEnd_3464556 : Nat := 4983230072969 + 3 ^ 40 * 3464556 * 2
def baseEnd_3464556 : Nat := 1778982482418452142416803

theorem tailTrace_3464556 : CollatzResearch.WordTrace tailWord_3464556 prefixEnd_3464556 1778982482418452142416803 := by
  unfold tailWord_3464556
  simp only [CollatzResearch.WordTrace]
  refine ⟨63181369218256392951170761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84241825624341857268227681 63181369218256392951170761)
  ·
    refine ⟨47386026913692294713378071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63181369218256392951170761 47386026913692294713378071)
    ·
      refine ⟨71079040370538442070067107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47386026913692294713378071 71079040370538442070067107)
      ·
        refine ⟨106618560555807663105100661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71079040370538442070067107 106618560555807663105100661)
        ·
          refine ⟨9995490052106968416103187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106618560555807663105100661 9995490052106968416103187)
          ·
            refine ⟨14993235078160452624154781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9995490052106968416103187 14993235078160452624154781)
            ·
              refine ⟨5622463154310169734058043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14993235078160452624154781 5622463154310169734058043)
              ·
                refine ⟨8433694731465254601087065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5622463154310169734058043 8433694731465254601087065)
                ·
                  refine ⟨6325271048598940950815299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8433694731465254601087065 6325271048598940950815299)
                  ·
                    refine ⟨9487906572898411426222949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6325271048598940950815299 9487906572898411426222949)
                    ·
                      refine ⟨1778982482418452142416803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9487906572898411426222949 1778982482418452142416803)
                      ·
                        rfl

theorem cell23_3464556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 4].length) (baseStart_3464556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464556 prefixEnd_3464556 := by exact prefixLift 3464556
  have htrace : WordTrace (prefixWord ++ tailWord_3464556) baseStart_3464556 baseEnd_3464556 := by
    simpa [prefixWord, tailWord_3464556, baseEnd_3464556] using wordTrace_append hprefix tailTrace_3464556
  have hstable : (prefixWord ++ tailWord_3464556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464556).length < 2 ^ (prefixWord ++ tailWord_3464556).sum := by decide
  have hdescent : baseEnd_3464556 < baseStart_3464556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464559 : List Nat := [1, 1, 2, 1, 3, 1, 5, 1, 1, 4, 3]
def baseStart_3464559 : Nat := 118140960795 + 3464559 * 2 ^ 59
def prefixEnd_3464559 : Nat := 4983230072969 + 3 ^ 40 * 3464559 * 2
def baseEnd_3464559 : Nat := 1778984022860415630679289

theorem tailTrace_3464559 : CollatzResearch.WordTrace tailWord_3464559 prefixEnd_3464559 1778984022860415630679289 := by
  unfold tailWord_3464559
  simp only [CollatzResearch.WordTrace]
  refine ⟨126362847855501917414700731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84241898570334611609800487 126362847855501917414700731)
  ·
    refine ⟨189544271783252876122051097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126362847855501917414700731 189544271783252876122051097)
    ·
      refine ⟨142158203837439657091538323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189544271783252876122051097 142158203837439657091538323)
      ·
        refine ⟨213237305756159485637307485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142158203837439657091538323 213237305756159485637307485)
        ·
          refine ⟨79963989658559807113990307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213237305756159485637307485 79963989658559807113990307)
          ·
            refine ⟨119945984487839710670985461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79963989658559807113990307 119945984487839710670985461)
            ·
              refine ⟨11244936045734972875404887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119945984487839710670985461 11244936045734972875404887)
              ·
                refine ⟨16867404068602459313107331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11244936045734972875404887 16867404068602459313107331)
                ·
                  refine ⟨25301106102903688969660997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16867404068602459313107331 25301106102903688969660997)
                  ·
                    refine ⟨4743957394294441681811437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25301106102903688969660997 4743957394294441681811437)
                    ·
                      refine ⟨1778984022860415630679289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4743957394294441681811437 1778984022860415630679289)
                      ·
                        rfl

theorem cell23_3464559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4, 3].length) (baseStart_3464559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464559 prefixEnd_3464559 := by exact prefixLift 3464559
  have htrace : WordTrace (prefixWord ++ tailWord_3464559) baseStart_3464559 baseEnd_3464559 := by
    simpa [prefixWord, tailWord_3464559, baseEnd_3464559] using wordTrace_append hprefix tailTrace_3464559
  have hstable : (prefixWord ++ tailWord_3464559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464559).length < 2 ^ (prefixWord ++ tailWord_3464559).sum := by decide
  have hdescent : baseEnd_3464559 < baseStart_3464559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464579 : List Nat := [1, 1, 1, 3, 5, 2, 1, 1, 8]
def baseStart_3464579 : Nat := 118140960795 + 3464579 * 2 ^ 59
def prefixEnd_3464579 : Nat := 4983230072969 + 3 ^ 40 * 3464579 * 2
def baseEnd_3464579 : Nat := 197666032497056172492133

theorem tailTrace_3464579 : CollatzResearch.WordTrace tailWord_3464579 prefixEnd_3464579 197666032497056172492133 := by
  unfold tailWord_3464579
  simp only [CollatzResearch.WordTrace]
  refine ⟨126363577315429460830428791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84242384876952973886952527 126363577315429460830428791)
  ·
    refine ⟨189545365973144191245643187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126363577315429460830428791 189545365973144191245643187)
    ·
      refine ⟨284318048959716286868464781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189545365973144191245643187 284318048959716286868464781)
      ·
        refine ⟨106619268359893607575674293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284318048959716286868464781 106619268359893607575674293)
        ·
          refine ⟨9995556408740025710219465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106619268359893607575674293 9995556408740025710219465)
          ·
            refine ⟨7496667306555019282664599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9995556408740025710219465 7496667306555019282664599)
            ·
              refine ⟨11245000959832528923996899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7496667306555019282664599 11245000959832528923996899)
              ·
                refine ⟨16867501439748793385995349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11245000959832528923996899 16867501439748793385995349)
                ·
                  refine ⟨197666032497056172492133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16867501439748793385995349 197666032497056172492133)
                  ·
                    rfl

theorem cell23_3464579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 8].length) (baseStart_3464579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464579 prefixEnd_3464579 := by exact prefixLift 3464579
  have htrace : WordTrace (prefixWord ++ tailWord_3464579) baseStart_3464579 baseEnd_3464579 := by
    simpa [prefixWord, tailWord_3464579, baseEnd_3464579] using wordTrace_append hprefix tailTrace_3464579
  have hstable : (prefixWord ++ tailWord_3464579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464579).length < 2 ^ (prefixWord ++ tailWord_3464579).sum := by decide
  have hdescent : baseEnd_3464579 < baseStart_3464579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464583 : List Nat := [1, 1, 4, 2, 2, 2, 2, 4, 1, 4]
def baseStart_3464583 : Nat := 118140960795 + 3464583 * 2 ^ 59
def prefixEnd_3464583 : Nat := 4983230072969 + 3 ^ 40 * 3464583 * 2
def baseEnd_3464583 : Nat := 592998782132041178926393

theorem tailTrace_3464583 : CollatzResearch.WordTrace tailWord_3464583 prefixEnd_3464583 592998782132041178926393 := by
  unfold tailWord_3464583
  simp only [CollatzResearch.WordTrace]
  refine ⟨126363723207414969513574403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84242482138276646342382935 126363723207414969513574403)
  ·
    refine ⟨189545584811122454270361605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126363723207414969513574403 189545584811122454270361605)
    ·
      refine ⟨35539797152085460175692801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189545584811122454270361605 35539797152085460175692801)
      ·
        refine ⟨26654847864064095131769601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35539797152085460175692801 26654847864064095131769601)
        ·
          refine ⟨19991135898048071348827201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26654847864064095131769601 19991135898048071348827201)
          ·
            refine ⟨14993351923536053511620401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19991135898048071348827201 14993351923536053511620401)
            ·
              refine ⟨11245013942652040133715301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14993351923536053511620401 11245013942652040133715301)
              ·
                refine ⟨2108440114247257525071619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11245013942652040133715301 2108440114247257525071619)
                ·
                  refine ⟨3162660171370886287607429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2108440114247257525071619 3162660171370886287607429)
                  ·
                    refine ⟨592998782132041178926393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3162660171370886287607429 592998782132041178926393)
                    ·
                      rfl

theorem cell23_3464583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_3464583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464583 prefixEnd_3464583 := by exact prefixLift 3464583
  have htrace : WordTrace (prefixWord ++ tailWord_3464583) baseStart_3464583 baseEnd_3464583 := by
    simpa [prefixWord, tailWord_3464583, baseEnd_3464583] using wordTrace_append hprefix tailTrace_3464583
  have hstable : (prefixWord ++ tailWord_3464583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464583).length < 2 ^ (prefixWord ++ tailWord_3464583).sum := by decide
  have hdescent : baseEnd_3464583 < baseStart_3464583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464649 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 2, 6, 3]
def baseStart_3464649 : Nat := 118140960795 + 3464649 * 2 ^ 59
def prefixEnd_3464649 : Nat := 4983230072969 + 3 ^ 40 * 3464649 * 2
def baseEnd_3464649 : Nat := 1779030236119320278553875

theorem tailTrace_3464649 : CollatzResearch.WordTrace tailWord_3464649 prefixEnd_3464649 1779030236119320278553875 := by
  unfold tailWord_3464649
  simp only [CollatzResearch.WordTrace]
  refine ⟨126366130425175862785477001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84244086950117241856984667 126366130425175862785477001)
  ·
    refine ⟨94774597818881897089107751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126366130425175862785477001 94774597818881897089107751)
    ·
      refine ⟨142161896728322845633661627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94774597818881897089107751 142161896728322845633661627)
      ·
        refine ⟨213242845092484268450492441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142161896728322845633661627 213242845092484268450492441)
        ·
          refine ⟨159932133819363201337869331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213242845092484268450492441 159932133819363201337869331)
          ·
            refine ⟨239898200729044802006803997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159932133819363201337869331 239898200729044802006803997)
            ·
              refine ⟨89961825273391800752551499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239898200729044802006803997 89961825273391800752551499)
              ·
                refine ⟨134942737910087701128827249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89961825273391800752551499 134942737910087701128827249)
                ·
                  refine ⟨101207053432565775846620437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134942737910087701128827249 101207053432565775846620437)
                  ·
                    refine ⟨4744080629651520742810333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101207053432565775846620437 4744080629651520742810333)
                    ·
                      refine ⟨1779030236119320278553875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4744080629651520742810333 1779030236119320278553875)
                      ·
                        rfl

theorem cell23_3464649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 6, 3].length) (baseStart_3464649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464649 prefixEnd_3464649 := by exact prefixLift 3464649
  have htrace : WordTrace (prefixWord ++ tailWord_3464649) baseStart_3464649 baseEnd_3464649 := by
    simpa [prefixWord, tailWord_3464649, baseEnd_3464649] using wordTrace_append hprefix tailTrace_3464649
  have hstable : (prefixWord ++ tailWord_3464649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464649).length < 2 ^ (prefixWord ++ tailWord_3464649).sum := by decide
  have hdescent : baseEnd_3464649 < baseStart_3464649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464656 : List Nat := [2, 1, 1, 1, 1, 2, 2, 7, 2, 4]
def baseStart_3464656 : Nat := 118140960795 + 3464656 * 2 ^ 59
def prefixEnd_3464656 : Nat := 4983230072969 + 3 ^ 40 * 3464656 * 2
def baseEnd_3464656 : Nat := 593011276827967250388781

theorem tailTrace_3464656 : CollatzResearch.WordTrace tailWord_3464656 prefixEnd_3464656 593011276827967250388781 := by
  unfold tailWord_3464656
  simp only [CollatzResearch.WordTrace]
  refine ⟨63183192868075251490490911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84244257157433668653987881 63183192868075251490490911)
  ·
    refine ⟨94774789302112877235736367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63183192868075251490490911 94774789302112877235736367)
    ·
      refine ⟨142162183953169315853604551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94774789302112877235736367 142162183953169315853604551)
      ·
        refine ⟨213243275929753973780406827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142162183953169315853604551 213243275929753973780406827)
        ·
          refine ⟨319864913894630960670610241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213243275929753973780406827 319864913894630960670610241)
          ·
            refine ⟨239898685420973220502957681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319864913894630960670610241 239898685420973220502957681)
            ·
              refine ⟨179924014065729915377218261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239898685420973220502957681 179924014065729915377218261)
              ·
                refine ⟨4216969079665544891653553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 179924014065729915377218261 4216969079665544891653553)
                ·
                  refine ⟨3162726809749158668740165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4216969079665544891653553 3162726809749158668740165)
                  ·
                    refine ⟨593011276827967250388781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3162726809749158668740165 593011276827967250388781)
                    ·
                      rfl

theorem cell23_3464656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 2, 4].length) (baseStart_3464656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464656 prefixEnd_3464656 := by exact prefixLift 3464656
  have htrace : WordTrace (prefixWord ++ tailWord_3464656) baseStart_3464656 baseEnd_3464656 := by
    simpa [prefixWord, tailWord_3464656, baseEnd_3464656] using wordTrace_append hprefix tailTrace_3464656
  have hstable : (prefixWord ++ tailWord_3464656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464656).length < 2 ^ (prefixWord ++ tailWord_3464656).sum := by decide
  have hdescent : baseEnd_3464656 < baseStart_3464656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464660 : List Nat := [2, 4, 1, 2, 3, 2, 1, 2, 1, 5]
def baseStart_3464660 : Nat := 118140960795 + 3464660 * 2 ^ 59
def prefixEnd_3464660 : Nat := 4983230072969 + 3 ^ 40 * 3464660 * 2
def baseEnd_3464660 : Nat := 593011961468839911838775

theorem tailTrace_3464660 : CollatzResearch.WordTrace tailWord_3464660 prefixEnd_3464660 593011961468839911838775 := by
  unfold tailWord_3464660
  simp only [CollatzResearch.WordTrace]
  refine ⟨63183265814068005832063717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84244354418757341109418289 63183265814068005832063717)
  ·
    refine ⟨11846862340137751093511947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63183265814068005832063717 11846862340137751093511947)
    ·
      refine ⟨17770293510206626640267921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11846862340137751093511947 17770293510206626640267921)
      ·
        refine ⟨13327720132654969980200941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17770293510206626640267921 13327720132654969980200941)
        ·
          refine ⟨4997895049745613742575353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13327720132654969980200941 4997895049745613742575353)
          ·
            refine ⟨3748421287309210306931515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4997895049745613742575353 3748421287309210306931515)
            ·
              refine ⟨5622631930963815460397273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3748421287309210306931515 5622631930963815460397273)
              ·
                refine ⟨4216973948222861595297955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5622631930963815460397273 4216973948222861595297955)
                ·
                  refine ⟨6325460922334292392946933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4216973948222861595297955 6325460922334292392946933)
                  ·
                    refine ⟨593011961468839911838775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6325460922334292392946933 593011961468839911838775)
                    ·
                      rfl

theorem cell23_3464660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_3464660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464660 prefixEnd_3464660 := by exact prefixLift 3464660
  have htrace : WordTrace (prefixWord ++ tailWord_3464660) baseStart_3464660 baseEnd_3464660 := by
    simpa [prefixWord, tailWord_3464660, baseEnd_3464660] using wordTrace_append hprefix tailTrace_3464660
  have hstable : (prefixWord ++ tailWord_3464660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464660).length < 2 ^ (prefixWord ++ tailWord_3464660).sum := by decide
  have hdescent : baseEnd_3464660 < baseStart_3464660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464663 : List Nat := [1, 1, 3, 2, 1, 1, 1, 6, 3, 2, 2]
def baseStart_3464663 : Nat := 118140960795 + 3464663 * 2 ^ 59
def prefixEnd_3464663 : Nat := 4983230072969 + 3 ^ 40 * 3464663 * 2
def baseEnd_3464663 : Nat := 1779037424848483223778811

theorem tailTrace_3464663 : CollatzResearch.WordTrace tailWord_3464663 prefixEnd_3464663 1779037424848483223778811 := by
  unfold tailWord_3464663
  simp only [CollatzResearch.WordTrace]
  refine ⟨126366641047125143176486643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84244427364750095450991095 126366641047125143176486643)
  ·
    refine ⟨189549961570687714764729965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126366641047125143176486643 189549961570687714764729965)
    ·
      refine ⟨71081235589007893036773737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189549961570687714764729965 71081235589007893036773737)
      ·
        refine ⟨53310926691755919777580303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71081235589007893036773737 53310926691755919777580303)
        ·
          refine ⟨79966390037633879666370455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53310926691755919777580303 79966390037633879666370455)
          ·
            refine ⟨119949585056450819499555683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79966390037633879666370455 119949585056450819499555683)
            ·
              refine ⟨179924377584676229249333525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119949585056450819499555683 179924377584676229249333525)
              ·
                refine ⟨8433955199281698246062509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 179924377584676229249333525 8433955199281698246062509)
                ·
                  refine ⟨3162733199730636842273441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8433955199281698246062509 3162733199730636842273441)
                  ·
                    refine ⟨2372049899797977631705081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3162733199730636842273441 2372049899797977631705081)
                    ·
                      refine ⟨1779037424848483223778811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2372049899797977631705081 1779037424848483223778811)
                      ·
                        rfl

theorem cell23_3464663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3, 2, 2].length) (baseStart_3464663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464663 prefixEnd_3464663 := by exact prefixLift 3464663
  have htrace : WordTrace (prefixWord ++ tailWord_3464663) baseStart_3464663 baseEnd_3464663 := by
    simpa [prefixWord, tailWord_3464663, baseEnd_3464663] using wordTrace_append hprefix tailTrace_3464663
  have hstable : (prefixWord ++ tailWord_3464663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464663).length < 2 ^ (prefixWord ++ tailWord_3464663).sum := by decide
  have hdescent : baseEnd_3464663 < baseStart_3464663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464690 : List Nat := [3, 2, 1, 4, 1, 2, 2, 2, 2, 4]
def baseStart_3464690 : Nat := 118140960795 + 3464690 * 2 ^ 59
def prefixEnd_3464690 : Nat := 4983230072969 + 3 ^ 40 * 3464690 * 2
def baseEnd_3464690 : Nat := 593017096275384872713729

theorem tailTrace_3464690 : CollatzResearch.WordTrace tailWord_3464690 prefixEnd_3464690 593017096275384872713729 := by
  unfold tailWord_3464690
  simp only [CollatzResearch.WordTrace]
  refine ⟨31591906454506831696929881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84245083878684884525146349 31591906454506831696929881)
  ·
    refine ⟨23693929840880123772697411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31591906454506831696929881 23693929840880123772697411)
    ·
      refine ⟨35540894761320185659046117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23693929840880123772697411 35540894761320185659046117)
      ·
        refine ⟨6663917767747534811071147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35540894761320185659046117 6663917767747534811071147)
        ·
          refine ⟨9995876651621302216606721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6663917767747534811071147 9995876651621302216606721)
          ·
            refine ⟨7496907488715976662455041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9995876651621302216606721 7496907488715976662455041)
            ·
              refine ⟨5622680616536982496841281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7496907488715976662455041 5622680616536982496841281)
              ·
                refine ⟨4217010462402736872630961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5622680616536982496841281 4217010462402736872630961)
                ·
                  refine ⟨3162757846802052654473221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4217010462402736872630961 3162757846802052654473221)
                  ·
                    refine ⟨593017096275384872713729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3162757846802052654473221 593017096275384872713729)
                    ·
                      rfl

theorem cell23_3464690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_3464690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464690 prefixEnd_3464690 := by exact prefixLift 3464690
  have htrace : WordTrace (prefixWord ++ tailWord_3464690) baseStart_3464690 baseEnd_3464690 := by
    simpa [prefixWord, tailWord_3464690, baseEnd_3464690] using wordTrace_append hprefix tailTrace_3464690
  have hstable : (prefixWord ++ tailWord_3464690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464690).length < 2 ^ (prefixWord ++ tailWord_3464690).sum := by decide
  have hdescent : baseEnd_3464690 < baseStart_3464690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464709 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 1, 4, 5]
def baseStart_3464709 : Nat := 118140960795 + 3464709 * 2 ^ 59
def prefixEnd_3464709 : Nat := 4983230072969 + 3 ^ 40 * 3464709 * 2
def baseEnd_3464709 : Nat := 1779061044958590043803599

theorem tailTrace_3464709 : CollatzResearch.WordTrace tailWord_3464709 prefixEnd_3464709 1779061044958590043803599 := by
  unfold tailWord_3464709
  simp only [CollatzResearch.WordTrace]
  refine ⟨126368318804958493032661181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84245545869972328688440787 126368318804958493032661181)
  ·
    refine ⟨47388119551859434887247943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126368318804958493032661181 47388119551859434887247943)
    ·
      refine ⟨71082179327789152330871915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47388119551859434887247943 71082179327789152330871915)
      ·
        refine ⟨106623268991683728496307873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71082179327789152330871915 106623268991683728496307873)
        ·
          refine ⟨79967451743762796372230905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106623268991683728496307873 79967451743762796372230905)
          ·
            refine ⟨59975588807822097279173179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79967451743762796372230905 59975588807822097279173179)
            ·
              refine ⟨89963383211733145918759769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59975588807822097279173179 89963383211733145918759769)
              ·
                refine ⟨67472537408799859439069827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89963383211733145918759769 67472537408799859439069827)
                ·
                  refine ⟨101208806113199789158604741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67472537408799859439069827 101208806113199789158604741)
                  ·
                    refine ⟨18976651146224960467238389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101208806113199789158604741 18976651146224960467238389)
                    ·
                      refine ⟨1779061044958590043803599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18976651146224960467238389 1779061044958590043803599)
                      ·
                        rfl

theorem cell23_3464709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_3464709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464709 prefixEnd_3464709 := by exact prefixLift 3464709
  have htrace : WordTrace (prefixWord ++ tailWord_3464709) baseStart_3464709 baseEnd_3464709 := by
    simpa [prefixWord, tailWord_3464709, baseEnd_3464709] using wordTrace_append hprefix tailTrace_3464709
  have hstable : (prefixWord ++ tailWord_3464709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464709).length < 2 ^ (prefixWord ++ tailWord_3464709).sum := by decide
  have hdescent : baseEnd_3464709 < baseStart_3464709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464713 : List Nat := [1, 2, 1, 1, 3, 1, 3, 5, 2, 1, 3]
def baseStart_3464713 : Nat := 118140960795 + 3464713 * 2 ^ 59
def prefixEnd_3464713 : Nat := 4983230072969 + 3 ^ 40 * 3464713 * 2
def baseEnd_3464713 : Nat := 1779063098881208028153581

theorem tailTrace_3464713 : CollatzResearch.WordTrace tailWord_3464713 prefixEnd_3464713 1779063098881208028153581 := by
  unfold tailWord_3464713
  simp only [CollatzResearch.WordTrace]
  refine ⟨126368464696944001715806793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84245643131296001143871195 126368464696944001715806793)
  ·
    refine ⟨94776348522708001286855095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126368464696944001715806793 94776348522708001286855095)
    ·
      refine ⟨142164522784062001930282643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94776348522708001286855095 142164522784062001930282643)
      ·
        refine ⟨213246784176093002895423965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142164522784062001930282643 213246784176093002895423965)
        ·
          refine ⟨79967544066034876085783987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213246784176093002895423965 79967544066034876085783987)
          ·
            refine ⟨119951316099052314128675981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79967544066034876085783987 119951316099052314128675981)
            ·
              refine ⟨44981743537144617798253493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119951316099052314128675981 44981743537144617798253493)
              ·
                refine ⟨4217038456607307918586265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44981743537144617798253493 4217038456607307918586265)
                ·
                  refine ⟨3162778842455480938939699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4217038456607307918586265 3162778842455480938939699)
                  ·
                    refine ⟨4744168263683221408409549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3162778842455480938939699 4744168263683221408409549)
                    ·
                      refine ⟨1779063098881208028153581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4744168263683221408409549 1779063098881208028153581)
                      ·
                        rfl

theorem cell23_3464713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2, 1, 3].length) (baseStart_3464713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464713 prefixEnd_3464713 := by exact prefixLift 3464713
  have htrace : WordTrace (prefixWord ++ tailWord_3464713) baseStart_3464713 baseEnd_3464713 := by
    simpa [prefixWord, tailWord_3464713, baseEnd_3464713] using wordTrace_append hprefix tailTrace_3464713
  have hstable : (prefixWord ++ tailWord_3464713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464713).length < 2 ^ (prefixWord ++ tailWord_3464713).sum := by decide
  have hdescent : baseEnd_3464713 < baseStart_3464713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464719 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 4]
def baseStart_3464719 : Nat := 118140960795 + 3464719 * 2 ^ 59
def prefixEnd_3464719 : Nat := 4983230072969 + 3 ^ 40 * 3464719 * 2
def baseEnd_3464719 : Nat := 1779066179765135004678553

theorem tailTrace_3464719 : CollatzResearch.WordTrace tailWord_3464719 prefixEnd_3464719 1779066179765135004678553 := by
  unfold tailWord_3464719
  simp only [CollatzResearch.WordTrace]
  refine ⟨126368683534922264740525211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84245789023281509827016807 126368683534922264740525211)
  ·
    refine ⟨189553025302383397110787817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126368683534922264740525211 189553025302383397110787817)
    ·
      refine ⟨142164768976787547833090863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189553025302383397110787817 142164768976787547833090863)
      ·
        refine ⟨213247153465181321749636295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142164768976787547833090863 213247153465181321749636295)
        ·
          refine ⟨319870730197771982624454443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213247153465181321749636295 319870730197771982624454443)
          ·
            refine ⟨479806095296657973936681665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319870730197771982624454443 479806095296657973936681665)
            ·
              refine ⟨359854571472493480452511249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 479806095296657973936681665 359854571472493480452511249)
              ·
                refine ⟨269890928604370110339383437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359854571472493480452511249 269890928604370110339383437)
                ·
                  refine ⟨101209098226638791377268789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269890928604370110339383437 101209098226638791377268789)
                  ·
                    refine ⟨9488352958747386691618949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101209098226638791377268789 9488352958747386691618949)
                    ·
                      refine ⟨1779066179765135004678553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9488352958747386691618949 1779066179765135004678553)
                      ·
                        rfl

theorem cell23_3464719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 4].length) (baseStart_3464719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464719 prefixEnd_3464719 := by exact prefixLift 3464719
  have htrace : WordTrace (prefixWord ++ tailWord_3464719) baseStart_3464719 baseEnd_3464719 := by
    simpa [prefixWord, tailWord_3464719, baseEnd_3464719] using wordTrace_append hprefix tailTrace_3464719
  have hstable : (prefixWord ++ tailWord_3464719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464719).length < 2 ^ (prefixWord ++ tailWord_3464719).sum := by decide
  have hdescent : baseEnd_3464719 < baseStart_3464719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464723 : List Nat := [1, 1, 1, 2, 1, 6, 2, 1, 3, 3, 2]
def baseStart_3464723 : Nat := 118140960795 + 3464723 * 2 ^ 59
def prefixEnd_3464723 : Nat := 4983230072969 + 3 ^ 40 * 3464723 * 2
def baseEnd_3464723 : Nat := 1779068233687752989028535

theorem tailTrace_3464723 : CollatzResearch.WordTrace tailWord_3464723 prefixEnd_3464723 1779068233687752989028535 := by
  unfold tailWord_3464723
  simp only [CollatzResearch.WordTrace]
  refine ⟨126368829426907773423670823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84245886284605182282447215 126368829426907773423670823)
  ·
    refine ⟨189553244140361660135506235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126368829426907773423670823 189553244140361660135506235)
    ·
      refine ⟨284329866210542490203259353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189553244140361660135506235 284329866210542490203259353)
      ·
        refine ⟨213247399657906867652444515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284329866210542490203259353 213247399657906867652444515)
        ·
          refine ⟨319871099486860301478666773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213247399657906867652444515 319871099486860301478666773)
          ·
            refine ⟨14993957788446576631812505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 319871099486860301478666773 14993957788446576631812505)
            ·
              refine ⟨11245468341334932473859379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14993957788446576631812505 11245468341334932473859379)
              ·
                refine ⟨16868202512002398710789069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11245468341334932473859379 16868202512002398710789069)
                ·
                  refine ⟨6325575942000899516545901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16868202512002398710789069 6325575942000899516545901)
                  ·
                    refine ⟨2372090978250337318704713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6325575942000899516545901 2372090978250337318704713)
                    ·
                      refine ⟨1779068233687752989028535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2372090978250337318704713 1779068233687752989028535)
                      ·
                        rfl

theorem cell23_3464723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 3, 2].length) (baseStart_3464723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464723 prefixEnd_3464723 := by exact prefixLift 3464723
  have htrace : WordTrace (prefixWord ++ tailWord_3464723) baseStart_3464723 baseEnd_3464723 := by
    simpa [prefixWord, tailWord_3464723, baseEnd_3464723] using wordTrace_append hprefix tailTrace_3464723
  have hstable : (prefixWord ++ tailWord_3464723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464723).length < 2 ^ (prefixWord ++ tailWord_3464723).sum := by decide
  have hdescent : baseEnd_3464723 < baseStart_3464723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464729 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 6, 6]
def baseStart_3464729 : Nat := 118140960795 + 3464729 * 2 ^ 59
def prefixEnd_3464729 : Nat := 4983230072969 + 3 ^ 40 * 3464729 * 2
def baseEnd_3464729 : Nat := 593023771523893321851169

theorem tailTrace_3464729 : CollatzResearch.WordTrace tailWord_3464729 prefixEnd_3464729 593023771523893321851169 := by
  unfold tailWord_3464729
  simp only [CollatzResearch.WordTrace]
  refine ⟨126369048264886036448389241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84246032176590690965592827 126369048264886036448389241)
  ·
    refine ⟨94776786198664527336291931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126369048264886036448389241 94776786198664527336291931)
    ·
      refine ⟨142165179297996791004437897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94776786198664527336291931 142165179297996791004437897)
      ·
        refine ⟨106623884473497593253328423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142165179297996791004437897 106623884473497593253328423)
        ·
          refine ⟨159935826710246389879992635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106623884473497593253328423 159935826710246389879992635)
          ·
            refine ⟨239903740065369584819988953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159935826710246389879992635 239903740065369584819988953)
            ·
              refine ⟨179927805049027188614991715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239903740065369584819988953 179927805049027188614991715)
              ·
                refine ⟨269891707573540782922487573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179927805049027188614991715 269891707573540782922487573)
                ·
                  refine ⟨12651173792509724199491605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 269891707573540782922487573 12651173792509724199491605)
                  ·
                    refine ⟨593023771523893321851169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12651173792509724199491605 593023771523893321851169)
                    ·
                      rfl

theorem cell23_3464729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 6].length) (baseStart_3464729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464729 prefixEnd_3464729 := by exact prefixLift 3464729
  have htrace : WordTrace (prefixWord ++ tailWord_3464729) baseStart_3464729 baseEnd_3464729 := by
    simpa [prefixWord, tailWord_3464729, baseEnd_3464729] using wordTrace_append hprefix tailTrace_3464729
  have hstable : (prefixWord ++ tailWord_3464729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464729).length < 2 ^ (prefixWord ++ tailWord_3464729).sum := by decide
  have hdescent : baseEnd_3464729 < baseStart_3464729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464746 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 4, 6]
def baseStart_3464746 : Nat := 118140960795 + 3464746 * 2 ^ 59
def prefixEnd_3464746 : Nat := 4983230072969 + 3 ^ 40 * 3464746 * 2
def baseEnd_3464746 : Nat := 593026681247602133013643

theorem tailTrace_3464746 : CollatzResearch.WordTrace tailWord_3464746 prefixEnd_3464746 593026681247602133013643 := by
  unfold tailWord_3464746
  simp only [CollatzResearch.WordTrace]
  refine ⟨31592417076456112087939523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84246445537216298901172061 31592417076456112087939523)
  ·
    refine ⟨47388625614684168131909285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31592417076456112087939523 47388625614684168131909285)
    ·
      refine ⟨8885367302753281524732991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47388625614684168131909285 8885367302753281524732991)
      ·
        refine ⟨13328050954129922287099487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8885367302753281524732991 13328050954129922287099487)
        ·
          refine ⟨19992076431194883430649231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13328050954129922287099487 19992076431194883430649231)
          ·
            refine ⟨29988114646792325145973847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19992076431194883430649231 29988114646792325145973847)
            ·
              refine ⟨44982171970188487718960771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29988114646792325145973847 44982171970188487718960771)
              ·
                refine ⟨67473257955282731578441157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44982171970188487718960771 67473257955282731578441157)
                ·
                  refine ⟨12651235866615512170957717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67473257955282731578441157 12651235866615512170957717)
                  ·
                    refine ⟨593026681247602133013643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12651235866615512170957717 593026681247602133013643)
                    ·
                      rfl

theorem cell23_3464746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_3464746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464746 prefixEnd_3464746 := by exact prefixLift 3464746
  have htrace : WordTrace (prefixWord ++ tailWord_3464746) baseStart_3464746 baseEnd_3464746 := by
    simpa [prefixWord, tailWord_3464746, baseEnd_3464746] using wordTrace_append hprefix tailTrace_3464746
  have hstable : (prefixWord ++ tailWord_3464746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464746).length < 2 ^ (prefixWord ++ tailWord_3464746).sum := by decide
  have hdescent : baseEnd_3464746 < baseStart_3464746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464816 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 7]
def baseStart_3464816 : Nat := 118140960795 + 3464816 * 2 ^ 59
def prefixEnd_3464816 : Nat := 4983230072969 + 3 ^ 40 * 3464816 * 2
def baseEnd_3464816 : Nat := 1779115987388621125165607

theorem tailTrace_3464816 : CollatzResearch.WordTrace tailWord_3464816 prefixEnd_3464816 1779115987388621125165607 := by
  unfold tailWord_3464816
  simp only [CollatzResearch.WordTrace]
  refine ⟨63186110707785425153403151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84248147610380566871204201 63186110707785425153403151)
  ·
    refine ⟨94779166061678137730104727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63186110707785425153403151 94779166061678137730104727)
    ·
      refine ⟨142168749092517206595157091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94779166061678137730104727 142168749092517206595157091)
      ·
        refine ⟨213253123638775809892735637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142168749092517206595157091 213253123638775809892735637)
        ·
          refine ⟨9996240170567616088721983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 213253123638775809892735637 9996240170567616088721983)
          ·
            refine ⟨14994360255851424133082975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9996240170567616088721983 14994360255851424133082975)
            ·
              refine ⟨22491540383777136199624463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14994360255851424133082975 22491540383777136199624463)
              ·
                refine ⟨33737310575665704299436695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22491540383777136199624463 33737310575665704299436695)
                ·
                  refine ⟨50605965863498556449155043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33737310575665704299436695 50605965863498556449155043)
                  ·
                    refine ⟨75908948795247834673732565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50605965863498556449155043 75908948795247834673732565)
                    ·
                      refine ⟨1779115987388621125165607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 75908948795247834673732565 1779115987388621125165607)
                      ·
                        rfl

theorem cell23_3464816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 7].length) (baseStart_3464816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464816 prefixEnd_3464816 := by exact prefixLift 3464816
  have htrace : WordTrace (prefixWord ++ tailWord_3464816) baseStart_3464816 baseEnd_3464816 := by
    simpa [prefixWord, tailWord_3464816, baseEnd_3464816] using wordTrace_append hprefix tailTrace_3464816
  have hstable : (prefixWord ++ tailWord_3464816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464816).length < 2 ^ (prefixWord ++ tailWord_3464816).sum := by decide
  have hdescent : baseEnd_3464816 < baseStart_3464816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464821 : List Nat := [1, 3, 4, 2, 1, 3, 2, 1, 2, 2, 2]
def baseStart_3464821 : Nat := 118140960795 + 3464821 * 2 ^ 59
def prefixEnd_3464821 : Nat := 4983230072969 + 3 ^ 40 * 3464821 * 2
def baseEnd_3464821 : Nat := 1779118554791893605603085

theorem tailTrace_3464821 : CollatzResearch.WordTrace tailWord_3464821 prefixEnd_3464821 1779118554791893605603085 := by
  unfold tailWord_3464821
  simp only [CollatzResearch.WordTrace]
  refine ⟨126372403780552736160738317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84248269187035157440492211 126372403780552736160738317)
  ·
    refine ⟨47389651417707276060276869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126372403780552736160738317 47389651417707276060276869)
    ·
      refine ⟨8885559640820114261301913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47389651417707276060276869 8885559640820114261301913)
      ·
        refine ⟨6664169730615085695976435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8885559640820114261301913 6664169730615085695976435)
        ·
          refine ⟨9996254595922628543964653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6664169730615085695976435 9996254595922628543964653)
          ·
            refine ⟨3748595473470985703986745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9996254595922628543964653 3748595473470985703986745)
            ·
              refine ⟨2811446605103239277990059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3748595473470985703986745 2811446605103239277990059)
              ·
                refine ⟨4217169907654858916985089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2811446605103239277990059 4217169907654858916985089)
                ·
                  refine ⟨3162877430741144187738817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4217169907654858916985089 3162877430741144187738817)
                  ·
                    refine ⟨2372158073055858140804113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3162877430741144187738817 2372158073055858140804113)
                    ·
                      refine ⟨1779118554791893605603085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2372158073055858140804113 1779118554791893605603085)
                      ·
                        rfl

theorem cell23_3464821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_3464821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464821 prefixEnd_3464821 := by exact prefixLift 3464821
  have htrace : WordTrace (prefixWord ++ tailWord_3464821) baseStart_3464821 baseEnd_3464821 := by
    simpa [prefixWord, tailWord_3464821, baseEnd_3464821] using wordTrace_append hprefix tailTrace_3464821
  have hstable : (prefixWord ++ tailWord_3464821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464821).length < 2 ^ (prefixWord ++ tailWord_3464821).sum := by decide
  have hdescent : baseEnd_3464821 < baseStart_3464821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464826 : List Nat := [3, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4]
def baseStart_3464826 : Nat := 118140960795 + 3464826 * 2 ^ 59
def prefixEnd_3464826 : Nat := 4983230072969 + 3 ^ 40 * 3464826 * 2
def baseEnd_3464826 : Nat := 1779121122195166086040561

theorem tailTrace_3464826 : CollatzResearch.WordTrace tailWord_3464826 prefixEnd_3464826 1779121122195166086040561 := by
  unfold tailWord_3464826
  simp only [CollatzResearch.WordTrace]
  refine ⟨31593146536383655503667583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84248390763689748009780221 31593146536383655503667583)
  ·
    refine ⟨47389719804575483255501375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31593146536383655503667583 47389719804575483255501375)
    ·
      refine ⟨71084579706863224883252063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47389719804575483255501375 71084579706863224883252063)
      ·
        refine ⟨106626869560294837324878095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71084579706863224883252063 106626869560294837324878095)
        ·
          refine ⟨159940304340442255987317143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106626869560294837324878095 159940304340442255987317143)
          ·
            refine ⟨239910456510663383980975715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159940304340442255987317143 239910456510663383980975715)
            ·
              refine ⟨359865684765995075971463573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239910456510663383980975715 359865684765995075971463573)
              ·
                refine ⟨16868703973406019186162355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 359865684765995075971463573 16868703973406019186162355)
                ·
                  refine ⟨25303055960109028779243533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16868703973406019186162355 25303055960109028779243533)
                  ·
                    refine ⟨9488645985040885792216325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25303055960109028779243533 9488645985040885792216325)
                    ·
                      refine ⟨1779121122195166086040561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9488645985040885792216325 1779121122195166086040561)
                      ·
                        rfl

theorem cell23_3464826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_3464826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464826 prefixEnd_3464826 := by exact prefixLift 3464826
  have htrace : WordTrace (prefixWord ++ tailWord_3464826) baseStart_3464826 baseEnd_3464826 := by
    simpa [prefixWord, tailWord_3464826, baseEnd_3464826] using wordTrace_append hprefix tailTrace_3464826
  have hstable : (prefixWord ++ tailWord_3464826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464826).length < 2 ^ (prefixWord ++ tailWord_3464826).sum := by decide
  have hdescent : baseEnd_3464826 < baseStart_3464826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464843 : List Nat := [1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 4]
def baseStart_3464843 : Nat := 118140960795 + 3464843 * 2 ^ 59
def prefixEnd_3464843 : Nat := 4983230072969 + 3 ^ 40 * 3464843 * 2
def baseEnd_3464843 : Nat := 1779129851366292519527983

theorem tailTrace_3464843 : CollatzResearch.WordTrace tailWord_3464843 prefixEnd_3464843 1779129851366292519527983 := by
  unfold tailWord_3464843
  simp only [CollatzResearch.WordTrace]
  refine ⟨126373206186473033918039183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84248804124315355945359455 126373206186473033918039183)
  ·
    refine ⟨189559809279709550877058775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126373206186473033918039183 189559809279709550877058775)
    ·
      refine ⟨284339713919564326315588163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189559809279709550877058775 284339713919564326315588163)
      ·
        refine ⟨426509570879346489473382245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284339713919564326315588163 426509570879346489473382245)
        ·
          refine ⟨79970544539877466776259171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 426509570879346489473382245 79970544539877466776259171)
          ·
            refine ⟨119955816809816200164388757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79970544539877466776259171 119955816809816200164388757)
            ·
              refine ⟨5622928912960134382705723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 119955816809816200164388757 5622928912960134382705723)
              ·
                refine ⟨8434393369440201574058585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5622928912960134382705723 8434393369440201574058585)
                ·
                  refine ⟨6325795027080151180543939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8434393369440201574058585 6325795027080151180543939)
                  ·
                    refine ⟨9488692540620226770815909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6325795027080151180543939 9488692540620226770815909)
                    ·
                      refine ⟨1779129851366292519527983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9488692540620226770815909 1779129851366292519527983)
                      ·
                        rfl

theorem cell23_3464843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 4].length) (baseStart_3464843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464843 prefixEnd_3464843 := by exact prefixLift 3464843
  have htrace : WordTrace (prefixWord ++ tailWord_3464843) baseStart_3464843 baseEnd_3464843 := by
    simpa [prefixWord, tailWord_3464843, baseEnd_3464843] using wordTrace_append hprefix tailTrace_3464843
  have hstable : (prefixWord ++ tailWord_3464843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464843).length < 2 ^ (prefixWord ++ tailWord_3464843).sum := by decide
  have hdescent : baseEnd_3464843 < baseStart_3464843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464910 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3]
def baseStart_3464910 : Nat := 118140960795 + 3464910 * 2 ^ 59
def prefixEnd_3464910 : Nat := 4983230072969 + 3 ^ 40 * 3464910 * 2
def baseEnd_3464910 : Nat := 1779164254570143757390175

theorem tailTrace_3464910 : CollatzResearch.WordTrace tailWord_3464910 prefixEnd_3464910 1779164254570143757390175 := by
  unfold tailWord_3464910
  simp only [CollatzResearch.WordTrace]
  refine ⟨15796956234653788045091023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84250433251486869573818789 15796956234653788045091023)
  ·
    refine ⟨23695434351980682067636535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15796956234653788045091023 23695434351980682067636535)
    ·
      refine ⟨35543151527971023101454803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23695434351980682067636535 35543151527971023101454803)
      ·
        refine ⟨53314727291956534652182205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35543151527971023101454803 53314727291956534652182205)
        ·
          refine ⟨19993022734483700494568327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53314727291956534652182205 19993022734483700494568327)
          ·
            refine ⟨29989534101725550741852491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19993022734483700494568327 29989534101725550741852491)
            ·
              refine ⟨44984301152588326112778737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29989534101725550741852491 44984301152588326112778737)
              ·
                refine ⟨33738225864441244584584053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44984301152588326112778737 33738225864441244584584053)
                ·
                  refine ⟨3162958674791366679804755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33738225864441244584584053 3162958674791366679804755)
                  ·
                    refine ⟨4744438012187050019707133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3162958674791366679804755 4744438012187050019707133)
                    ·
                      refine ⟨1779164254570143757390175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4744438012187050019707133 1779164254570143757390175)
                      ·
                        rfl

theorem cell23_3464910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_3464910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464910 prefixEnd_3464910 := by exact prefixLift 3464910
  have htrace : WordTrace (prefixWord ++ tailWord_3464910) baseStart_3464910 baseEnd_3464910 := by
    simpa [prefixWord, tailWord_3464910, baseEnd_3464910] using wordTrace_append hprefix tailTrace_3464910
  have hstable : (prefixWord ++ tailWord_3464910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464910).length < 2 ^ (prefixWord ++ tailWord_3464910).sum := by decide
  have hdescent : baseEnd_3464910 < baseStart_3464910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464920 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 4, 3, 2]
def baseStart_3464920 : Nat := 118140960795 + 3464920 * 2 ^ 59
def prefixEnd_3464920 : Nat := 4983230072969 + 3 ^ 40 * 3464920 * 2
def baseEnd_3464920 : Nat := 1779169389376688718265129

theorem tailTrace_3464920 : CollatzResearch.WordTrace tailWord_3464920 prefixEnd_3464920 1779169389376688718265129 := by
  unfold tailWord_3464920
  simp only [CollatzResearch.WordTrace]
  refine ⟨63188007303597038034296107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84250676404796050712394809 63188007303597038034296107)
  ·
    refine ⟨94782010955395557051444161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63188007303597038034296107 94782010955395557051444161)
    ·
      refine ⟨71086508216546667788583121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94782010955395557051444161 71086508216546667788583121)
      ·
        refine ⟨53314881162410000841437341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71086508216546667788583121 53314881162410000841437341)
        ·
          refine ⟨19993080435903750315539003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53314881162410000841437341 19993080435903750315539003)
          ·
            refine ⟨29989620653855625473308505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19993080435903750315539003 29989620653855625473308505)
            ·
              refine ⟨22492215490391719104981379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29989620653855625473308505 22492215490391719104981379)
              ·
                refine ⟨33738323235587578657472069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22492215490391719104981379 33738323235587578657472069)
                ·
                  refine ⟨6325935606672670998276013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33738323235587578657472069 6325935606672670998276013)
                  ·
                    refine ⟨2372225852502251624353505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6325935606672670998276013 2372225852502251624353505)
                    ·
                      refine ⟨1779169389376688718265129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2372225852502251624353505 1779169389376688718265129)
                      ·
                        rfl

theorem cell23_3464920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 4, 3, 2].length) (baseStart_3464920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464920 prefixEnd_3464920 := by exact prefixLift 3464920
  have htrace : WordTrace (prefixWord ++ tailWord_3464920) baseStart_3464920 baseEnd_3464920 := by
    simpa [prefixWord, tailWord_3464920, baseEnd_3464920] using wordTrace_append hprefix tailTrace_3464920
  have hstable : (prefixWord ++ tailWord_3464920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464920).length < 2 ^ (prefixWord ++ tailWord_3464920).sum := by decide
  have hdescent : baseEnd_3464920 < baseStart_3464920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464927 : List Nat := [1, 1, 2, 3, 2, 2, 1, 6, 1, 1, 3]
def baseStart_3464927 : Nat := 118140960795 + 3464927 * 2 ^ 59
def prefixEnd_3464927 : Nat := 4983230072969 + 3 ^ 40 * 3464927 * 2
def baseEnd_3464927 : Nat := 1779172983741270190877597

theorem tailTrace_3464927 : CollatzResearch.WordTrace tailWord_3464927 prefixEnd_3464927 1779172983741270190877597 := by
  unfold tailWord_3464927
  simp only [CollatzResearch.WordTrace]
  refine ⟨126376269918168716264097035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84250846612112477509398023 126376269918168716264097035)
  ·
    refine ⟨189564404877253074396145553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126376269918168716264097035 189564404877253074396145553)
    ·
      refine ⟨142173303657939805797109165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189564404877253074396145553 142173303657939805797109165)
      ·
        refine ⟨53314988871727427173915937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142173303657939805797109165 53314988871727427173915937)
        ·
          refine ⟨39986241653795570380436953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53314988871727427173915937 39986241653795570380436953)
          ·
            refine ⟨29989681240346677785327715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39986241653795570380436953 29989681240346677785327715)
            ·
              refine ⟨44984521860520016677991573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29989681240346677785327715 44984521860520016677991573)
              ·
                refine ⟨2108649462211875781780855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44984521860520016677991573 2108649462211875781780855)
                ·
                  refine ⟨3162974193317813672671283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2108649462211875781780855 3162974193317813672671283)
                  ·
                    refine ⟨4744461289976720509006925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3162974193317813672671283 4744461289976720509006925)
                    ·
                      refine ⟨1779172983741270190877597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4744461289976720509006925 1779172983741270190877597)
                      ·
                        rfl

theorem cell23_3464927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6, 1, 1, 3].length) (baseStart_3464927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464927 prefixEnd_3464927 := by exact prefixLift 3464927
  have htrace : WordTrace (prefixWord ++ tailWord_3464927) baseStart_3464927 baseEnd_3464927 := by
    simpa [prefixWord, tailWord_3464927, baseEnd_3464927] using wordTrace_append hprefix tailTrace_3464927
  have hstable : (prefixWord ++ tailWord_3464927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464927).length < 2 ^ (prefixWord ++ tailWord_3464927).sum := by decide
  have hdescent : baseEnd_3464927 < baseStart_3464927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464963 : List Nat := [1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 4]
def baseStart_3464963 : Nat := 118140960795 + 3464963 * 2 ^ 59
def prefixEnd_3464963 : Nat := 4983230072969 + 3 ^ 40 * 3464963 * 2
def baseEnd_3464963 : Nat := 1779191469044832050027431

theorem tailTrace_3464963 : CollatzResearch.WordTrace tailWord_3464963 prefixEnd_3464963 1779191469044832050027431 := by
  unfold tailWord_3464963
  simp only [CollatzResearch.WordTrace]
  refine ⟨126377582946038294412407543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84251721964025529608271695 126377582946038294412407543)
  ·
    refine ⟨189566374419057441618611315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126377582946038294412407543 189566374419057441618611315)
    ·
      refine ⟨284349561628586162427916973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189566374419057441618611315 284349561628586162427916973)
      ·
        refine ⟨106631085610719810910468865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284349561628586162427916973 106631085610719810910468865)
        ·
          refine ⟨79973314208039858182851649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106631085610719810910468865 79973314208039858182851649)
          ·
            refine ⟨59979985656029893637138737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79973314208039858182851649 59979985656029893637138737)
            ·
              refine ⟨44984989242022420227854053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59979985656029893637138737 44984989242022420227854053)
              ·
                refine ⟨8434685482879203792722635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44984989242022420227854053 8434685482879203792722635)
                ·
                  refine ⟨12652028224318805689083953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8434685482879203792722635 12652028224318805689083953)
                  ·
                    refine ⟨9489021168239104266812965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12652028224318805689083953 9489021168239104266812965)
                    ·
                      refine ⟨1779191469044832050027431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9489021168239104266812965 1779191469044832050027431)
                      ·
                        rfl

theorem cell23_3464963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_3464963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464963 prefixEnd_3464963 := by exact prefixLift 3464963
  have htrace : WordTrace (prefixWord ++ tailWord_3464963) baseStart_3464963 baseEnd_3464963 := by
    simpa [prefixWord, tailWord_3464963, baseEnd_3464963] using wordTrace_append hprefix tailTrace_3464963
  have hstable : (prefixWord ++ tailWord_3464963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464963).length < 2 ^ (prefixWord ++ tailWord_3464963).sum := by decide
  have hdescent : baseEnd_3464963 < baseStart_3464963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464970 : List Nat := [3, 1, 2, 2, 1, 4, 2, 1, 1, 1, 5]
def baseStart_3464970 : Nat := 118140960795 + 3464970 * 2 ^ 59
def prefixEnd_3464970 : Nat := 4983230072969 + 3 ^ 40 * 3464970 * 2
def baseEnd_3464970 : Nat := 1779195063409413522639899

theorem tailTrace_3464970 : CollatzResearch.WordTrace tailWord_3464970 prefixEnd_3464970 1779195063409413522639899 := by
  unfold tailWord_3464970
  simp only [CollatzResearch.WordTrace]
  refine ⟨31594459564253233651978091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84251892171341956405274909 31594459564253233651978091)
  ·
    refine ⟨47391689346379850477967137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31594459564253233651978091 47391689346379850477967137)
    ·
      refine ⟨35543767009784887858475353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47391689346379850477967137 35543767009784887858475353)
      ·
        refine ⟨26657825257338665893856515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35543767009784887858475353 26657825257338665893856515)
        ·
          refine ⟨39986737886007998840784773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26657825257338665893856515 39986737886007998840784773)
          ·
            refine ⟨7497513353626499782647145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39986737886007998840784773 7497513353626499782647145)
            ·
              refine ⟨5623135015219874836985359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7497513353626499782647145 5623135015219874836985359)
              ·
                refine ⟨8434702522829812255478039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5623135015219874836985359 8434702522829812255478039)
                ·
                  refine ⟨12652053784244718383217059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8434702522829812255478039 12652053784244718383217059)
                  ·
                    refine ⟨18978080676367077574825589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12652053784244718383217059 18978080676367077574825589)
                    ·
                      refine ⟨1779195063409413522639899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18978080676367077574825589 1779195063409413522639899)
                      ·
                        rfl

theorem cell23_3464970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_3464970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464970 prefixEnd_3464970 := by exact prefixLift 3464970
  have htrace : WordTrace (prefixWord ++ tailWord_3464970) baseStart_3464970 baseEnd_3464970 := by
    simpa [prefixWord, tailWord_3464970, baseEnd_3464970] using wordTrace_append hprefix tailTrace_3464970
  have hstable : (prefixWord ++ tailWord_3464970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464970).length < 2 ^ (prefixWord ++ tailWord_3464970).sum := by decide
  have hdescent : baseEnd_3464970 < baseStart_3464970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464978 : List Nat := [3, 2, 4, 1, 1, 2, 3, 2, 1, 1, 3]
def baseStart_3464978 : Nat := 118140960795 + 3464978 * 2 ^ 59
def prefixEnd_3464978 : Nat := 4983230072969 + 3 ^ 40 * 3464978 * 2
def baseEnd_3464978 : Nat := 1779199171254649491339863

theorem tailTrace_3464978 : CollatzResearch.WordTrace tailWord_3464978 prefixEnd_3464978 1779199171254649491339863 := by
  unfold tailWord_3464978
  simp only [CollatzResearch.WordTrace]
  refine ⟨31594532510245987993550897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84252086693989301316135725 31594532510245987993550897)
  ·
    refine ⟨23695899382684490995163173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31594532510245987993550897 23695899382684490995163173)
    ·
      refine ⟨4442981134253342061593095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23695899382684490995163173 4442981134253342061593095)
      ·
        refine ⟨6664471701380013092389643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4442981134253342061593095 6664471701380013092389643)
        ·
          refine ⟨9996707552070019638584465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6664471701380013092389643 9996707552070019638584465)
          ·
            refine ⟨7497530664052514728938349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9996707552070019638584465 7497530664052514728938349)
            ·
              refine ⟨2811573999019693023351881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7497530664052514728938349 2811573999019693023351881)
              ·
                refine ⟨2108680499264769767513911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2811573999019693023351881 2108680499264769767513911)
                ·
                  refine ⟨3163020748897154651270867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2108680499264769767513911 3163020748897154651270867)
                  ·
                    refine ⟨4744531123345731976906301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3163020748897154651270867 4744531123345731976906301)
                    ·
                      refine ⟨1779199171254649491339863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4744531123345731976906301 1779199171254649491339863)
                      ·
                        rfl

theorem cell23_3464978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_3464978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464978 prefixEnd_3464978 := by exact prefixLift 3464978
  have htrace : WordTrace (prefixWord ++ tailWord_3464978) baseStart_3464978 baseEnd_3464978 := by
    simpa [prefixWord, tailWord_3464978, baseEnd_3464978] using wordTrace_append hprefix tailTrace_3464978
  have hstable : (prefixWord ++ tailWord_3464978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464978).length < 2 ^ (prefixWord ++ tailWord_3464978).sum := by decide
  have hdescent : baseEnd_3464978 < baseStart_3464978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3464984 : List Nat := [2, 1, 2, 3, 1, 1, 2, 6, 1, 2, 2]
def baseStart_3464984 : Nat := 118140960795 + 3464984 * 2 ^ 59
def prefixEnd_3464984 : Nat := 4983230072969 + 3 ^ 40 * 3464984 * 2
def baseEnd_3464984 : Nat := 1779202252138576467864835

theorem tailTrace_3464984 : CollatzResearch.WordTrace tailWord_3464984 prefixEnd_3464984 1779202252138576467864835 := by
  unfold tailWord_3464984
  simp only [CollatzResearch.WordTrace]
  refine ⟨63189174439481107499461003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84252232585974809999281337 63189174439481107499461003)
  ·
    refine ⟨94783761659221661249191505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63189174439481107499461003 94783761659221661249191505)
    ·
      refine ⟨71087821244416245936893629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94783761659221661249191505 71087821244416245936893629)
      ·
        refine ⟨26657932966656092226335111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71087821244416245936893629 26657932966656092226335111)
        ·
          refine ⟨39986899449984138339502667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26657932966656092226335111 39986899449984138339502667)
          ·
            refine ⟨59980349174976207509254001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39986899449984138339502667 59980349174976207509254001)
            ·
              refine ⟨44985261881232155631940501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59980349174976207509254001 44985261881232155631940501)
              ·
                refine ⟨2108684150682757295247211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44985261881232155631940501 2108684150682757295247211)
                ·
                  refine ⟨3163026226024135942870817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2108684150682757295247211 3163026226024135942870817)
                  ·
                    refine ⟨2372269669518101957153113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3163026226024135942870817 2372269669518101957153113)
                    ·
                      refine ⟨1779202252138576467864835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2372269669518101957153113 1779202252138576467864835)
                      ·
                        rfl

theorem cell23_3464984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_3464984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3464984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3464984 prefixEnd_3464984 := by exact prefixLift 3464984
  have htrace : WordTrace (prefixWord ++ tailWord_3464984) baseStart_3464984 baseEnd_3464984 := by
    simpa [prefixWord, tailWord_3464984, baseEnd_3464984] using wordTrace_append hprefix tailTrace_3464984
  have hstable : (prefixWord ++ tailWord_3464984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3464984).length < 2 ^ (prefixWord ++ tailWord_3464984).sum := by decide
  have hdescent : baseEnd_3464984 < baseStart_3464984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3464984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465033 : List Nat := [1, 2, 1, 1, 2, 4, 2, 2, 2, 6]
def baseStart_3465033 : Nat := 118140960795 + 3465033 * 2 ^ 59
def prefixEnd_3465033 : Nat := 4983230072969 + 3 ^ 40 * 3465033 * 2
def baseEnd_3465033 : Nat := 593075804230215592050703

theorem tailTrace_3465033 : CollatzResearch.WordTrace tailWord_3465033 prefixEnd_3465033 593075804230215592050703 := by
  unfold tailWord_3465033
  simp only [CollatzResearch.WordTrace]
  refine ⟨126380136055784696367455753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84253424037189797578303835 126380136055784696367455753)
  ·
    refine ⟨94785102041838522275591815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126380136055784696367455753 94785102041838522275591815)
    ·
      refine ⟨142177653062757783413387723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94785102041838522275591815 142177653062757783413387723)
      ·
        refine ⟨213266479594136675120081585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142177653062757783413387723 213266479594136675120081585)
        ·
          refine ⟨159949859695602506340061189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213266479594136675120081585 159949859695602506340061189)
          ·
            refine ⟨29990598692925469938761473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159949859695602506340061189 29990598692925469938761473)
            ·
              refine ⟨22492949019694102454071105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29990598692925469938761473 22492949019694102454071105)
              ·
                refine ⟨16869711764770576840553329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22492949019694102454071105 16869711764770576840553329)
                ·
                  refine ⟨12652283823577932630414997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16869711764770576840553329 12652283823577932630414997)
                  ·
                    refine ⟨593075804230215592050703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12652283823577932630414997 593075804230215592050703)
                    ·
                      rfl

theorem cell23_3465033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 6].length) (baseStart_3465033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465033 prefixEnd_3465033 := by exact prefixLift 3465033
  have htrace : WordTrace (prefixWord ++ tailWord_3465033) baseStart_3465033 baseEnd_3465033 := by
    simpa [prefixWord, tailWord_3465033, baseEnd_3465033] using wordTrace_append hprefix tailTrace_3465033
  have hstable : (prefixWord ++ tailWord_3465033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465033).length < 2 ^ (prefixWord ++ tailWord_3465033).sum := by decide
  have hdescent : baseEnd_3465033 < baseStart_3465033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465040 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 5, 4, 2]
def baseStart_3465040 : Nat := 118140960795 + 3465040 * 2 ^ 59
def prefixEnd_3465040 : Nat := 4983230072969 + 3 ^ 40 * 3465040 * 2
def baseEnd_3465040 : Nat := 1779231007055228248764577

theorem tailTrace_3465040 : CollatzResearch.WordTrace tailWord_3465040 prefixEnd_3465040 1779231007055228248764577 := by
  unfold tailWord_3465040
  simp only [CollatzResearch.WordTrace]
  refine ⟨63190195683379668281480287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84253594244506224375307049 63190195683379668281480287)
  ·
    refine ⟨94785293525069502422220431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63190195683379668281480287 94785293525069502422220431)
    ·
      refine ⟨142177940287604253633330647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94785293525069502422220431 142177940287604253633330647)
      ·
        refine ⟨213266910431406380449995971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142177940287604253633330647 213266910431406380449995971)
        ·
          refine ⟨319900365647109570674993957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213266910431406380449995971 319900365647109570674993957)
          ·
            refine ⟨59981318558833044501561367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 319900365647109570674993957 59981318558833044501561367)
            ·
              refine ⟨89971977838249566752342051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59981318558833044501561367 89971977838249566752342051)
              ·
                refine ⟨134957966757374350128513077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89971977838249566752342051 134957966757374350128513077)
                ·
                  refine ⟨12652309383503845324548101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134957966757374350128513077 12652309383503845324548101)
                  ·
                    refine ⟨2372308009406970998352769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12652309383503845324548101 2372308009406970998352769)
                    ·
                      refine ⟨1779231007055228248764577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2372308009406970998352769 1779231007055228248764577)
                      ·
                        rfl

theorem cell23_3465040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 5, 4, 2].length) (baseStart_3465040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465040 prefixEnd_3465040 := by exact prefixLift 3465040
  have htrace : WordTrace (prefixWord ++ tailWord_3465040) baseStart_3465040 baseEnd_3465040 := by
    simpa [prefixWord, tailWord_3465040, baseEnd_3465040] using wordTrace_append hprefix tailTrace_3465040
  have hstable : (prefixWord ++ tailWord_3465040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465040).length < 2 ^ (prefixWord ++ tailWord_3465040).sum := by decide
  have hdescent : baseEnd_3465040 < baseStart_3465040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465057 : List Nat := [1, 2, 3, 1, 1, 1, 6, 1, 1, 4, 2]
def baseStart_3465057 : Nat := 118140960795 + 3465057 * 2 ^ 59
def prefixEnd_3465057 : Nat := 4983230072969 + 3 ^ 40 * 3465057 * 2
def baseEnd_3465057 : Nat := 1779239736226354682251999

theorem tailTrace_3465057 : CollatzResearch.WordTrace tailWord_3465057 prefixEnd_3465057 1779239736226354682251999 := by
  unfold tailWord_3465057
  simp only [CollatzResearch.WordTrace]
  refine ⟨126381011407697748466329425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84254007605131832310886283 126381011407697748466329425)
  ·
    refine ⟨94785758555773311349747069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126381011407697748466329425 94785758555773311349747069)
    ·
      refine ⟨35544659458414991756155151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94785758555773311349747069 35544659458414991756155151)
      ·
        refine ⟨53316989187622487634232727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35544659458414991756155151 53316989187622487634232727)
        ·
          refine ⟨79975483781433731451349091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53316989187622487634232727 79975483781433731451349091)
          ·
            refine ⟨119963225672150597177023637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79975483781433731451349091 119963225672150597177023637)
            ·
              refine ⟨5623276203382059242672983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 119963225672150597177023637 5623276203382059242672983)
              ·
                refine ⟨8434914305073088864009475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5623276203382059242672983 8434914305073088864009475)
                ·
                  refine ⟨12652371457609633296014213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8434914305073088864009475 12652371457609633296014213)
                  ·
                    refine ⟨2372319648301806243002665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12652371457609633296014213 2372319648301806243002665)
                    ·
                      refine ⟨1779239736226354682251999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2372319648301806243002665 1779239736226354682251999)
                      ·
                        rfl

theorem cell23_3465057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 4, 2].length) (baseStart_3465057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465057 prefixEnd_3465057 := by exact prefixLift 3465057
  have htrace : WordTrace (prefixWord ++ tailWord_3465057) baseStart_3465057 baseEnd_3465057 := by
    simpa [prefixWord, tailWord_3465057, baseEnd_3465057] using wordTrace_append hprefix tailTrace_3465057
  have hstable : (prefixWord ++ tailWord_3465057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465057).length < 2 ^ (prefixWord ++ tailWord_3465057).sum := by decide
  have hdescent : baseEnd_3465057 < baseStart_3465057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465091 : List Nat := [1, 1, 1, 3, 4, 4, 1, 2, 2, 2, 2]
def baseStart_3465091 : Nat := 118140960795 + 3465091 * 2 ^ 59
def prefixEnd_3465091 : Nat := 4983230072969 + 3 ^ 40 * 3465091 * 2
def baseEnd_3465091 : Nat := 1779257194568607549226843

theorem tailTrace_3465091 : CollatzResearch.WordTrace tailWord_3465091 prefixEnd_3465091 1779257194568607549226843 := by
  unfold tailWord_3465091
  simp only [CollatzResearch.WordTrace]
  refine ⟨126382251489574572273067127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84254834326383048182044751 126382251489574572273067127)
  ·
    refine ⟨189573377234361858409600691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126382251489574572273067127 189573377234361858409600691)
    ·
      refine ⟨284360065851542787614401037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189573377234361858409600691 284360065851542787614401037)
      ·
        refine ⟨106635024694328545355400389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284360065851542787614401037 106635024694328545355400389)
        ·
          refine ⟨19994067130186602254137573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106635024694328545355400389 19994067130186602254137573)
          ·
            refine ⟨3748887586909987922650795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19994067130186602254137573 3748887586909987922650795)
            ·
              refine ⟨5623331380364981883976193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3748887586909987922650795 5623331380364981883976193)
              ·
                refine ⟨4217498535273736412982145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5623331380364981883976193 4217498535273736412982145)
                ·
                  refine ⟨3163123901455302309736609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4217498535273736412982145 3163123901455302309736609)
                  ·
                    refine ⟨2372342926091476732302457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3163123901455302309736609 2372342926091476732302457)
                    ·
                      refine ⟨1779257194568607549226843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2372342926091476732302457 1779257194568607549226843)
                      ·
                        rfl

theorem cell23_3465091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2, 2, 2].length) (baseStart_3465091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465091 prefixEnd_3465091 := by exact prefixLift 3465091
  have htrace : WordTrace (prefixWord ++ tailWord_3465091) baseStart_3465091 baseEnd_3465091 := by
    simpa [prefixWord, tailWord_3465091, baseEnd_3465091] using wordTrace_append hprefix tailTrace_3465091
  have hstable : (prefixWord ++ tailWord_3465091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465091).length < 2 ^ (prefixWord ++ tailWord_3465091).sum := by decide
  have hdescent : baseEnd_3465091 < baseStart_3465091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465103 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 5]
def baseStart_3465103 : Nat := 118140960795 + 3465103 * 2 ^ 59
def prefixEnd_3465103 : Nat := 4983230072969 + 3 ^ 40 * 3465103 * 2
def baseEnd_3465103 : Nat := 1779263356336461502276787

theorem tailTrace_3465103 : CollatzResearch.WordTrace tailWord_3465103 prefixEnd_3465103 1779263356336461502276787 := by
  unfold tailWord_3465103
  simp only [CollatzResearch.WordTrace]
  refine ⟨126382689165531098322503963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84255126110354065548335975 126382689165531098322503963)
  ·
    refine ⟨189574033748296647483755945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126382689165531098322503963 189574033748296647483755945)
    ·
      refine ⟨142180525311222485612816959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189574033748296647483755945 142180525311222485612816959)
      ·
        refine ⟨213270787966833728419225439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142180525311222485612816959 213270787966833728419225439)
        ·
          refine ⟨319906181950250592628838159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213270787966833728419225439 319906181950250592628838159)
          ·
            refine ⟨479859272925375888943257239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319906181950250592628838159 479859272925375888943257239)
            ·
              refine ⟨719788909388063833414885859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479859272925375888943257239 719788909388063833414885859)
              ·
                refine ⟨1079683364082095750122328789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 719788909388063833414885859 1079683364082095750122328789)
                ·
                  refine ⟨25305078845674119143492081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1079683364082095750122328789 25305078845674119143492081)
                  ·
                    refine ⟨18978809134255589357619061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25305078845674119143492081 18978809134255589357619061)
                    ·
                      refine ⟨1779263356336461502276787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18978809134255589357619061 1779263356336461502276787)
                      ·
                        rfl

theorem cell23_3465103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 5].length) (baseStart_3465103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465103 prefixEnd_3465103 := by exact prefixLift 3465103
  have htrace : WordTrace (prefixWord ++ tailWord_3465103) baseStart_3465103 baseEnd_3465103 := by
    simpa [prefixWord, tailWord_3465103, baseEnd_3465103] using wordTrace_append hprefix tailTrace_3465103
  have hstable : (prefixWord ++ tailWord_3465103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465103).length < 2 ^ (prefixWord ++ tailWord_3465103).sum := by decide
  have hdescent : baseEnd_3465103 < baseStart_3465103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465108 : List Nat := [2, 4, 2, 1, 1, 3, 3, 1, 2, 2, 2]
def baseStart_3465108 : Nat := 118140960795 + 3465108 * 2 ^ 59
def prefixEnd_3465108 : Nat := 4983230072969 + 3 ^ 40 * 3465108 * 2
def baseEnd_3465108 : Nat := 1779265923739733982714265

theorem tailTrace_3465108 : CollatzResearch.WordTrace tailWord_3465108 prefixEnd_3465108 1779265923739733982714265 := by
  unfold tailWord_3465108
  simp only [CollatzResearch.WordTrace]
  refine ⟨63191435765256492088217989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84255247687008656117623985 63191435765256492088217989)
  ·
    refine ⟨11848394205985592266540873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63191435765256492088217989 11848394205985592266540873)
    ·
      refine ⟨8886295654489194199905655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11848394205985592266540873 8886295654489194199905655)
      ·
        refine ⟨13329443481733791299858483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8886295654489194199905655 13329443481733791299858483)
        ·
          refine ⟨19994165222600686949787725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13329443481733791299858483 19994165222600686949787725)
          ·
            refine ⟨7497811958475257606170397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19994165222600686949787725 7497811958475257606170397)
            ·
              refine ⟨2811679484428221602313899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7497811958475257606170397 2811679484428221602313899)
              ·
                refine ⟨4217519226642332403470849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2811679484428221602313899 4217519226642332403470849)
                ·
                  refine ⟨3163139419981749302603137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4217519226642332403470849 3163139419981749302603137)
                  ·
                    refine ⟨2372354564986311976952353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3163139419981749302603137 2372354564986311976952353)
                    ·
                      refine ⟨1779265923739733982714265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2372354564986311976952353 1779265923739733982714265)
                      ·
                        rfl

theorem cell23_3465108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_3465108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465108 prefixEnd_3465108 := by exact prefixLift 3465108
  have htrace : WordTrace (prefixWord ++ tailWord_3465108) baseStart_3465108 baseEnd_3465108 := by
    simpa [prefixWord, tailWord_3465108, baseEnd_3465108] using wordTrace_append hprefix tailTrace_3465108
  have hstable : (prefixWord ++ tailWord_3465108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465108).length < 2 ^ (prefixWord ++ tailWord_3465108).sum := by decide
  have hdescent : baseEnd_3465108 < baseStart_3465108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465123 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 1, 10]
def baseStart_3465123 : Nat := 118140960795 + 3465123 * 2 ^ 59
def prefixEnd_3465123 : Nat := 4983230072969 + 3 ^ 40 * 3465123 * 2
def baseEnd_3465123 : Nat := 593091208649850474675565

theorem tailTrace_3465123 : CollatzResearch.WordTrace tailWord_3465123 prefixEnd_3465123 593091208649850474675565 := by
  unfold tailWord_3465123
  simp only [CollatzResearch.WordTrace]
  refine ⟨126383418625458641738232023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84255612416972427825488015 126383418625458641738232023)
  ·
    refine ⟨189575127938187962607348035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126383418625458641738232023 189575127938187962607348035)
    ·
      refine ⟨284362691907281943911022053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189575127938187962607348035 284362691907281943911022053)
      ·
        refine ⟨53318004732615364483316635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 284362691907281943911022053 53318004732615364483316635)
        ·
          refine ⟨79977007098923046724974953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53318004732615364483316635 79977007098923046724974953)
          ·
            refine ⟨59982755324192285043731215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79977007098923046724974953 59982755324192285043731215)
            ·
              refine ⟨89974132986288427565596823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59982755324192285043731215 89974132986288427565596823)
              ·
                refine ⟨134961199479432641348395235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89974132986288427565596823 134961199479432641348395235)
                ·
                  refine ⟨202441799219148962022592853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134961199479432641348395235 202441799219148962022592853)
                  ·
                    refine ⟨593091208649850474675565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 202441799219148962022592853 593091208649850474675565)
                    ·
                      rfl

theorem cell23_3465123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 10].length) (baseStart_3465123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465123 prefixEnd_3465123 := by exact prefixLift 3465123
  have htrace : WordTrace (prefixWord ++ tailWord_3465123) baseStart_3465123 baseEnd_3465123 := by
    simpa [prefixWord, tailWord_3465123, baseEnd_3465123] using wordTrace_append hprefix tailTrace_3465123
  have hstable : (prefixWord ++ tailWord_3465123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465123).length < 2 ^ (prefixWord ++ tailWord_3465123).sum := by decide
  have hdescent : baseEnd_3465123 < baseStart_3465123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465247 : List Nat := [1, 1, 2, 4, 1, 2, 2, 2, 4, 4]
def baseStart_3465247 : Nat := 118140960795 + 3465247 * 2 ^ 59
def prefixEnd_3465247 : Nat := 4983230072969 + 3 ^ 40 * 3465247 * 2
def baseEnd_3465247 : Nat := 593112432516902979625375

theorem tailTrace_3465247 : CollatzResearch.WordTrace tailWord_3465247 prefixEnd_3465247 593112432516902979625375 := by
  unfold tailWord_3465247
  simp only [CollatzResearch.WordTrace]
  refine ⟨126387941277009410915745995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84258627518006273943830663 126387941277009410915745995)
  ·
    refine ⟨189581911915514116373618993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126387941277009410915745995 189581911915514116373618993)
    ·
      refine ⟨142186433936635587280214245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189581911915514116373618993 142186433936635587280214245)
      ·
        refine ⟨26659956363119172615040171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142186433936635587280214245 26659956363119172615040171)
        ·
          refine ⟨39989934544678758922560257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26659956363119172615040171 39989934544678758922560257)
          ·
            refine ⟨29992450908509069191920193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39989934544678758922560257 29992450908509069191920193)
            ·
              refine ⟨22494338181381801893940145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29992450908509069191920193 22494338181381801893940145)
              ·
                refine ⟨16870753636036351420455109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22494338181381801893940145 16870753636036351420455109)
                ·
                  refine ⟨3163266306756815891335333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16870753636036351420455109 3163266306756815891335333)
                  ·
                    refine ⟨593112432516902979625375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3163266306756815891335333 593112432516902979625375)
                    ·
                      rfl

theorem cell23_3465247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4, 4].length) (baseStart_3465247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465247 prefixEnd_3465247 := by exact prefixLift 3465247
  have htrace : WordTrace (prefixWord ++ tailWord_3465247) baseStart_3465247 baseEnd_3465247 := by
    simpa [prefixWord, tailWord_3465247, baseEnd_3465247] using wordTrace_append hprefix tailTrace_3465247
  have hstable : (prefixWord ++ tailWord_3465247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465247).length < 2 ^ (prefixWord ++ tailWord_3465247).sum := by decide
  have hdescent : baseEnd_3465247 < baseStart_3465247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465264 : List Nat := [2, 1, 1, 1, 2, 5, 3, 2, 2, 4]
def baseStart_3465264 : Nat := 118140960795 + 3465264 * 2 ^ 59
def prefixEnd_3465264 : Nat := 4983230072969 + 3 ^ 40 * 3465264 * 2
def baseEnd_3465264 : Nat := 593115342240611790787849

theorem tailTrace_3465264 : CollatzResearch.WordTrace tailWord_3465264 prefixEnd_3465264 593115342240611790787849 := by
  unfold tailWord_3465264
  simp only [CollatzResearch.WordTrace]
  refine ⟨63194280658973911409557423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84259040878631881879409897 63194280658973911409557423)
  ·
    refine ⟨94791420988460867114336135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63194280658973911409557423 94791420988460867114336135)
    ·
      refine ⟨142187131482691300671504203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94791420988460867114336135 142187131482691300671504203)
      ·
        refine ⟨213280697224036951007256305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142187131482691300671504203 213280697224036951007256305)
        ·
          refine ⟨159960522918027713255442229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213280697224036951007256305 159960522918027713255442229)
          ·
            refine ⟨14996299023565098117697709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 159960522918027713255442229 14996299023565098117697709)
            ·
              refine ⟨5623612133836911794136641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14996299023565098117697709 5623612133836911794136641)
              ·
                refine ⟨4217709100377683845602481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5623612133836911794136641 4217709100377683845602481)
                ·
                  refine ⟨3163281825283262884201861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4217709100377683845602481 3163281825283262884201861)
                  ·
                    refine ⟨593115342240611790787849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3163281825283262884201861 593115342240611790787849)
                    ·
                      rfl

theorem cell23_3465264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 2, 4].length) (baseStart_3465264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465264 prefixEnd_3465264 := by exact prefixLift 3465264
  have htrace : WordTrace (prefixWord ++ tailWord_3465264) baseStart_3465264 baseEnd_3465264 := by
    simpa [prefixWord, tailWord_3465264, baseEnd_3465264] using wordTrace_append hprefix tailTrace_3465264
  have hstable : (prefixWord ++ tailWord_3465264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465264).length < 2 ^ (prefixWord ++ tailWord_3465264).sum := by decide
  have hdescent : baseEnd_3465264 < baseStart_3465264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465294 : List Nat := [4, 1, 1, 1, 1, 6, 2, 7]
def baseStart_3465294 : Nat := 118140960795 + 3465294 * 2 ^ 59
def prefixEnd_3465294 : Nat := 4983230072969 + 3 ^ 40 * 3465294 * 2
def baseEnd_3465294 : Nat := 65902275227461861295867

theorem tailTrace_3465294 : CollatzResearch.WordTrace tailWord_3465294 prefixEnd_3465294 65902275227461861295867 := by
  unfold tailWord_3465294
  simp only [CollatzResearch.WordTrace]
  refine ⟨15798706938479892242838367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84259770338559425295137957 15798706938479892242838367)
  ·
    refine ⟨23698060407719838364257551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15798706938479892242838367 23698060407719838364257551)
    ·
      refine ⟨35547090611579757546386327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23698060407719838364257551 35547090611579757546386327)
      ·
        refine ⟨53320635917369636319579491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35547090611579757546386327 53320635917369636319579491)
        ·
          refine ⟨79980953876054454479369237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53320635917369636319579491 79980953876054454479369237)
          ·
            refine ⟨3749107212940052553720433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 79980953876054454479369237 3749107212940052553720433)
            ·
              refine ⟨2811830409705039415290325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3749107212940052553720433 2811830409705039415290325)
              ·
                refine ⟨65902275227461861295867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2811830409705039415290325 65902275227461861295867)
                ·
                  rfl

theorem cell23_3465294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 7].length) (baseStart_3465294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465294 prefixEnd_3465294 := by exact prefixLift 3465294
  have htrace : WordTrace (prefixWord ++ tailWord_3465294) baseStart_3465294 baseEnd_3465294 := by
    simpa [prefixWord, tailWord_3465294, baseEnd_3465294] using wordTrace_append hprefix tailTrace_3465294
  have hstable : (prefixWord ++ tailWord_3465294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465294).length < 2 ^ (prefixWord ++ tailWord_3465294).sum := by decide
  have hdescent : baseEnd_3465294 < baseStart_3465294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
