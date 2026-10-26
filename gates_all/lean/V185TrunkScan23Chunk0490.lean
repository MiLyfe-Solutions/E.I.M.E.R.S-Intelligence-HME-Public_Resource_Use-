import V185TrunkScan23Chunk0489

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2898190 : List Nat := [4, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3]
def baseStart_2898190 : Nat := 118140960795 + 2898190 * 2 ^ 59
def prefixEnd_2898190 : Nat := 4983230072969 + 3 ^ 40 * 2898190 * 2
def baseEnd_2898190 : Nat := 1488164498054121051996473

theorem tailTrace_2898190 : CollatzResearch.WordTrace tailWord_2898190 prefixEnd_2898190 1488164498054121051996473 := by
  unfold tailWord_2898190
  simp only [CollatzResearch.WordTrace]
  refine ⟨13213209171295009536302503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70470448913573384193613349 13213209171295009536302503)
  ·
    refine ⟨19819813756942514304453755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13213209171295009536302503 19819813756942514304453755)
    ·
      refine ⟨29729720635413771456680633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19819813756942514304453755 29729720635413771456680633)
      ·
        refine ⟨22297290476560328592510475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29729720635413771456680633 22297290476560328592510475)
        ·
          refine ⟨33445935714840492888765713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22297290476560328592510475 33445935714840492888765713)
          ·
            refine ⟨25084451786130369666574285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33445935714840492888765713 25084451786130369666574285)
            ·
              refine ⟨9406669419798888624965357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25084451786130369666574285 9406669419798888624965357)
              ·
                refine ⟨3527501032424583234362009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9406669419798888624965357 3527501032424583234362009)
                ·
                  refine ⟨2645625774318437425771507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3527501032424583234362009 2645625774318437425771507)
                  ·
                    refine ⟨3968438661477656138657261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2645625774318437425771507 3968438661477656138657261)
                    ·
                      refine ⟨1488164498054121051996473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3968438661477656138657261 1488164498054121051996473)
                      ·
                        rfl

theorem cell23_2898190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_2898190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898190 prefixEnd_2898190 := by exact prefixLift 2898190
  have htrace : WordTrace (prefixWord ++ tailWord_2898190) baseStart_2898190 baseEnd_2898190 := by
    simpa [prefixWord, tailWord_2898190, baseEnd_2898190] using wordTrace_append hprefix tailTrace_2898190
  have hstable : (prefixWord ++ tailWord_2898190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898190).length < 2 ^ (prefixWord ++ tailWord_2898190).sum := by decide
  have hdescent : baseEnd_2898190 < baseStart_2898190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898233 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 2, 4, 3]
def baseStart_2898233 : Nat := 118140960795 + 2898233 * 2 ^ 59
def prefixEnd_2898233 : Nat := 4983230072969 + 3 ^ 40 * 2898233 * 2
def baseEnd_2898233 : Nat := 1488186577722264383758775

theorem tailTrace_2898233 : CollatzResearch.WordTrace tailWord_2898233 prefixEnd_2898233 1488186577722264383758775 := by
  unfold tailWord_2898233
  simp only [CollatzResearch.WordTrace]
  refine ⟨105707241709204294634235353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70471494472802863089490235 105707241709204294634235353)
  ·
    refine ⟨79280431281903220975676515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105707241709204294634235353 79280431281903220975676515)
    ·
      refine ⟨118920646922854831463514773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79280431281903220975676515 118920646922854831463514773)
      ·
        refine ⟨5574405324508820224852255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 118920646922854831463514773 5574405324508820224852255)
        ·
          refine ⟨8361607986763230337278383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5574405324508820224852255 8361607986763230337278383)
          ·
            refine ⟨12542411980144845505917575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8361607986763230337278383 12542411980144845505917575)
            ·
              refine ⟨18813617970217268258876363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12542411980144845505917575 18813617970217268258876363)
              ·
                refine ⟨28220426955325902388314545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18813617970217268258876363 28220426955325902388314545)
                ·
                  refine ⟨21165320216494426791235909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28220426955325902388314545 21165320216494426791235909)
                  ·
                    refine ⟨3968497540592705023356733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21165320216494426791235909 3968497540592705023356733)
                    ·
                      refine ⟨1488186577722264383758775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3968497540592705023356733 1488186577722264383758775)
                      ·
                        rfl

theorem cell23_2898233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_2898233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898233 prefixEnd_2898233 := by exact prefixLift 2898233
  have htrace : WordTrace (prefixWord ++ tailWord_2898233) baseStart_2898233 baseEnd_2898233 := by
    simpa [prefixWord, tailWord_2898233, baseEnd_2898233] using wordTrace_append hprefix tailTrace_2898233
  have hstable : (prefixWord ++ tailWord_2898233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898233).length < 2 ^ (prefixWord ++ tailWord_2898233).sum := by decide
  have hdescent : baseEnd_2898233 < baseStart_2898233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898236 : List Nat := [2, 2, 2, 2, 1, 2, 2, 3, 7]
def baseStart_2898236 : Nat := 118140960795 + 2898236 * 2 ^ 59
def prefixEnd_2898236 : Nat := 4983230072969 + 3 ^ 40 * 2898236 * 2
def baseEnd_2898236 : Nat := 165354235351580874669029

theorem tailTrace_2898236 : CollatzResearch.WordTrace tailWord_2898236 prefixEnd_2898236 165354235351580874669029 := by
  unfold tailWord_2898236
  simp only [CollatzResearch.WordTrace]
  refine ⟨52853675564096713073297281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70471567418795617431063041 52853675564096713073297281)
  ·
    refine ⟨39640256673072534804972961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52853675564096713073297281 39640256673072534804972961)
    ·
      refine ⟨29730192504804401103729721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39640256673072534804972961 29730192504804401103729721)
      ·
        refine ⟨22297644378603300827797291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29730192504804401103729721 22297644378603300827797291)
        ·
          refine ⟨33446466567904951241695937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22297644378603300827797291 33446466567904951241695937)
          ·
            refine ⟨25084849925928713431271953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33446466567904951241695937 25084849925928713431271953)
            ·
              refine ⟨18813637444446535073453965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25084849925928713431271953 18813637444446535073453965)
              ·
                refine ⟨7055114041667450652545237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18813637444446535073453965 7055114041667450652545237)
                ·
                  refine ⟨165354235351580874669029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7055114041667450652545237 165354235351580874669029)
                  ·
                    rfl

theorem cell23_2898236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 7].length) (baseStart_2898236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898236 prefixEnd_2898236 := by exact prefixLift 2898236
  have htrace : WordTrace (prefixWord ++ tailWord_2898236) baseStart_2898236 baseEnd_2898236 := by
    simpa [prefixWord, tailWord_2898236, baseEnd_2898236] using wordTrace_append hprefix tailTrace_2898236
  have hstable : (prefixWord ++ tailWord_2898236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898236).length < 2 ^ (prefixWord ++ tailWord_2898236).sum := by decide
  have hdescent : baseEnd_2898236 < baseStart_2898236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898268 : List Nat := [2, 2, 4, 3, 2, 1, 2, 1, 1, 3, 2]
def baseStart_2898268 : Nat := 118140960795 + 2898268 * 2 ^ 59
def prefixEnd_2898268 : Nat := 4983230072969 + 3 ^ 40 * 2898268 * 2
def baseEnd_2898268 : Nat := 1488204549545171746821115

theorem tailTrace_2898268 : CollatzResearch.WordTrace tailWord_2898268 prefixEnd_2898268 1488204549545171746821115 := by
  unfold tailWord_2898268
  simp only [CollatzResearch.WordTrace]
  refine ⟨52854259132038747805879729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70472345509384997074506305 52854259132038747805879729)
  ·
    refine ⟨39640694349029060854409797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52854259132038747805879729 39640694349029060854409797)
    ·
      refine ⟨7432630190442948910201837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39640694349029060854409797 7432630190442948910201837)
      ·
        refine ⟨2787236321416105841325689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7432630190442948910201837 2787236321416105841325689)
        ·
          refine ⟨2090427241062079380994267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2787236321416105841325689 2090427241062079380994267)
          ·
            refine ⟨3135640861593119071491401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2090427241062079380994267 3135640861593119071491401)
            ·
              refine ⟨2351730646194839303618551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3135640861593119071491401 2351730646194839303618551)
              ·
                refine ⟨3527595969292258955427827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2351730646194839303618551 3527595969292258955427827)
                ·
                  refine ⟨5291393953938388433141741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3527595969292258955427827 5291393953938388433141741)
                  ·
                    refine ⟨1984272732726895662428153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5291393953938388433141741 1984272732726895662428153)
                    ·
                      refine ⟨1488204549545171746821115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1984272732726895662428153 1488204549545171746821115)
                      ·
                        rfl

theorem cell23_2898268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_2898268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898268 prefixEnd_2898268 := by exact prefixLift 2898268
  have htrace : WordTrace (prefixWord ++ tailWord_2898268) baseStart_2898268 baseEnd_2898268 := by
    simpa [prefixWord, tailWord_2898268, baseEnd_2898268] using wordTrace_append hprefix tailTrace_2898268
  have hstable : (prefixWord ++ tailWord_2898268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898268).length < 2 ^ (prefixWord ++ tailWord_2898268).sum := by decide
  have hdescent : baseEnd_2898268 < baseStart_2898268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898337 : List Nat := [1, 2, 3, 5, 1, 1, 1, 2, 2, 1, 4]
def baseStart_2898337 : Nat := 118140960795 + 2898337 * 2 ^ 59
def prefixEnd_2898337 : Nat := 4983230072969 + 3 ^ 40 * 2898337 * 2
def baseEnd_2898337 : Nat := 1488239979710331976858297

theorem tailTrace_2898337 : CollatzResearch.WordTrace tailWord_2898337 prefixEnd_2898337 1488239979710331976858297 := by
  unfold tailWord_2898337
  simp only [CollatzResearch.WordTrace]
  refine ⟨105711034900827520396021265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70474023267218346930680843 105711034900827520396021265)
  ·
    refine ⟨79283276175620640297015949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105711034900827520396021265 79283276175620640297015949)
    ·
      refine ⟨29731228565857740111380981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79283276175620640297015949 29731228565857740111380981)
      ·
        refine ⟨2787302678049163135441967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29731228565857740111380981 2787302678049163135441967)
        ·
          refine ⟨4180954017073744703162951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2787302678049163135441967 4180954017073744703162951)
          ·
            refine ⟨6271431025610617054744427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4180954017073744703162951 6271431025610617054744427)
            ·
              refine ⟨9407146538415925582116641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6271431025610617054744427 9407146538415925582116641)
              ·
                refine ⟨7055359903811944186587481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9407146538415925582116641 7055359903811944186587481)
                ·
                  refine ⟨5291519927858958139940611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7055359903811944186587481 5291519927858958139940611)
                  ·
                    refine ⟨7937279891788437209910917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5291519927858958139940611 7937279891788437209910917)
                    ·
                      refine ⟨1488239979710331976858297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7937279891788437209910917 1488239979710331976858297)
                      ·
                        rfl

theorem cell23_2898337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_2898337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898337 prefixEnd_2898337 := by exact prefixLift 2898337
  have htrace : WordTrace (prefixWord ++ tailWord_2898337) baseStart_2898337 baseEnd_2898337 := by
    simpa [prefixWord, tailWord_2898337, baseEnd_2898337] using wordTrace_append hprefix tailTrace_2898337
  have hstable : (prefixWord ++ tailWord_2898337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898337).length < 2 ^ (prefixWord ++ tailWord_2898337).sum := by decide
  have hdescent : baseEnd_2898337 < baseStart_2898337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898343 : List Nat := [1, 1, 6, 1, 1, 2, 2, 1, 8]
def baseStart_2898343 : Nat := 118140960795 + 2898343 * 2 ^ 59
def prefixEnd_2898343 : Nat := 4983230072969 + 3 ^ 40 * 2898343 * 2
def baseEnd_2898343 : Nat := 165360340066028772598141

theorem tailTrace_2898343 : CollatzResearch.WordTrace tailWord_2898343 prefixEnd_2898343 165360340066028772598141 := by
  unfold tailWord_2898343
  simp only [CollatzResearch.WordTrace]
  refine ⟨105711253738805783420739683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70474169159203855613826455 105711253738805783420739683)
  ·
    refine ⟨158566880608208675131109525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105711253738805783420739683 158566880608208675131109525)
    ·
      refine ⟨7432822528509781646770759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 158566880608208675131109525 7432822528509781646770759)
      ·
        refine ⟨11149233792764672470156139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7432822528509781646770759 11149233792764672470156139)
        ·
          refine ⟨16723850689147008705234209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11149233792764672470156139 16723850689147008705234209)
          ·
            refine ⟨12542888016860256528925657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16723850689147008705234209 12542888016860256528925657)
            ·
              refine ⟨9407166012645192396694243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12542888016860256528925657 9407166012645192396694243)
              ·
                refine ⟨14110749018967788595041365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9407166012645192396694243 14110749018967788595041365)
                ·
                  refine ⟨165360340066028772598141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14110749018967788595041365 165360340066028772598141)
                  ·
                    rfl

theorem cell23_2898343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 8].length) (baseStart_2898343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898343 prefixEnd_2898343 := by exact prefixLift 2898343
  have htrace : WordTrace (prefixWord ++ tailWord_2898343) baseStart_2898343 baseEnd_2898343 := by
    simpa [prefixWord, tailWord_2898343, baseEnd_2898343] using wordTrace_append hprefix tailTrace_2898343
  have hstable : (prefixWord ++ tailWord_2898343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898343).length < 2 ^ (prefixWord ++ tailWord_2898343).sum := by decide
  have hdescent : baseEnd_2898343 < baseStart_2898343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898397 : List Nat := [1, 4, 3, 1, 1, 1, 1, 4, 2, 3, 2]
def baseStart_2898397 : Nat := 118140960795 + 2898397 * 2 ^ 59
def prefixEnd_2898397 : Nat := 4983230072969 + 3 ^ 40 * 2898397 * 2
def baseEnd_2898397 : Nat := 1488270788549601742108021

theorem tailTrace_2898397 : CollatzResearch.WordTrace tailWord_2898397 prefixEnd_2898397 1488270788549601742108021 := by
  unfold tailWord_2898397
  simp only [CollatzResearch.WordTrace]
  refine ⟨105713223280610150643205445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70475482187073433762136963 105713223280610150643205445)
  ·
    refine ⟨19821229365114403245601021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105713223280610150643205445 19821229365114403245601021)
    ·
      refine ⟨7432961011917901217100383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19821229365114403245601021 7432961011917901217100383)
      ·
        refine ⟨11149441517876851825650575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7432961011917901217100383 11149441517876851825650575)
        ·
          refine ⟨16724162276815277738475863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11149441517876851825650575 16724162276815277738475863)
          ·
            refine ⟨25086243415222916607713795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16724162276815277738475863 25086243415222916607713795)
            ·
              refine ⟨37629365122834374911570693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25086243415222916607713795 37629365122834374911570693)
              ·
                refine ⟨7055505960531445295919505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37629365122834374911570693 7055505960531445295919505)
                ·
                  refine ⟨5291629470398583971939629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7055505960531445295919505 5291629470398583971939629)
                  ·
                    refine ⟨1984361051399468989477361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5291629470398583971939629 1984361051399468989477361)
                    ·
                      refine ⟨1488270788549601742108021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1984361051399468989477361 1488270788549601742108021)
                      ·
                        rfl

theorem cell23_2898397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_2898397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898397 prefixEnd_2898397 := by exact prefixLift 2898397
  have htrace : WordTrace (prefixWord ++ tailWord_2898397) baseStart_2898397 baseEnd_2898397 := by
    simpa [prefixWord, tailWord_2898397, baseEnd_2898397] using wordTrace_append hprefix tailTrace_2898397
  have hstable : (prefixWord ++ tailWord_2898397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898397).length < 2 ^ (prefixWord ++ tailWord_2898397).sum := by decide
  have hdescent : baseEnd_2898397 < baseStart_2898397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898410 : List Nat := [3, 1, 3, 1, 3, 1, 1, 2, 3, 1, 4]
def baseStart_2898410 : Nat := 118140960795 + 2898410 * 2 ^ 59
def prefixEnd_2898410 : Nat := 4983230072969 + 3 ^ 40 * 2898410 * 2
def baseEnd_2898410 : Nat := 1488277463798110191245461

theorem tailTrace_2898410 : CollatzResearch.WordTrace tailWord_2898410 prefixEnd_2898410 1488277463798110191245461 := by
  unfold tailWord_2898410
  simp only [CollatzResearch.WordTrace]
  refine ⟨26428424357390763465857171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70475798286375369242285789 26428424357390763465857171)
  ·
    refine ⟨39642636536086145198785757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26428424357390763465857171 39642636536086145198785757)
    ·
      refine ⟨14865988701032304449544659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39642636536086145198785757 14865988701032304449544659)
      ·
        refine ⟨22298983051548456674316989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14865988701032304449544659 22298983051548456674316989)
        ·
          refine ⟨8362118644330671252868871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22298983051548456674316989 8362118644330671252868871)
          ·
            refine ⟨12543177966496006879303307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8362118644330671252868871 12543177966496006879303307)
            ·
              refine ⟨18814766949744010318954961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12543177966496006879303307 18814766949744010318954961)
              ·
                refine ⟨14111075212308007739216221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18814766949744010318954961 14111075212308007739216221)
                ·
                  refine ⟨5291653204615502902206083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14111075212308007739216221 5291653204615502902206083)
                  ·
                    refine ⟨7937479806923254353309125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5291653204615502902206083 7937479806923254353309125)
                    ·
                      refine ⟨1488277463798110191245461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7937479806923254353309125 1488277463798110191245461)
                      ·
                        rfl

theorem cell23_2898410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_2898410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898410 prefixEnd_2898410 := by exact prefixLift 2898410
  have htrace : WordTrace (prefixWord ++ tailWord_2898410) baseStart_2898410 baseEnd_2898410 := by
    simpa [prefixWord, tailWord_2898410, baseEnd_2898410] using wordTrace_append hprefix tailTrace_2898410
  have hstable : (prefixWord ++ tailWord_2898410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898410).length < 2 ^ (prefixWord ++ tailWord_2898410).sum := by decide
  have hdescent : baseEnd_2898410 < baseStart_2898410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898444 : List Nat := [2, 2, 1, 2, 4, 3, 2, 1, 1, 1, 4]
def baseStart_2898444 : Nat := 118140960795 + 2898444 * 2 ^ 59
def prefixEnd_2898444 : Nat := 4983230072969 + 3 ^ 40 * 2898444 * 2
def baseEnd_2898444 : Nat := 1488294922140363058220305

theorem tailTrace_2898444 : CollatzResearch.WordTrace tailWord_2898444 prefixEnd_2898444 1488294922140363058220305 := by
  unfold tailWord_2898444
  simp only [CollatzResearch.WordTrace]
  refine ⟨52857468755719938835083193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70476625007626585113444257 52857468755719938835083193)
  ·
    refine ⟨39643101566789954126312395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52857468755719938835083193 39643101566789954126312395)
    ·
      refine ⟨59464652350184931189468593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39643101566789954126312395 59464652350184931189468593)
      ·
        refine ⟨44598489262638698392101445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59464652350184931189468593 44598489262638698392101445)
        ·
          refine ⟨8362216736744755948519021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44598489262638698392101445 8362216736744755948519021)
          ·
            refine ⟨3135831276279283480694633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8362216736744755948519021 3135831276279283480694633)
            ·
              refine ⟨2351873457209462610520975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3135831276279283480694633 2351873457209462610520975)
              ·
                refine ⟨3527810185814193915781463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2351873457209462610520975 3527810185814193915781463)
                ·
                  refine ⟨5291715278721290873672195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3527810185814193915781463 5291715278721290873672195)
                  ·
                    refine ⟨7937572918081936310508293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5291715278721290873672195 7937572918081936310508293)
                    ·
                      refine ⟨1488294922140363058220305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7937572918081936310508293 1488294922140363058220305)
                      ·
                        rfl

theorem cell23_2898444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 1, 1, 4].length) (baseStart_2898444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898444 prefixEnd_2898444 := by exact prefixLift 2898444
  have htrace : WordTrace (prefixWord ++ tailWord_2898444) baseStart_2898444 baseEnd_2898444 := by
    simpa [prefixWord, tailWord_2898444, baseEnd_2898444] using wordTrace_append hprefix tailTrace_2898444
  have hstable : (prefixWord ++ tailWord_2898444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898444).length < 2 ^ (prefixWord ++ tailWord_2898444).sum := by decide
  have hdescent : baseEnd_2898444 < baseStart_2898444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898461 : List Nat := [1, 4, 2, 2, 1, 2, 2, 4, 1, 2, 2]
def baseStart_2898461 : Nat := 118140960795 + 2898461 * 2 ^ 59
def prefixEnd_2898461 : Nat := 4983230072969 + 3 ^ 40 * 2898461 * 2
def baseEnd_2898461 : Nat := 1488303651311489491707727

theorem tailTrace_2898461 : CollatzResearch.WordTrace tailWord_2898461 prefixEnd_2898461 1488303651311489491707727 := by
  unfold tailWord_2898461
  simp only [CollatzResearch.WordTrace]
  refine ⟨105715557552378289573535237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70477038368252193049023491 105715557552378289573535237)
  ·
    refine ⟨19821667041070929295037857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105715557552378289573535237 19821667041070929295037857)
    ·
      refine ⟨14866250280803196971278393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19821667041070929295037857 14866250280803196971278393)
      ·
        refine ⟨11149687710602397728458795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14866250280803196971278393 11149687710602397728458795)
        ·
          refine ⟨16724531565903596592688193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11149687710602397728458795 16724531565903596592688193)
          ·
            refine ⟨12543398674427697444516145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16724531565903596592688193 12543398674427697444516145)
            ·
              refine ⟨9407549005820773083387109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12543398674427697444516145 9407549005820773083387109)
              ·
                refine ⟨1763915438591394953135083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9407549005820773083387109 1763915438591394953135083)
                ·
                  refine ⟨2645873157887092429702625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1763915438591394953135083 2645873157887092429702625)
                  ·
                    refine ⟨1984404868415319322276969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2645873157887092429702625 1984404868415319322276969)
                    ·
                      refine ⟨1488303651311489491707727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1984404868415319322276969 1488303651311489491707727)
                      ·
                        rfl

theorem cell23_2898461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_2898461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898461 prefixEnd_2898461 := by exact prefixLift 2898461
  have htrace : WordTrace (prefixWord ++ tailWord_2898461) baseStart_2898461 baseEnd_2898461 := by
    simpa [prefixWord, tailWord_2898461, baseEnd_2898461] using wordTrace_append hprefix tailTrace_2898461
  have hstable : (prefixWord ++ tailWord_2898461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898461).length < 2 ^ (prefixWord ++ tailWord_2898461).sum := by decide
  have hdescent : baseEnd_2898461 < baseStart_2898461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898471 : List Nat := [1, 1, 7, 2, 2, 1, 1, 1, 1, 6]
def baseStart_2898471 : Nat := 118140960795 + 2898471 * 2 ^ 59
def prefixEnd_2898471 : Nat := 4983230072969 + 3 ^ 40 * 2898471 * 2
def baseEnd_2898471 : Nat := 496102928706011484194227

theorem tailTrace_2898471 : CollatzResearch.WordTrace tailWord_2898471 prefixEnd_2898471 496102928706011484194227 := by
  unfold tailWord_2898471
  simp only [CollatzResearch.WordTrace]
  refine ⟨105715922282342061281399267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70477281521561374187599511 105715922282342061281399267)
  ·
    refine ⟨158573883423513091922098901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105715922282342061281399267 158573883423513091922098901)
    ·
      refine ⟨3716575392738588091924193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 158573883423513091922098901 3716575392738588091924193)
      ·
        refine ⟨2787431544553941068943145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3716575392738588091924193 2787431544553941068943145)
        ·
          refine ⟨2090573658415455801707359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2787431544553941068943145 2090573658415455801707359)
          ·
            refine ⟨3135860487623183702561039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2090573658415455801707359 3135860487623183702561039)
            ·
              refine ⟨4703790731434775553841559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3135860487623183702561039 4703790731434775553841559)
              ·
                refine ⟨7055686097152163330762339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4703790731434775553841559 7055686097152163330762339)
                ·
                  refine ⟨10583529145728244996143509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7055686097152163330762339 10583529145728244996143509)
                  ·
                    refine ⟨496102928706011484194227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10583529145728244996143509 496102928706011484194227)
                    ·
                      rfl

theorem cell23_2898471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_2898471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898471 prefixEnd_2898471 := by exact prefixLift 2898471
  have htrace : WordTrace (prefixWord ++ tailWord_2898471) baseStart_2898471 baseEnd_2898471 := by
    simpa [prefixWord, tailWord_2898471, baseEnd_2898471] using wordTrace_append hprefix tailTrace_2898471
  have hstable : (prefixWord ++ tailWord_2898471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898471).length < 2 ^ (prefixWord ++ tailWord_2898471).sum := by decide
  have hdescent : baseEnd_2898471 < baseStart_2898471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898607 : List Nat := [1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 4]
def baseStart_2898607 : Nat := 118140960795 + 2898607 * 2 ^ 59
def prefixEnd_2898607 : Nat := 4983230072969 + 3 ^ 40 * 2898607 * 2
def baseEnd_2898607 : Nat := 1488378619487045920482055

theorem tailTrace_2898607 : CollatzResearch.WordTrace tailWord_2898607 prefixEnd_2898607 1488378619487045920482055 := by
  unfold tailWord_2898607
  simp only [CollatzResearch.WordTrace]
  refine ⟨105720882609849356508350075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70480588406566237672233383 105720882609849356508350075)
  ·
    refine ⟨158581323914774034762525113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105720882609849356508350075 158581323914774034762525113)
    ·
      refine ⟨118935992936080526071893835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158581323914774034762525113 118935992936080526071893835)
      ·
        refine ⟨178403989404120789107840753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118935992936080526071893835 178403989404120789107840753)
        ·
          refine ⟨133802992053090591830880565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178403989404120789107840753 133802992053090591830880565)
          ·
            refine ⟨12544030504977242984145053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133802992053090591830880565 12544030504977242984145053)
            ·
              refine ⟨4704011439366466119054395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12544030504977242984145053 4704011439366466119054395)
              ·
                refine ⟨7056017159049699178581593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4704011439366466119054395 7056017159049699178581593)
                ·
                  refine ⟨5292012869287274383936195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7056017159049699178581593 5292012869287274383936195)
                  ·
                    refine ⟨7938019303930911575904293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5292012869287274383936195 7938019303930911575904293)
                    ·
                      refine ⟨1488378619487045920482055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7938019303930911575904293 1488378619487045920482055)
                      ·
                        rfl

theorem cell23_2898607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 4].length) (baseStart_2898607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898607 prefixEnd_2898607 := by exact prefixLift 2898607
  have htrace : WordTrace (prefixWord ++ tailWord_2898607) baseStart_2898607 baseEnd_2898607 := by
    simpa [prefixWord, tailWord_2898607, baseEnd_2898607] using wordTrace_append hprefix tailTrace_2898607
  have hstable : (prefixWord ++ tailWord_2898607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898607).length < 2 ^ (prefixWord ++ tailWord_2898607).sum := by decide
  have hdescent : baseEnd_2898607 < baseStart_2898607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898620 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 1, 3, 6]
def baseStart_2898620 : Nat := 118140960795 + 2898620 * 2 ^ 59
def prefixEnd_2898620 : Nat := 4983230072969 + 3 ^ 40 * 2898620 * 2
def baseEnd_2898620 : Nat := 1488385294735554369619495

theorem tailTrace_2898620 : CollatzResearch.WordTrace tailWord_2898620 prefixEnd_2898620 1488385294735554369619495 := by
  unfold tailWord_2898620
  simp only [CollatzResearch.WordTrace]
  refine ⟨52860678379401129864286657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70480904505868173152382209 52860678379401129864286657)
  ·
    refine ⟨39645508784550847398214993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52860678379401129864286657 39645508784550847398214993)
    ·
      refine ⟨29734131588413135548661245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39645508784550847398214993 29734131588413135548661245)
      ·
        refine ⟨11150299345654925830747967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29734131588413135548661245 11150299345654925830747967)
        ·
          refine ⟨16725449018482388746121951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11150299345654925830747967 16725449018482388746121951)
          ·
            refine ⟨25088173527723583119182927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16725449018482388746121951 25088173527723583119182927)
            ·
              refine ⟨37632260291585374678774391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25088173527723583119182927 37632260291585374678774391)
              ·
                refine ⟨56448390437378062018161587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37632260291585374678774391 56448390437378062018161587)
                ·
                  refine ⟨84672585656067093027242381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56448390437378062018161587 84672585656067093027242381)
                  ·
                    refine ⟨31752219621025159885215893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84672585656067093027242381 31752219621025159885215893)
                    ·
                      refine ⟨1488385294735554369619495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31752219621025159885215893 1488385294735554369619495)
                      ·
                        rfl

theorem cell23_2898620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_2898620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898620 prefixEnd_2898620 := by exact prefixLift 2898620
  have htrace : WordTrace (prefixWord ++ tailWord_2898620) baseStart_2898620 baseEnd_2898620 := by
    simpa [prefixWord, tailWord_2898620, baseEnd_2898620] using wordTrace_append hprefix tailTrace_2898620
  have hstable : (prefixWord ++ tailWord_2898620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898620).length < 2 ^ (prefixWord ++ tailWord_2898620).sum := by decide
  have hdescent : baseEnd_2898620 < baseStart_2898620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898634 : List Nat := [3, 1, 2, 1, 4, 2, 2, 1, 3, 4]
def baseStart_2898634 : Nat := 118140960795 + 2898634 * 2 ^ 59
def prefixEnd_2898634 : Nat := 4983230072969 + 3 ^ 40 * 2898634 * 2
def baseEnd_2898634 : Nat := 496130827821572438281477

theorem tailTrace_2898634 : CollatzResearch.WordTrace tailWord_2898634 prefixEnd_2898634 496130827821572438281477 := by
  unfold tailWord_2898634
  simp only [CollatzResearch.WordTrace]
  refine ⟨26430466845187885029895739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70481244920501026746388637 26430466845187885029895739)
  ·
    refine ⟨39645700267781827544843609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26430466845187885029895739 39645700267781827544843609)
    ·
      refine ⟨29734275200836370658632707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39645700267781827544843609 29734275200836370658632707)
      ·
        refine ⟨44601412801254555987949061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29734275200836370658632707 44601412801254555987949061)
        ·
          refine ⟨8362764900235229247740449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44601412801254555987949061 8362764900235229247740449)
          ·
            refine ⟨6272073675176421935805337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8362764900235229247740449 6272073675176421935805337)
            ·
              refine ⟨4704055256382316451854003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6272073675176421935805337 4704055256382316451854003)
              ·
                refine ⟨7056082884573474677781005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4704055256382316451854003 7056082884573474677781005)
                ·
                  refine ⟨2646031081715053004167877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7056082884573474677781005 2646031081715053004167877)
                  ·
                    refine ⟨496130827821572438281477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2646031081715053004167877 496130827821572438281477)
                    ·
                      rfl

theorem cell23_2898634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_2898634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898634 prefixEnd_2898634 := by exact prefixLift 2898634
  have htrace : WordTrace (prefixWord ++ tailWord_2898634) baseStart_2898634 baseEnd_2898634 := by
    simpa [prefixWord, tailWord_2898634, baseEnd_2898634] using wordTrace_append hprefix tailTrace_2898634
  have hstable : (prefixWord ++ tailWord_2898634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898634).length < 2 ^ (prefixWord ++ tailWord_2898634).sum := by decide
  have hdescent : baseEnd_2898634 < baseStart_2898634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898650 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6]
def baseStart_2898650 : Nat := 118140960795 + 2898650 * 2 ^ 59
def prefixEnd_2898650 : Nat := 4983230072969 + 3 ^ 40 * 2898650 * 2
def baseEnd_2898650 : Nat := 1488400699155189252244357

theorem tailTrace_2898650 : CollatzResearch.WordTrace tailWord_2898650 prefixEnd_2898650 1488400699155189252244357 := by
  unfold tailWord_2898650
  simp only [CollatzResearch.WordTrace]
  refine ⟨26430612737173393713041351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70481633965795716568110269 26430612737173393713041351)
  ·
    refine ⟨39645919105760090569562027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26430612737173393713041351 39645919105760090569562027)
    ·
      refine ⟨59468878658640135854343041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39645919105760090569562027 59468878658640135854343041)
      ·
        refine ⟨44601658993980101890757281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59468878658640135854343041 44601658993980101890757281)
        ·
          refine ⟨33451244245485076418067961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44601658993980101890757281 33451244245485076418067961)
          ·
            refine ⟨25088433184113807313550971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33451244245485076418067961 25088433184113807313550971)
            ·
              refine ⟨37632649776170710970326457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25088433184113807313550971 37632649776170710970326457)
              ·
                refine ⟨28224487332128033227744843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37632649776170710970326457 28224487332128033227744843)
                ·
                  refine ⟨42336730998192049841617265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28224487332128033227744843 42336730998192049841617265)
                  ·
                    refine ⟨31752548248644037381212949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42336730998192049841617265 31752548248644037381212949)
                    ·
                      refine ⟨1488400699155189252244357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31752548248644037381212949 1488400699155189252244357)
                      ·
                        rfl

theorem cell23_2898650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_2898650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898650 prefixEnd_2898650 := by exact prefixLift 2898650
  have htrace : WordTrace (prefixWord ++ tailWord_2898650) baseStart_2898650 baseEnd_2898650 := by
    simpa [prefixWord, tailWord_2898650, baseEnd_2898650] using wordTrace_append hprefix tailTrace_2898650
  have hstable : (prefixWord ++ tailWord_2898650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898650).length < 2 ^ (prefixWord ++ tailWord_2898650).sum := by decide
  have hdescent : baseEnd_2898650 < baseStart_2898650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898684 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 4, 3, 2]
def baseStart_2898684 : Nat := 118140960795 + 2898684 * 2 ^ 59
def prefixEnd_2898684 : Nat := 4983230072969 + 3 ^ 40 * 2898684 * 2
def baseEnd_2898684 : Nat := 1488418157497442119219201

theorem tailTrace_2898684 : CollatzResearch.WordTrace tailWord_2898684 prefixEnd_2898684 1488418157497442119219201 := by
  unfold tailWord_2898684
  simp only [CollatzResearch.WordTrace]
  refine ⟨52861845515285199329451553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70482460687046932439268737 52861845515285199329451553)
  ·
    refine ⟨39646384136463899497088665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52861845515285199329451553 39646384136463899497088665)
    ·
      refine ⟨29734788102347924622816499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39646384136463899497088665 29734788102347924622816499)
      ·
        refine ⟨44602182153521886934224749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29734788102347924622816499 44602182153521886934224749)
        ·
          refine ⟨16725818307570707600334281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44602182153521886934224749 16725818307570707600334281)
          ·
            refine ⟨12544363730678030700250711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16725818307570707600334281 12544363730678030700250711)
            ·
              refine ⟨18816545596017046050376067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12544363730678030700250711 18816545596017046050376067)
              ·
                refine ⟨28224818394025569075564101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18816545596017046050376067 28224818394025569075564101)
                ·
                  refine ⟨5292153448879794201668269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28224818394025569075564101 5292153448879794201668269)
                  ·
                    refine ⟨1984557543329922825625601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5292153448879794201668269 1984557543329922825625601)
                    ·
                      refine ⟨1488418157497442119219201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1984557543329922825625601 1488418157497442119219201)
                      ·
                        rfl

theorem cell23_2898684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 4, 3, 2].length) (baseStart_2898684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898684 prefixEnd_2898684 := by exact prefixLift 2898684
  have htrace : WordTrace (prefixWord ++ tailWord_2898684) baseStart_2898684 baseEnd_2898684 := by
    simpa [prefixWord, tailWord_2898684, baseEnd_2898684] using wordTrace_append hprefix tailTrace_2898684
  have hstable : (prefixWord ++ tailWord_2898684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898684).length < 2 ^ (prefixWord ++ tailWord_2898684).sum := by decide
  have hdescent : baseEnd_2898684 < baseStart_2898684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898711 : List Nat := [1, 1, 3, 4, 3, 2, 1, 2, 1, 5]
def baseStart_2898711 : Nat := 118140960795 + 2898711 * 2 ^ 59
def prefixEnd_2898711 : Nat := 4983230072969 + 3 ^ 40 * 2898711 * 2
def baseEnd_2898711 : Nat := 496144007158371171193859

theorem tailTrace_2898711 : CollatzResearch.WordTrace tailWord_2898711 prefixEnd_2898711 496144007158371171193859 := by
  unfold tailWord_2898711
  simp only [CollatzResearch.WordTrace]
  refine ⟨105724675801472582270135987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70483117200981721513423991 105724675801472582270135987)
  ·
    refine ⟨158587013702208873405203981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105724675801472582270135987 158587013702208873405203981)
    ·
      refine ⟨59470130138328327526951493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158587013702208873405203981 59470130138328327526951493)
      ·
        refine ⟨11150649400936561411303405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59470130138328327526951493 11150649400936561411303405)
        ·
          refine ⟨4181493525351210529238777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11150649400936561411303405 4181493525351210529238777)
          ·
            refine ⟨3136120144013407896929083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4181493525351210529238777 3136120144013407896929083)
            ·
              refine ⟨4704180216020111845393625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3136120144013407896929083 4704180216020111845393625)
              ·
                refine ⟨3528135162015083884045219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4704180216020111845393625 3528135162015083884045219)
                ·
                  refine ⟨5292202743022625826067829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3528135162015083884045219 5292202743022625826067829)
                  ·
                    refine ⟨496144007158371171193859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5292202743022625826067829 496144007158371171193859)
                    ·
                      rfl

theorem cell23_2898711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 5].length) (baseStart_2898711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898711 prefixEnd_2898711 := by exact prefixLift 2898711
  have htrace : WordTrace (prefixWord ++ tailWord_2898711) baseStart_2898711 baseEnd_2898711 := by
    simpa [prefixWord, tailWord_2898711, baseEnd_2898711] using wordTrace_append hprefix tailTrace_2898711
  have hstable : (prefixWord ++ tailWord_2898711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898711).length < 2 ^ (prefixWord ++ tailWord_2898711).sum := by decide
  have hdescent : baseEnd_2898711 < baseStart_2898711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898724 : List Nat := [2, 3, 1, 3, 3, 1, 1, 2, 1, 6]
def baseStart_2898724 : Nat := 118140960795 + 2898724 * 2 ^ 59
def prefixEnd_2898724 : Nat := 4983230072969 + 3 ^ 40 * 2898724 * 2
def baseEnd_2898724 : Nat := 496146232241207320906339

theorem tailTrace_2898724 : CollatzResearch.WordTrace tailWord_2898724 prefixEnd_2898724 496146232241207320906339 := by
  unfold tailWord_2898724
  simp only [CollatzResearch.WordTrace]
  refine ⟨52862574975212742745179613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70483433300283656993572817 52862574975212742745179613)
  ·
    refine ⟨19823465615704778529442355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52862574975212742745179613 19823465615704778529442355)
    ·
      refine ⟨29735198423557167794163533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19823465615704778529442355 29735198423557167794163533)
      ·
        refine ⟨11150699408833937922811325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29735198423557167794163533 11150699408833937922811325)
        ·
          refine ⟨4181512278312726721054247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11150699408833937922811325 4181512278312726721054247)
          ·
            refine ⟨6272268417469090081581371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4181512278312726721054247 6272268417469090081581371)
            ·
              refine ⟨9408402626203635122372057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6272268417469090081581371 9408402626203635122372057)
              ·
                refine ⟨7056301969652726341779043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9408402626203635122372057 7056301969652726341779043)
                ·
                  refine ⟨10584452954479089512668565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7056301969652726341779043 10584452954479089512668565)
                  ·
                    refine ⟨496146232241207320906339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10584452954479089512668565 496146232241207320906339)
                    ·
                      rfl

theorem cell23_2898724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_2898724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898724 prefixEnd_2898724 := by exact prefixLift 2898724
  have htrace : WordTrace (prefixWord ++ tailWord_2898724) baseStart_2898724 baseEnd_2898724 := by
    simpa [prefixWord, tailWord_2898724, baseEnd_2898724] using wordTrace_append hprefix tailTrace_2898724
  have hstable : (prefixWord ++ tailWord_2898724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898724).length < 2 ^ (prefixWord ++ tailWord_2898724).sum := by decide
  have hdescent : baseEnd_2898724 < baseStart_2898724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898741 : List Nat := [1, 3, 3, 1, 3, 2, 2, 2, 2, 4]
def baseStart_2898741 : Nat := 118140960795 + 2898741 * 2 ^ 59
def prefixEnd_2898741 : Nat := 4983230072969 + 3 ^ 40 * 2898741 * 2
def baseEnd_2898741 : Nat := 496149141964916132068813

theorem tailTrace_2898741 : CollatzResearch.WordTrace tailWord_2898741 prefixEnd_2898741 496149141964916132068813 := by
  unfold tailWord_2898741
  simp only [CollatzResearch.WordTrace]
  refine ⟨105725769991363897393728077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70483846660909264929152051 105725769991363897393728077)
  ·
    refine ⟨39647163746761461522648029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105725769991363897393728077 39647163746761461522648029)
    ·
      refine ⟨14867686405035548070993011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39647163746761461522648029 14867686405035548070993011)
      ·
        refine ⟨22301529607553322106489517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14867686405035548070993011 22301529607553322106489517)
        ·
          refine ⟨8363073602832495789933569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22301529607553322106489517 8363073602832495789933569)
          ·
            refine ⟨6272305202124371842450177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8363073602832495789933569 6272305202124371842450177)
            ·
              refine ⟨4704228901593278881837633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6272305202124371842450177 4704228901593278881837633)
              ·
                refine ⟨3528171676194959161378225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4704228901593278881837633 3528171676194959161378225)
                ·
                  refine ⟨2646128757146219371033669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3528171676194959161378225 2646128757146219371033669)
                  ·
                    refine ⟨496149141964916132068813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2646128757146219371033669 496149141964916132068813)
                    ·
                      rfl

theorem cell23_2898741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_2898741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898741 prefixEnd_2898741 := by exact prefixLift 2898741
  have htrace : WordTrace (prefixWord ++ tailWord_2898741) baseStart_2898741 baseEnd_2898741 := by
    simpa [prefixWord, tailWord_2898741, baseEnd_2898741] using wordTrace_append hprefix tailTrace_2898741
  have hstable : (prefixWord ++ tailWord_2898741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898741).length < 2 ^ (prefixWord ++ tailWord_2898741).sum := by decide
  have hdescent : baseEnd_2898741 < baseStart_2898741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898758 : List Nat := [6, 1, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_2898758 : Nat := 118140960795 + 2898758 * 2 ^ 59
def prefixEnd_2898758 : Nat := 4983230072969 + 3 ^ 40 * 2898758 * 2
def baseEnd_2898758 : Nat := 496152051688624943231287

theorem tailTrace_2898758 : CollatzResearch.WordTrace tailWord_2898758 prefixEnd_2898758 496152051688624943231287 := by
  unfold tailWord_2898758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3303949688509447165534279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 70484260021534872864731285 3303949688509447165534279)
  ·
    refine ⟨4955924532764170748301419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3303949688509447165534279 4955924532764170748301419)
    ·
      refine ⟨7433886799146256122452129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4955924532764170748301419 7433886799146256122452129)
      ·
        refine ⟨5575415099359692091839097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7433886799146256122452129 5575415099359692091839097)
        ·
          refine ⟨4181561324519769068879323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5575415099359692091839097 4181561324519769068879323)
          ·
            refine ⟨6272341986779653603318985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4181561324519769068879323 6272341986779653603318985)
            ·
              refine ⟨4704256490084740202489239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6272341986779653603318985 4704256490084740202489239)
              ·
                refine ⟨7056384735127110303733859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4704256490084740202489239 7056384735127110303733859)
                ·
                  refine ⟨10584577102690665455600789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7056384735127110303733859 10584577102690665455600789)
                  ·
                    refine ⟨496152051688624943231287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10584577102690665455600789 496152051688624943231287)
                    ·
                      rfl

theorem cell23_2898758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_2898758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898758 prefixEnd_2898758 := by exact prefixLift 2898758
  have htrace : WordTrace (prefixWord ++ tailWord_2898758) baseStart_2898758 baseEnd_2898758 := by
    simpa [prefixWord, tailWord_2898758, baseEnd_2898758] using wordTrace_append hprefix tailTrace_2898758
  have hstable : (prefixWord ++ tailWord_2898758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898758).length < 2 ^ (prefixWord ++ tailWord_2898758).sum := by decide
  have hdescent : baseEnd_2898758 < baseStart_2898758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898764 : List Nat := [2, 2, 1, 3, 3, 1, 1, 3, 1, 3, 3]
def baseStart_2898764 : Nat := 118140960795 + 2898764 * 2 ^ 59
def prefixEnd_2898764 : Nat := 4983230072969 + 3 ^ 40 * 2898764 * 2
def baseEnd_2898764 : Nat := 1488459235949801806218833

theorem tailTrace_2898764 : CollatzResearch.WordTrace tailWord_2898764 prefixEnd_2898764 1488459235949801806218833 := by
  unfold tailWord_2898764
  simp only [CollatzResearch.WordTrace]
  refine ⟨52863304435140286160907673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70484405913520381547876897 52863304435140286160907673)
  ·
    refine ⟨39647478326355214620680755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52863304435140286160907673 39647478326355214620680755)
    ·
      refine ⟨59471217489532821931021133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39647478326355214620680755 59471217489532821931021133)
      ·
        refine ⟨22301706558574808224132925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59471217489532821931021133 22301706558574808224132925)
        ·
          refine ⟨8363139959465553084049847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22301706558574808224132925 8363139959465553084049847)
          ·
            refine ⟨12544709939198329626074771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8363139959465553084049847 12544709939198329626074771)
            ·
              refine ⟨18817064908797494439112157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12544709939198329626074771 18817064908797494439112157)
              ·
                refine ⟨7056399340799060414667059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18817064908797494439112157 7056399340799060414667059)
                ·
                  refine ⟨10584599011198590622000589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7056399340799060414667059 10584599011198590622000589)
                  ·
                    refine ⟨3969224629199471483250221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10584599011198590622000589 3969224629199471483250221)
                    ·
                      refine ⟨1488459235949801806218833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3969224629199471483250221 1488459235949801806218833)
                      ·
                        rfl

theorem cell23_2898764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_2898764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898764 prefixEnd_2898764 := by exact prefixLift 2898764
  have htrace : WordTrace (prefixWord ++ tailWord_2898764) baseStart_2898764 baseEnd_2898764 := by
    simpa [prefixWord, tailWord_2898764, baseEnd_2898764] using wordTrace_append hprefix tailTrace_2898764
  have hstable : (prefixWord ++ tailWord_2898764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898764).length < 2 ^ (prefixWord ++ tailWord_2898764).sum := by decide
  have hdescent : baseEnd_2898764 < baseStart_2898764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898765 : List Nat := [1, 6, 1, 2, 2, 1, 1, 2, 3, 2, 2]
def baseStart_2898765 : Nat := 118140960795 + 2898765 * 2 ^ 59
def prefixEnd_2898765 : Nat := 4983230072969 + 3 ^ 40 * 2898765 * 2
def baseEnd_2898765 : Nat := 1488459749430456302306329

theorem tailTrace_2898765 : CollatzResearch.WordTrace tailWord_2898765 prefixEnd_2898765 1488459749430456302306329 := by
  unfold tailWord_2898765
  simp only [CollatzResearch.WordTrace]
  refine ⟨105726645343276949492601749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70484430228851299661734499 105726645343276949492601749)
  ·
    refine ⟨4955936500466107007465707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 105726645343276949492601749 4955936500466107007465707)
    ·
      refine ⟨7433904750699160511198561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4955936500466107007465707 7433904750699160511198561)
      ·
        refine ⟨5575428563024370383398921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7433904750699160511198561 5575428563024370383398921)
        ·
          refine ⟨4181571422268277787549191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5575428563024370383398921 4181571422268277787549191)
          ·
            refine ⟨6272357133402416681323787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4181571422268277787549191 6272357133402416681323787)
            ·
              refine ⟨9408535700103625021985681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6272357133402416681323787 9408535700103625021985681)
              ·
                refine ⟨7056401775077718766489261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9408535700103625021985681 7056401775077718766489261)
                ·
                  refine ⟨2646150665654144537433473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7056401775077718766489261 2646150665654144537433473)
                  ·
                    refine ⟨1984612999240608403075105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2646150665654144537433473 1984612999240608403075105)
                    ·
                      refine ⟨1488459749430456302306329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1984612999240608403075105 1488459749430456302306329)
                      ·
                        rfl

theorem cell23_2898765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_2898765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898765 prefixEnd_2898765 := by exact prefixLift 2898765
  have htrace : WordTrace (prefixWord ++ tailWord_2898765) baseStart_2898765 baseEnd_2898765 := by
    simpa [prefixWord, tailWord_2898765, baseEnd_2898765] using wordTrace_append hprefix tailTrace_2898765
  have hstable : (prefixWord ++ tailWord_2898765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898765).length < 2 ^ (prefixWord ++ tailWord_2898765).sum := by decide
  have hdescent : baseEnd_2898765 < baseStart_2898765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898798 : List Nat := [4, 1, 2, 3, 2, 1, 1, 1, 4, 1, 3]
def baseStart_2898798 : Nat := 118140960795 + 2898798 * 2 ^ 59
def prefixEnd_2898798 : Nat := 4983230072969 + 3 ^ 40 * 2898798 * 2
def baseEnd_2898798 : Nat := 1488476694292054673193677

theorem tailTrace_2898798 : CollatzResearch.WordTrace tailWord_2898798 prefixEnd_2898798 1488476694292054673193677 := by
  unfold tailWord_2898798
  simp only [CollatzResearch.WordTrace]
  refine ⟨13215981119019674516069131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70485232634771597419035365 13215981119019674516069131)
  ·
    refine ⟨19823971678529511774103697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13215981119019674516069131 19823971678529511774103697)
    ·
      refine ⟨14867978758897133830577773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19823971678529511774103697 14867978758897133830577773)
      ·
        refine ⟨5575492034586425186466665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14867978758897133830577773 5575492034586425186466665)
        ·
          refine ⟨4181619025939818889849999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5575492034586425186466665 4181619025939818889849999)
          ·
            refine ⟨6272428538909728334774999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4181619025939818889849999 6272428538909728334774999)
            ·
              refine ⟨9408642808364592502162499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6272428538909728334774999 9408642808364592502162499)
              ·
                refine ⟨14112964212546888753243749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9408642808364592502162499 14112964212546888753243749)
                ·
                  refine ⟨2646180789852541641233203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14112964212546888753243749 2646180789852541641233203)
                  ·
                    refine ⟨3969271184778812461849805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2646180789852541641233203 3969271184778812461849805)
                    ·
                      refine ⟨1488476694292054673193677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3969271184778812461849805 1488476694292054673193677)
                      ·
                        rfl

theorem cell23_2898798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_2898798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898798 prefixEnd_2898798 := by exact prefixLift 2898798
  have htrace : WordTrace (prefixWord ++ tailWord_2898798) baseStart_2898798 baseEnd_2898798 := by
    simpa [prefixWord, tailWord_2898798, baseEnd_2898798] using wordTrace_append hprefix tailTrace_2898798
  have hstable : (prefixWord ++ tailWord_2898798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898798).length < 2 ^ (prefixWord ++ tailWord_2898798).sum := by decide
  have hdescent : baseEnd_2898798 < baseStart_2898798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898807 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 1, 6, 3]
def baseStart_2898807 : Nat := 118140960795 + 2898807 * 2 ^ 59
def prefixEnd_2898807 : Nat := 4983230072969 + 3 ^ 40 * 2898807 * 2
def baseEnd_2898807 : Nat := 1488481315617945137981135

theorem tailTrace_2898807 : CollatzResearch.WordTrace tailWord_2898807 prefixEnd_2898807 1488481315617945137981135 := by
  unfold tailWord_2898807
  simp only [CollatzResearch.WordTrace]
  refine ⟨105728177209124790665630675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70485451472749860443753783 105728177209124790665630675)
  ·
    refine ⟨158592265813687185998446013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105728177209124790665630675 158592265813687185998446013)
    ·
      refine ⟨59472099680132694749417255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158592265813687185998446013 59472099680132694749417255)
      ·
        refine ⟨89208149520199042124125883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59472099680132694749417255 89208149520199042124125883)
        ·
          refine ⟨133812224280298563186188825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89208149520199042124125883 133812224280298563186188825)
          ·
            refine ⟨100359168210223922389641619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133812224280298563186188825 100359168210223922389641619)
            ·
              refine ⟨150538752315335883584462429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100359168210223922389641619 150538752315335883584462429)
              ·
                refine ⟨56452032118250956344173411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150538752315335883584462429 56452032118250956344173411)
                ·
                  refine ⟨84678048177376434516260117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56452032118250956344173411 84678048177376434516260117)
                  ·
                    refine ⟨3969283508314520367949693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84678048177376434516260117 3969283508314520367949693)
                    ·
                      refine ⟨1488481315617945137981135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3969283508314520367949693 1488481315617945137981135)
                      ·
                        rfl

theorem cell23_2898807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6, 3].length) (baseStart_2898807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898807 prefixEnd_2898807 := by exact prefixLift 2898807
  have htrace : WordTrace (prefixWord ++ tailWord_2898807) baseStart_2898807 baseEnd_2898807 := by
    simpa [prefixWord, tailWord_2898807, baseEnd_2898807] using wordTrace_append hprefix tailTrace_2898807
  have hstable : (prefixWord ++ tailWord_2898807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898807).length < 2 ^ (prefixWord ++ tailWord_2898807).sum := by decide
  have hdescent : baseEnd_2898807 < baseStart_2898807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898821 : List Nat := [1, 3, 1, 1, 3, 3, 3, 1, 1, 4, 2]
def baseStart_2898821 : Nat := 118140960795 + 2898821 * 2 ^ 59
def prefixEnd_2898821 : Nat := 4983230072969 + 3 ^ 40 * 2898821 * 2
def baseEnd_2898821 : Nat := 1488488504347108083206071

theorem tailTrace_2898821 : CollatzResearch.WordTrace tailWord_2898821 prefixEnd_2898821 1488488504347108083206071 := by
  unfold tailWord_2898821
  simp only [CollatzResearch.WordTrace]
  refine ⟨105728687831074071056640317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70485791887382714037760211 105728687831074071056640317)
  ·
    refine ⟨39648257936652776646240119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105728687831074071056640317 39648257936652776646240119)
    ·
      refine ⟨59472386904979164969360179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39648257936652776646240119 59472386904979164969360179)
      ·
        refine ⟨89208580357468747454040269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59472386904979164969360179 89208580357468747454040269)
        ·
          refine ⟨33453217634050780295265101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89208580357468747454040269 33453217634050780295265101)
          ·
            refine ⟨12544956612769042610724413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33453217634050780295265101 12544956612769042610724413)
            ·
              refine ⟨4704358729788390979021655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12544956612769042610724413 4704358729788390979021655)
              ·
                refine ⟨7056538094682586468532483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4704358729788390979021655 7056538094682586468532483)
                ·
                  refine ⟨10584807142023879702798725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7056538094682586468532483 10584807142023879702798725)
                  ·
                    refine ⟨1984651339129477444274761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10584807142023879702798725 1984651339129477444274761)
                    ·
                      refine ⟨1488488504347108083206071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1984651339129477444274761 1488488504347108083206071)
                      ·
                        rfl

theorem cell23_2898821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 4, 2].length) (baseStart_2898821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898821 prefixEnd_2898821 := by exact prefixLift 2898821
  have htrace : WordTrace (prefixWord ++ tailWord_2898821) baseStart_2898821 baseEnd_2898821 := by
    simpa [prefixWord, tailWord_2898821, baseEnd_2898821] using wordTrace_append hprefix tailTrace_2898821
  have hstable : (prefixWord ++ tailWord_2898821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898821).length < 2 ^ (prefixWord ++ tailWord_2898821).sum := by decide
  have hdescent : baseEnd_2898821 < baseStart_2898821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898827 : List Nat := [1, 1, 1, 1, 4, 2, 4, 2, 7]
def baseStart_2898827 : Nat := 118140960795 + 2898827 * 2 ^ 59
def prefixEnd_2898827 : Nat := 4983230072969 + 3 ^ 40 * 2898827 * 2
def baseEnd_2898827 : Nat := 165387953914559451081227

theorem tailTrace_2898827 : CollatzResearch.WordTrace tailWord_2898827 prefixEnd_2898827 165387953914559451081227 := by
  unfold tailWord_2898827
  simp only [CollatzResearch.WordTrace]
  refine ⟨105728906669052334081358735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70485937779368222720905823 105728906669052334081358735)
  ·
    refine ⟨158593360003578501122038103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105728906669052334081358735 158593360003578501122038103)
    ·
      refine ⟨237890040005367751683057155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158593360003578501122038103 237890040005367751683057155)
      ·
        refine ⟨356835060008051627524585733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237890040005367751683057155 356835060008051627524585733)
        ·
          refine ⟨66906573751509680160859825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 356835060008051627524585733 66906573751509680160859825)
          ·
            refine ⟨50179930313632260120644869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66906573751509680160859825 50179930313632260120644869)
            ·
              refine ⟨9408736933806048772620913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50179930313632260120644869 9408736933806048772620913)
              ·
                refine ⟨7056552700354536579465685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9408736933806048772620913 7056552700354536579465685)
                ·
                  refine ⟨165387953914559451081227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7056552700354536579465685 165387953914559451081227)
                  ·
                    rfl

theorem cell23_2898827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 7].length) (baseStart_2898827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898827 prefixEnd_2898827 := by exact prefixLift 2898827
  have htrace : WordTrace (prefixWord ++ tailWord_2898827) baseStart_2898827 baseEnd_2898827 := by
    simpa [prefixWord, tailWord_2898827, baseEnd_2898827] using wordTrace_append hprefix tailTrace_2898827
  have hstable : (prefixWord ++ tailWord_2898827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898827).length < 2 ^ (prefixWord ++ tailWord_2898827).sum := by decide
  have hdescent : baseEnd_2898827 < baseStart_2898827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898887 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 2, 8]
def baseStart_2898887 : Nat := 118140960795 + 2898887 * 2 ^ 59
def prefixEnd_2898887 : Nat := 4983230072969 + 3 ^ 40 * 2898887 * 2
def baseEnd_2898887 : Nat := 496174131356768274993589

theorem tailTrace_2898887 : CollatzResearch.WordTrace tailWord_2898887 prefixEnd_2898887 496174131356768274993589 := by
  unfold tailWord_2898887
  simp only [CollatzResearch.WordTrace]
  refine ⟨105731095048834964328542915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70487396699223309552361943 105731095048834964328542915)
  ·
    refine ⟨158596642573252446492814373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105731095048834964328542915 158596642573252446492814373)
    ·
      refine ⟨29736870482484833717402695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158596642573252446492814373 29736870482484833717402695)
      ·
        refine ⟨44605305723727250576104043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29736870482484833717402695 44605305723727250576104043)
        ·
          refine ⟨66907958585590875864156065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44605305723727250576104043 66907958585590875864156065)
          ·
            refine ⟨50180968939193156898117049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66907958585590875864156065 50180968939193156898117049)
            ·
              refine ⟨37635726704394867673587787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50180968939193156898117049 37635726704394867673587787)
              ·
                refine ⟨56453590056592301510381681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37635726704394867673587787 56453590056592301510381681)
                ·
                  refine ⟨42340192542444226132786261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56453590056592301510381681 42340192542444226132786261)
                  ·
                    refine ⟨496174131356768274993589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42340192542444226132786261 496174131356768274993589)
                    ·
                      rfl

theorem cell23_2898887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_2898887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898887 prefixEnd_2898887 := by exact prefixLift 2898887
  have htrace : WordTrace (prefixWord ++ tailWord_2898887) baseStart_2898887 baseEnd_2898887 := by
    simpa [prefixWord, tailWord_2898887, baseEnd_2898887] using wordTrace_append hprefix tailTrace_2898887
  have hstable : (prefixWord ++ tailWord_2898887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898887).length < 2 ^ (prefixWord ++ tailWord_2898887).sum := by decide
  have hdescent : baseEnd_2898887 < baseStart_2898887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898978 : List Nat := [3, 3, 1, 1, 1, 3, 1, 3, 3, 1, 3]
def baseStart_2898978 : Nat := 118140960795 + 2898978 * 2 ^ 59
def prefixEnd_2898978 : Nat := 4983230072969 + 3 ^ 40 * 2898978 * 2
def baseEnd_2898978 : Nat := 1488569120809863968942849

theorem tailTrace_2898978 : CollatzResearch.WordTrace tailWord_2898978 prefixEnd_2898978 1488569120809863968942849 := by
  unfold tailWord_2898978
  simp only [CollatzResearch.WordTrace]
  refine ⟨26433603522876321717526397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70489609394336857913403725 26433603522876321717526397)
  ·
    refine ⟨9912601321078620644072399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26433603522876321717526397 9912601321078620644072399)
    ·
      refine ⟨14868901981617930966108599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9912601321078620644072399 14868901981617930966108599)
      ·
        refine ⟨22303352972426896449162899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14868901981617930966108599 22303352972426896449162899)
        ·
          refine ⟨33455029458640344673744349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22303352972426896449162899 33455029458640344673744349)
          ·
            refine ⟨12545636046990129252654131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33455029458640344673744349 12545636046990129252654131)
            ·
              refine ⟨18818454070485193878981197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12545636046990129252654131 18818454070485193878981197)
              ·
                refine ⟨7056920276431947704617949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18818454070485193878981197 7056920276431947704617949)
                ·
                  refine ⟨2646345103661980389231731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7056920276431947704617949 2646345103661980389231731)
                  ·
                    refine ⟨3969517655492970583847597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2646345103661980389231731 3969517655492970583847597)
                    ·
                      refine ⟨1488569120809863968942849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3969517655492970583847597 1488569120809863968942849)
                      ·
                        rfl

theorem cell23_2898978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_2898978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898978 prefixEnd_2898978 := by exact prefixLift 2898978
  have htrace : WordTrace (prefixWord ++ tailWord_2898978) baseStart_2898978 baseEnd_2898978 := by
    simpa [prefixWord, tailWord_2898978, baseEnd_2898978] using wordTrace_append hprefix tailTrace_2898978
  have hstable : (prefixWord ++ tailWord_2898978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898978).length < 2 ^ (prefixWord ++ tailWord_2898978).sum := by decide
  have hdescent : baseEnd_2898978 < baseStart_2898978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898998 : List Nat := [5, 1, 2, 1, 1, 2, 1, 4, 1, 5]
def baseStart_2898998 : Nat := 118140960795 + 2898998 * 2 ^ 59
def prefixEnd_2898998 : Nat := 4983230072969 + 3 ^ 40 * 2898998 * 2
def baseEnd_2898998 : Nat := 496193130140984630230919

theorem tailTrace_2898998 : CollatzResearch.WordTrace tailWord_2898998 prefixEnd_2898998 496193130140984630230919 := by
  unfold tailWord_2898998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6608446471964551892864603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70490095700955220190555765 6608446471964551892864603)
  ·
    refine ⟨9912669707946827839296905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6608446471964551892864603 9912669707946827839296905)
    ·
      refine ⟨7434502280960120879472679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9912669707946827839296905 7434502280960120879472679)
      ·
        refine ⟨11151753421440181319209019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7434502280960120879472679 11151753421440181319209019)
        ·
          refine ⟨16727630132160271978813529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11151753421440181319209019 16727630132160271978813529)
          ·
            refine ⟨12545722599120203984110147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16727630132160271978813529 12545722599120203984110147)
            ·
              refine ⟨18818583898680305976165221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12545722599120203984110147 18818583898680305976165221)
              ·
                refine ⟨3528484481002557370530979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18818583898680305976165221 3528484481002557370530979)
                ·
                  refine ⟨5292726721503836055796469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3528484481002557370530979 5292726721503836055796469)
                  ·
                    refine ⟨496193130140984630230919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5292726721503836055796469 496193130140984630230919)
                    ·
                      rfl

theorem cell23_2898998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_2898998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898998 prefixEnd_2898998 := by exact prefixLift 2898998
  have htrace : WordTrace (prefixWord ++ tailWord_2898998) baseStart_2898998 baseEnd_2898998 := by
    simpa [prefixWord, tailWord_2898998, baseEnd_2898998] using wordTrace_append hprefix tailTrace_2898998
  have hstable : (prefixWord ++ tailWord_2898998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898998).length < 2 ^ (prefixWord ++ tailWord_2898998).sum := by decide
  have hdescent : baseEnd_2898998 < baseStart_2898998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899018 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 5, 2, 2]
def baseStart_2899018 : Nat := 118140960795 + 2899018 * 2 ^ 59
def prefixEnd_2899018 : Nat := 4983230072969 + 3 ^ 40 * 2899018 * 2
def baseEnd_2899018 : Nat := 1488589660036043812442665

theorem tailTrace_2899018 : CollatzResearch.WordTrace tailWord_2899018 prefixEnd_2899018 1488589660036043812442665 := by
  unfold tailWord_2899018
  simp only [CollatzResearch.WordTrace]
  refine ⟨26433968252840093425390427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70490582007573582467707805 26433968252840093425390427)
  ·
    refine ⟨39650952379260140138085641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26433968252840093425390427 39650952379260140138085641)
    ·
      refine ⟨29738214284445105103564231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39650952379260140138085641 29738214284445105103564231)
      ·
        refine ⟨44607321426667657655346347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29738214284445105103564231 44607321426667657655346347)
        ·
          refine ⟨66910982140001486483019521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44607321426667657655346347 66910982140001486483019521)
          ·
            refine ⟨50183236605001114862264641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66910982140001486483019521 50183236605001114862264641)
            ·
              refine ⟨37637427453750836146698481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50183236605001114862264641 37637427453750836146698481)
              ·
                refine ⟨28228070590313127110023861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37637427453750836146698481 28228070590313127110023861)
                ·
                  refine ⟨2646381617841855666564737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28228070590313127110023861 2646381617841855666564737)
                  ·
                    refine ⟨1984786213381391749923553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2646381617841855666564737 1984786213381391749923553)
                    ·
                      refine ⟨1488589660036043812442665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1984786213381391749923553 1488589660036043812442665)
                      ·
                        rfl

theorem cell23_2899018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 5, 2, 2].length) (baseStart_2899018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899018 prefixEnd_2899018 := by exact prefixLift 2899018
  have htrace : WordTrace (prefixWord ++ tailWord_2899018) baseStart_2899018 baseEnd_2899018 := by
    simpa [prefixWord, tailWord_2899018, baseEnd_2899018] using wordTrace_append hprefix tailTrace_2899018
  have hstable : (prefixWord ++ tailWord_2899018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899018).length < 2 ^ (prefixWord ++ tailWord_2899018).sum := by decide
  have hdescent : baseEnd_2899018 < baseStart_2899018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899044 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 1, 4, 6]
def baseStart_2899044 : Nat := 118140960795 + 2899044 * 2 ^ 59
def prefixEnd_2899044 : Nat := 4983230072969 + 3 ^ 40 * 2899044 * 2
def baseEnd_2899044 : Nat := 1488603010533060710717545

theorem tailTrace_2899044 : CollatzResearch.WordTrace tailWord_2899044 prefixEnd_2899044 1488603010533060710717545 := by
  unfold tailWord_2899044
  simp only [CollatzResearch.WordTrace]
  refine ⟨52868410654633090071004093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70491214206177453428005457 52868410654633090071004093)
  ·
    refine ⟨19825653995487408776626535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52868410654633090071004093 19825653995487408776626535)
    ·
      refine ⟨29738480993231113164939803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19825653995487408776626535 29738480993231113164939803)
      ·
        refine ⟨44607721489846669747409705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29738480993231113164939803 44607721489846669747409705)
        ·
          refine ⟨33455791117385002310557279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44607721489846669747409705 33455791117385002310557279)
          ·
            refine ⟨50183686676077503465835919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33455791117385002310557279 50183686676077503465835919)
            ·
              refine ⟨75275530014116255198753879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50183686676077503465835919 75275530014116255198753879)
              ·
                refine ⟨112913295021174382798130819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75275530014116255198753879 112913295021174382798130819)
                ·
                  refine ⟨169369942531761574197196229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112913295021174382798130819 169369942531761574197196229)
                  ·
                    refine ⟨31756864224705295161974293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 169369942531761574197196229 31756864224705295161974293)
                    ·
                      refine ⟨1488603010533060710717545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31756864224705295161974293 1488603010533060710717545)
                      ·
                        rfl

theorem cell23_2899044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_2899044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899044 prefixEnd_2899044 := by exact prefixLift 2899044
  have htrace : WordTrace (prefixWord ++ tailWord_2899044) baseStart_2899044 baseEnd_2899044 := by
    simpa [prefixWord, tailWord_2899044, baseEnd_2899044] using wordTrace_append hprefix tailTrace_2899044
  have hstable : (prefixWord ++ tailWord_2899044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899044).length < 2 ^ (prefixWord ++ tailWord_2899044).sum := by decide
  have hdescent : baseEnd_2899044 < baseStart_2899044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899064 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 1, 4, 5]
def baseStart_2899064 : Nat := 118140960795 + 2899064 * 2 ^ 59
def prefixEnd_2899064 : Nat := 4983230072969 + 3 ^ 40 * 2899064 * 2
def baseEnd_2899064 : Nat := 1488613280146150632467453

theorem tailTrace_2899064 : CollatzResearch.WordTrace tailWord_2899064 prefixEnd_2899064 1488613280146150632467453 := by
  unfold tailWord_2899064
  simp only [CollatzResearch.WordTrace]
  refine ⟨52868775384596861778868123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70491700512795815705157497 52868775384596861778868123)
  ·
    refine ⟨79303163076895292668302185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52868775384596861778868123 79303163076895292668302185)
    ·
      refine ⟨59477372307671469501226639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79303163076895292668302185 59477372307671469501226639)
      ·
        refine ⟨89216058461507204251839959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59477372307671469501226639 89216058461507204251839959)
        ·
          refine ⟨133824087692260806377759939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89216058461507204251839959 133824087692260806377759939)
          ·
            refine ⟨200736131538391209566639909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133824087692260806377759939 200736131538391209566639909)
            ·
              refine ⟨37638024663448351793744983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 200736131538391209566639909 37638024663448351793744983)
              ·
                refine ⟨56457036995172527690617475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37638024663448351793744983 56457036995172527690617475)
                ·
                  refine ⟨84685555492758791535926213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56457036995172527690617475 84685555492758791535926213)
                  ·
                    refine ⟨15878541654892273412986165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84685555492758791535926213 15878541654892273412986165)
                    ·
                      refine ⟨1488613280146150632467453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15878541654892273412986165 1488613280146150632467453)
                      ·
                        rfl

theorem cell23_2899064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_2899064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899064 prefixEnd_2899064 := by exact prefixLift 2899064
  have htrace : WordTrace (prefixWord ++ tailWord_2899064) baseStart_2899064 baseEnd_2899064 := by
    simpa [prefixWord, tailWord_2899064, baseEnd_2899064] using wordTrace_append hprefix tailTrace_2899064
  have hstable : (prefixWord ++ tailWord_2899064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899064).length < 2 ^ (prefixWord ++ tailWord_2899064).sum := by decide
  have hdescent : baseEnd_2899064 < baseStart_2899064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899084 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 3, 8]
def baseStart_2899084 : Nat := 118140960795 + 2899084 * 2 ^ 59
def prefixEnd_2899084 : Nat := 4983230072969 + 3 ^ 40 * 2899084 * 2
def baseEnd_2899084 : Nat := 496207849919746851405787

theorem tailTrace_2899084 : CollatzResearch.WordTrace tailWord_2899084 prefixEnd_2899084 496207849919746851405787 := by
  unfold tailWord_2899084
  simp only [CollatzResearch.WordTrace]
  refine ⟨52869140114560633486732153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70492186819414177982309537 52869140114560633486732153)
  ·
    refine ⟨39651855085920475115049115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52869140114560633486732153 39651855085920475115049115)
    ·
      refine ⟨59477782628880712672573673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39651855085920475115049115 59477782628880712672573673)
      ·
        refine ⟨44608336971660534504430255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59477782628880712672573673 44608336971660534504430255)
        ·
          refine ⟨66912505457490801756645383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44608336971660534504430255 66912505457490801756645383)
          ·
            refine ⟨100368758186236202634968075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66912505457490801756645383 100368758186236202634968075)
            ·
              refine ⟨150553137279354303952452113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100368758186236202634968075 150553137279354303952452113)
              ·
                refine ⟨112914852959515727964339085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150553137279354303952452113 112914852959515727964339085)
                ·
                  refine ⟨42343069859818397986627157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112914852959515727964339085 42343069859818397986627157)
                  ·
                    refine ⟨496207849919746851405787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42343069859818397986627157 496207849919746851405787)
                    ·
                      rfl

theorem cell23_2899084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 8].length) (baseStart_2899084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899084 prefixEnd_2899084 := by exact prefixLift 2899084
  have htrace : WordTrace (prefixWord ++ tailWord_2899084) baseStart_2899084 baseEnd_2899084 := by
    simpa [prefixWord, tailWord_2899084, baseEnd_2899084] using wordTrace_append hprefix tailTrace_2899084
  have hstable : (prefixWord ++ tailWord_2899084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899084).length < 2 ^ (prefixWord ++ tailWord_2899084).sum := by decide
  have hdescent : baseEnd_2899084 < baseStart_2899084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899086 : List Nat := [4, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2]
def baseStart_2899086 : Nat := 118140960795 + 2899086 * 2 ^ 59
def prefixEnd_2899086 : Nat := 4983230072969 + 3 ^ 40 * 2899086 * 2
def baseEnd_2899086 : Nat := 1488624576720549546392353

theorem tailTrace_2899086 : CollatzResearch.WordTrace tailWord_2899086 prefixEnd_2899086 1488624576720549546392353 := by
  unfold tailWord_2899086
  simp only [CollatzResearch.WordTrace]
  refine ⟨13217294146889252664379639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70492235450076014210024741 13217294146889252664379639)
  ·
    refine ⟨19825941220333878996569459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13217294146889252664379639 19825941220333878996569459)
    ·
      refine ⟨29738911830500818494854189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19825941220333878996569459 29738911830500818494854189)
      ·
        refine ⟨11152091936437806935570321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29738911830500818494854189 11152091936437806935570321)
        ·
          refine ⟨8364068952328355201677741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11152091936437806935570321 8364068952328355201677741)
          ·
            refine ⟨3136525857123133200629153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8364068952328355201677741 3136525857123133200629153)
            ·
              refine ⟨2352394392842349900471865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3136525857123133200629153 2352394392842349900471865)
              ·
                refine ⟨1764295794631762425353899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2352394392842349900471865 1764295794631762425353899)
                ·
                  refine ⟨2646443691947643638030849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1764295794631762425353899 2646443691947643638030849)
                  ·
                    refine ⟨1984832768960732728523137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2646443691947643638030849 1984832768960732728523137)
                    ·
                      refine ⟨1488624576720549546392353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1984832768960732728523137 1488624576720549546392353)
                      ·
                        rfl

theorem cell23_2899086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_2899086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899086 prefixEnd_2899086 := by exact prefixLift 2899086
  have htrace : WordTrace (prefixWord ++ tailWord_2899086) baseStart_2899086 baseEnd_2899086 := by
    simpa [prefixWord, tailWord_2899086, baseEnd_2899086] using wordTrace_append hprefix tailTrace_2899086
  have hstable : (prefixWord ++ tailWord_2899086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899086).length < 2 ^ (prefixWord ++ tailWord_2899086).sum := by decide
  have hdescent : baseEnd_2899086 < baseStart_2899086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899101 : List Nat := [1, 4, 2, 1, 1, 2, 3, 1, 2, 6]
def baseStart_2899101 : Nat := 118140960795 + 2899101 * 2 ^ 59
def prefixEnd_2899101 : Nat := 4983230072969 + 3 ^ 40 * 2899101 * 2
def baseEnd_2899101 : Nat := 496210759643455662568261

theorem tailTrace_2899101 : CollatzResearch.WordTrace tailWord_2899101 prefixEnd_2899101 496210759643455662568261 := by
  unfold tailWord_2899101
  simp only [CollatzResearch.WordTrace]
  refine ⟨105738900270059678876833157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70492600180039785917888771 105738900270059678876833157)
  ·
    refine ⟨19826043800636189789406217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105738900270059678876833157 19826043800636189789406217)
    ·
      refine ⟨14869532850477142342054663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19826043800636189789406217 14869532850477142342054663)
      ·
        refine ⟨22304299275715713513081995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14869532850477142342054663 22304299275715713513081995)
        ·
          refine ⟨33456448913573570269622993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22304299275715713513081995 33456448913573570269622993)
          ·
            refine ⟨25092336685180177702217245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33456448913573570269622993 25092336685180177702217245)
            ·
              refine ⟨9409626256942566638331467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25092336685180177702217245 9409626256942566638331467)
              ·
                refine ⟨14114439385413849957497201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9409626256942566638331467 14114439385413849957497201)
                ·
                  refine ⟨10585829539060387468122901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14114439385413849957497201 10585829539060387468122901)
                  ·
                    refine ⟨496210759643455662568261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10585829539060387468122901 496210759643455662568261)
                    ·
                      rfl

theorem cell23_2899101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_2899101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899101 prefixEnd_2899101 := by exact prefixLift 2899101
  have htrace : WordTrace (prefixWord ++ tailWord_2899101) baseStart_2899101 baseEnd_2899101 := by
    simpa [prefixWord, tailWord_2899101, baseEnd_2899101] using wordTrace_append hprefix tailTrace_2899101
  have hstable : (prefixWord ++ tailWord_2899101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899101).length < 2 ^ (prefixWord ++ tailWord_2899101).sum := by decide
  have hdescent : baseEnd_2899101 < baseStart_2899101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899102 : List Nat := [4, 3, 1, 1, 2, 1, 2, 3, 2, 1, 3]
def baseStart_2899102 : Nat := 118140960795 + 2899102 * 2 ^ 59
def prefixEnd_2899102 : Nat := 4983230072969 + 3 ^ 40 * 2899102 * 2
def baseEnd_2899102 : Nat := 1488632792411021483792279

theorem tailTrace_2899102 : CollatzResearch.WordTrace tailWord_2899102 prefixEnd_2899102 1488632792411021483792279 := by
  unfold tailWord_2899102
  simp only [CollatzResearch.WordTrace]
  refine ⟨13217367092882007005952445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70492624495370704031746373 13217367092882007005952445)
  ·
    refine ⟨4956512659830752627232167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13217367092882007005952445 4956512659830752627232167)
    ·
      refine ⟨7434768989746128940848251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4956512659830752627232167 7434768989746128940848251)
      ·
        refine ⟨11152153484619193411272377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7434768989746128940848251 11152153484619193411272377)
        ·
          refine ⟨8364115113464395058454283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11152153484619193411272377 8364115113464395058454283)
          ·
            refine ⟨12546172670196592587681425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8364115113464395058454283 12546172670196592587681425)
            ·
              refine ⟨9409629502647444440761069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12546172670196592587681425 9409629502647444440761069)
              ·
                refine ⟨3528611063492791665285401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9409629502647444440761069 3528611063492791665285401)
                ·
                  refine ⟨2646458297619593748964051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3528611063492791665285401 2646458297619593748964051)
                  ·
                    refine ⟨3969687446429390623446077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2646458297619593748964051 3969687446429390623446077)
                    ·
                      refine ⟨1488632792411021483792279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3969687446429390623446077 1488632792411021483792279)
                      ·
                        rfl

theorem cell23_2899102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_2899102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899102 prefixEnd_2899102 := by exact prefixLift 2899102
  have htrace : WordTrace (prefixWord ++ tailWord_2899102) baseStart_2899102 baseEnd_2899102 := by
    simpa [prefixWord, tailWord_2899102, baseEnd_2899102] using wordTrace_append hprefix tailTrace_2899102
  have hstable : (prefixWord ++ tailWord_2899102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899102).length < 2 ^ (prefixWord ++ tailWord_2899102).sum := by decide
  have hdescent : baseEnd_2899102 < baseStart_2899102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899235 : List Nat := [1, 1, 1, 4, 2, 4, 2, 1, 2, 2, 3]
def baseStart_2899235 : Nat := 118140960795 + 2899235 * 2 ^ 59
def prefixEnd_2899235 : Nat := 4983230072969 + 3 ^ 40 * 2899235 * 2
def baseEnd_2899235 : Nat := 1488701085338069463429167

theorem tailTrace_2899235 : CollatzResearch.WordTrace tailWord_2899235 prefixEnd_2899235 1488701085338069463429167 := by
  unfold tailWord_2899235
  simp only [CollatzResearch.WordTrace]
  refine ⟨105743787651574219762211159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70495858434382813174807439 105743787651574219762211159)
  ·
    refine ⟨158615681477361329643316739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105743787651574219762211159 158615681477361329643316739)
    ·
      refine ⟨237923522216041994464975109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158615681477361329643316739 237923522216041994464975109)
      ·
        refine ⟨44610660415507873962182833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 237923522216041994464975109 44610660415507873962182833)
        ·
          refine ⟨33457995311630905471637125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44610660415507873962182833 33457995311630905471637125)
          ·
            refine ⟨6273374120930794775931961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33457995311630905471637125 6273374120930794775931961)
            ·
              refine ⟨4705030590698096081948971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6273374120930794775931961 4705030590698096081948971)
              ·
                refine ⟨7057545886047144122923457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4705030590698096081948971 7057545886047144122923457)
                ·
                  refine ⟨5293159414535358092192593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7057545886047144122923457 5293159414535358092192593)
                  ·
                    refine ⟨3969869560901518569144445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5293159414535358092192593 3969869560901518569144445)
                    ·
                      refine ⟨1488701085338069463429167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3969869560901518569144445 1488701085338069463429167)
                      ·
                        rfl

theorem cell23_2899235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_2899235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899235 prefixEnd_2899235 := by exact prefixLift 2899235
  have htrace : WordTrace (prefixWord ++ tailWord_2899235) baseStart_2899235 baseEnd_2899235 := by
    simpa [prefixWord, tailWord_2899235, baseEnd_2899235] using wordTrace_append hprefix tailTrace_2899235
  have hstable : (prefixWord ++ tailWord_2899235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899235).length < 2 ^ (prefixWord ++ tailWord_2899235).sum := by decide
  have hdescent : baseEnd_2899235 < baseStart_2899235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899286 : List Nat := [5, 2, 3, 1, 1, 1, 1, 1, 1, 4, 3]
def baseStart_2899286 : Nat := 118140960795 + 2899286 * 2 ^ 59
def prefixEnd_2899286 : Nat := 4983230072969 + 3 ^ 40 * 2899286 * 2
def baseEnd_2899286 : Nat := 1488727272851448763891433

theorem tailTrace_2899286 : CollatzResearch.WordTrace tailWord_2899286 prefixEnd_2899286 1488727272851448763891433 := by
  unfold tailWord_2899286
  simp only [CollatzResearch.WordTrace]
  refine ⟨6609102985899340967019857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70497098516259636981545141 6609102985899340967019857)
  ·
    refine ⟨4956827239424505725264893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6609102985899340967019857 4956827239424505725264893)
    ·
      refine ⟨1858810214784189646974335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4956827239424505725264893 1858810214784189646974335)
      ·
        refine ⟨2788215322176284470461503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1858810214784189646974335 2788215322176284470461503)
        ·
          refine ⟨4182322983264426705692255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2788215322176284470461503 4182322983264426705692255)
          ·
            refine ⟨6273484474896640058538383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4182322983264426705692255 6273484474896640058538383)
            ·
              refine ⟨9410226712344960087807575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6273484474896640058538383 9410226712344960087807575)
              ·
                refine ⟨14115340068517440131711363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9410226712344960087807575 14115340068517440131711363)
                ·
                  refine ⟨21173010102776160197567045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14115340068517440131711363 21173010102776160197567045)
                  ·
                    refine ⟨3969939394270530037043821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21173010102776160197567045 3969939394270530037043821)
                    ·
                      refine ⟨1488727272851448763891433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3969939394270530037043821 1488727272851448763891433)
                      ·
                        rfl

theorem cell23_2899286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_2899286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899286 prefixEnd_2899286 := by exact prefixLift 2899286
  have htrace : WordTrace (prefixWord ++ tailWord_2899286) baseStart_2899286 baseEnd_2899286 := by
    simpa [prefixWord, tailWord_2899286, baseEnd_2899286] using wordTrace_append hprefix tailTrace_2899286
  have hstable : (prefixWord ++ tailWord_2899286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899286).length < 2 ^ (prefixWord ++ tailWord_2899286).sum := by decide
  have hdescent : baseEnd_2899286 < baseStart_2899286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899288 : List Nat := [2, 1, 2, 2, 1, 1, 3, 3, 3, 1, 4]
def baseStart_2899288 : Nat := 118140960795 + 2899288 * 2 ^ 59
def prefixEnd_2899288 : Nat := 4983230072969 + 3 ^ 40 * 2899288 * 2
def baseEnd_2899288 : Nat := 1488728299812757756066423

theorem tailTrace_2899288 : CollatzResearch.WordTrace tailWord_2899288 prefixEnd_2899288 1488728299812757756066423 := by
  unfold tailWord_2899288
  simp only [CollatzResearch.WordTrace]
  refine ⟨52872860360191104906945259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70497147146921473209260345 52872860360191104906945259)
  ·
    refine ⟨79309290540286657360417889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52872860360191104906945259 79309290540286657360417889)
    ·
      refine ⟨59481967905214993020313417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79309290540286657360417889 59481967905214993020313417)
      ·
        refine ⟨44611475928911244765235063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59481967905214993020313417 44611475928911244765235063)
        ·
          refine ⟨66917213893366867147852595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44611475928911244765235063 66917213893366867147852595)
          ·
            refine ⟨100375820840050300721778893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66917213893366867147852595 100375820840050300721778893)
            ·
              refine ⟨37640932815018862770667085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100375820840050300721778893 37640932815018862770667085)
              ·
                refine ⟨14115349805632073539000157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37640932815018862770667085 14115349805632073539000157)
                ·
                  refine ⟨5293256177112027577125059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14115349805632073539000157 5293256177112027577125059)
                  ·
                    refine ⟨7939884265668041365687589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5293256177112027577125059 7939884265668041365687589)
                    ·
                      refine ⟨1488728299812757756066423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7939884265668041365687589 1488728299812757756066423)
                      ·
                        rfl

theorem cell23_2899288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_2899288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899288 prefixEnd_2899288 := by exact prefixLift 2899288
  have htrace : WordTrace (prefixWord ++ tailWord_2899288) baseStart_2899288 baseEnd_2899288 := by
    simpa [prefixWord, tailWord_2899288, baseEnd_2899288] using wordTrace_append hprefix tailTrace_2899288
  have hstable : (prefixWord ++ tailWord_2899288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899288).length < 2 ^ (prefixWord ++ tailWord_2899288).sum := by decide
  have hdescent : baseEnd_2899288 < baseStart_2899288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899293 : List Nat := [1, 4, 5, 1, 1, 1, 2, 3, 1, 4]
def baseStart_2899293 : Nat := 118140960795 + 2899293 * 2 ^ 59
def prefixEnd_2899293 : Nat := 4983230072969 + 3 ^ 40 * 2899293 * 2
def baseEnd_2899293 : Nat := 496243622405343412167967

theorem tailTrace_2899293 : CollatzResearch.WordTrace tailWord_2899293 prefixEnd_2899293 496243622405343412167967 := by
  unfold tailWord_2899293
  simp only [CollatzResearch.WordTrace]
  refine ⟨105745903085364095667822533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70497268723576063778548355 105745903085364095667822533)
  ·
    refine ⟨19827356828505767937716725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105745903085364095667822533 19827356828505767937716725)
    ·
      refine ⟨1858814702672415744160943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19827356828505767937716725 1858814702672415744160943)
      ·
        refine ⟨2788222054008623616241415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1858814702672415744160943 2788222054008623616241415)
        ·
          refine ⟨4182333081012935424362123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2788222054008623616241415 4182333081012935424362123)
          ·
            refine ⟨6273499621519403136543185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4182333081012935424362123 6273499621519403136543185)
            ·
              refine ⟨4705124716139552352407389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6273499621519403136543185 4705124716139552352407389)
              ·
                refine ⟨1764421768552332132152771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4705124716139552352407389 1764421768552332132152771)
                ·
                  refine ⟨2646632652828498198229157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1764421768552332132152771 2646632652828498198229157)
                  ·
                    refine ⟨496243622405343412167967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2646632652828498198229157 496243622405343412167967)
                    ·
                      rfl

theorem cell23_2899293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_2899293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899293 prefixEnd_2899293 := by exact prefixLift 2899293
  have htrace : WordTrace (prefixWord ++ tailWord_2899293) baseStart_2899293 baseEnd_2899293 := by
    simpa [prefixWord, tailWord_2899293, baseEnd_2899293] using wordTrace_append hprefix tailTrace_2899293
  have hstable : (prefixWord ++ tailWord_2899293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899293).length < 2 ^ (prefixWord ++ tailWord_2899293).sum := by decide
  have hdescent : baseEnd_2899293 < baseStart_2899293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899299 : List Nat := [1, 1, 1, 5, 2, 3, 2, 3, 1, 1, 3]
def baseStart_2899299 : Nat := 118140960795 + 2899299 * 2 ^ 59
def prefixEnd_2899299 : Nat := 4983230072969 + 3 ^ 40 * 2899299 * 2
def baseEnd_2899299 : Nat := 1488733948099957213028873

theorem tailTrace_2899299 : CollatzResearch.WordTrace tailWord_2899299 prefixEnd_2899299 1488733948099957213028873 := by
  unfold tailWord_2899299
  simp only [CollatzResearch.WordTrace]
  refine ⟨105746121923342358692540951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70497414615561572461693967 105746121923342358692540951)
  ·
    refine ⟨158619182885013538038811427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105746121923342358692540951 158619182885013538038811427)
    ·
      refine ⟨237928774327520307058217141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158619182885013538038811427 237928774327520307058217141)
      ·
        refine ⟨22305822593205028786707857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 237928774327520307058217141 22305822593205028786707857)
        ·
          refine ⟨16729366944903771590030893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22305822593205028786707857 16729366944903771590030893)
          ·
            refine ⟨6273512604338914346261585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16729366944903771590030893 6273512604338914346261585)
            ·
              refine ⟨4705134453254185759696189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6273512604338914346261585 4705134453254185759696189)
              ·
                refine ⟨1764425419970319659886071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4705134453254185759696189 1764425419970319659886071)
                ·
                  refine ⟨2646638129955479489829107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1764425419970319659886071 2646638129955479489829107)
                  ·
                    refine ⟨3969957194933219234743661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2646638129955479489829107 3969957194933219234743661)
                    ·
                      refine ⟨1488733948099957213028873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3969957194933219234743661 1488733948099957213028873)
                      ·
                        rfl

theorem cell23_2899299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_2899299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899299 prefixEnd_2899299 := by exact prefixLift 2899299
  have htrace : WordTrace (prefixWord ++ tailWord_2899299) baseStart_2899299 baseEnd_2899299 := by
    simpa [prefixWord, tailWord_2899299, baseEnd_2899299] using wordTrace_append hprefix tailTrace_2899299
  have hstable : (prefixWord ++ tailWord_2899299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899299).length < 2 ^ (prefixWord ++ tailWord_2899299).sum := by decide
  have hdescent : baseEnd_2899299 < baseStart_2899299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899311 : List Nat := [1, 1, 2, 1, 3, 1, 14]
def baseStart_2899311 : Nat := 118140960795 + 2899311 * 2 ^ 59
def prefixEnd_2899311 : Nat := 4983230072969 + 3 ^ 40 * 2899311 * 2
def baseEnd_2899311 : Nat := 18379507529232236618257

theorem tailTrace_2899311 : CollatzResearch.WordTrace tailWord_2899311 prefixEnd_2899311 18379507529232236618257 := by
  unfold tailWord_2899311
  simp only [CollatzResearch.WordTrace]
  refine ⟨105746559599298884741977787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70497706399532589827985191 105746559599298884741977787)
  ·
    refine ⟨158619839398948327112966681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105746559599298884741977787 158619839398948327112966681)
    ·
      refine ⟨118964879549211245334725011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158619839398948327112966681 118964879549211245334725011)
      ·
        refine ⟨178447319323816868002087517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118964879549211245334725011 178447319323816868002087517)
        ·
          refine ⟨66917744746431325500782819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178447319323816868002087517 66917744746431325500782819)
          ·
            refine ⟨100376617119646988251174229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66917744746431325500782819 100376617119646988251174229)
            ·
              refine ⟨18379507529232236618257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 100376617119646988251174229 18379507529232236618257)
              ·
                rfl

theorem cell23_2899311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 14].length) (baseStart_2899311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899311 prefixEnd_2899311 := by exact prefixLift 2899311
  have htrace : WordTrace (prefixWord ++ tailWord_2899311) baseStart_2899311 baseEnd_2899311 := by
    simpa [prefixWord, tailWord_2899311, baseEnd_2899311] using wordTrace_append hprefix tailTrace_2899311
  have hstable : (prefixWord ++ tailWord_2899311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899311).length < 2 ^ (prefixWord ++ tailWord_2899311).sum := by decide
  have hdescent : baseEnd_2899311 < baseStart_2899311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899335 : List Nat := [1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 4]
def baseStart_2899335 : Nat := 118140960795 + 2899335 * 2 ^ 59
def prefixEnd_2899335 : Nat := 4983230072969 + 3 ^ 40 * 2899335 * 2
def baseEnd_2899335 : Nat := 1488752433403519072178707

theorem tailTrace_2899335 : CollatzResearch.WordTrace tailWord_2899335 prefixEnd_2899335 1488752433403519072178707 := by
  unfold tailWord_2899335
  simp only [CollatzResearch.WordTrace]
  refine ⟨105747434951211936840851459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70498289967474624560567639 105747434951211936840851459)
  ·
    refine ⟨158621152426817905261277189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105747434951211936840851459 158621152426817905261277189)
    ·
      refine ⟨29741466080028357236489473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158621152426817905261277189 29741466080028357236489473)
      ·
        refine ⟨22306099560021267927367105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29741466080028357236489473 22306099560021267927367105)
        ·
          refine ⟨16729574670015950945525329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22306099560021267927367105 16729574670015950945525329)
          ·
            refine ⟨12547181002511963209143997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16729574670015950945525329 12547181002511963209143997)
            ·
              refine ⟨4705192875941986203428999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12547181002511963209143997 4705192875941986203428999)
              ·
                refine ⟨7057789313912979305143499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4705192875941986203428999 7057789313912979305143499)
                ·
                  refine ⟨10586683970869468957715249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7057789313912979305143499 10586683970869468957715249)
                  ·
                    refine ⟨7940012978152101718286437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10586683970869468957715249 7940012978152101718286437)
                    ·
                      refine ⟨1488752433403519072178707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7940012978152101718286437 1488752433403519072178707)
                      ·
                        rfl

theorem cell23_2899335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_2899335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899335 prefixEnd_2899335 := by exact prefixLift 2899335
  have htrace : WordTrace (prefixWord ++ tailWord_2899335) baseStart_2899335 baseEnd_2899335 := by
    simpa [prefixWord, tailWord_2899335, baseEnd_2899335] using wordTrace_append hprefix tailTrace_2899335
  have hstable : (prefixWord ++ tailWord_2899335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899335).length < 2 ^ (prefixWord ++ tailWord_2899335).sum := by decide
  have hdescent : baseEnd_2899335 < baseStart_2899335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899408 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 4]
def baseStart_2899408 : Nat := 118140960795 + 2899408 * 2 ^ 59
def prefixEnd_2899408 : Nat := 4983230072969 + 3 ^ 40 * 2899408 * 2
def baseEnd_2899408 : Nat := 1488789917491297286565871

theorem tailTrace_2899408 : CollatzResearch.WordTrace tailWord_2899408 prefixEnd_2899408 1488789917491297286565871 := by
  unfold tailWord_2899408
  simp only [CollatzResearch.WordTrace]
  refine ⟨52875048739973735154129439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70500064986631646872172585 52875048739973735154129439)
  ·
    refine ⟨79312573109960602731194159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52875048739973735154129439 79312573109960602731194159)
    ·
      refine ⟨118968859664940904096791239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79312573109960602731194159 118968859664940904096791239)
      ·
        refine ⟨178453289497411356145186859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118968859664940904096791239 178453289497411356145186859)
        ·
          refine ⟨267679934246117034217780289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178453289497411356145186859 267679934246117034217780289)
          ·
            refine ⟨200759950684587775663335217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267679934246117034217780289 200759950684587775663335217)
            ·
              refine ⟨150569963013440831747501413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200759950684587775663335217 150569963013440831747501413)
              ·
                refine ⟨28231868065020155952656515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150569963013440831747501413 28231868065020155952656515)
                ·
                  refine ⟨42347802097530233928984773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28231868065020155952656515 42347802097530233928984773)
                  ·
                    refine ⟨7940212893286918861684645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42347802097530233928984773 7940212893286918861684645)
                    ·
                      refine ⟨1488789917491297286565871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7940212893286918861684645 1488789917491297286565871)
                      ·
                        rfl

theorem cell23_2899408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 4].length) (baseStart_2899408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899408 prefixEnd_2899408 := by exact prefixLift 2899408
  have htrace : WordTrace (prefixWord ++ tailWord_2899408) baseStart_2899408 baseEnd_2899408 := by
    simpa [prefixWord, tailWord_2899408, baseEnd_2899408] using wordTrace_append hprefix tailTrace_2899408
  have hstable : (prefixWord ++ tailWord_2899408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899408).length < 2 ^ (prefixWord ++ tailWord_2899408).sum := by decide
  have hdescent : baseEnd_2899408 < baseStart_2899408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899428 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 1, 2, 7]
def baseStart_2899428 : Nat := 118140960795 + 2899428 * 2 ^ 59
def prefixEnd_2899428 : Nat := 4983230072969 + 3 ^ 40 * 2899428 * 2
def baseEnd_2899428 : Nat := 1488800187104387208315779

theorem tailTrace_2899428 : CollatzResearch.WordTrace tailWord_2899428 prefixEnd_2899428 1488800187104387208315779 := by
  unfold tailWord_2899428
  simp only [CollatzResearch.WordTrace]
  refine ⟨52875413469937506861993469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70500551293250009149324625 52875413469937506861993469)
  ·
    refine ⟨19828280051226565073247551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52875413469937506861993469 19828280051226565073247551)
    ·
      refine ⟨29742420076839847609871327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19828280051226565073247551 29742420076839847609871327)
      ·
        refine ⟨44613630115259771414806991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29742420076839847609871327 44613630115259771414806991)
        ·
          refine ⟨66920445172889657122210487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44613630115259771414806991 66920445172889657122210487)
          ·
            refine ⟨100380667759334485683315731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66920445172889657122210487 100380667759334485683315731)
            ·
              refine ⟨150571001639001728524973597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100380667759334485683315731 150571001639001728524973597)
              ·
                refine ⟨56464125614625648196865099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150571001639001728524973597 56464125614625648196865099)
                ·
                  refine ⟨84696188421938472295297649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56464125614625648196865099 84696188421938472295297649)
                  ·
                    refine ⟨63522141316453854221473237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84696188421938472295297649 63522141316453854221473237)
                    ·
                      refine ⟨1488800187104387208315779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 63522141316453854221473237 1488800187104387208315779)
                      ·
                        rfl

theorem cell23_2899428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_2899428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899428 prefixEnd_2899428 := by exact prefixLift 2899428
  have htrace : WordTrace (prefixWord ++ tailWord_2899428) baseStart_2899428 baseEnd_2899428 := by
    simpa [prefixWord, tailWord_2899428, baseEnd_2899428] using wordTrace_append hprefix tailTrace_2899428
  have hstable : (prefixWord ++ tailWord_2899428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899428).length < 2 ^ (prefixWord ++ tailWord_2899428).sum := by decide
  have hdescent : baseEnd_2899428 < baseStart_2899428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899442 : List Nat := [3, 2, 1, 4, 1, 2, 1, 1, 2, 2, 4]
def baseStart_2899442 : Nat := 118140960795 + 2899442 * 2 ^ 59
def prefixEnd_2899442 : Nat := 4983230072969 + 3 ^ 40 * 2899442 * 2
def baseEnd_2899442 : Nat := 1488807375833550153540715

theorem tailTrace_2899442 : CollatzResearch.WordTrace tailWord_2899442 prefixEnd_2899442 1488807375833550153540715 := by
  unfold tailWord_2899442
  simp only [CollatzResearch.WordTrace]
  refine ⟨26437834390456073528749145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70500891707882862743331053 26437834390456073528749145)
  ·
    refine ⟨19828375792842055146561859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26437834390456073528749145 19828375792842055146561859)
    ·
      refine ⟨29742563689263082719842789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19828375792842055146561859 29742563689263082719842789)
      ·
        refine ⟨5576730691736828009970523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29742563689263082719842789 5576730691736828009970523)
        ·
          refine ⟨8365096037605242014955785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5576730691736828009970523 8365096037605242014955785)
          ·
            refine ⟨6273822028203931511216839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8365096037605242014955785 6273822028203931511216839)
            ·
              refine ⟨9410733042305897266825259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6273822028203931511216839 9410733042305897266825259)
              ·
                refine ⟨14116099563458845900237889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9410733042305897266825259 14116099563458845900237889)
                ·
                  refine ⟨10587074672594134425178417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14116099563458845900237889 10587074672594134425178417)
                  ·
                    refine ⟨7940306004445600818883813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10587074672594134425178417 7940306004445600818883813)
                    ·
                      refine ⟨1488807375833550153540715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7940306004445600818883813 1488807375833550153540715)
                      ·
                        rfl

theorem cell23_2899442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_2899442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899442 prefixEnd_2899442 := by exact prefixLift 2899442
  have htrace : WordTrace (prefixWord ++ tailWord_2899442) baseStart_2899442 baseEnd_2899442 := by
    simpa [prefixWord, tailWord_2899442, baseEnd_2899442] using wordTrace_append hprefix tailTrace_2899442
  have hstable : (prefixWord ++ tailWord_2899442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899442).length < 2 ^ (prefixWord ++ tailWord_2899442).sum := by decide
  have hdescent : baseEnd_2899442 < baseStart_2899442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899446 : List Nat := [5, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2]
def baseStart_2899446 : Nat := 118140960795 + 2899446 * 2 ^ 59
def prefixEnd_2899446 : Nat := 4983230072969 + 3 ^ 40 * 2899446 * 2
def baseEnd_2899446 : Nat := 1488809429756168137890697

theorem tailTrace_2899446 : CollatzResearch.WordTrace tailWord_2899446 prefixEnd_2899446 1488809429756168137890697 := by
  unfold tailWord_2899446
  simp only [CollatzResearch.WordTrace]
  refine ⟨6609467715863112674883887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70500988969206535198761461 6609467715863112674883887)
  ·
    refine ⟨9914201573794669012325831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6609467715863112674883887 9914201573794669012325831)
    ·
      refine ⟨14871302360692003518488747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9914201573794669012325831 14871302360692003518488747)
      ·
        refine ⟨22306953541038005277733121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14871302360692003518488747 22306953541038005277733121)
        ·
          refine ⟨16730215155778503958299841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22306953541038005277733121 16730215155778503958299841)
          ·
            refine ⟨12547661366833877968724881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16730215155778503958299841 12547661366833877968724881)
            ·
              refine ⟨9410746025125408476543661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12547661366833877968724881 9410746025125408476543661)
              ·
                refine ⟨3529029759422028178703873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9410746025125408476543661 3529029759422028178703873)
                ·
                  refine ⟨2646772319566521134027905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3529029759422028178703873 2646772319566521134027905)
                  ·
                    refine ⟨1985079239674890850520929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2646772319566521134027905 1985079239674890850520929)
                    ·
                      refine ⟨1488809429756168137890697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1985079239674890850520929 1488809429756168137890697)
                      ·
                        rfl

theorem cell23_2899446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_2899446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899446 prefixEnd_2899446 := by exact prefixLift 2899446
  have htrace : WordTrace (prefixWord ++ tailWord_2899446) baseStart_2899446 baseEnd_2899446 := by
    simpa [prefixWord, tailWord_2899446, baseEnd_2899446] using wordTrace_append hprefix tailTrace_2899446
  have hstable : (prefixWord ++ tailWord_2899446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899446).length < 2 ^ (prefixWord ++ tailWord_2899446).sum := by decide
  have hdescent : baseEnd_2899446 < baseStart_2899446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899502 : List Nat := [4, 1, 3, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_2899502 : Nat := 118140960795 + 2899502 * 2 ^ 59
def prefixEnd_2899502 : Nat := 4983230072969 + 3 ^ 40 * 2899502 * 2
def baseEnd_2899502 : Nat := 1488838184672819918790439

theorem tailTrace_2899502 : CollatzResearch.WordTrace tailWord_2899502 prefixEnd_2899502 1488838184672819918790439 := by
  unfold tailWord_2899502
  simp only [CollatzResearch.WordTrace]
  refine ⟨13219190742700865545272595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70502350627737949574787173 13219190742700865545272595)
  ·
    refine ⟨19828786114051298317908893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13219190742700865545272595 19828786114051298317908893)
    ·
      refine ⟨7435794792769236869215835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19828786114051298317908893 7435794792769236869215835)
      ·
        refine ⟨11153692189153855303823753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7435794792769236869215835 11153692189153855303823753)
        ·
          refine ⟨8365269141865391477867815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11153692189153855303823753 8365269141865391477867815)
          ·
            refine ⟨12547903712798087216801723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8365269141865391477867815 12547903712798087216801723)
            ·
              refine ⟨18821855569197130825202585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12547903712798087216801723 18821855569197130825202585)
              ·
                refine ⟨14116391676897848118901939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18821855569197130825202585 14116391676897848118901939)
                ·
                  refine ⟨21174587515346772178352909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14116391676897848118901939 21174587515346772178352909)
                  ·
                    refine ⟨7940470318255039566882341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21174587515346772178352909 7940470318255039566882341)
                    ·
                      refine ⟨1488838184672819918790439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7940470318255039566882341 1488838184672819918790439)
                      ·
                        rfl

theorem cell23_2899502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_2899502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899502 prefixEnd_2899502 := by exact prefixLift 2899502
  have htrace : WordTrace (prefixWord ++ tailWord_2899502) baseStart_2899502 baseEnd_2899502 := by
    simpa [prefixWord, tailWord_2899502, baseEnd_2899502] using wordTrace_append hprefix tailTrace_2899502
  have hstable : (prefixWord ++ tailWord_2899502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899502).length < 2 ^ (prefixWord ++ tailWord_2899502).sum := by decide
  have hdescent : baseEnd_2899502 < baseStart_2899502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899512 : List Nat := [2, 1, 2, 1, 4, 2, 2, 2, 3, 4]
def baseStart_2899512 : Nat := 118140960795 + 2899512 * 2 ^ 59
def prefixEnd_2899512 : Nat := 4983230072969 + 3 ^ 40 * 2899512 * 2
def baseEnd_2899512 : Nat := 496281106493121626555131

theorem tailTrace_2899512 : CollatzResearch.WordTrace tailWord_2899512 prefixEnd_2899512 496281106493121626555131 := by
  unfold tailWord_2899512
  simp only [CollatzResearch.WordTrace]
  refine ⟨52876945335785348035022395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70502593781047130713363193 52876945335785348035022395)
  ·
    refine ⟨79315418003678022052533593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52876945335785348035022395 79315418003678022052533593)
    ·
      refine ⟨59486563502758516539400195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79315418003678022052533593 59486563502758516539400195)
      ·
        refine ⟨89229845254137774809100293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59486563502758516539400195 89229845254137774809100293)
        ·
          refine ⟨16730595985150832776706305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89229845254137774809100293 16730595985150832776706305)
          ·
            refine ⟨12547946988863124582529729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16730595985150832776706305 12547946988863124582529729)
            ·
              refine ⟨9410960241647343436897297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12547946988863124582529729 9410960241647343436897297)
              ·
                refine ⟨7058220181235507577672973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9410960241647343436897297 7058220181235507577672973)
                ·
                  refine ⟨2646832567963315341627365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7058220181235507577672973 2646832567963315341627365)
                  ·
                    refine ⟨496281106493121626555131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2646832567963315341627365 496281106493121626555131)
                    ·
                      rfl

theorem cell23_2899512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 3, 4].length) (baseStart_2899512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899512 prefixEnd_2899512 := by exact prefixLift 2899512
  have htrace : WordTrace (prefixWord ++ tailWord_2899512) baseStart_2899512 baseEnd_2899512 := by
    simpa [prefixWord, tailWord_2899512, baseEnd_2899512] using wordTrace_append hprefix tailTrace_2899512
  have hstable : (prefixWord ++ tailWord_2899512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899512).length < 2 ^ (prefixWord ++ tailWord_2899512).sum := by decide
  have hdescent : baseEnd_2899512 < baseStart_2899512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899579 : List Nat := [1, 1, 1, 1, 1, 4, 6, 1, 2, 3, 2]
def baseStart_2899579 : Nat := 118140960795 + 2899579 * 2 ^ 59
def prefixEnd_2899579 : Nat := 4983230072969 + 3 ^ 40 * 2899579 * 2
def baseEnd_2899579 : Nat := 1488877722683216117527585

theorem tailTrace_2899579 : CollatzResearch.WordTrace tailWord_2899579 prefixEnd_2899579 1488877722683216117527585 := by
  unfold tailWord_2899579
  simp only [CollatzResearch.WordTrace]
  refine ⟨105756334362327966512733791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70504222908218644341822527 105756334362327966512733791)
  ·
    refine ⟨158634501543491949769100687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105756334362327966512733791 158634501543491949769100687)
    ·
      refine ⟨237951752315237924653651031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158634501543491949769100687 237951752315237924653651031)
      ·
        refine ⟨356927628472856886980476547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237951752315237924653651031 356927628472856886980476547)
        ·
          refine ⟨535391442709285330470714821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356927628472856886980476547 535391442709285330470714821)
          ·
            refine ⟨100385895507990999463259029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 535391442709285330470714821 100385895507990999463259029)
            ·
              refine ⟨4705588851937078099840267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 100385895507990999463259029 4705588851937078099840267)
              ·
                refine ⟨7058383277905617149760401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4705588851937078099840267 7058383277905617149760401)
                ·
                  refine ⟨5293787458429212862320301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7058383277905617149760401 5293787458429212862320301)
                  ·
                    refine ⟨1985170296910954823370113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5293787458429212862320301 1985170296910954823370113)
                    ·
                      refine ⟨1488877722683216117527585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1985170296910954823370113 1488877722683216117527585)
                      ·
                        rfl

theorem cell23_2899579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 3, 2].length) (baseStart_2899579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899579 prefixEnd_2899579 := by exact prefixLift 2899579
  have htrace : WordTrace (prefixWord ++ tailWord_2899579) baseStart_2899579 baseEnd_2899579 := by
    simpa [prefixWord, tailWord_2899579, baseEnd_2899579] using wordTrace_append hprefix tailTrace_2899579
  have hstable : (prefixWord ++ tailWord_2899579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899579).length < 2 ^ (prefixWord ++ tailWord_2899579).sum := by decide
  have hdescent : baseEnd_2899579 < baseStart_2899579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899589 : List Nat := [1, 3, 1, 1, 4, 1, 5, 1, 1, 5]
def baseStart_2899589 : Nat := 118140960795 + 2899589 * 2 ^ 59
def prefixEnd_2899589 : Nat := 4983230072969 + 3 ^ 40 * 2899589 * 2
def baseEnd_2899589 : Nat := 496294285829920359467513

theorem tailTrace_2899589 : CollatzResearch.WordTrace tailWord_2899589 prefixEnd_2899589 496294285829920359467513 := by
  unfold tailWord_2899589
  simp only [CollatzResearch.WordTrace]
  refine ⟨105756699092291738220597821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70504466061527825480398547 105756699092291738220597821)
  ·
    refine ⟨39658762159609401832724183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105756699092291738220597821 39658762159609401832724183)
    ·
      refine ⟨59488143239414102749086275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39658762159609401832724183 59488143239414102749086275)
      ·
        refine ⟨89232214859121154123629413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59488143239414102749086275 89232214859121154123629413)
        ·
          refine ⟨16731040286085216398180515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89232214859121154123629413 16731040286085216398180515)
          ·
            refine ⟨25096560429127824597270773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16731040286085216398180515 25096560429127824597270773)
            ·
              refine ⟨2352802540230733555994135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25096560429127824597270773 2352802540230733555994135)
              ·
                refine ⟨3529203810346100333991203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2352802540230733555994135 3529203810346100333991203)
                ·
                  refine ⟨5293805715519150500986805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3529203810346100333991203 5293805715519150500986805)
                  ·
                    refine ⟨496294285829920359467513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5293805715519150500986805 496294285829920359467513)
                    ·
                      rfl

theorem cell23_2899589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 1, 5].length) (baseStart_2899589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899589 prefixEnd_2899589 := by exact prefixLift 2899589
  have htrace : WordTrace (prefixWord ++ tailWord_2899589) baseStart_2899589 baseEnd_2899589 := by
    simpa [prefixWord, tailWord_2899589, baseEnd_2899589] using wordTrace_append hprefix tailTrace_2899589
  have hstable : (prefixWord ++ tailWord_2899589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899589).length < 2 ^ (prefixWord ++ tailWord_2899589).sum := by decide
  have hdescent : baseEnd_2899589 < baseStart_2899589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899605 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 3, 1, 6]
def baseStart_2899605 : Nat := 118140960795 + 2899605 * 2 ^ 59
def prefixEnd_2899605 : Nat := 4983230072969 + 3 ^ 40 * 2899605 * 2
def baseEnd_2899605 : Nat := 1488891073180233015802465

theorem tailTrace_2899605 : CollatzResearch.WordTrace tailWord_2899605 prefixEnd_2899605 1488891073180233015802465 := by
  unfold tailWord_2899605
  simp only [CollatzResearch.WordTrace]
  refine ⟨105757282660233772953180269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70504855106822515302120179 105757282660233772953180269)
  ·
    refine ⟨39658980997587664857442601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105757282660233772953180269 39658980997587664857442601)
    ·
      refine ⟨29744235748190748643081951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39658980997587664857442601 29744235748190748643081951)
      ·
        refine ⟨44616353622286122964622927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29744235748190748643081951 44616353622286122964622927)
        ·
          refine ⟨66924530433429184446934391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44616353622286122964622927 66924530433429184446934391)
          ·
            refine ⟨100386795650143776670401587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66924530433429184446934391 100386795650143776670401587)
            ·
              refine ⟨150580193475215665005602381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100386795650143776670401587 150580193475215665005602381)
              ·
                refine ⟨56467572553205874377100893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150580193475215665005602381 56467572553205874377100893)
                ·
                  refine ⟨21175339707452202891412835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56467572553205874377100893 21175339707452202891412835)
                  ·
                    refine ⟨31763009561178304337119253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21175339707452202891412835 31763009561178304337119253)
                    ·
                      refine ⟨1488891073180233015802465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31763009561178304337119253 1488891073180233015802465)
                      ·
                        rfl

theorem cell23_2899605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_2899605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899605 prefixEnd_2899605 := by exact prefixLift 2899605
  have htrace : WordTrace (prefixWord ++ tailWord_2899605) baseStart_2899605 baseEnd_2899605 := by
    simpa [prefixWord, tailWord_2899605, baseEnd_2899605] using wordTrace_append hprefix tailTrace_2899605
  have hstable : (prefixWord ++ tailWord_2899605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899605).length < 2 ^ (prefixWord ++ tailWord_2899605).sum := by decide
  have hdescent : baseEnd_2899605 < baseStart_2899605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899629 : List Nat := [1, 5, 2, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_2899629 : Nat := 118140960795 + 2899629 * 2 ^ 59
def prefixEnd_2899629 : Nat := 4983230072969 + 3 ^ 40 * 2899629 * 2
def baseEnd_2899629 : Nat := 1488903396715940921902355

theorem tailTrace_2899629 : CollatzResearch.WordTrace tailWord_2899629 prefixEnd_2899629 1488903396715940921902355 := by
  unfold tailWord_2899629
  simp only [CollatzResearch.WordTrace]
  refine ⟨105758158012146825052053941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70505438674764550034702627 105758158012146825052053941)
  ·
    refine ⟨9914827313638764848630057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105758158012146825052053941 9914827313638764848630057)
    ·
      refine ⟨7436120485229073636472543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9914827313638764848630057 7436120485229073636472543)
      ·
        refine ⟨11154180727843610454708815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7436120485229073636472543 11154180727843610454708815)
        ·
          refine ⟨16731271091765415682063223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11154180727843610454708815 16731271091765415682063223)
          ·
            refine ⟨25096906637648123523094835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16731271091765415682063223 25096906637648123523094835)
            ·
              refine ⟨37645359956472185284642253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25096906637648123523094835 37645359956472185284642253)
              ·
                refine ⟨14117009983677069481740845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37645359956472185284642253 14117009983677069481740845)
                ·
                  refine ⟨5293878743878901055652817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14117009983677069481740845 5293878743878901055652817)
                  ·
                    refine ⟨3970409057909175791739613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5293878743878901055652817 3970409057909175791739613)
                    ·
                      refine ⟨1488903396715940921902355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3970409057909175791739613 1488903396715940921902355)
                      ·
                        rfl

theorem cell23_2899629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_2899629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899629 prefixEnd_2899629 := by exact prefixLift 2899629
  have htrace : WordTrace (prefixWord ++ tailWord_2899629) baseStart_2899629 baseEnd_2899629 := by
    simpa [prefixWord, tailWord_2899629, baseEnd_2899629] using wordTrace_append hprefix tailTrace_2899629
  have hstable : (prefixWord ++ tailWord_2899629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899629).length < 2 ^ (prefixWord ++ tailWord_2899629).sum := by decide
  have hdescent : baseEnd_2899629 < baseStart_2899629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899630 : List Nat := [4, 1, 4, 1, 2, 2, 1, 1, 2, 3, 2]
def baseStart_2899630 : Nat := 118140960795 + 2899630 * 2 ^ 59
def prefixEnd_2899630 : Nat := 4983230072969 + 3 ^ 40 * 2899630 * 2
def baseEnd_2899630 : Nat := 1488903910196595417989851

theorem tailTrace_2899630 : CollatzResearch.WordTrace tailWord_2899630 prefixEnd_2899630 1488903910196595417989851 := by
  unfold tailWord_2899630
  simp only [CollatzResearch.WordTrace]
  refine ⟨13219774310642900277855043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70505462990095468148560229 13219774310642900277855043)
  ·
    refine ⟨19829661465964350416782565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13219774310642900277855043 19829661465964350416782565)
    ·
      refine ⟨3718061524868315703146731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19829661465964350416782565 3718061524868315703146731)
      ·
        refine ⟨5577092287302473554720097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3718061524868315703146731 5577092287302473554720097)
        ·
          refine ⟨4182819215476855166040073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5577092287302473554720097 4182819215476855166040073)
          ·
            refine ⟨3137114411607641374530055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4182819215476855166040073 3137114411607641374530055)
            ·
              refine ⟨4705671617411462061795083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3137114411607641374530055 4705671617411462061795083)
              ·
                refine ⟨7058507426117193092692625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4705671617411462061795083 7058507426117193092692625)
                ·
                  refine ⟨5293880569587894819519469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7058507426117193092692625 5293880569587894819519469)
                  ·
                    refine ⟨1985205213595460557319801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5293880569587894819519469 1985205213595460557319801)
                    ·
                      refine ⟨1488903910196595417989851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1985205213595460557319801 1488903910196595417989851)
                      ·
                        rfl

theorem cell23_2899630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_2899630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899630 prefixEnd_2899630 := by exact prefixLift 2899630
  have htrace : WordTrace (prefixWord ++ tailWord_2899630) baseStart_2899630 baseEnd_2899630 := by
    simpa [prefixWord, tailWord_2899630, baseEnd_2899630] using wordTrace_append hprefix tailTrace_2899630
  have hstable : (prefixWord ++ tailWord_2899630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899630).length < 2 ^ (prefixWord ++ tailWord_2899630).sum := by decide
  have hdescent : baseEnd_2899630 < baseStart_2899630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899646 : List Nat := [4, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3]
def baseStart_2899646 : Nat := 118140960795 + 2899646 * 2 ^ 59
def prefixEnd_2899646 : Nat := 4983230072969 + 3 ^ 40 * 2899646 * 2
def baseEnd_2899646 : Nat := 1488912125887067355389777

theorem tailTrace_2899646 : CollatzResearch.WordTrace tailWord_2899646 prefixEnd_2899646 1488912125887067355389777 := by
  unfold tailWord_2899646
  simp only [CollatzResearch.WordTrace]
  refine ⟨13219847256635654619427849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70505852035390157970281861 13219847256635654619427849)
  ·
    refine ⟨9914885442476740964570887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13219847256635654619427849 9914885442476740964570887)
    ·
      refine ⟨14872328163715111446856331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9914885442476740964570887 14872328163715111446856331)
      ·
        refine ⟨22308492245572667170284497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14872328163715111446856331 22308492245572667170284497)
        ·
          refine ⟨16731369184179500377713373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22308492245572667170284497 16731369184179500377713373)
          ·
            refine ⟨6274263444067312641642515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16731369184179500377713373 6274263444067312641642515)
            ·
              refine ⟨9411395166100968962463773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6274263444067312641642515 9411395166100968962463773)
              ·
                refine ⟨3529273187287863360923915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9411395166100968962463773 3529273187287863360923915)
                ·
                  refine ⟨5293909780931795041385873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3529273187287863360923915 5293909780931795041385873)
                  ·
                    refine ⟨3970432335698846281039405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5293909780931795041385873 3970432335698846281039405)
                    ·
                      refine ⟨1488912125887067355389777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3970432335698846281039405 1488912125887067355389777)
                      ·
                        rfl

theorem cell23_2899646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_2899646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899646 prefixEnd_2899646 := by exact prefixLift 2899646
  have htrace : WordTrace (prefixWord ++ tailWord_2899646) baseStart_2899646 baseEnd_2899646 := by
    simpa [prefixWord, tailWord_2899646, baseEnd_2899646] using wordTrace_append hprefix tailTrace_2899646
  have hstable : (prefixWord ++ tailWord_2899646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899646).length < 2 ^ (prefixWord ++ tailWord_2899646).sum := by decide
  have hdescent : baseEnd_2899646 < baseStart_2899646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899670 : List Nat := [5, 2, 1, 3, 2, 1, 1, 1, 1, 6]
def baseStart_2899670 : Nat := 118140960795 + 2899670 * 2 ^ 59
def prefixEnd_2899670 : Nat := 4983230072969 + 3 ^ 40 * 2899670 * 2
def baseEnd_2899670 : Nat := 496308149807591753829889

theorem tailTrace_2899670 : CollatzResearch.WordTrace tailWord_2899670 prefixEnd_2899670 496308149807591753829889 := by
  unfold tailWord_2899670
  simp only [CollatzResearch.WordTrace]
  refine ⟨6609978337812393065893529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70506435603332192702864309 6609978337812393065893529)
  ·
    refine ⟨4957483753359294799420147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6609978337812393065893529 4957483753359294799420147)
    ·
      refine ⟨7436225630038942199130221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4957483753359294799420147 7436225630038942199130221)
      ·
        refine ⟨2788584611264603324673833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7436225630038942199130221 2788584611264603324673833)
        ·
          refine ⟨2091438458448452493505375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2788584611264603324673833 2091438458448452493505375)
          ·
            refine ⟨3137157687672678740258063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2091438458448452493505375 3137157687672678740258063)
            ·
              refine ⟨4705736531509018110387095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3137157687672678740258063 4705736531509018110387095)
              ·
                refine ⟨7058604797263527165580643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4705736531509018110387095 7058604797263527165580643)
                ·
                  refine ⟨10587907195895290748370965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7058604797263527165580643 10587907195895290748370965)
                  ·
                    refine ⟨496308149807591753829889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10587907195895290748370965 496308149807591753829889)
                    ·
                      rfl

theorem cell23_2899670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_2899670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899670 prefixEnd_2899670 := by exact prefixLift 2899670
  have htrace : WordTrace (prefixWord ++ tailWord_2899670) baseStart_2899670 baseEnd_2899670 := by
    simpa [prefixWord, tailWord_2899670, baseEnd_2899670] using wordTrace_append hprefix tailTrace_2899670
  have hstable : (prefixWord ++ tailWord_2899670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899670).length < 2 ^ (prefixWord ++ tailWord_2899670).sum := by decide
  have hdescent : baseEnd_2899670 < baseStart_2899670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899699 : List Nat := [1, 1, 1, 2, 2, 3, 2, 4, 1, 4, 2]
def baseStart_2899699 : Nat := 118140960795 + 2899699 * 2 ^ 59
def prefixEnd_2899699 : Nat := 4983230072969 + 3 ^ 40 * 2899699 * 2
def baseEnd_2899699 : Nat := 1488939340361755648027033

theorem tailTrace_2899699 : CollatzResearch.WordTrace tailWord_2899699 prefixEnd_2899699 1488939340361755648027033 := by
  unfold tailWord_2899699
  simp only [CollatzResearch.WordTrace]
  refine ⟨105760711121893227007102151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70507140747928818004734767 105760711121893227007102151)
  ·
    refine ⟨158641066682839840510653227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105760711121893227007102151 158641066682839840510653227)
    ·
      refine ⟨237961600024259760765979841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158641066682839840510653227 237961600024259760765979841)
      ·
        refine ⟨178471200018194820574484881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237961600024259760765979841 178471200018194820574484881)
        ·
          refine ⟨133853400013646115430863661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178471200018194820574484881 133853400013646115430863661)
          ·
            refine ⟨50195025005117293286573873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133853400013646115430863661 50195025005117293286573873)
            ·
              refine ⟨37646268753837969964930405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50195025005117293286573873 37646268753837969964930405)
              ·
                refine ⟨7058675391344619368424451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37646268753837969964930405 7058675391344619368424451)
                ·
                  refine ⟨10588013087016929052636677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7058675391344619368424451 10588013087016929052636677)
                  ·
                    refine ⟨1985252453815674197369377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10588013087016929052636677 1985252453815674197369377)
                    ·
                      refine ⟨1488939340361755648027033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1985252453815674197369377 1488939340361755648027033)
                      ·
                        rfl

theorem cell23_2899699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 4, 2].length) (baseStart_2899699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899699 prefixEnd_2899699 := by exact prefixLift 2899699
  have htrace : WordTrace (prefixWord ++ tailWord_2899699) baseStart_2899699 baseEnd_2899699 := by
    simpa [prefixWord, tailWord_2899699, baseEnd_2899699] using wordTrace_append hprefix tailTrace_2899699
  have hstable : (prefixWord ++ tailWord_2899699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899699).length < 2 ^ (prefixWord ++ tailWord_2899699).sum := by decide
  have hdescent : baseEnd_2899699 < baseStart_2899699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899733 : List Nat := [1, 3, 2, 1, 2, 4, 1, 3, 2, 2, 2]
def baseStart_2899733 : Nat := 118140960795 + 2899733 * 2 ^ 59
def prefixEnd_2899733 : Nat := 4983230072969 + 3 ^ 40 * 2899733 * 2
def baseEnd_2899733 : Nat := 1488956798704008515001877

theorem tailTrace_2899733 : CollatzResearch.WordTrace tailWord_2899733 prefixEnd_2899733 1488956798704008515001877 := by
  unfold tailWord_2899733
  simp only [CollatzResearch.WordTrace]
  refine ⟨105761951203770050813839853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70507967469180033875893235 105761951203770050813839853)
  ·
    refine ⟨39660731701413769055189945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105761951203770050813839853 39660731701413769055189945)
    ·
      refine ⟨29745548776060326791392459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39660731701413769055189945 29745548776060326791392459)
      ·
        refine ⟨44618323164090490187088689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29745548776060326791392459 44618323164090490187088689)
        ·
          refine ⟨33463742373067867640316517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44618323164090490187088689 33463742373067867640316517)
          ·
            refine ⟨6274451694950225182559347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33463742373067867640316517 6274451694950225182559347)
            ·
              refine ⟨9411677542425337773839021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6274451694950225182559347 9411677542425337773839021)
              ·
                refine ⟨3529379078409501665189633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9411677542425337773839021 3529379078409501665189633)
                ·
                  refine ⟨2647034308807126248892225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3529379078409501665189633 2647034308807126248892225)
                  ·
                    refine ⟨1985275731605344686669169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2647034308807126248892225 1985275731605344686669169)
                    ·
                      refine ⟨1488956798704008515001877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1985275731605344686669169 1488956798704008515001877)
                      ·
                        rfl

theorem cell23_2899733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2, 2, 2].length) (baseStart_2899733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899733 prefixEnd_2899733 := by exact prefixLift 2899733
  have htrace : WordTrace (prefixWord ++ tailWord_2899733) baseStart_2899733 baseEnd_2899733 := by
    simpa [prefixWord, tailWord_2899733, baseEnd_2899733] using wordTrace_append hprefix tailTrace_2899733
  have hstable : (prefixWord ++ tailWord_2899733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899733).length < 2 ^ (prefixWord ++ tailWord_2899733).sum := by decide
  have hdescent : baseEnd_2899733 < baseStart_2899733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899773 : List Nat := [1, 4, 1, 4, 1, 1, 4, 2, 5]
def baseStart_2899773 : Nat := 118140960795 + 2899773 * 2 ^ 59
def prefixEnd_2899773 : Nat := 4983230072969 + 3 ^ 40 * 2899773 * 2
def baseEnd_2899773 : Nat := 165441926436687595389077

theorem tailTrace_2899773 : CollatzResearch.WordTrace tailWord_2899773 prefixEnd_2899773 165441926436687595389077 := by
  unfold tailWord_2899773
  simp only [CollatzResearch.WordTrace]
  refine ⟨105763410123625137645295973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70508940082416758430197315 105763410123625137645295973)
  ·
    refine ⟨19830639398179713308492995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105763410123625137645295973 19830639398179713308492995)
    ·
      refine ⟨29745959097269569962739493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19830639398179713308492995 29745959097269569962739493)
      ·
        refine ⟨5577367330738044368013655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29745959097269569962739493 5577367330738044368013655)
        ·
          refine ⟨8366050996107066552020483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5577367330738044368013655 8366050996107066552020483)
          ·
            refine ⟨12549076494160599828030725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8366050996107066552020483 12549076494160599828030725)
            ·
              refine ⟨2352951842655112467755761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12549076494160599828030725 2352951842655112467755761)
              ·
                refine ⟨1764713881991334350816821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2352951842655112467755761 1764713881991334350816821)
                ·
                  refine ⟨165441926436687595389077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1764713881991334350816821 165441926436687595389077)
                  ·
                    rfl

theorem cell23_2899773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2, 5].length) (baseStart_2899773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899773 prefixEnd_2899773 := by exact prefixLift 2899773
  have htrace : WordTrace (prefixWord ++ tailWord_2899773) baseStart_2899773 baseEnd_2899773 := by
    simpa [prefixWord, tailWord_2899773, baseEnd_2899773] using wordTrace_append hprefix tailTrace_2899773
  have hstable : (prefixWord ++ tailWord_2899773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899773).length < 2 ^ (prefixWord ++ tailWord_2899773).sum := by decide
  have hdescent : baseEnd_2899773 < baseStart_2899773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899809 : List Nat := [1, 2, 3, 1, 1, 1, 5, 1, 1, 4, 3]
def baseStart_2899809 : Nat := 118140960795 + 2899809 * 2 ^ 59
def prefixEnd_2899809 : Nat := 4983230072969 + 3 ^ 40 * 2899809 * 2
def baseEnd_2899809 : Nat := 1488995823233750217651527

theorem tailTrace_2899809 : CollatzResearch.WordTrace tailWord_2899809 prefixEnd_2899809 1488995823233750217651527 := by
  unfold tailWord_2899809
  simp only [CollatzResearch.WordTrace]
  refine ⟨105764723151494715793606481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70509815434329810529070987 105764723151494715793606481)
  ·
    refine ⟨79323542363621036845204861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105764723151494715793606481 79323542363621036845204861)
    ·
      refine ⟨29746328386357888816951823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79323542363621036845204861 29746328386357888816951823)
      ·
        refine ⟨44619492579536833225427735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29746328386357888816951823 44619492579536833225427735)
        ·
          refine ⟨66929238869305249838141603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44619492579536833225427735 66929238869305249838141603)
          ·
            refine ⟨100393858303957874757212405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66929238869305249838141603 100393858303957874757212405)
            ·
              refine ⟨9411924215996050758488663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100393858303957874757212405 9411924215996050758488663)
              ·
                refine ⟨14117886323994076137732995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9411924215996050758488663 14117886323994076137732995)
                ·
                  refine ⟨21176829485991114206599493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14117886323994076137732995 21176829485991114206599493)
                  ·
                    refine ⟨3970655528623333913737405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21176829485991114206599493 3970655528623333913737405)
                    ·
                      refine ⟨1488995823233750217651527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3970655528623333913737405 1488995823233750217651527)
                      ·
                        rfl

theorem cell23_2899809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_2899809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899809 prefixEnd_2899809 := by exact prefixLift 2899809
  have htrace : WordTrace (prefixWord ++ tailWord_2899809) baseStart_2899809 baseEnd_2899809 := by
    simpa [prefixWord, tailWord_2899809, baseEnd_2899809] using wordTrace_append hprefix tailTrace_2899809
  have hstable : (prefixWord ++ tailWord_2899809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899809).length < 2 ^ (prefixWord ++ tailWord_2899809).sum := by decide
  have hdescent : baseEnd_2899809 < baseStart_2899809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899829 : List Nat := [1, 3, 4, 1, 1, 1, 3, 1, 8]
def baseStart_2899829 : Nat := 118140960795 + 2899829 * 2 ^ 59
def prefixEnd_2899829 : Nat := 4983230072969 + 3 ^ 40 * 2899829 * 2
def baseEnd_2899829 : Nat := 165445121427426682155715

theorem tailTrace_2899829 : CollatzResearch.WordTrace tailWord_2899829 prefixEnd_2899829 165445121427426682155715 := by
  unfold tailWord_2899829
  simp only [CollatzResearch.WordTrace]
  refine ⟨105765452611422259209334541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70510301740948172806223027 105765452611422259209334541)
  ·
    refine ⟨39662044729283347203500453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105765452611422259209334541 39662044729283347203500453)
    ·
      refine ⟨7436633386740627600656335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39662044729283347203500453 7436633386740627600656335)
      ·
        refine ⟨11154950080110941400984503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7436633386740627600656335 11154950080110941400984503)
        ·
          refine ⟨16732425120166412101476755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11154950080110941400984503 16732425120166412101476755)
          ·
            refine ⟨25098637680249618152215133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16732425120166412101476755 25098637680249618152215133)
            ·
              refine ⟨9411989130093606807080675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25098637680249618152215133 9411989130093606807080675)
              ·
                refine ⟨14117983695140410210621013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9411989130093606807080675 14117983695140410210621013)
                ·
                  refine ⟨165445121427426682155715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14117983695140410210621013 165445121427426682155715)
                  ·
                    rfl

theorem cell23_2899829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 8].length) (baseStart_2899829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899829 prefixEnd_2899829 := by exact prefixLift 2899829
  have htrace : WordTrace (prefixWord ++ tailWord_2899829) baseStart_2899829 baseEnd_2899829 := by
    simpa [prefixWord, tailWord_2899829, baseEnd_2899829] using wordTrace_append hprefix tailTrace_2899829
  have hstable : (prefixWord ++ tailWord_2899829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899829).length < 2 ^ (prefixWord ++ tailWord_2899829).sum := by decide
  have hdescent : baseEnd_2899829 < baseStart_2899829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899876 : List Nat := [2, 3, 1, 2, 1, 3, 2, 3, 1, 5]
def baseStart_2899876 : Nat := 118140960795 + 2899876 * 2 ^ 59
def prefixEnd_2899876 : Nat := 4983230072969 + 3 ^ 40 * 2899876 * 2
def baseEnd_2899876 : Nat := 496343408812533818504573

theorem tailTrace_2899876 : CollatzResearch.WordTrace tailWord_2899876 prefixEnd_2899876 496343408812533818504573 := by
  unfold tailWord_2899876
  simp only [CollatzResearch.WordTrace]
  refine ⟨52883583421125993118147741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70511444561501324157530321 52883583421125993118147741)
  ·
    refine ⟨19831343782922247419305403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52883583421125993118147741 19831343782922247419305403)
    ·
      refine ⟨29747015674383371128958105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19831343782922247419305403 29747015674383371128958105)
      ·
        refine ⟨22310261755787528346718579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29747015674383371128958105 22310261755787528346718579)
        ·
          refine ⟨33465392633681292520077869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22310261755787528346718579 33465392633681292520077869)
          ·
            refine ⟨12549522237630484695029201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33465392633681292520077869 12549522237630484695029201)
            ·
              refine ⟨9412141678222863521271901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12549522237630484695029201 9412141678222863521271901)
              ·
                refine ⟨3529553129333573820476963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9412141678222863521271901 3529553129333573820476963)
                ·
                  refine ⟨5294329694000360730715445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3529553129333573820476963 5294329694000360730715445)
                  ·
                    refine ⟨496343408812533818504573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5294329694000360730715445 496343408812533818504573)
                    ·
                      rfl

theorem cell23_2899876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_2899876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899876 prefixEnd_2899876 := by exact prefixLift 2899876
  have htrace : WordTrace (prefixWord ++ tailWord_2899876) baseStart_2899876 baseEnd_2899876 := by
    simpa [prefixWord, tailWord_2899876, baseEnd_2899876] using wordTrace_append hprefix tailTrace_2899876
  have hstable : (prefixWord ++ tailWord_2899876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899876).length < 2 ^ (prefixWord ++ tailWord_2899876).sum := by decide
  have hdescent : baseEnd_2899876 < baseStart_2899876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899930 : List Nat := [3, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4]
def baseStart_2899930 : Nat := 118140960795 + 2899930 * 2 ^ 59
def prefixEnd_2899930 : Nat := 4983230072969 + 3 ^ 40 * 2899930 * 2
def baseEnd_2899930 : Nat := 1489057954392944244238471

theorem tailTrace_2899930 : CollatzResearch.WordTrace tailWord_2899930 prefixEnd_2899930 1489057954392944244238471 := by
  unfold tailWord_2899930
  simp only [CollatzResearch.WordTrace]
  refine ⟨26442284096014088364690311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70512757589370902305840829 26442284096014088364690311)
  ·
    refine ⟨39663426144021132547035467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26442284096014088364690311 39663426144021132547035467)
    ·
      refine ⟨59495139216031698820553201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39663426144021132547035467 59495139216031698820553201)
      ·
        refine ⟨44621354412023774115414901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59495139216031698820553201 44621354412023774115414901)
        ·
          refine ⟨4183251976127228823320147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44621354412023774115414901 4183251976127228823320147)
          ·
            refine ⟨6274877964190843234980221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4183251976127228823320147 6274877964190843234980221)
            ·
              refine ⟨2353079236571566213117583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6274877964190843234980221 2353079236571566213117583)
              ·
                refine ⟨3529618854857349319676375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2353079236571566213117583 3529618854857349319676375)
                ·
                  refine ⟨5294428282286023979514563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3529618854857349319676375 5294428282286023979514563)
                  ·
                    refine ⟨7941642423429035969271845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5294428282286023979514563 7941642423429035969271845)
                    ·
                      refine ⟨1489057954392944244238471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7941642423429035969271845 1489057954392944244238471)
                      ·
                        rfl

theorem cell23_2899930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4].length) (baseStart_2899930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899930 prefixEnd_2899930 := by exact prefixLift 2899930
  have htrace : WordTrace (prefixWord ++ tailWord_2899930) baseStart_2899930 baseEnd_2899930 := by
    simpa [prefixWord, tailWord_2899930, baseEnd_2899930] using wordTrace_append hprefix tailTrace_2899930
  have hstable : (prefixWord ++ tailWord_2899930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899930).length < 2 ^ (prefixWord ++ tailWord_2899930).sum := by decide
  have hdescent : baseEnd_2899930 < baseStart_2899930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899946 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 3, 3, 3]
def baseStart_2899946 : Nat := 118140960795 + 2899946 * 2 ^ 59
def prefixEnd_2899946 : Nat := 4983230072969 + 3 ^ 40 * 2899946 * 2
def baseEnd_2899946 : Nat := 1489066170083416181638397

theorem tailTrace_2899946 : CollatzResearch.WordTrace tailWord_2899946 prefixEnd_2899946 1489066170083416181638397 := by
  unfold tailWord_2899946
  simp only [CollatzResearch.WordTrace]
  refine ⟨26442429987999597047835923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70513146634665592127562461 26442429987999597047835923)
  ·
    refine ⟨39663644981999395571753885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26442429987999597047835923 39663644981999395571753885)
    ·
      refine ⟨14873866868249773339407707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39663644981999395571753885 14873866868249773339407707)
      ·
        refine ⟨22310800302374660009111561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14873866868249773339407707 22310800302374660009111561)
        ·
          refine ⟨16733100226780995006833671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22310800302374660009111561 16733100226780995006833671)
          ·
            refine ⟨25099650340171492510250507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16733100226780995006833671 25099650340171492510250507)
            ·
              refine ⟨37649475510257238765375761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25099650340171492510250507 37649475510257238765375761)
              ·
                refine ⟨28237106632692929074031821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37649475510257238765375761 28237106632692929074031821)
                ·
                  refine ⟨10588914987259848402761933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28237106632692929074031821 10588914987259848402761933)
                  ·
                    refine ⟨3970843120222443151035725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10588914987259848402761933 3970843120222443151035725)
                    ·
                      refine ⟨1489066170083416181638397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3970843120222443151035725 1489066170083416181638397)
                      ·
                        rfl

theorem cell23_2899946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_2899946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899946 prefixEnd_2899946 := by exact prefixLift 2899946
  have htrace : WordTrace (prefixWord ++ tailWord_2899946) baseStart_2899946 baseEnd_2899946 := by
    simpa [prefixWord, tailWord_2899946, baseEnd_2899946] using wordTrace_append hprefix tailTrace_2899946
  have hstable : (prefixWord ++ tailWord_2899946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899946).length < 2 ^ (prefixWord ++ tailWord_2899946).sum := by decide
  have hdescent : baseEnd_2899946 < baseStart_2899946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899953 : List Nat := [1, 2, 2, 2, 6, 1, 1, 8]
def baseStart_2899953 : Nat := 118140960795 + 2899953 * 2 ^ 59
def prefixEnd_2899953 : Nat := 4983230072969 + 3 ^ 40 * 2899953 * 2
def baseEnd_2899953 : Nat := 55150732016592505712995

theorem tailTrace_2899953 : CollatzResearch.WordTrace tailWord_2899953 prefixEnd_2899953 55150732016592505712995 := by
  unfold tailWord_2899953
  simp only [CollatzResearch.WordTrace]
  refine ⟨105769975262973028386848513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70513316841982018924565675 105769975262973028386848513)
  ·
    refine ⟨79327481447229771290136385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105769975262973028386848513 79327481447229771290136385)
    ·
      refine ⟨59495611085422328467602289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79327481447229771290136385 59495611085422328467602289)
      ·
        refine ⟨44621708314066746350701717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59495611085422328467602289 44621708314066746350701717)
        ·
          refine ⟨2091642577221878735189143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44621708314066746350701717 2091642577221878735189143)
          ·
            refine ⟨3137463865832818102783715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2091642577221878735189143 3137463865832818102783715)
            ·
              refine ⟨4706195798749227154175573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3137463865832818102783715 4706195798749227154175573)
              ·
                refine ⟨55150732016592505712995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4706195798749227154175573 55150732016592505712995)
                ·
                  rfl

theorem cell23_2899953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 8].length) (baseStart_2899953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899953 prefixEnd_2899953 := by exact prefixLift 2899953
  have htrace : WordTrace (prefixWord ++ tailWord_2899953) baseStart_2899953 baseEnd_2899953 := by
    simpa [prefixWord, tailWord_2899953, baseEnd_2899953] using wordTrace_append hprefix tailTrace_2899953
  have hstable : (prefixWord ++ tailWord_2899953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899953).length < 2 ^ (prefixWord ++ tailWord_2899953).sum := by decide
  have hdescent : baseEnd_2899953 < baseStart_2899953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899963 : List Nat := [1, 1, 1, 1, 1, 3, 6, 3, 2, 1, 3]
def baseStart_2899963 : Nat := 118140960795 + 2899963 * 2 ^ 59
def prefixEnd_2899963 : Nat := 4983230072969 + 3 ^ 40 * 2899963 * 2
def baseEnd_2899963 : Nat := 1489074899254542615125819

theorem tailTrace_2899963 : CollatzResearch.WordTrace tailWord_2899963 prefixEnd_2899963 1489074899254542615125819 := by
  unfold tailWord_2899963
  simp only [CollatzResearch.WordTrace]
  refine ⟨105770339992936800094712543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70513559995291200063141695 105770339992936800094712543)
  ·
    refine ⟨158655509989405200142068815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105770339992936800094712543 158655509989405200142068815)
    ·
      refine ⟨237983264984107800213103223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158655509989405200142068815 237983264984107800213103223)
      ·
        refine ⟨356974897476161700319654835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237983264984107800213103223 356974897476161700319654835)
        ·
          refine ⟨535462346214242550479482253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356974897476161700319654835 535462346214242550479482253)
          ·
            refine ⟨200798379830340956429805845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 535462346214242550479482253 200798379830340956429805845)
            ·
              refine ⟨9412424054547232332647149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 200798379830340956429805845 9412424054547232332647149)
              ·
                refine ⟨3529659020455212124742681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9412424054547232332647149 3529659020455212124742681)
                ·
                  refine ⟨2647244265341409093557011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3529659020455212124742681 2647244265341409093557011)
                  ·
                    refine ⟨3970866398012113640335517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2647244265341409093557011 3970866398012113640335517)
                    ·
                      refine ⟨1489074899254542615125819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3970866398012113640335517 1489074899254542615125819)
                      ·
                        rfl

theorem cell23_2899963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2, 1, 3].length) (baseStart_2899963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899963 prefixEnd_2899963 := by exact prefixLift 2899963
  have htrace : WordTrace (prefixWord ++ tailWord_2899963) baseStart_2899963 baseEnd_2899963 := by
    simpa [prefixWord, tailWord_2899963, baseEnd_2899963] using wordTrace_append hprefix tailTrace_2899963
  have hstable : (prefixWord ++ tailWord_2899963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899963).length < 2 ^ (prefixWord ++ tailWord_2899963).sum := by decide
  have hdescent : baseEnd_2899963 < baseStart_2899963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899973 : List Nat := [1, 3, 1, 1, 2, 4, 2, 1, 3, 3, 2]
def baseStart_2899973 : Nat := 118140960795 + 2899973 * 2 ^ 59
def prefixEnd_2899973 : Nat := 4983230072969 + 3 ^ 40 * 2899973 * 2
def baseEnd_2899973 : Nat := 1489080034061087576000773

theorem tailTrace_2899973 : CollatzResearch.WordTrace tailWord_2899973 prefixEnd_2899973 1489080034061087576000773 := by
  unfold tailWord_2899973
  simp only [CollatzResearch.WordTrace]
  refine ⟨105770704722900571802576573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70513803148600381201717715 105770704722900571802576573)
  ·
    refine ⟨39664014271087714425966215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105770704722900571802576573 39664014271087714425966215)
    ·
      refine ⟨59496021406631571638949323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39664014271087714425966215 59496021406631571638949323)
      ·
        refine ⟨89244032109947357458423985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59496021406631571638949323 89244032109947357458423985)
        ·
          refine ⟨66933024082460518093817989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89244032109947357458423985 66933024082460518093817989)
          ·
            refine ⟨12549942015461347142590873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66933024082460518093817989 12549942015461347142590873)
            ·
              refine ⟨9412456511596010356943155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12549942015461347142590873 9412456511596010356943155)
              ·
                refine ⟨14118684767394015535414733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9412456511596010356943155 14118684767394015535414733)
                ·
                  refine ⟨5294506787772755825780525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14118684767394015535414733 5294506787772755825780525)
                  ·
                    refine ⟨1985440045414783434667697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5294506787772755825780525 1985440045414783434667697)
                    ·
                      refine ⟨1489080034061087576000773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1985440045414783434667697 1489080034061087576000773)
                      ·
                        rfl

theorem cell23_2899973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 3, 2].length) (baseStart_2899973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899973 prefixEnd_2899973 := by exact prefixLift 2899973
  have htrace : WordTrace (prefixWord ++ tailWord_2899973) baseStart_2899973 baseEnd_2899973 := by
    simpa [prefixWord, tailWord_2899973, baseEnd_2899973] using wordTrace_append hprefix tailTrace_2899973
  have hstable : (prefixWord ++ tailWord_2899973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899973).length < 2 ^ (prefixWord ++ tailWord_2899973).sum := by decide
  have hdescent : baseEnd_2899973 < baseStart_2899973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899979 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 1, 8]
def baseStart_2899979 : Nat := 118140960795 + 2899979 * 2 ^ 59
def prefixEnd_2899979 : Nat := 4983230072969 + 3 ^ 40 * 2899979 * 2
def baseEnd_2899979 : Nat := 496361038315004850841915

theorem tailTrace_2899979 : CollatzResearch.WordTrace tailWord_2899979 prefixEnd_2899979 496361038315004850841915 := by
  unfold tailWord_2899979
  simp only [CollatzResearch.WordTrace]
  refine ⟨105770923560878834827294991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70513949040585889884863327 105770923560878834827294991)
  ·
    refine ⟨158656385341318252240942487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105770923560878834827294991 158656385341318252240942487)
    ·
      refine ⟨237984578011977378361413731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158656385341318252240942487 237984578011977378361413731)
      ·
        refine ⟨356976867017966067542120597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237984578011977378361413731 356976867017966067542120597)
        ·
          refine ⟨16733290641467159416036903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 356976867017966067542120597 16733290641467159416036903)
          ·
            refine ⟨25099935962200739124055355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16733290641467159416036903 25099935962200739124055355)
            ·
              refine ⟨37649903943301108686083033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25099935962200739124055355 37649903943301108686083033)
              ·
                refine ⟨28237427957475831514562275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37649903943301108686083033 28237427957475831514562275)
                ·
                  refine ⟨42356141936213747271843413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28237427957475831514562275 42356141936213747271843413)
                  ·
                    refine ⟨496361038315004850841915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42356141936213747271843413 496361038315004850841915)
                    ·
                      rfl

theorem cell23_2899979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 8].length) (baseStart_2899979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899979 prefixEnd_2899979 := by exact prefixLift 2899979
  have htrace : WordTrace (prefixWord ++ tailWord_2899979) baseStart_2899979 baseEnd_2899979 := by
    simpa [prefixWord, tailWord_2899979, baseEnd_2899979] using wordTrace_append hprefix tailTrace_2899979
  have hstable : (prefixWord ++ tailWord_2899979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899979).length < 2 ^ (prefixWord ++ tailWord_2899979).sum := by decide
  have hdescent : baseEnd_2899979 < baseStart_2899979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899981 : List Nat := [1, 7, 1, 2, 1, 2, 2, 1, 1, 1, 4]
def baseStart_2899981 : Nat := 118140960795 + 2899981 * 2 ^ 59
def prefixEnd_2899981 : Nat := 4983230072969 + 3 ^ 40 * 2899981 * 2
def baseEnd_2899981 : Nat := 1489084141906323544700737

theorem tailTrace_2899981 : CollatzResearch.WordTrace tailWord_2899981 prefixEnd_2899981 1489084141906323544700737 := by
  unfold tailWord_2899981
  simp only [CollatzResearch.WordTrace]
  refine ⟨105770996506871589168867797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70513997671247726112578531 105770996506871589168867797)
  ·
    refine ⟨2479007730629802871145339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 105770996506871589168867797 2479007730629802871145339)
    ·
      refine ⟨3718511595944704306718009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2479007730629802871145339 3718511595944704306718009)
      ·
        refine ⟨2788883696958528230038507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3718511595944704306718009 2788883696958528230038507)
        ·
          refine ⟨4183325545437792345057761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2788883696958528230038507 4183325545437792345057761)
          ·
            refine ⟨3137494159078344258793321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4183325545437792345057761 3137494159078344258793321)
            ·
              refine ⟨2353120619308758194094991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3137494159078344258793321 2353120619308758194094991)
              ·
                refine ⟨3529680928963137291142487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2353120619308758194094991 3529680928963137291142487)
                ·
                  refine ⟨5294521393444705936713731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3529680928963137291142487 5294521393444705936713731)
                  ·
                    refine ⟨7941782090167058905070597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5294521393444705936713731 7941782090167058905070597)
                    ·
                      refine ⟨1489084141906323544700737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7941782090167058905070597 1489084141906323544700737)
                      ·
                        rfl

theorem cell23_2899981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_2899981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899981 prefixEnd_2899981 := by exact prefixLift 2899981
  have htrace : WordTrace (prefixWord ++ tailWord_2899981) baseStart_2899981 baseEnd_2899981 := by
    simpa [prefixWord, tailWord_2899981, baseEnd_2899981] using wordTrace_append hprefix tailTrace_2899981
  have hstable : (prefixWord ++ tailWord_2899981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899981).length < 2 ^ (prefixWord ++ tailWord_2899981).sum := by decide
  have hdescent : baseEnd_2899981 < baseStart_2899981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899996 : List Nat := [2, 2, 3, 1, 3, 1, 1, 2, 2, 6]
def baseStart_2899996 : Nat := 118140960795 + 2899996 * 2 ^ 59
def prefixEnd_2899996 : Nat := 4983230072969 + 3 ^ 40 * 2899996 * 2
def baseEnd_2899996 : Nat := 496363948038713662004389

theorem tailTrace_2899996 : CollatzResearch.WordTrace tailWord_2899996 prefixEnd_2899996 496363948038713662004389 := by
  unfold tailWord_2899996
  simp only [CollatzResearch.WordTrace]
  refine ⟨52885771800908623365331921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70514362401211497820442561 52885771800908623365331921)
  ·
    refine ⟨39664328850681467523998941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52885771800908623365331921 39664328850681467523998941)
    ·
      refine ⟨14874123319005550321499603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39664328850681467523998941 14874123319005550321499603)
      ·
        refine ⟨22311184978508325482249405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14874123319005550321499603 22311184978508325482249405)
        ·
          refine ⟨8366694366940622055843527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22311184978508325482249405 8366694366940622055843527)
          ·
            refine ⟨12550041550410933083765291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8366694366940622055843527 12550041550410933083765291)
            ·
              refine ⟨18825062325616399625647937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12550041550410933083765291 18825062325616399625647937)
              ·
                refine ⟨14118796744212299719235953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18825062325616399625647937 14118796744212299719235953)
                ·
                  refine ⟨10589097558159224789426965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14118796744212299719235953 10589097558159224789426965)
                  ·
                    refine ⟨496363948038713662004389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10589097558159224789426965 496363948038713662004389)
                    ·
                      rfl

theorem cell23_2899996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_2899996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899996 prefixEnd_2899996 := by exact prefixLift 2899996
  have htrace : WordTrace (prefixWord ++ tailWord_2899996) baseStart_2899996 baseEnd_2899996 := by
    simpa [prefixWord, tailWord_2899996, baseEnd_2899996] using wordTrace_append hprefix tailTrace_2899996
  have hstable : (prefixWord ++ tailWord_2899996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899996).length < 2 ^ (prefixWord ++ tailWord_2899996).sum := by decide
  have hdescent : baseEnd_2899996 < baseStart_2899996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2899997 : List Nat := [1, 4, 2, 2, 2, 3, 1, 2, 2, 1, 3]
def baseStart_2899997 : Nat := 118140960795 + 2899997 * 2 ^ 59
def prefixEnd_2899997 : Nat := 4983230072969 + 3 ^ 40 * 2899997 * 2
def baseEnd_2899997 : Nat := 1489092357596795482100663

theorem tailTrace_2899997 : CollatzResearch.WordTrace tailWord_2899997 prefixEnd_2899997 1489092357596795482100663 := by
  unfold tailWord_2899997
  simp only [CollatzResearch.WordTrace]
  refine ⟨105771580074813623901450245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70514386716542415934300163 105771580074813623901450245)
  ·
    refine ⟨19832171264027554481521921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105771580074813623901450245 19832171264027554481521921)
    ·
      refine ⟨14874128448020665861141441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19832171264027554481521921 14874128448020665861141441)
      ·
        refine ⟨11155596336015499395856081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14874128448020665861141441 11155596336015499395856081)
        ·
          refine ⟨8366697252011624546892061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11155596336015499395856081 8366697252011624546892061)
          ·
            refine ⟨3137511469504359205084523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8366697252011624546892061 3137511469504359205084523)
            ·
              refine ⟨4706267204256538807626785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3137511469504359205084523 4706267204256538807626785)
              ·
                refine ⟨3529700403192404105720089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4706267204256538807626785 3529700403192404105720089)
                ·
                  refine ⟨2647275302394303079290067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3529700403192404105720089 2647275302394303079290067)
                  ·
                    refine ⟨3970912953591454618935101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2647275302394303079290067 3970912953591454618935101)
                    ·
                      refine ⟨1489092357596795482100663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3970912953591454618935101 1489092357596795482100663)
                      ·
                        rfl

theorem cell23_2899997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_2899997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2899997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2899997 prefixEnd_2899997 := by exact prefixLift 2899997
  have htrace : WordTrace (prefixWord ++ tailWord_2899997) baseStart_2899997 baseEnd_2899997 := by
    simpa [prefixWord, tailWord_2899997, baseEnd_2899997] using wordTrace_append hprefix tailTrace_2899997
  have hstable : (prefixWord ++ tailWord_2899997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2899997).length < 2 ^ (prefixWord ++ tailWord_2899997).sum := by decide
  have hdescent : baseEnd_2899997 < baseStart_2899997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2899997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900016 : List Nat := [2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 4]
def baseStart_2900016 : Nat := 118140960795 + 2900016 * 2 ^ 59
def prefixEnd_2900016 : Nat := 4983230072969 + 3 ^ 40 * 2900016 * 2
def baseEnd_2900016 : Nat := 1489102113729230907763075

theorem tailTrace_2900016 : CollatzResearch.WordTrace tailWord_2900016 prefixEnd_2900016 1489102113729230907763075 := by
  unfold tailWord_2900016
  simp only [CollatzResearch.WordTrace]
  refine ⟨52886136530872395073195951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70514848707829860097594601 52886136530872395073195951)
  ·
    refine ⟨79329204796308592609793927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52886136530872395073195951 79329204796308592609793927)
    ·
      refine ⟨118993807194462888914690891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79329204796308592609793927 118993807194462888914690891)
      ·
        refine ⟨178490710791694333372036337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118993807194462888914690891 178490710791694333372036337)
        ·
          refine ⟨133868033093770750029027253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178490710791694333372036337 133868033093770750029027253)
          ·
            refine ⟨12550128102541007815221305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133868033093770750029027253 12550128102541007815221305)
            ·
              refine ⟨9412596076905755861415979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12550128102541007815221305 9412596076905755861415979)
              ·
                refine ⟨14118894115358633792123969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9412596076905755861415979 14118894115358633792123969)
                ·
                  refine ⟨10589170586518975344092977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14118894115358633792123969 10589170586518975344092977)
                  ·
                    refine ⟨7941877939889231508069733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10589170586518975344092977 7941877939889231508069733)
                    ·
                      refine ⟨1489102113729230907763075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7941877939889231508069733 1489102113729230907763075)
                      ·
                        rfl

theorem cell23_2900016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 4].length) (baseStart_2900016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900016 prefixEnd_2900016 := by exact prefixLift 2900016
  have htrace : WordTrace (prefixWord ++ tailWord_2900016) baseStart_2900016 baseEnd_2900016 := by
    simpa [prefixWord, tailWord_2900016, baseEnd_2900016] using wordTrace_append hprefix tailTrace_2900016
  have hstable : (prefixWord ++ tailWord_2900016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900016).length < 2 ^ (prefixWord ++ tailWord_2900016).sum := by decide
  have hdescent : baseEnd_2900016 < baseStart_2900016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900054 : List Nat := [5, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2]
def baseStart_2900054 : Nat := 118140960795 + 2900054 * 2 ^ 59
def prefixEnd_2900054 : Nat := 4983230072969 + 3 ^ 40 * 2900054 * 2
def baseEnd_2900054 : Nat := 1489121625994101759087901

theorem tailTrace_2900054 : CollatzResearch.WordTrace tailWord_2900054 prefixEnd_2900054 1489121625994101759087901 := by
  unfold tailWord_2900054
  simp only [CollatzResearch.WordTrace]
  refine ⟨6610853689725445164767201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70515772690404748424183477 6610853689725445164767201)
  ·
    refine ⟨4958140267294083873575401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6610853689725445164767201 4958140267294083873575401)
    ·
      refine ⟨3718605200470562905181551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4958140267294083873575401 3718605200470562905181551)
      ·
        refine ⟨5577907800705844357772327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3718605200470562905181551 5577907800705844357772327)
        ·
          refine ⟨8366861701058766536658491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5577907800705844357772327 8366861701058766536658491)
          ·
            refine ⟨12550292551588149804987737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8366861701058766536658491 12550292551588149804987737)
            ·
              refine ⟨9412719413691112353740803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12550292551588149804987737 9412719413691112353740803)
              ·
                refine ⟨14119079120536668530611205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9412719413691112353740803 14119079120536668530611205)
                ·
                  refine ⟨2647327335100625349489601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14119079120536668530611205 2647327335100625349489601)
                  ·
                    refine ⟨1985495501325469012117201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2647327335100625349489601 1985495501325469012117201)
                    ·
                      refine ⟨1489121625994101759087901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1985495501325469012117201 1489121625994101759087901)
                      ·
                        rfl

theorem cell23_2900054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_2900054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900054 prefixEnd_2900054 := by exact prefixLift 2900054
  have htrace : WordTrace (prefixWord ++ tailWord_2900054) baseStart_2900054 baseEnd_2900054 := by
    simpa [prefixWord, tailWord_2900054, baseEnd_2900054] using wordTrace_append hprefix tailTrace_2900054
  have hstable : (prefixWord ++ tailWord_2900054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900054).length < 2 ^ (prefixWord ++ tailWord_2900054).sum := by decide
  have hdescent : baseEnd_2900054 < baseStart_2900054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900056 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 4, 5]
def baseStart_2900056 : Nat := 118140960795 + 2900056 * 2 ^ 59
def prefixEnd_2900056 : Nat := 4983230072969 + 3 ^ 40 * 2900056 * 2
def baseEnd_2900056 : Nat := 496374217651803583754297

theorem tailTrace_2900056 : CollatzResearch.WordTrace tailWord_2900056 prefixEnd_2900056 496374217651803583754297 := by
  unfold tailWord_2900056
  simp only [CollatzResearch.WordTrace]
  refine ⟨52886865990799938488924011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70515821321066584651898681 52886865990799938488924011)
  ·
    refine ⟨79330298986199907733386017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52886865990799938488924011 79330298986199907733386017)
    ·
      refine ⟨59497724239649930800039513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79330298986199907733386017 59497724239649930800039513)
      ·
        refine ⟨44623293179737448100029635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59497724239649930800039513 44623293179737448100029635)
        ·
          refine ⟨66934939769606172150044453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44623293179737448100029635 66934939769606172150044453)
          ·
            refine ⟨12550301206801157278133335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66934939769606172150044453 12550301206801157278133335)
            ·
              refine ⟨18825451810201735917200003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12550301206801157278133335 18825451810201735917200003)
              ·
                refine ⟨28238177715302603875800005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18825451810201735917200003 28238177715302603875800005)
                ·
                  refine ⟨5294658321619238226712501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28238177715302603875800005 5294658321619238226712501)
                  ·
                    refine ⟨496374217651803583754297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5294658321619238226712501 496374217651803583754297)
                    ·
                      rfl

theorem cell23_2900056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 4, 5].length) (baseStart_2900056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900056 prefixEnd_2900056 := by exact prefixLift 2900056
  have htrace : WordTrace (prefixWord ++ tailWord_2900056) baseStart_2900056 baseEnd_2900056 := by
    simpa [prefixWord, tailWord_2900056, baseEnd_2900056] using wordTrace_append hprefix tailTrace_2900056
  have hstable : (prefixWord ++ tailWord_2900056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900056).length < 2 ^ (prefixWord ++ tailWord_2900056).sum := by decide
  have hdescent : baseEnd_2900056 < baseStart_2900056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900093 : List Nat := [1, 4, 1, 1, 3, 2, 1, 3, 2, 1, 4]
def baseStart_2900093 : Nat := 118140960795 + 2900093 * 2 ^ 59
def prefixEnd_2900093 : Nat := 4983230072969 + 3 ^ 40 * 2900093 * 2
def baseEnd_2900093 : Nat := 1489141651739627106500221

theorem tailTrace_2900093 : CollatzResearch.WordTrace tailWord_2900093 prefixEnd_2900093 1489141651739627106500221 := by
  unfold tailWord_2900093
  simp only [CollatzResearch.WordTrace]
  refine ⟨105775081482465832296944933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70516720988310554864629955 105775081482465832296944933)
  ·
    refine ⟨19832827777962343555677175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105775081482465832296944933 19832827777962343555677175)
    ·
      refine ⟨29749241666943515333515763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19832827777962343555677175 29749241666943515333515763)
      ·
        refine ⟨44623862500415273000273645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29749241666943515333515763 44623862500415273000273645)
        ·
          refine ⟨16733948437655727375102617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44623862500415273000273645 16733948437655727375102617)
          ·
            refine ⟨12550461328241795531326963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16733948437655727375102617 12550461328241795531326963)
            ·
              refine ⟨18825691992362693296990445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12550461328241795531326963 18825691992362693296990445)
              ·
                refine ⟨7059634497136009986371417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18825691992362693296990445 7059634497136009986371417)
                ·
                  refine ⟨5294725872852007489778563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7059634497136009986371417 5294725872852007489778563)
                  ·
                    refine ⟨7942088809278011234667845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5294725872852007489778563 7942088809278011234667845)
                    ·
                      refine ⟨1489141651739627106500221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7942088809278011234667845 1489141651739627106500221)
                      ·
                        rfl

theorem cell23_2900093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_2900093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900093 prefixEnd_2900093 := by exact prefixLift 2900093
  have htrace : WordTrace (prefixWord ++ tailWord_2900093) baseStart_2900093 baseEnd_2900093 := by
    simpa [prefixWord, tailWord_2900093, baseEnd_2900093] using wordTrace_append hprefix tailTrace_2900093
  have hstable : (prefixWord ++ tailWord_2900093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900093).length < 2 ^ (prefixWord ++ tailWord_2900093).sum := by decide
  have hdescent : baseEnd_2900093 < baseStart_2900093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900170 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 4, 3, 2]
def baseStart_2900170 : Nat := 118140960795 + 2900170 * 2 ^ 59
def prefixEnd_2900170 : Nat := 4983230072969 + 3 ^ 40 * 2900170 * 2
def baseEnd_2900170 : Nat := 1489181189750023305237367

theorem tailTrace_2900170 : CollatzResearch.WordTrace tailWord_2900170 prefixEnd_2900170 1489181189750023305237367 := by
  unfold tailWord_2900170
  simp only [CollatzResearch.WordTrace]
  refine ⟨26444472475796718611874491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70518593268791249631665309 26444472475796718611874491)
  ·
    refine ⟨39666708713695077917811737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26444472475796718611874491 39666708713695077917811737)
    ·
      refine ⟨29750031535271308438358803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39666708713695077917811737 29750031535271308438358803)
      ·
        refine ⟨44625047302906962657538205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29750031535271308438358803 44625047302906962657538205)
        ·
          refine ⟨16734392738590110996576827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44625047302906962657538205 16734392738590110996576827)
          ·
            refine ⟨25101589107885166494865241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16734392738590110996576827 25101589107885166494865241)
            ·
              refine ⟨18826191830913874871148931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25101589107885166494865241 18826191830913874871148931)
              ·
                refine ⟨28239287746370812306723397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18826191830913874871148931 28239287746370812306723397)
                ·
                  refine ⟨5294866452444527307510637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28239287746370812306723397 5294866452444527307510637)
                  ·
                    refine ⟨1985574919666697740316489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5294866452444527307510637 1985574919666697740316489)
                    ·
                      refine ⟨1489181189750023305237367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1985574919666697740316489 1489181189750023305237367)
                      ·
                        rfl

theorem cell23_2900170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 4, 3, 2].length) (baseStart_2900170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900170 prefixEnd_2900170 := by exact prefixLift 2900170
  have htrace : WordTrace (prefixWord ++ tailWord_2900170) baseStart_2900170 baseEnd_2900170 := by
    simpa [prefixWord, tailWord_2900170, baseEnd_2900170] using wordTrace_append hprefix tailTrace_2900170
  have hstable : (prefixWord ++ tailWord_2900170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900170).length < 2 ^ (prefixWord ++ tailWord_2900170).sum := by decide
  have hdescent : baseEnd_2900170 < baseStart_2900170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900177 : List Nat := [1, 2, 2, 1, 2, 2, 4, 4, 1, 1, 3]
def baseStart_2900177 : Nat := 118140960795 + 2900177 * 2 ^ 59
def prefixEnd_2900177 : Nat := 4983230072969 + 3 ^ 40 * 2900177 * 2
def baseEnd_2900177 : Nat := 1489184784114604777849835

theorem tailTrace_2900177 : CollatzResearch.WordTrace tailWord_2900177 prefixEnd_2900177 1489184784114604777849835 := by
  unfold tailWord_2900177
  simp only [CollatzResearch.WordTrace]
  refine ⟨105778145214161514643002785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70518763476107676428668523 105778145214161514643002785)
  ·
    refine ⟨79333608910621135982252089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105778145214161514643002785 79333608910621135982252089)
    ·
      refine ⟨59500206682965851986689067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79333608910621135982252089 59500206682965851986689067)
      ·
        refine ⟨89250310024448777980033601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59500206682965851986689067 89250310024448777980033601)
        ·
          refine ⟨66937732518336583485025201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89250310024448777980033601 66937732518336583485025201)
          ·
            refine ⟨50203299388752437613768901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66937732518336583485025201 50203299388752437613768901)
            ·
              refine ⟨9413118635391082052581669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50203299388752437613768901 9413118635391082052581669)
              ·
                refine ⟨1764959744135827884859063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9413118635391082052581669 1764959744135827884859063)
                ·
                  refine ⟨2647439616203741827288595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1764959744135827884859063 2647439616203741827288595)
                  ·
                    refine ⟨3971159424305612740932893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2647439616203741827288595 3971159424305612740932893)
                    ·
                      refine ⟨1489184784114604777849835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3971159424305612740932893 1489184784114604777849835)
                      ·
                        rfl

theorem cell23_2900177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4, 1, 1, 3].length) (baseStart_2900177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900177 prefixEnd_2900177 := by exact prefixLift 2900177
  have htrace : WordTrace (prefixWord ++ tailWord_2900177) baseStart_2900177 baseEnd_2900177 := by
    simpa [prefixWord, tailWord_2900177, baseEnd_2900177] using wordTrace_append hprefix tailTrace_2900177
  have hstable : (prefixWord ++ tailWord_2900177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900177).length < 2 ^ (prefixWord ++ tailWord_2900177).sum := by decide
  have hdescent : baseEnd_2900177 < baseStart_2900177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900200 : List Nat := [2, 1, 4, 1, 2, 2, 1, 4, 1, 1, 4]
def baseStart_2900200 : Nat := 118140960795 + 2900200 * 2 ^ 59
def prefixEnd_2900200 : Nat := 4983230072969 + 3 ^ 40 * 2900200 * 2
def baseEnd_2900200 : Nat := 1489196594169658187862229

theorem tailTrace_2900200 : CollatzResearch.WordTrace tailWord_2900200 prefixEnd_2900200 1489196594169658187862229 := by
  unfold tailWord_2900200
  simp only [CollatzResearch.WordTrace]
  refine ⟨52889492046539094785545027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70519322728718793047393369 52889492046539094785545027)
  ·
    refine ⟨79334238069808642178317541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52889492046539094785545027 79334238069808642178317541)
    ·
      refine ⟨14875169638089120408434539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79334238069808642178317541 14875169638089120408434539)
      ·
        refine ⟨22312754457133680612651809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14875169638089120408434539 22312754457133680612651809)
        ·
          refine ⟨16734565842850260459488857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22312754457133680612651809 16734565842850260459488857)
          ·
            refine ⟨12550924382137695344616643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16734565842850260459488857 12550924382137695344616643)
            ·
              refine ⟨18826386573206543016924965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12550924382137695344616643 18826386573206543016924965)
              ·
                refine ⟨3529947482476226815673431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18826386573206543016924965 3529947482476226815673431)
                ·
                  refine ⟨5294921223714340223510147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3529947482476226815673431 5294921223714340223510147)
                  ·
                    refine ⟨7942381835571510335265221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5294921223714340223510147 7942381835571510335265221)
                    ·
                      refine ⟨1489196594169658187862229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7942381835571510335265221 1489196594169658187862229)
                      ·
                        rfl

theorem cell23_2900200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_2900200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900200 prefixEnd_2900200 := by exact prefixLift 2900200
  have htrace : WordTrace (prefixWord ++ tailWord_2900200) baseStart_2900200 baseEnd_2900200 := by
    simpa [prefixWord, tailWord_2900200, baseEnd_2900200] using wordTrace_append hprefix tailTrace_2900200
  have hstable : (prefixWord ++ tailWord_2900200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900200).length < 2 ^ (prefixWord ++ tailWord_2900200).sum := by decide
  have hdescent : baseEnd_2900200 < baseStart_2900200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900210 : List Nat := [3, 2, 1, 3, 2, 1, 1, 2, 4, 4]
def baseStart_2900210 : Nat := 118140960795 + 2900210 * 2 ^ 59
def prefixEnd_2900210 : Nat := 4983230072969 + 3 ^ 40 * 2900210 * 2
def baseEnd_2900210 : Nat := 496400576325401049579061

theorem tailTrace_2900210 : CollatzResearch.WordTrace tailWord_2900210 prefixEnd_2900210 496400576325401049579061 := by
  unfold tailWord_2900210
  simp only [CollatzResearch.WordTrace]
  refine ⟨26444837205760490319738521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70519565882027974185969389 26444837205760490319738521)
  ·
    refine ⟨19833627904320367739803891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26444837205760490319738521 19833627904320367739803891)
    ·
      refine ⟨29750441856480551609705837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19833627904320367739803891 29750441856480551609705837)
      ·
        refine ⟨11156415696180206853639689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29750441856480551609705837 11156415696180206853639689)
        ·
          refine ⟨8367311772135155140229767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11156415696180206853639689 8367311772135155140229767)
          ·
            refine ⟨12550967658202732710344651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8367311772135155140229767 12550967658202732710344651)
            ·
              refine ⟨18826451487304099065516977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12550967658202732710344651 18826451487304099065516977)
              ·
                refine ⟨14119838615478074299137733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18826451487304099065516977 14119838615478074299137733)
                ·
                  refine ⟨2647469740402138931088325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14119838615478074299137733 2647469740402138931088325)
                  ·
                    refine ⟨496400576325401049579061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2647469740402138931088325 496400576325401049579061)
                    ·
                      rfl

theorem cell23_2900210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_2900210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900210 prefixEnd_2900210 := by exact prefixLift 2900210
  have htrace : WordTrace (prefixWord ++ tailWord_2900210) baseStart_2900210 baseEnd_2900210 := by
    simpa [prefixWord, tailWord_2900210, baseEnd_2900210] using wordTrace_append hprefix tailTrace_2900210
  have hstable : (prefixWord ++ tailWord_2900210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900210).length < 2 ^ (prefixWord ++ tailWord_2900210).sum := by decide
  have hdescent : baseEnd_2900210 < baseStart_2900210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900220 : List Nat := [2, 2, 2, 1, 4, 2, 2, 1, 1, 1, 5]
def baseStart_2900220 : Nat := 118140960795 + 2900220 * 2 ^ 59
def prefixEnd_2900220 : Nat := 4983230072969 + 3 ^ 40 * 2900220 * 2
def baseEnd_2900220 : Nat := 1489206863782748109612137

theorem tailTrace_2900220 : CollatzResearch.WordTrace tailWord_2900220 prefixEnd_2900220 1489206863782748109612137 := by
  unfold tailWord_2900220
  simp only [CollatzResearch.WordTrace]
  refine ⟨52889856776502866493409057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70519809035337155324545409 52889856776502866493409057)
  ·
    refine ⟨39667392582377149870056793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52889856776502866493409057 39667392582377149870056793)
    ·
      refine ⟨29750544436782862402542595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39667392582377149870056793 29750544436782862402542595)
      ·
        refine ⟨44625816655174293603813893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29750544436782862402542595 44625816655174293603813893)
        ·
          refine ⟨8367340622845180050715105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44625816655174293603813893 8367340622845180050715105)
          ·
            refine ⟨6275505467133885038036329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8367340622845180050715105 6275505467133885038036329)
            ·
              refine ⟨4706629100350413778527247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6275505467133885038036329 4706629100350413778527247)
              ·
                refine ⟨7059943650525620667790871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4706629100350413778527247 7059943650525620667790871)
                ·
                  refine ⟨10589915475788431001686307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7059943650525620667790871 10589915475788431001686307)
                  ·
                    refine ⟨15884873213682646502529461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10589915475788431001686307 15884873213682646502529461)
                    ·
                      refine ⟨1489206863782748109612137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15884873213682646502529461 1489206863782748109612137)
                      ·
                        rfl

theorem cell23_2900220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_2900220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900220 prefixEnd_2900220 := by exact prefixLift 2900220
  have htrace : WordTrace (prefixWord ++ tailWord_2900220) baseStart_2900220 baseEnd_2900220 := by
    simpa [prefixWord, tailWord_2900220, baseEnd_2900220] using wordTrace_append hprefix tailTrace_2900220
  have hstable : (prefixWord ++ tailWord_2900220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900220).length < 2 ^ (prefixWord ++ tailWord_2900220).sum := by decide
  have hdescent : baseEnd_2900220 < baseStart_2900220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900234 : List Nat := [3, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2]
def baseStart_2900234 : Nat := 118140960795 + 2900234 * 2 ^ 59
def prefixEnd_2900234 : Nat := 4983230072969 + 3 ^ 40 * 2900234 * 2
def baseEnd_2900234 : Nat := 1489214052511911054837073

theorem tailTrace_2900234 : CollatzResearch.WordTrace tailWord_2900234 prefixEnd_2900234 1489214052511911054837073 := by
  unfold tailWord_2900234
  simp only [CollatzResearch.WordTrace]
  refine ⟨26445056043738753344456939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70520149449970008918551837 26445056043738753344456939)
  ·
    refine ⟨39667584065608130016685409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26445056043738753344456939 39667584065608130016685409)
    ·
      refine ⟨29750688049206097512514057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39667584065608130016685409 29750688049206097512514057)
      ·
        refine ⟨22313016036904573134385543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29750688049206097512514057 22313016036904573134385543)
        ·
          refine ⟨33469524055356859701578315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22313016036904573134385543 33469524055356859701578315)
          ·
            refine ⟨50204286083035289552367473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33469524055356859701578315 50204286083035289552367473)
            ·
              refine ⟨37653214562276467164275605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50204286083035289552367473 37653214562276467164275605)
              ·
                refine ⟨1764994432606709398325419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37653214562276467164275605 1764994432606709398325419)
                ·
                  refine ⟨2647491648910064097488129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1764994432606709398325419 2647491648910064097488129)
                  ·
                    refine ⟨1985618736682548073116097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2647491648910064097488129 1985618736682548073116097)
                    ·
                      refine ⟨1489214052511911054837073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1985618736682548073116097 1489214052511911054837073)
                      ·
                        rfl

theorem cell23_2900234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_2900234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900234 prefixEnd_2900234 := by exact prefixLift 2900234
  have htrace : WordTrace (prefixWord ++ tailWord_2900234) baseStart_2900234 baseEnd_2900234 := by
    simpa [prefixWord, tailWord_2900234, baseEnd_2900234] using wordTrace_append hprefix tailTrace_2900234
  have hstable : (prefixWord ++ tailWord_2900234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900234).length < 2 ^ (prefixWord ++ tailWord_2900234).sum := by decide
  have hdescent : baseEnd_2900234 < baseStart_2900234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900254 : List Nat := [4, 3, 2, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_2900254 : Nat := 118140960795 + 2900254 * 2 ^ 59
def prefixEnd_2900254 : Nat := 4983230072969 + 3 ^ 40 * 2900254 * 2
def baseEnd_2900254 : Nat := 1489224322125000976586981

theorem tailTrace_2900254 : CollatzResearch.WordTrace tailWord_2900254 prefixEnd_2900254 1489224322125000976586981 := by
  unfold tailWord_2900254
  simp only [CollatzResearch.WordTrace]
  refine ⟨13222619204360319599194477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70520635756588371195703877 13222619204360319599194477)
  ·
    refine ⟨4958482201635119849697929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13222619204360319599194477 4958482201635119849697929)
    ·
      refine ⟨3718861651226339887273447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4958482201635119849697929 3718861651226339887273447)
      ·
        refine ⟨5578292476839509830910171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3718861651226339887273447 5578292476839509830910171)
        ·
          refine ⟨8367438715259264746365257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5578292476839509830910171 8367438715259264746365257)
          ·
            refine ⟨6275579036444448559773943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8367438715259264746365257 6275579036444448559773943)
            ·
              refine ⟨9413368554666672839660915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6275579036444448559773943 9413368554666672839660915)
              ·
                refine ⟨14120052832000009259491373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9413368554666672839660915 14120052832000009259491373)
                ·
                  refine ⟨5295019812000003472309265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14120052832000009259491373 5295019812000003472309265)
                  ·
                    refine ⟨3971264859000002604231949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5295019812000003472309265 3971264859000002604231949)
                    ·
                      refine ⟨1489224322125000976586981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3971264859000002604231949 1489224322125000976586981)
                      ·
                        rfl

theorem cell23_2900254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_2900254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900254 prefixEnd_2900254 := by exact prefixLift 2900254
  have htrace : WordTrace (prefixWord ++ tailWord_2900254) baseStart_2900254 baseEnd_2900254 := by
    simpa [prefixWord, tailWord_2900254, baseEnd_2900254] using wordTrace_append hprefix tailTrace_2900254
  have hstable : (prefixWord ++ tailWord_2900254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900254).length < 2 ^ (prefixWord ++ tailWord_2900254).sum := by decide
  have hdescent : baseEnd_2900254 < baseStart_2900254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900341 : List Nat := [1, 3, 4, 1, 2, 1, 3, 2, 2, 2, 2]
def baseStart_2900341 : Nat := 118140960795 + 2900341 * 2 ^ 59
def prefixEnd_2900341 : Nat := 4983230072969 + 3 ^ 40 * 2900341 * 2
def baseEnd_2900341 : Nat := 1489268994941942136199081

theorem tailTrace_2900341 : CollatzResearch.WordTrace tailWord_2900341 prefixEnd_2900341 1489268994941942136199081 := by
  unfold tailWord_2900341
  simp only [CollatzResearch.WordTrace]
  refine ⟨105784126785567370651972877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70522751190378247101315251 105784126785567370651972877)
  ·
    refine ⟨39669047544587763994489829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105784126785567370651972877 39669047544587763994489829)
    ·
      refine ⟨7437946414610205748966843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39669047544587763994489829 7437946414610205748966843)
      ·
        refine ⟨11156919621915308623450265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7437946414610205748966843 11156919621915308623450265)
        ·
          refine ⟨8367689716436481467587699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11156919621915308623450265 8367689716436481467587699)
          ·
            refine ⟨12551534574654722201381549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8367689716436481467587699 12551534574654722201381549)
            ·
              refine ⟨4706825465495520825518081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12551534574654722201381549 4706825465495520825518081)
              ·
                refine ⟨3530119099121640619138561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4706825465495520825518081 3530119099121640619138561)
                ·
                  refine ⟨2647589324341230464353921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3530119099121640619138561 2647589324341230464353921)
                  ·
                    refine ⟨1985691993255922848265441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2647589324341230464353921 1985691993255922848265441)
                    ·
                      refine ⟨1489268994941942136199081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1985691993255922848265441 1489268994941942136199081)
                      ·
                        rfl

theorem cell23_2900341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_2900341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900341 prefixEnd_2900341 := by exact prefixLift 2900341
  have htrace : WordTrace (prefixWord ++ tailWord_2900341) baseStart_2900341 baseEnd_2900341 := by
    simpa [prefixWord, tailWord_2900341, baseEnd_2900341] using wordTrace_append hprefix tailTrace_2900341
  have hstable : (prefixWord ++ tailWord_2900341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900341).length < 2 ^ (prefixWord ++ tailWord_2900341).sum := by decide
  have hdescent : baseEnd_2900341 < baseStart_2900341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900373 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 1, 10]
def baseStart_2900373 : Nat := 118140960795 + 2900373 * 2 ^ 59
def prefixEnd_2900373 : Nat := 4983230072969 + 3 ^ 40 * 2900373 * 2
def baseEnd_2900373 : Nat := 496428475440962003666311

theorem tailTrace_2900373 : CollatzResearch.WordTrace tailWord_2900373 prefixEnd_2900373 496428475440962003666311 := by
  unfold tailWord_2900373
  simp only [CollatzResearch.WordTrace]
  refine ⟨105785293921451440117137773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70523529280967626744758515 105785293921451440117137773)
  ·
    refine ⟨39669485220544290043926665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105785293921451440117137773 39669485220544290043926665)
    ·
      refine ⟨29752113915408217532944999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39669485220544290043926665 29752113915408217532944999)
      ·
        refine ⟨44628170873112326299417499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29752113915408217532944999 44628170873112326299417499)
        ·
          refine ⟨66942256309668489449126249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44628170873112326299417499 66942256309668489449126249)
          ·
            refine ⟨50206692232251367086844687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66942256309668489449126249 50206692232251367086844687)
            ·
              refine ⟨75310038348377050630267031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50206692232251367086844687 75310038348377050630267031)
              ·
                refine ⟨112965057522565575945400547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75310038348377050630267031 112965057522565575945400547)
                ·
                  refine ⟨169447586283848363918100821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112965057522565575945400547 169447586283848363918100821)
                  ·
                    refine ⟨496428475440962003666311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 169447586283848363918100821 496428475440962003666311)
                    ·
                      rfl

theorem cell23_2900373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_2900373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900373 prefixEnd_2900373 := by exact prefixLift 2900373
  have htrace : WordTrace (prefixWord ++ tailWord_2900373) baseStart_2900373 baseEnd_2900373 := by
    simpa [prefixWord, tailWord_2900373, baseEnd_2900373] using wordTrace_append hprefix tailTrace_2900373
  have hstable : (prefixWord ++ tailWord_2900373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900373).length < 2 ^ (prefixWord ++ tailWord_2900373).sum := by decide
  have hdescent : baseEnd_2900373 < baseStart_2900373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900381 : List Nat := [1, 4, 2, 1, 5, 1, 1, 3, 5]
def baseStart_2900381 : Nat := 118140960795 + 2900381 * 2 ^ 59
def prefixEnd_2900381 : Nat := 4983230072969 + 3 ^ 40 * 2900381 * 2
def baseEnd_2900381 : Nat := 165476614907569108855433

theorem tailTrace_2900381 : CollatzResearch.WordTrace tailWord_2900381 prefixEnd_2900381 165476614907569108855433 := by
  unfold tailWord_2900381
  simp only [CollatzResearch.WordTrace]
  refine ⟨105785585705422457483428997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70523723803614971655619331 105785585705422457483428997)
  ·
    refine ⟨19834797319766710778142937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105785585705422457483428997 19834797319766710778142937)
    ·
      refine ⟨14876097989825033083607203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19834797319766710778142937 14876097989825033083607203)
      ·
        refine ⟨22314146984737549625410805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14876097989825033083607203 22314146984737549625410805)
        ·
          refine ⟨2091951279819145277382263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22314146984737549625410805 2091951279819145277382263)
          ·
            refine ⟨3137926919728717916073395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2091951279819145277382263 3137926919728717916073395)
            ·
              refine ⟨4706890379593076874110093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3137926919728717916073395 4706890379593076874110093)
              ·
                refine ⟨1765083892347403827791285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4706890379593076874110093 1765083892347403827791285)
                ·
                  refine ⟨165476614907569108855433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1765083892347403827791285 165476614907569108855433)
                  ·
                    rfl

theorem cell23_2900381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3, 5].length) (baseStart_2900381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900381 prefixEnd_2900381 := by exact prefixLift 2900381
  have htrace : WordTrace (prefixWord ++ tailWord_2900381) baseStart_2900381 baseEnd_2900381 := by
    simpa [prefixWord, tailWord_2900381, baseEnd_2900381] using wordTrace_append hprefix tailTrace_2900381
  have hstable : (prefixWord ++ tailWord_2900381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900381).length < 2 ^ (prefixWord ++ tailWord_2900381).sum := by decide
  have hdescent : baseEnd_2900381 < baseStart_2900381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900393 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 1, 3, 6]
def baseStart_2900393 : Nat := 118140960795 + 2900393 * 2 ^ 59
def prefixEnd_2900393 : Nat := 4983230072969 + 3 ^ 40 * 2900393 * 2
def baseEnd_2900393 : Nat := 1489295695935975932748841

theorem tailTrace_2900393 : CollatzResearch.WordTrace tailWord_2900393 prefixEnd_2900393 1489295695935975932748841 := by
  unfold tailWord_2900393
  simp only [CollatzResearch.WordTrace]
  refine ⟨105786023381378983532865833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70524015587585989021910555 105786023381378983532865833)
  ·
    refine ⟨79339517536034237649649375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105786023381378983532865833 79339517536034237649649375)
    ·
      refine ⟨119009276304051356474474063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79339517536034237649649375 119009276304051356474474063)
      ·
        refine ⟨178513914456077034711711095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119009276304051356474474063 178513914456077034711711095)
        ·
          refine ⟨267770871684115552067566643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178513914456077034711711095 267770871684115552067566643)
          ·
            refine ⟨401656307526173328101349965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267770871684115552067566643 401656307526173328101349965)
            ·
              refine ⟨150621115322314998038006237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 401656307526173328101349965 150621115322314998038006237)
              ·
                refine ⟨56482918245868124264252339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150621115322314998038006237 56482918245868124264252339)
                ·
                  refine ⟨84724377368802186396378509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56482918245868124264252339 84724377368802186396378509)
                  ·
                    refine ⟨31771641513300819898641941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84724377368802186396378509 31771641513300819898641941)
                    ·
                      refine ⟨1489295695935975932748841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31771641513300819898641941 1489295695935975932748841)
                      ·
                        rfl

theorem cell23_2900393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 3, 6].length) (baseStart_2900393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900393 prefixEnd_2900393 := by exact prefixLift 2900393
  have htrace : WordTrace (prefixWord ++ tailWord_2900393) baseStart_2900393 baseEnd_2900393 := by
    simpa [prefixWord, tailWord_2900393, baseEnd_2900393] using wordTrace_append hprefix tailTrace_2900393
  have hstable : (prefixWord ++ tailWord_2900393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900393).length < 2 ^ (prefixWord ++ tailWord_2900393).sum := by decide
  have hdescent : baseEnd_2900393 < baseStart_2900393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900407 : List Nat := [1, 1, 3, 1, 3, 3, 3, 1, 3, 4]
def baseStart_2900407 : Nat := 118140960795 + 2900407 * 2 ^ 59
def prefixEnd_2900407 : Nat := 4983230072969 + 3 ^ 40 * 2900407 * 2
def baseEnd_2900407 : Nat := 496434294888379625991259

theorem tailTrace_2900407 : CollatzResearch.WordTrace tailWord_2900407 prefixEnd_2900407 496434294888379625991259 := by
  unfold tailWord_2900407
  simp only [CollatzResearch.WordTrace]
  refine ⟨105786534003328263923875475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70524356002218842615916983 105786534003328263923875475)
  ·
    refine ⟨158679801004992395885813213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105786534003328263923875475 158679801004992395885813213)
    ·
      refine ⟨59504925376872148457179955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158679801004992395885813213 59504925376872148457179955)
      ·
        refine ⟨89257388065308222685769933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59504925376872148457179955 89257388065308222685769933)
        ·
          refine ⟨33471520524490583507163725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89257388065308222685769933 33471520524490583507163725)
          ·
            refine ⟨12551820196683968815186397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33471520524490583507163725 12551820196683968815186397)
            ·
              refine ⟨4706932573756488305694899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12551820196683968815186397 4706932573756488305694899)
              ·
                refine ⟨7060398860634732458542349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4706932573756488305694899 7060398860634732458542349)
                ·
                  refine ⟨2647649572738024671953381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7060398860634732458542349 2647649572738024671953381)
                  ·
                    refine ⟨496434294888379625991259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2647649572738024671953381 496434294888379625991259)
                    ·
                      rfl

theorem cell23_2900407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3, 4].length) (baseStart_2900407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900407 prefixEnd_2900407 := by exact prefixLift 2900407
  have htrace : WordTrace (prefixWord ++ tailWord_2900407) baseStart_2900407 baseEnd_2900407 := by
    simpa [prefixWord, tailWord_2900407, baseEnd_2900407] using wordTrace_append hprefix tailTrace_2900407
  have hstable : (prefixWord ++ tailWord_2900407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900407).length < 2 ^ (prefixWord ++ tailWord_2900407).sum := by decide
  have hdescent : baseEnd_2900407 < baseStart_2900407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900457 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 4, 3, 2]
def baseStart_2900457 : Nat := 118140960795 + 2900457 * 2 ^ 59
def prefixEnd_2900457 : Nat := 4983230072969 + 3 ^ 40 * 2900457 * 2
def baseEnd_2900457 : Nat := 1489328558697863682348547

theorem tailTrace_2900457 : CollatzResearch.WordTrace tailWord_2900457 prefixEnd_2900457 1489328558697863682348547 := by
  unfold tailWord_2900457
  simp only [CollatzResearch.WordTrace]
  refine ⟨105788357653147122463195625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70525571768764748308797083 105788357653147122463195625)
  ·
    refine ⟨79341268239860341847396719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105788357653147122463195625 79341268239860341847396719)
    ·
      refine ⟨119011902359790512771095079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79341268239860341847396719 119011902359790512771095079)
      ·
        refine ⟨178517853539685769156642619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119011902359790512771095079 178517853539685769156642619)
        ·
          refine ⟨267776780309528653734963929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178517853539685769156642619 267776780309528653734963929)
          ·
            refine ⟨200832585232146490301222947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267776780309528653734963929 200832585232146490301222947)
            ·
              refine ⟨301248877848219735451834421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200832585232146490301222947 301248877848219735451834421)
              ·
                refine ⟨28242082298270600198609477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 301248877848219735451834421 28242082298270600198609477)
                ·
                  refine ⟨5295390430925737537239277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28242082298270600198609477 5295390430925737537239277)
                  ·
                    refine ⟨1985771411597151576464729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5295390430925737537239277 1985771411597151576464729)
                    ·
                      refine ⟨1489328558697863682348547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1985771411597151576464729 1489328558697863682348547)
                      ·
                        rfl

theorem cell23_2900457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 3, 2].length) (baseStart_2900457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900457 prefixEnd_2900457 := by exact prefixLift 2900457
  have htrace : WordTrace (prefixWord ++ tailWord_2900457) baseStart_2900457 baseEnd_2900457 := by
    simpa [prefixWord, tailWord_2900457, baseEnd_2900457] using wordTrace_append hprefix tailTrace_2900457
  have hstable : (prefixWord ++ tailWord_2900457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900457).length < 2 ^ (prefixWord ++ tailWord_2900457).sum := by decide
  have hdescent : baseEnd_2900457 < baseStart_2900457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900458 : List Nat := [3, 1, 3, 1, 3, 3, 2, 2, 1, 4]
def baseStart_2900458 : Nat := 118140960795 + 2900458 * 2 ^ 59
def prefixEnd_2900458 : Nat := 4983230072969 + 3 ^ 40 * 2900458 * 2
def baseEnd_2900458 : Nat := 496443024059506059478681

theorem tailTrace_2900458 : CollatzResearch.WordTrace tailWord_2900458 prefixEnd_2900458 496443024059506059478681 := by
  unfold tailWord_2900458
  simp only [CollatzResearch.WordTrace]
  refine ⟨26447098531535874908495507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70525596084095666422654685 26447098531535874908495507)
  ·
    refine ⟨39670647797303812362743261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26447098531535874908495507 39670647797303812362743261)
    ·
      refine ⟨14876492923988929636028723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39670647797303812362743261 14876492923988929636028723)
      ·
        refine ⟨22314739385983394454043085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14876492923988929636028723 22314739385983394454043085)
        ·
          refine ⟨8368027269743772920266157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22314739385983394454043085 8368027269743772920266157)
          ·
            refine ⟨3138010226153914845099809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8368027269743772920266157 3138010226153914845099809)
            ·
              refine ⟨2353507669615436133824857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3138010226153914845099809 2353507669615436133824857)
              ·
                refine ⟨1765130752211577100368643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2353507669615436133824857 1765130752211577100368643)
                ·
                  refine ⟨2647696128317365650552965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1765130752211577100368643 2647696128317365650552965)
                  ·
                    refine ⟨496443024059506059478681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2647696128317365650552965 496443024059506059478681)
                    ·
                      rfl

theorem cell23_2900458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_2900458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900458 prefixEnd_2900458 := by exact prefixLift 2900458
  have htrace : WordTrace (prefixWord ++ tailWord_2900458) baseStart_2900458 baseEnd_2900458 := by
    simpa [prefixWord, tailWord_2900458, baseEnd_2900458] using wordTrace_append hprefix tailTrace_2900458
  have hstable : (prefixWord ++ tailWord_2900458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900458).length < 2 ^ (prefixWord ++ tailWord_2900458).sum := by decide
  have hdescent : baseEnd_2900458 < baseStart_2900458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900491 : List Nat := [1, 1, 1, 1, 7, 3, 1, 1, 2, 3, 2]
def baseStart_2900491 : Nat := 118140960795 + 2900491 * 2 ^ 59
def prefixEnd_2900491 : Nat := 4983230072969 + 3 ^ 40 * 2900491 * 2
def baseEnd_2900491 : Nat := 1489346017040116549323391

theorem tailTrace_2900491 : CollatzResearch.WordTrace tailWord_2900491 prefixEnd_2900491 1489346017040116549323391 := by
  unfold tailWord_2900491
  simp only [CollatzResearch.WordTrace]
  refine ⟨105789597735023946269933327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70526398490015964179955551 105789597735023946269933327)
  ·
    refine ⟨158684396602535919404899991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105789597735023946269933327 158684396602535919404899991)
    ·
      refine ⟨238026594903803879107349987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158684396602535919404899991 238026594903803879107349987)
      ·
        refine ⟨357039892355705818661024981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238026594903803879107349987 357039892355705818661024981)
        ·
          refine ⟨8368122477086855124867773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 357039892355705818661024981 8368122477086855124867773)
          ·
            refine ⟨3138045928907570671825415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8368122477086855124867773 3138045928907570671825415)
            ·
              refine ⟨4707068893361356007738123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3138045928907570671825415 4707068893361356007738123)
              ·
                refine ⟨7060603340042034011607185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4707068893361356007738123 7060603340042034011607185)
                ·
                  refine ⟨5295452505031525508705389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7060603340042034011607185 5295452505031525508705389)
                  ·
                    refine ⟨1985794689386822065764521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5295452505031525508705389 1985794689386822065764521)
                    ·
                      refine ⟨1489346017040116549323391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1985794689386822065764521 1489346017040116549323391)
                      ·
                        rfl

theorem cell23_2900491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 3, 2].length) (baseStart_2900491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900491 prefixEnd_2900491 := by exact prefixLift 2900491
  have htrace : WordTrace (prefixWord ++ tailWord_2900491) baseStart_2900491 baseEnd_2900491 := by
    simpa [prefixWord, tailWord_2900491, baseEnd_2900491] using wordTrace_append hprefix tailTrace_2900491
  have hstable : (prefixWord ++ tailWord_2900491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900491).length < 2 ^ (prefixWord ++ tailWord_2900491).sum := by decide
  have hdescent : baseEnd_2900491 < baseStart_2900491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900504 : List Nat := [2, 1, 2, 3, 3, 2, 1, 3, 1, 1, 4]
def baseStart_2900504 : Nat := 118140960795 + 2900504 * 2 ^ 59
def prefixEnd_2900504 : Nat := 4983230072969 + 3 ^ 40 * 2900504 * 2
def baseEnd_2900504 : Nat := 1489352692288624998460831

theorem tailTrace_2900504 : CollatzResearch.WordTrace tailWord_2900504 prefixEnd_2900504 1489352692288624998460831 := by
  unfold tailWord_2900504
  simp only [CollatzResearch.WordTrace]
  refine ⟨52895035941988424745078283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70526714589317899660104377 52895035941988424745078283)
  ·
    refine ⟨79342553912982637117617425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52895035941988424745078283 79342553912982637117617425)
    ·
      refine ⟨59506915434736977838213069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79342553912982637117617425 59506915434736977838213069)
      ·
        refine ⟨22315093288026366689329901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59506915434736977838213069 22315093288026366689329901)
        ·
          refine ⟨8368159983009887508498713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22315093288026366689329901 8368159983009887508498713)
          ·
            refine ⟨6276119987257415631374035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8368159983009887508498713 6276119987257415631374035)
            ·
              refine ⟨9414179980886123447061053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6276119987257415631374035 9414179980886123447061053)
              ·
                refine ⟨3530317492832296292647895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9414179980886123447061053 3530317492832296292647895)
                ·
                  refine ⟨5295476239248444438971843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3530317492832296292647895 5295476239248444438971843)
                  ·
                    refine ⟨7943214358872666658457765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5295476239248444438971843 7943214358872666658457765)
                    ·
                      refine ⟨1489352692288624998460831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7943214358872666658457765 1489352692288624998460831)
                      ·
                        rfl

theorem cell23_2900504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_2900504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900504 prefixEnd_2900504 := by exact prefixLift 2900504
  have htrace : WordTrace (prefixWord ++ tailWord_2900504) baseStart_2900504 baseEnd_2900504 := by
    simpa [prefixWord, tailWord_2900504, baseEnd_2900504] using wordTrace_append hprefix tailTrace_2900504
  have hstable : (prefixWord ++ tailWord_2900504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900504).length < 2 ^ (prefixWord ++ tailWord_2900504).sum := by decide
  have hdescent : baseEnd_2900504 < baseStart_2900504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900534 : List Nat := [5, 1, 2, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_2900534 : Nat := 118140960795 + 2900534 * 2 ^ 59
def prefixEnd_2900534 : Nat := 4983230072969 + 3 ^ 40 * 2900534 * 2
def baseEnd_2900534 : Nat := 1489368096708259881085693

theorem tailTrace_2900534 : CollatzResearch.WordTrace tailWord_2900534 prefixEnd_2900534 1489368096708259881085693 := by
  unfold tailWord_2900534
  simp only [CollatzResearch.WordTrace]
  refine ⟨6611947879616760288359291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70527444049245443075832437 6611947879616760288359291)
  ·
    refine ⟨9917921819425140432538937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6611947879616760288359291 9917921819425140432538937)
    ·
      refine ⟨7438441364568855324404203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9917921819425140432538937 7438441364568855324404203)
      ·
        refine ⟨11157662046853282986606305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7438441364568855324404203 11157662046853282986606305)
        ·
          refine ⟨8368246535139962239954729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11157662046853282986606305 8368246535139962239954729)
          ·
            refine ⟨6276184901354971679966047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8368246535139962239954729 6276184901354971679966047)
            ·
              refine ⟨9414277352032457519949071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6276184901354971679966047 9414277352032457519949071)
              ·
                refine ⟨14121416028048686279923607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9414277352032457519949071 14121416028048686279923607)
                ·
                  refine ⟨21182124042073029419885411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14121416028048686279923607 21182124042073029419885411)
                  ·
                    refine ⟨31773186063109544129828117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21182124042073029419885411 31773186063109544129828117)
                    ·
                      refine ⟨1489368096708259881085693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31773186063109544129828117 1489368096708259881085693)
                      ·
                        rfl

theorem cell23_2900534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_2900534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900534 prefixEnd_2900534 := by exact prefixLift 2900534
  have htrace : WordTrace (prefixWord ++ tailWord_2900534) baseStart_2900534 baseEnd_2900534 := by
    simpa [prefixWord, tailWord_2900534, baseEnd_2900534] using wordTrace_append hprefix tailTrace_2900534
  have hstable : (prefixWord ++ tailWord_2900534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900534).length < 2 ^ (prefixWord ++ tailWord_2900534).sum := by decide
  have hdescent : baseEnd_2900534 < baseStart_2900534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900541 : List Nat := [1, 4, 1, 3, 2, 2, 2, 2, 1, 2, 3]
def baseStart_2900541 : Nat := 118140960795 + 2900541 * 2 ^ 59
def prefixEnd_2900541 : Nat := 4983230072969 + 3 ^ 40 * 2900541 * 2
def baseEnd_2900541 : Nat := 1489371691072841353698161

theorem tailTrace_2900541 : CollatzResearch.WordTrace tailWord_2900541 prefixEnd_2900541 1489371691072841353698161 := by
  unfold tailWord_2900541
  simp only [CollatzResearch.WordTrace]
  refine ⟨105791421384842804809253477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70527614256561869872835651 105791421384842804809253477)
  ·
    refine ⟨19835891509658025901735027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105791421384842804809253477 19835891509658025901735027)
    ·
      refine ⟨29753837264487038852602541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19835891509658025901735027 29753837264487038852602541)
      ·
        refine ⟨11157688974182639569725953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29753837264487038852602541 11157688974182639569725953)
        ·
          refine ⟨8368266730636979677294465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11157688974182639569725953 8368266730636979677294465)
          ·
            refine ⟨6276200047977734757970849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8368266730636979677294465 6276200047977734757970849)
            ·
              refine ⟨4707150035983301068478137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6276200047977734757970849 4707150035983301068478137)
              ·
                refine ⟨3530362526987475801358603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4707150035983301068478137 3530362526987475801358603)
                ·
                  refine ⟨5295543790481213702037905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3530362526987475801358603 5295543790481213702037905)
                  ·
                    refine ⟨3971657842860910276528429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5295543790481213702037905 3971657842860910276528429)
                    ·
                      refine ⟨1489371691072841353698161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3971657842860910276528429 1489371691072841353698161)
                      ·
                        rfl

theorem cell23_2900541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_2900541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900541 prefixEnd_2900541 := by exact prefixLift 2900541
  have htrace : WordTrace (prefixWord ++ tailWord_2900541) baseStart_2900541 baseEnd_2900541 := by
    simpa [prefixWord, tailWord_2900541, baseEnd_2900541] using wordTrace_append hprefix tailTrace_2900541
  have hstable : (prefixWord ++ tailWord_2900541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900541).length < 2 ^ (prefixWord ++ tailWord_2900541).sum := by decide
  have hdescent : baseEnd_2900541 < baseStart_2900541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900547 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 2, 7, 2]
def baseStart_2900547 : Nat := 118140960795 + 2900547 * 2 ^ 59
def prefixEnd_2900547 : Nat := 4983230072969 + 3 ^ 40 * 2900547 * 2
def baseEnd_2900547 : Nat := 1489374771956768330223133

theorem tailTrace_2900547 : CollatzResearch.WordTrace tailWord_2900547 prefixEnd_2900547 1489374771956768330223133 := by
  unfold tailWord_2900547
  simp only [CollatzResearch.WordTrace]
  refine ⟨105791640222821067833971895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70527760148547378555981263 105791640222821067833971895)
  ·
    refine ⟨158687460334231601750957843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105791640222821067833971895 158687460334231601750957843)
    ·
      refine ⟨238031190501347402626436765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158687460334231601750957843 238031190501347402626436765)
      ·
        refine ⟨89261696438005275984913787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238031190501347402626436765 89261696438005275984913787)
        ·
          refine ⟨133892544657007913977370681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89261696438005275984913787 133892544657007913977370681)
          ·
            refine ⟨100419408492755935483028011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133892544657007913977370681 100419408492755935483028011)
            ·
              refine ⟨150629112739133903224542017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100419408492755935483028011 150629112739133903224542017)
              ·
                refine ⟨112971834554350427418406513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150629112739133903224542017 112971834554350427418406513)
                ·
                  refine ⟨84728875915762820563804885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112971834554350427418406513 84728875915762820563804885)
                  ·
                    refine ⟨1985833029275691106964177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 84728875915762820563804885 1985833029275691106964177)
                    ·
                      refine ⟨1489374771956768330223133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1985833029275691106964177 1489374771956768330223133)
                      ·
                        rfl

theorem cell23_2900547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 7, 2].length) (baseStart_2900547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900547 prefixEnd_2900547 := by exact prefixLift 2900547
  have htrace : WordTrace (prefixWord ++ tailWord_2900547) baseStart_2900547 baseEnd_2900547 := by
    simpa [prefixWord, tailWord_2900547, baseEnd_2900547] using wordTrace_append hprefix tailTrace_2900547
  have hstable : (prefixWord ++ tailWord_2900547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900547).length < 2 ^ (prefixWord ++ tailWord_2900547).sum := by decide
  have hdescent : baseEnd_2900547 < baseStart_2900547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900554 : List Nat := [3, 1, 2, 1, 1, 4, 1, 2, 4, 1, 3]
def baseStart_2900554 : Nat := 118140960795 + 2900554 * 2 ^ 59
def prefixEnd_2900554 : Nat := 4983230072969 + 3 ^ 40 * 2900554 * 2
def baseEnd_2900554 : Nat := 1489378366321349802835601

theorem tailTrace_2900554 : CollatzResearch.WordTrace tailWord_2900554 prefixEnd_2900554 1489378366321349802835601 := by
  unfold tailWord_2900554
  simp only [CollatzResearch.WordTrace]
  refine ⟨26447973883448927007369179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70527930355863805352984477 26447973883448927007369179)
  ·
    refine ⟨39671960825173390511053769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26447973883448927007369179 39671960825173390511053769)
    ·
      refine ⟨29753970618880042883290327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39671960825173390511053769 29753970618880042883290327)
      ·
        refine ⟨44630955928320064324935491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29753970618880042883290327 44630955928320064324935491)
        ·
          refine ⟨66946433892480096487403237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44630955928320064324935491 66946433892480096487403237)
          ·
            refine ⟨12552456354840018091388107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66946433892480096487403237 12552456354840018091388107)
            ·
              refine ⟨18828684532260027137082161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12552456354840018091388107 18828684532260027137082161)
              ·
                refine ⟨14121513399195020352811621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18828684532260027137082161 14121513399195020352811621)
                ·
                  refine ⟨2647783762349066316152179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14121513399195020352811621 2647783762349066316152179)
                  ·
                    refine ⟨3971675643523599474228269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2647783762349066316152179 3971675643523599474228269)
                    ·
                      refine ⟨1489378366321349802835601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3971675643523599474228269 1489378366321349802835601)
                      ·
                        rfl

theorem cell23_2900554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_2900554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900554 prefixEnd_2900554 := by exact prefixLift 2900554
  have htrace : WordTrace (prefixWord ++ tailWord_2900554) baseStart_2900554 baseEnd_2900554 := by
    simpa [prefixWord, tailWord_2900554, baseEnd_2900554] using wordTrace_append hprefix tailTrace_2900554
  have hstable : (prefixWord ++ tailWord_2900554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900554).length < 2 ^ (prefixWord ++ tailWord_2900554).sum := by decide
  have hdescent : baseEnd_2900554 < baseStart_2900554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900572 : List Nat := [2, 2, 4, 1, 3, 1, 3, 2, 1, 2, 2]
def baseStart_2900572 : Nat := 118140960795 + 2900572 * 2 ^ 59
def prefixEnd_2900572 : Nat := 4983230072969 + 3 ^ 40 * 2900572 * 2
def baseEnd_2900572 : Nat := 1489387608973130732410519

theorem tailTrace_2900572 : CollatzResearch.WordTrace tailWord_2900572 prefixEnd_2900572 1489387608973130732410519 := by
  unfold tailWord_2900572
  simp only [CollatzResearch.WordTrace]
  refine ⟨52896276023865248551815985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70528368031820331402421313 52896276023865248551815985)
  ·
    refine ⟨39672207017898936413861989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52896276023865248551815985 39672207017898936413861989)
    ·
      refine ⟨7438538815856050577599123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39672207017898936413861989 7438538815856050577599123)
      ·
        refine ⟨11157808223784075866398685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7438538815856050577599123 11157808223784075866398685)
        ·
          refine ⟨4184178083919028449899507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11157808223784075866398685 4184178083919028449899507)
          ·
            refine ⟨6276267125878542674849261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4184178083919028449899507 6276267125878542674849261)
            ·
              refine ⟨2353600172204453503068473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6276267125878542674849261 2353600172204453503068473)
              ·
                refine ⟨1765200129153340127301355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2353600172204453503068473 1765200129153340127301355)
                ·
                  refine ⟨2647800193730010190952033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1765200129153340127301355 2647800193730010190952033)
                  ·
                    refine ⟨1985850145297507643214025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2647800193730010190952033 1985850145297507643214025)
                    ·
                      refine ⟨1489387608973130732410519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1985850145297507643214025 1489387608973130732410519)
                      ·
                        rfl

theorem cell23_2900572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_2900572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900572 prefixEnd_2900572 := by exact prefixLift 2900572
  have htrace : WordTrace (prefixWord ++ tailWord_2900572) baseStart_2900572 baseEnd_2900572 := by
    simpa [prefixWord, tailWord_2900572, baseEnd_2900572] using wordTrace_append hprefix tailTrace_2900572
  have hstable : (prefixWord ++ tailWord_2900572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900572).length < 2 ^ (prefixWord ++ tailWord_2900572).sum := by decide
  have hdescent : baseEnd_2900572 < baseStart_2900572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900598 : List Nat := [5, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2]
def baseStart_2900598 : Nat := 118140960795 + 2900598 * 2 ^ 59
def prefixEnd_2900598 : Nat := 4983230072969 + 3 ^ 40 * 2900598 * 2
def baseEnd_2900598 : Nat := 1489400959470147630685399

theorem tailTrace_2900598 : CollatzResearch.WordTrace tailWord_2900598 prefixEnd_2900598 1489400959470147630685399 := by
  unfold tailWord_2900598
  simp only [CollatzResearch.WordTrace]
  refine ⟨6612093771602268971504903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70529000230424202362718965 6612093771602268971504903)
  ·
    refine ⟨9918140657403403457257355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6612093771602268971504903 9918140657403403457257355)
    ·
      refine ⟨14877210986105105185886033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9918140657403403457257355 14877210986105105185886033)
      ·
        refine ⟨11157908239578828889414525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14877210986105105185886033 11157908239578828889414525)
        ·
          refine ⟨4184215589842060833530447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11157908239578828889414525 4184215589842060833530447)
          ·
            refine ⟨6276323384763091250295671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4184215589842060833530447 6276323384763091250295671)
            ·
              refine ⟨9414485077144636875443507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6276323384763091250295671 9414485077144636875443507)
              ·
                refine ⟨14121727615716955313165261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9414485077144636875443507 14121727615716955313165261)
                ·
                  refine ⟨5295647855893858242436973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14121727615716955313165261 5295647855893858242436973)
                  ·
                    refine ⟨1985867945960196840913865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5295647855893858242436973 1985867945960196840913865)
                    ·
                      refine ⟨1489400959470147630685399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1985867945960196840913865 1489400959470147630685399)
                      ·
                        rfl

theorem cell23_2900598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_2900598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900598 prefixEnd_2900598 := by exact prefixLift 2900598
  have htrace : WordTrace (prefixWord ++ tailWord_2900598) baseStart_2900598 baseEnd_2900598 := by
    simpa [prefixWord, tailWord_2900598, baseEnd_2900598] using wordTrace_append hprefix tailTrace_2900598
  have hstable : (prefixWord ++ tailWord_2900598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900598).length < 2 ^ (prefixWord ++ tailWord_2900598).sum := by decide
  have hdescent : baseEnd_2900598 < baseStart_2900598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900627 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 4, 3, 3]
def baseStart_2900627 : Nat := 118140960795 + 2900627 * 2 ^ 59
def prefixEnd_2900627 : Nat := 4983230072969 + 3 ^ 40 * 2900627 * 2
def baseEnd_2900627 : Nat := 1489415850409128017222765

theorem tailTrace_2900627 : CollatzResearch.WordTrace tailWord_2900627 prefixEnd_2900627 1489415850409128017222765 := by
  unfold tailWord_2900627
  simp only [CollatzResearch.WordTrace]
  refine ⟨105794558062531241496884135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70529705375020827664589423 105794558062531241496884135)
  ·
    refine ⟨158691837093796862245326203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105794558062531241496884135 158691837093796862245326203)
    ·
      refine ⟨238037755640695293367989305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158691837093796862245326203 238037755640695293367989305)
      ·
        refine ⟨178528316730521470025991979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238037755640695293367989305 178528316730521470025991979)
        ·
          refine ⟨267792475095782205038987969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178528316730521470025991979 267792475095782205038987969)
          ·
            refine ⟨200844356321836653779240977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267792475095782205038987969 200844356321836653779240977)
            ·
              refine ⟨150633267241377490334430733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200844356321836653779240977 150633267241377490334430733)
              ·
                refine ⟨56487475215516558875411525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150633267241377490334430733 56487475215516558875411525)
                ·
                  refine ⟨10591401602909354789139661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56487475215516558875411525 10591401602909354789139661)
                  ·
                    refine ⟨3971775601091008045927373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10591401602909354789139661 3971775601091008045927373)
                    ·
                      refine ⟨1489415850409128017222765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3971775601091008045927373 1489415850409128017222765)
                      ·
                        rfl

theorem cell23_2900627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3, 3].length) (baseStart_2900627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900627 prefixEnd_2900627 := by exact prefixLift 2900627
  have htrace : WordTrace (prefixWord ++ tailWord_2900627) baseStart_2900627 baseEnd_2900627 := by
    simpa [prefixWord, tailWord_2900627, baseEnd_2900627] using wordTrace_append hprefix tailTrace_2900627
  have hstable : (prefixWord ++ tailWord_2900627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900627).length < 2 ^ (prefixWord ++ tailWord_2900627).sum := by decide
  have hdescent : baseEnd_2900627 < baseStart_2900627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900644 : List Nat := [2, 3, 1, 2, 2, 1, 3, 1, 2, 3, 3]
def baseStart_2900644 : Nat := 118140960795 + 2900644 * 2 ^ 59
def prefixEnd_2900644 : Nat := 4983230072969 + 3 ^ 40 * 2900644 * 2
def baseEnd_2900644 : Nat := 1489424579580254450710187

theorem tailTrace_2900644 : CollatzResearch.WordTrace tailWord_2900644 prefixEnd_2900644 1489424579580254450710187 := by
  unfold tailWord_2900644
  simp only [CollatzResearch.WordTrace]
  refine ⟨52897589051734826700126493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70530118735646435600168657 52897589051734826700126493)
  ·
    refine ⟨19836595894400560012547435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52897589051734826700126493 19836595894400560012547435)
    ·
      refine ⟨29754893841600840018821153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19836595894400560012547435 29754893841600840018821153)
      ·
        refine ⟨22316170381200630014115865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29754893841600840018821153 22316170381200630014115865)
        ·
          refine ⟨16737127785900472510586899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22316170381200630014115865 16737127785900472510586899)
          ·
            refine ⟨25105691678850708765880349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16737127785900472510586899 25105691678850708765880349)
            ·
              refine ⟨9414634379569015787205131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25105691678850708765880349 9414634379569015787205131)
              ·
                refine ⟨14121951569353523680807697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9414634379569015787205131 14121951569353523680807697)
                ·
                  refine ⟨10591463677015142760605773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14121951569353523680807697 10591463677015142760605773)
                  ·
                    refine ⟨3971798878880678535227165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10591463677015142760605773 3971798878880678535227165)
                    ·
                      refine ⟨1489424579580254450710187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3971798878880678535227165 1489424579580254450710187)
                      ·
                        rfl

theorem cell23_2900644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_2900644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900644 prefixEnd_2900644 := by exact prefixLift 2900644
  have htrace : WordTrace (prefixWord ++ tailWord_2900644) baseStart_2900644 baseEnd_2900644 := by
    simpa [prefixWord, tailWord_2900644, baseEnd_2900644] using wordTrace_append hprefix tailTrace_2900644
  have hstable : (prefixWord ++ tailWord_2900644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900644).length < 2 ^ (prefixWord ++ tailWord_2900644).sum := by decide
  have hdescent : baseEnd_2900644 < baseStart_2900644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900697 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 2, 1, 6]
def baseStart_2900697 : Nat := 118140960795 + 2900697 * 2 ^ 59
def prefixEnd_2900697 : Nat := 4983230072969 + 3 ^ 40 * 2900697 * 2
def baseEnd_2900697 : Nat := 1489451794054942743347443

theorem tailTrace_2900697 : CollatzResearch.WordTrace tailWord_2900697 prefixEnd_2900697 1489451794054942743347443 := by
  unfold tailWord_2900697
  simp only [CollatzResearch.WordTrace]
  refine ⟨105797111172277643451932345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70531407448185095634621563 105797111172277643451932345)
  ·
    refine ⟨79347833379208232588949259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105797111172277643451932345 79347833379208232588949259)
    ·
      refine ⟨119021750068812348883423889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79347833379208232588949259 119021750068812348883423889)
      ·
        refine ⟨89266312551609261662567917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119021750068812348883423889 89266312551609261662567917)
        ·
          refine ⟨33474867206853473123462969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89266312551609261662567917 33474867206853473123462969)
          ·
            refine ⟨25106150405140104842597227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33474867206853473123462969 25106150405140104842597227)
            ·
              refine ⟨37659225607710157263895841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25106150405140104842597227 37659225607710157263895841)
              ·
                refine ⟨28244419205782617947921881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37659225607710157263895841 28244419205782617947921881)
                ·
                  refine ⟨21183314404336963460941411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28244419205782617947921881 21183314404336963460941411)
                  ·
                    refine ⟨31774971606505445191412117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21183314404336963460941411 31774971606505445191412117)
                    ·
                      refine ⟨1489451794054942743347443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31774971606505445191412117 1489451794054942743347443)
                      ·
                        rfl

theorem cell23_2900697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_2900697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900697 prefixEnd_2900697 := by exact prefixLift 2900697
  have htrace : WordTrace (prefixWord ++ tailWord_2900697) baseStart_2900697 baseEnd_2900697 := by
    simpa [prefixWord, tailWord_2900697, baseEnd_2900697] using wordTrace_append hprefix tailTrace_2900697
  have hstable : (prefixWord ++ tailWord_2900697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900697).length < 2 ^ (prefixWord ++ tailWord_2900697).sum := by decide
  have hdescent : baseEnd_2900697 < baseStart_2900697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900738 : List Nat := [3, 4, 1, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_2900738 : Nat := 118140960795 + 2900738 * 2 ^ 59
def prefixEnd_2900738 : Nat := 4983230072969 + 3 ^ 40 * 2900738 * 2
def baseEnd_2900738 : Nat := 1489472846761777082934755

theorem tailTrace_2900738 : CollatzResearch.WordTrace tailWord_2900738 prefixEnd_2900738 1489472846761777082934755 := by
  unfold tailWord_2900738
  simp only [CollatzResearch.WordTrace]
  refine ⟨26449651641282276863543717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70532404376752738302783245 26449651641282276863543717)
  ·
    refine ⟨4959309682740426911914447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26449651641282276863543717 4959309682740426911914447)
    ·
      refine ⟨7438964524110640367871671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4959309682740426911914447 7438964524110640367871671)
      ·
        refine ⟨11158446786165960551807507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7438964524110640367871671 11158446786165960551807507)
        ·
          refine ⟨16737670179248940827711261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11158446786165960551807507 16737670179248940827711261)
          ·
            refine ⟨6276626317218352810391723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16737670179248940827711261 6276626317218352810391723)
            ·
              refine ⟨9414939475827529215587585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6276626317218352810391723 9414939475827529215587585)
              ·
                refine ⟨7061204606870646911690689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9414939475827529215587585 7061204606870646911690689)
                ·
                  refine ⟨5295903455152985183768017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7061204606870646911690689 5295903455152985183768017)
                  ·
                    refine ⟨3971927591364738887826013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5295903455152985183768017 3971927591364738887826013)
                    ·
                      refine ⟨1489472846761777082934755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3971927591364738887826013 1489472846761777082934755)
                      ·
                        rfl

theorem cell23_2900738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_2900738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900738 prefixEnd_2900738 := by exact prefixLift 2900738
  have htrace : WordTrace (prefixWord ++ tailWord_2900738) baseStart_2900738 baseEnd_2900738 := by
    simpa [prefixWord, tailWord_2900738, baseEnd_2900738] using wordTrace_append hprefix tailTrace_2900738
  have hstable : (prefixWord ++ tailWord_2900738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900738).length < 2 ^ (prefixWord ++ tailWord_2900738).sum := by decide
  have hdescent : baseEnd_2900738 < baseStart_2900738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900747 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 7]
def baseStart_2900747 : Nat := 118140960795 + 2900747 * 2 ^ 59
def prefixEnd_2900747 : Nat := 4983230072969 + 3 ^ 40 * 2900747 * 2
def baseEnd_2900747 : Nat := 1489477468087667547722213

theorem tailTrace_2900747 : CollatzResearch.WordTrace tailWord_2900747 prefixEnd_2900747 1489477468087667547722213 := by
  unfold tailWord_2900747
  simp only [CollatzResearch.WordTrace]
  refine ⟨105798934822096501991252495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70532623214731001327501663 105798934822096501991252495)
  ·
    refine ⟨158698402233144752986878743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105798934822096501991252495 158698402233144752986878743)
    ·
      refine ⟨238047603349717129480318115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158698402233144752986878743 238047603349717129480318115)
      ·
        refine ⟨357071405024575694220477173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238047603349717129480318115 357071405024575694220477173)
        ·
          refine ⟨33475444221053971333169735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 357071405024575694220477173 33475444221053971333169735)
          ·
            refine ⟨50213166331580956999754603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33475444221053971333169735 50213166331580956999754603)
            ·
              refine ⟨75319749497371435499631905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50213166331580956999754603 75319749497371435499631905)
              ·
                refine ⟨56489812123028576624723929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75319749497371435499631905 56489812123028576624723929)
                ·
                  refine ⟨42367359092271432468542947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56489812123028576624723929 42367359092271432468542947)
                  ·
                    refine ⟨63551038638407148702814421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42367359092271432468542947 63551038638407148702814421)
                    ·
                      refine ⟨1489477468087667547722213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 63551038638407148702814421 1489477468087667547722213)
                      ·
                        rfl

theorem cell23_2900747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 7].length) (baseStart_2900747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900747 prefixEnd_2900747 := by exact prefixLift 2900747
  have htrace : WordTrace (prefixWord ++ tailWord_2900747) baseStart_2900747 baseEnd_2900747 := by
    simpa [prefixWord, tailWord_2900747, baseEnd_2900747] using wordTrace_append hprefix tailTrace_2900747
  have hstable : (prefixWord ++ tailWord_2900747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900747).length < 2 ^ (prefixWord ++ tailWord_2900747).sum := by decide
  have hdescent : baseEnd_2900747 < baseStart_2900747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900784 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 6, 4]
def baseStart_2900784 : Nat := 118140960795 + 2900784 * 2 ^ 59
def prefixEnd_2900784 : Nat := 4983230072969 + 3 ^ 40 * 2900784 * 2
def baseEnd_2900784 : Nat := 496498822290627967653181

theorem tailTrace_2900784 : CollatzResearch.WordTrace tailWord_2900784 prefixEnd_2900784 496498822290627967653181 := by
  unfold tailWord_2900784
  simp only [CollatzResearch.WordTrace]
  refine ⟨52900142161481228655174703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70533522881974971540232937 52900142161481228655174703)
  ·
    refine ⟨79350213242221842982762055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52900142161481228655174703 79350213242221842982762055)
    ·
      refine ⟨119025319863332764474143083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79350213242221842982762055 119025319863332764474143083)
      ·
        refine ⟨178537979794999146711214625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119025319863332764474143083 178537979794999146711214625)
        ·
          refine ⟨133903484846249360033410969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178537979794999146711214625 133903484846249360033410969)
          ·
            refine ⟨100427613634687020025058227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133903484846249360033410969 100427613634687020025058227)
            ·
              refine ⟨150641420452030530037587341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100427613634687020025058227 150641420452030530037587341)
              ·
                refine ⟨56490532669511448764095253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150641420452030530037587341 56490532669511448764095253)
                ·
                  refine ⟨2647993718883349160816965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56490532669511448764095253 2647993718883349160816965)
                  ·
                    refine ⟨496498822290627967653181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2647993718883349160816965 496498822290627967653181)
                    ·
                      rfl

theorem cell23_2900784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 6, 4].length) (baseStart_2900784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900784 prefixEnd_2900784 := by exact prefixLift 2900784
  have htrace : WordTrace (prefixWord ++ tailWord_2900784) baseStart_2900784 baseEnd_2900784 := by
    simpa [prefixWord, tailWord_2900784, baseEnd_2900784] using wordTrace_append hprefix tailTrace_2900784
  have hstable : (prefixWord ++ tailWord_2900784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900784).length < 2 ^ (prefixWord ++ tailWord_2900784).sum := by decide
  have hdescent : baseEnd_2900784 < baseStart_2900784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900808 : List Nat := [2, 1, 3, 1, 1, 3, 2, 3, 3, 2, 2]
def baseStart_2900808 : Nat := 118140960795 + 2900808 * 2 ^ 59
def prefixEnd_2900808 : Nat := 4983230072969 + 3 ^ 40 * 2900808 * 2
def baseEnd_2900808 : Nat := 1489508790407591809059433

theorem tailTrace_2900808 : CollatzResearch.WordTrace tailWord_2900808 prefixEnd_2900808 1489508790407591809059433 := by
  unfold tailWord_2900808
  simp only [CollatzResearch.WordTrace]
  refine ⟨52900579837437754704611539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70534106449917006272815385 52900579837437754704611539)
  ·
    refine ⟨79350869756156632056917309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52900579837437754704611539 79350869756156632056917309)
    ·
      refine ⟨29756576158558737021343991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79350869756156632056917309 29756576158558737021343991)
      ·
        refine ⟨44634864237838105532015987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29756576158558737021343991 44634864237838105532015987)
        ·
          refine ⟨66952296356757158298023981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44634864237838105532015987 66952296356757158298023981)
          ·
            refine ⟨25107111133783934361758993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66952296356757158298023981 25107111133783934361758993)
            ·
              refine ⟨18830333350337950771319245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25107111133783934361758993 18830333350337950771319245)
              ·
                refine ⟨7061375006376731539244717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18830333350337950771319245 7061375006376731539244717)
                ·
                  refine ⟨2648015627391274327216769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7061375006376731539244717 2648015627391274327216769)
                  ·
                    refine ⟨1986011720543455745412577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2648015627391274327216769 1986011720543455745412577)
                    ·
                      refine ⟨1489508790407591809059433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1986011720543455745412577 1489508790407591809059433)
                      ·
                        rfl

theorem cell23_2900808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 3, 2, 2].length) (baseStart_2900808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900808 prefixEnd_2900808 := by exact prefixLift 2900808
  have htrace : WordTrace (prefixWord ++ tailWord_2900808) baseStart_2900808 baseEnd_2900808 := by
    simpa [prefixWord, tailWord_2900808, baseEnd_2900808] using wordTrace_append hprefix tailTrace_2900808
  have hstable : (prefixWord ++ tailWord_2900808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900808).length < 2 ^ (prefixWord ++ tailWord_2900808).sum := by decide
  have hdescent : baseEnd_2900808 < baseStart_2900808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900821 : List Nat := [1, 3, 2, 2, 2, 1, 4, 1, 1, 2, 4]
def baseStart_2900821 : Nat := 118140960795 + 2900821 * 2 ^ 59
def prefixEnd_2900821 : Nat := 4983230072969 + 3 ^ 40 * 2900821 * 2
def baseEnd_2900821 : Nat := 1489515465656100258196873

theorem tailTrace_2900821 : CollatzResearch.WordTrace tailWord_2900821 prefixEnd_2900821 1489515465656100258196873 := by
  unfold tailWord_2900821
  simp only [CollatzResearch.WordTrace]
  refine ⟨105801633823828412629446317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70534422549218941752964211 105801633823828412629446317)
  ·
    refine ⟨39675612683935654736042369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105801633823828412629446317 39675612683935654736042369)
    ·
      refine ⟨29756709512951741052031777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39675612683935654736042369 29756709512951741052031777)
      ·
        refine ⟨22317532134713805789023833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29756709512951741052031777 22317532134713805789023833)
        ·
          refine ⟨16738149101035354341767875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22317532134713805789023833 16738149101035354341767875)
          ·
            refine ⟨25107223651553031512651813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16738149101035354341767875 25107223651553031512651813)
            ·
              refine ⟨4707604434666193408622215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25107223651553031512651813 4707604434666193408622215)
              ·
                refine ⟨7061406651999290112933323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4707604434666193408622215 7061406651999290112933323)
                ·
                  refine ⟨10592109977998935169399985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7061406651999290112933323 10592109977998935169399985)
                  ·
                    refine ⟨7944082483499201377049989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10592109977998935169399985 7944082483499201377049989)
                    ·
                      refine ⟨1489515465656100258196873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7944082483499201377049989 1489515465656100258196873)
                      ·
                        rfl

theorem cell23_2900821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_2900821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900821 prefixEnd_2900821 := by exact prefixLift 2900821
  have htrace : WordTrace (prefixWord ++ tailWord_2900821) baseStart_2900821 baseEnd_2900821 := by
    simpa [prefixWord, tailWord_2900821, baseEnd_2900821] using wordTrace_append hprefix tailTrace_2900821
  have hstable : (prefixWord ++ tailWord_2900821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900821).length < 2 ^ (prefixWord ++ tailWord_2900821).sum := by decide
  have hdescent : baseEnd_2900821 < baseStart_2900821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900828 : List Nat := [2, 2, 4, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_2900828 : Nat := 118140960795 + 2900828 * 2 ^ 59
def prefixEnd_2900828 : Nat := 4983230072969 + 3 ^ 40 * 2900828 * 2
def baseEnd_2900828 : Nat := 1489519060020681730809341

theorem tailTrace_2900828 : CollatzResearch.WordTrace tailWord_2900828 prefixEnd_2900828 1489519060020681730809341 := by
  unfold tailWord_2900828
  simp only [CollatzResearch.WordTrace]
  refine ⟨52900944567401526412475569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70534592756535368549967425 52900944567401526412475569)
  ·
    refine ⟨39675708425551144809356677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52900944567401526412475569 39675708425551144809356677)
    ·
      refine ⟨7439195329790839651754377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39675708425551144809356677 7439195329790839651754377)
      ·
        refine ⟨5579396497343129738815783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7439195329790839651754377 5579396497343129738815783)
        ·
          refine ⟨8369094746014694608223675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5579396497343129738815783 8369094746014694608223675)
          ·
            refine ⟨12553642119022041912335513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8369094746014694608223675 12553642119022041912335513)
            ·
              refine ⟨9415231589266531434251635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12553642119022041912335513 9415231589266531434251635)
              ·
                refine ⟨14122847383899797151377453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9415231589266531434251635 14122847383899797151377453)
                ·
                  refine ⟨5296067768962423931766545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14122847383899797151377453 5296067768962423931766545)
                  ·
                    refine ⟨3972050826721817948824909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5296067768962423931766545 3972050826721817948824909)
                    ·
                      refine ⟨1489519060020681730809341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3972050826721817948824909 1489519060020681730809341)
                      ·
                        rfl

theorem cell23_2900828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_2900828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900828 prefixEnd_2900828 := by exact prefixLift 2900828
  have htrace : WordTrace (prefixWord ++ tailWord_2900828) baseStart_2900828 baseEnd_2900828 := by
    simpa [prefixWord, tailWord_2900828, baseEnd_2900828] using wordTrace_append hprefix tailTrace_2900828
  have hstable : (prefixWord ++ tailWord_2900828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900828).length < 2 ^ (prefixWord ++ tailWord_2900828).sum := by decide
  have hdescent : baseEnd_2900828 < baseStart_2900828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900864 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 4]
def baseStart_2900864 : Nat := 118140960795 + 2900864 * 2 ^ 59
def prefixEnd_2900864 : Nat := 4983230072969 + 3 ^ 40 * 2900864 * 2
def baseEnd_2900864 : Nat := 1489537545324243589959175

theorem tailTrace_2900864 : CollatzResearch.WordTrace tailWord_2900864 prefixEnd_2900864 1489537545324243589959175 := by
  unfold tailWord_2900864
  simp only [CollatzResearch.WordTrace]
  refine ⟨52901601081336315486630823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70535468108448420648841097 52901601081336315486630823)
  ·
    refine ⟨79352401622004473229946235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52901601081336315486630823 79352401622004473229946235)
    ·
      refine ⟨119028602433006709844919353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79352401622004473229946235 119028602433006709844919353)
      ·
        refine ⟨89271451824755032383689515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119028602433006709844919353 89271451824755032383689515)
        ·
          refine ⟨133907177737132548575534273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89271451824755032383689515 133907177737132548575534273)
          ·
            refine ⟨100430383302849411431650705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133907177737132548575534273 100430383302849411431650705)
            ·
              refine ⟨75322787477137058573738029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100430383302849411431650705 75322787477137058573738029)
              ·
                refine ⟨28246045303926396965151761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75322787477137058573738029 28246045303926396965151761)
                ·
                  refine ⟨21184533977944797723863821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28246045303926396965151761 21184533977944797723863821)
                  ·
                    refine ⟨7944200241729299146448933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21184533977944797723863821 7944200241729299146448933)
                    ·
                      refine ⟨1489537545324243589959175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7944200241729299146448933 1489537545324243589959175)
                      ·
                        rfl

theorem cell23_2900864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_2900864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900864 prefixEnd_2900864 := by exact prefixLift 2900864
  have htrace : WordTrace (prefixWord ++ tailWord_2900864) baseStart_2900864 baseEnd_2900864 := by
    simpa [prefixWord, tailWord_2900864, baseEnd_2900864] using wordTrace_append hprefix tailTrace_2900864
  have hstable : (prefixWord ++ tailWord_2900864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900864).length < 2 ^ (prefixWord ++ tailWord_2900864).sum := by decide
  have hdescent : baseEnd_2900864 < baseStart_2900864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900885 : List Nat := [1, 3, 2, 1, 1, 5, 2, 2, 1, 3, 2]
def baseStart_2900885 : Nat := 118140960795 + 2900885 * 2 ^ 59
def prefixEnd_2900885 : Nat := 4983230072969 + 3 ^ 40 * 2900885 * 2
def baseEnd_2900885 : Nat := 1489548328417988007796579

theorem tailTrace_2900885 : CollatzResearch.WordTrace tailWord_2900885 prefixEnd_2900885 1489548328417988007796579 := by
  unfold tailWord_2900885
  simp only [CollatzResearch.WordTrace]
  refine ⟨105803968095596551559776109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70535978730397701039850739 105803968095596551559776109)
  ·
    refine ⟨39676488035848706834916041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105803968095596551559776109 39676488035848706834916041)
    ·
      refine ⟨29757366026886530126187031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39676488035848706834916041 29757366026886530126187031)
      ·
        refine ⟨44636049040329795189280547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29757366026886530126187031 44636049040329795189280547)
        ·
          refine ⟨66954073560494692783920821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44636049040329795189280547 66954073560494692783920821)
          ·
            refine ⟨6276944396296377448492577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66954073560494692783920821 6276944396296377448492577)
            ·
              refine ⟨4707708297222283086369433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6276944396296377448492577 4707708297222283086369433)
              ·
                refine ⟨3530781222916712314777075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4707708297222283086369433 3530781222916712314777075)
                ·
                  refine ⟨5296171834375068472165613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3530781222916712314777075 5296171834375068472165613)
                  ·
                    refine ⟨1986064437890650677062105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5296171834375068472165613 1986064437890650677062105)
                    ·
                      refine ⟨1489548328417988007796579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1986064437890650677062105 1489548328417988007796579)
                      ·
                        rfl

theorem cell23_2900885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 3, 2].length) (baseStart_2900885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900885 prefixEnd_2900885 := by exact prefixLift 2900885
  have htrace : WordTrace (prefixWord ++ tailWord_2900885) baseStart_2900885 baseEnd_2900885 := by
    simpa [prefixWord, tailWord_2900885, baseEnd_2900885] using wordTrace_append hprefix tailTrace_2900885
  have hstable : (prefixWord ++ tailWord_2900885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900885).length < 2 ^ (prefixWord ++ tailWord_2900885).sum := by decide
  have hdescent : baseEnd_2900885 < baseStart_2900885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900921 : List Nat := [1, 2, 1, 4, 2, 2, 3, 1, 7]
def baseStart_2900921 : Nat := 118140960795 + 2900921 * 2 ^ 59
def prefixEnd_2900921 : Nat := 4983230072969 + 3 ^ 40 * 2900921 * 2
def baseEnd_2900921 : Nat := 165507423746838874105157

theorem tailTrace_2900921 : CollatzResearch.WordTrace tailWord_2900921 prefixEnd_2900921 165507423746838874105157 := by
  unfold tailWord_2900921
  simp only [CollatzResearch.WordTrace]
  refine ⟨105805281123466129708086617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70536854082310753138724411 105805281123466129708086617)
  ·
    refine ⟨79353960842599597281064963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105805281123466129708086617 79353960842599597281064963)
    ·
      refine ⟨119030941263899395921597445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79353960842599597281064963 119030941263899395921597445)
      ·
        refine ⟨22318301486981136735299521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119030941263899395921597445 22318301486981136735299521)
        ·
          refine ⟨16738726115235852551474641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22318301486981136735299521 16738726115235852551474641)
          ·
            refine ⟨12554044586426889413605981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16738726115235852551474641 12554044586426889413605981)
            ·
              refine ⟨4707766719910083530102243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12554044586426889413605981 4707766719910083530102243)
              ·
                refine ⟨7061650079865125295153365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4707766719910083530102243 7061650079865125295153365)
                ·
                  refine ⟨165507423746838874105157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7061650079865125295153365 165507423746838874105157)
                  ·
                    rfl

theorem cell23_2900921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 7].length) (baseStart_2900921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900921 prefixEnd_2900921 := by exact prefixLift 2900921
  have htrace : WordTrace (prefixWord ++ tailWord_2900921) baseStart_2900921 baseEnd_2900921 := by
    simpa [prefixWord, tailWord_2900921, baseEnd_2900921] using wordTrace_append hprefix tailTrace_2900921
  have hstable : (prefixWord ++ tailWord_2900921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900921).length < 2 ^ (prefixWord ++ tailWord_2900921).sum := by decide
  have hdescent : baseEnd_2900921 < baseStart_2900921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900944 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 7]
def baseStart_2900944 : Nat := 118140960795 + 2900944 * 2 ^ 59
def prefixEnd_2900944 : Nat := 4983230072969 + 3 ^ 40 * 2900944 * 2
def baseEnd_2900944 : Nat := 1489578623776603276958807

theorem tailTrace_2900944 : CollatzResearch.WordTrace tailWord_2900944 prefixEnd_2900944 1489578623776603276958807 := by
  unfold tailWord_2900944
  simp only [CollatzResearch.WordTrace]
  refine ⟨52903060001191402318086943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70537413334921869757449257 52903060001191402318086943)
  ·
    refine ⟨79354590001787103477130415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52903060001191402318086943 79354590001787103477130415)
    ·
      refine ⟨119031885002680655215695623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79354590001787103477130415 119031885002680655215695623)
      ·
        refine ⟨178547827504020982823543435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119031885002680655215695623 178547827504020982823543435)
        ·
          refine ⟨267821741256031474235315153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178547827504020982823543435 267821741256031474235315153)
          ·
            refine ⟨200866305942023605676486365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267821741256031474235315153 200866305942023605676486365)
            ·
              refine ⟨75324864728258852128682387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200866305942023605676486365 75324864728258852128682387)
              ·
                refine ⟨112987297092388278193023581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75324864728258852128682387 112987297092388278193023581)
                ·
                  refine ⟨42370236409645604322383843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112987297092388278193023581 42370236409645604322383843)
                  ·
                    refine ⟨63555354614468406483575765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42370236409645604322383843 63555354614468406483575765)
                    ·
                      refine ⟨1489578623776603276958807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 63555354614468406483575765 1489578623776603276958807)
                      ·
                        rfl

theorem cell23_2900944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 7].length) (baseStart_2900944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900944 prefixEnd_2900944 := by exact prefixLift 2900944
  have htrace : WordTrace (prefixWord ++ tailWord_2900944) baseStart_2900944 baseEnd_2900944 := by
    simpa [prefixWord, tailWord_2900944, baseEnd_2900944] using wordTrace_append hprefix tailTrace_2900944
  have hstable : (prefixWord ++ tailWord_2900944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900944).length < 2 ^ (prefixWord ++ tailWord_2900944).sum := by decide
  have hdescent : baseEnd_2900944 < baseStart_2900944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2900988 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 1, 6, 2]
def baseStart_2900988 : Nat := 118140960795 + 2900988 * 2 ^ 59
def prefixEnd_2900988 : Nat := 4983230072969 + 3 ^ 40 * 2900988 * 2
def baseEnd_2900988 : Nat := 1489601216925401104808605

theorem tailTrace_2900988 : CollatzResearch.WordTrace tailWord_2900988 prefixEnd_2900988 1489601216925401104808605 := by
  unfold tailWord_2900988
  simp only [CollatzResearch.WordTrace]
  refine ⟨52903862407111700075387809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70538483209482266767183745 52903862407111700075387809)
  ·
    refine ⟨39677896805333775056540857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52903862407111700075387809 39677896805333775056540857)
    ·
      refine ⟨29758422604000331292405643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39677896805333775056540857 29758422604000331292405643)
      ·
        refine ⟨44637633906000496938608465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29758422604000331292405643 44637633906000496938608465)
        ·
          refine ⟨33478225429500372703956349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44637633906000496938608465 33478225429500372703956349)
          ·
            refine ⟨12554334536062639763983631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33478225429500372703956349 12554334536062639763983631)
            ·
              refine ⟨18831501804093959645975447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12554334536062639763983631 18831501804093959645975447)
              ·
                refine ⟨28247252706140939468963171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18831501804093959645975447 28247252706140939468963171)
                ·
                  refine ⟨42370879059211409203444757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28247252706140939468963171 42370879059211409203444757)
                  ·
                    refine ⟨1986134955900534806411473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42370879059211409203444757 1986134955900534806411473)
                    ·
                      refine ⟨1489601216925401104808605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1986134955900534806411473 1489601216925401104808605)
                      ·
                        rfl

theorem cell23_2900988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 1, 6, 2].length) (baseStart_2900988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2900988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2900988 prefixEnd_2900988 := by exact prefixLift 2900988
  have htrace : WordTrace (prefixWord ++ tailWord_2900988) baseStart_2900988 baseEnd_2900988 := by
    simpa [prefixWord, tailWord_2900988, baseEnd_2900988] using wordTrace_append hprefix tailTrace_2900988
  have hstable : (prefixWord ++ tailWord_2900988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2900988).length < 2 ^ (prefixWord ++ tailWord_2900988).sum := by decide
  have hdescent : baseEnd_2900988 < baseStart_2900988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2900988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901028 : List Nat := [2, 3, 1, 4, 1, 2, 1, 1, 8]
def baseStart_2901028 : Nat := 118140960795 + 2901028 * 2 ^ 59
def prefixEnd_2901028 : Nat := 4983230072969 + 3 ^ 40 * 2901028 * 2
def baseEnd_2901028 : Nat := 165513528461286772034269

theorem tailTrace_2901028 : CollatzResearch.WordTrace tailWord_2901028 prefixEnd_2901028 165513528461286772034269 := by
  unfold tailWord_2901028
  simp only [CollatzResearch.WordTrace]
  refine ⟨52904591867039243491115869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70539455822718991321487825 52904591867039243491115869)
  ·
    refine ⟨19839221950139716309168451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52904591867039243491115869 19839221950139716309168451)
    ·
      refine ⟨29758832925209574463752677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19839221950139716309168451 29758832925209574463752677)
      ·
        refine ⟨5579781173476795211953627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29758832925209574463752677 5579781173476795211953627)
        ·
          refine ⟨8369671760215192817930441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5579781173476795211953627 8369671760215192817930441)
          ·
            refine ⟨6277253820161394613447831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8369671760215192817930441 6277253820161394613447831)
            ·
              refine ⟨9415880730242091920171747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6277253820161394613447831 9415880730242091920171747)
              ·
                refine ⟨14123821095363137880257621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9415880730242091920171747 14123821095363137880257621)
                ·
                  refine ⟨165513528461286772034269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14123821095363137880257621 165513528461286772034269)
                  ·
                    rfl

theorem cell23_2901028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 8].length) (baseStart_2901028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901028 prefixEnd_2901028 := by exact prefixLift 2901028
  have htrace : WordTrace (prefixWord ++ tailWord_2901028) baseStart_2901028 baseEnd_2901028 := by
    simpa [prefixWord, tailWord_2901028, baseEnd_2901028] using wordTrace_append hprefix tailTrace_2901028
  have hstable : (prefixWord ++ tailWord_2901028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901028).length < 2 ^ (prefixWord ++ tailWord_2901028).sum := by decide
  have hdescent : baseEnd_2901028 < baseStart_2901028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901088 : List Nat := [2, 1, 1, 3, 2, 2, 1, 3, 4, 4]
def baseStart_2901088 : Nat := 118140960795 + 2901088 * 2 ^ 59
def prefixEnd_2901088 : Nat := 4983230072969 + 3 ^ 40 * 2901088 * 2
def baseEnd_2901088 : Nat := 496550854996950237852715

theorem tailTrace_2901088 : CollatzResearch.WordTrace tailWord_2901088 prefixEnd_2901088 496550854996950237852715 := by
  unfold tailWord_2901088
  simp only [CollatzResearch.WordTrace]
  refine ⟨52905686056930558614707959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70540914742574078152943945 52905686056930558614707959)
  ·
    refine ⟨79358529085395837922061939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52905686056930558614707959 79358529085395837922061939)
    ·
      refine ⟨119037793628093756883092909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79358529085395837922061939 119037793628093756883092909)
      ·
        refine ⟨44639172610535158831159841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119037793628093756883092909 44639172610535158831159841)
        ·
          refine ⟨33479379457901369123369881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44639172610535158831159841 33479379457901369123369881)
          ·
            refine ⟨25109534593426026842527411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33479379457901369123369881 25109534593426026842527411)
            ·
              refine ⟨37664301890139040263791117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25109534593426026842527411 37664301890139040263791117)
              ·
                refine ⟨14124113208802140098921669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37664301890139040263791117 14124113208802140098921669)
                ·
                  refine ⟨2648271226650401268547813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14124113208802140098921669 2648271226650401268547813)
                  ·
                    refine ⟨496550854996950237852715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2648271226650401268547813 496550854996950237852715)
                    ·
                      rfl

theorem cell23_2901088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 4, 4].length) (baseStart_2901088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901088 prefixEnd_2901088 := by exact prefixLift 2901088
  have htrace : WordTrace (prefixWord ++ tailWord_2901088) baseStart_2901088 baseEnd_2901088 := by
    simpa [prefixWord, tailWord_2901088, baseEnd_2901088] using wordTrace_append hprefix tailTrace_2901088
  have hstable : (prefixWord ++ tailWord_2901088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901088).length < 2 ^ (prefixWord ++ tailWord_2901088).sum := by decide
  have hdescent : baseEnd_2901088 < baseStart_2901088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901109 : List Nat := [1, 3, 4, 3, 1, 2, 1, 2, 1, 5]
def baseStart_2901109 : Nat := 118140960795 + 2901109 * 2 ^ 59
def prefixEnd_2901109 : Nat := 4983230072969 + 3 ^ 40 * 2901109 * 2
def baseEnd_2901109 : Nat := 496554449361531710465183

theorem tailTrace_2901109 : CollatzResearch.WordTrace tailWord_2901109 prefixEnd_2901109 496554449361531710465183 := by
  unfold tailWord_2901109
  simp only [CollatzResearch.WordTrace]
  refine ⟨105812138046785037815930381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70541425364523358543953587 105812138046785037815930381)
  ·
    refine ⟨39679551767544389180973893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105812138046785037815930381 39679551767544389180973893)
    ·
      refine ⟨7439915956414572971432605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39679551767544389180973893 7439915956414572971432605)
      ·
        refine ⟨2789968483655464864287227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7439915956414572971432605 2789968483655464864287227)
        ·
          refine ⟨4184952725483197296430841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2789968483655464864287227 4184952725483197296430841)
          ·
            refine ⟨3138714544112397972323131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4184952725483197296430841 3138714544112397972323131)
            ·
              refine ⟨4708071816168596958484697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3138714544112397972323131 4708071816168596958484697)
              ·
                refine ⟨3531053862126447718863523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4708071816168596958484697 3531053862126447718863523)
                ·
                  refine ⟨5296580793189671578295285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3531053862126447718863523 5296580793189671578295285)
                  ·
                    refine ⟨496554449361531710465183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5296580793189671578295285 496554449361531710465183)
                    ·
                      rfl

theorem cell23_2901109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_2901109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901109 prefixEnd_2901109 := by exact prefixLift 2901109
  have htrace : WordTrace (prefixWord ++ tailWord_2901109) baseStart_2901109 baseEnd_2901109 := by
    simpa [prefixWord, tailWord_2901109, baseEnd_2901109] using wordTrace_append hprefix tailTrace_2901109
  have hstable : (prefixWord ++ tailWord_2901109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901109).length < 2 ^ (prefixWord ++ tailWord_2901109).sum := by decide
  have hdescent : baseEnd_2901109 < baseStart_2901109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901125 : List Nat := [1, 3, 1, 1, 6, 1, 1, 2, 1, 2, 4]
def baseStart_2901125 : Nat := 118140960795 + 2901125 * 2 ^ 59
def prefixEnd_2901125 : Nat := 4983230072969 + 3 ^ 40 * 2901125 * 2
def baseEnd_2901125 : Nat := 1489671563775067068795475

theorem tailTrace_2901125 : CollatzResearch.WordTrace tailWord_2901125 prefixEnd_2901125 1489671563775067068795475 := by
  unfold tailWord_2901125
  simp only [CollatzResearch.WordTrace]
  refine ⟨105812721614727072548512829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70541814409818048365675219 105812721614727072548512829)
  ·
    refine ⟨39679770605522652205692311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105812721614727072548512829 39679770605522652205692311)
    ·
      refine ⟨59519655908283978308538467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39679770605522652205692311 59519655908283978308538467)
      ·
        refine ⟨89279483862425967462807701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59519655908283978308538467 89279483862425967462807701)
        ·
          refine ⟨4184975806051217224819111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 89279483862425967462807701 4184975806051217224819111)
          ·
            refine ⟨6277463709076825837228667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4184975806051217224819111 6277463709076825837228667)
            ·
              refine ⟨9416195563615238755843001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6277463709076825837228667 9416195563615238755843001)
              ·
                refine ⟨7062146672711429066882251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9416195563615238755843001 7062146672711429066882251)
                ·
                  refine ⟨10593220009067143600323377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7062146672711429066882251 10593220009067143600323377)
                  ·
                    refine ⟨7944915006800357700242533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10593220009067143600323377 7944915006800357700242533)
                    ·
                      refine ⟨1489671563775067068795475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7944915006800357700242533 1489671563775067068795475)
                      ·
                        rfl

theorem cell23_2901125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 2, 4].length) (baseStart_2901125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901125 prefixEnd_2901125 := by exact prefixLift 2901125
  have htrace : WordTrace (prefixWord ++ tailWord_2901125) baseStart_2901125 baseEnd_2901125 := by
    simpa [prefixWord, tailWord_2901125, baseEnd_2901125] using wordTrace_append hprefix tailTrace_2901125
  have hstable : (prefixWord ++ tailWord_2901125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901125).length < 2 ^ (prefixWord ++ tailWord_2901125).sum := by decide
  have hdescent : baseEnd_2901125 < baseStart_2901125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901131 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 4, 7]
def baseStart_2901131 : Nat := 118140960795 + 2901131 * 2 ^ 59
def prefixEnd_2901131 : Nat := 4983230072969 + 3 ^ 40 * 2901131 * 2
def baseEnd_2901131 : Nat := 496558214886331348440149

theorem tailTrace_2901131 : CollatzResearch.WordTrace tailWord_2901131 prefixEnd_2901131 496558214886331348440149 := by
  unfold tailWord_2901131
  simp only [CollatzResearch.WordTrace]
  refine ⟨105812940452705335573231247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70541960301803557048820831 105812940452705335573231247)
  ·
    refine ⟨158719410679058003359846871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105812940452705335573231247 158719410679058003359846871)
    ·
      refine ⟨238079116018587005039770307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158719410679058003359846871 238079116018587005039770307)
      ·
        refine ⟨357118674027880507559655461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238079116018587005039770307 357118674027880507559655461)
        ·
          refine ⟨66959751380227595167435399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 357118674027880507559655461 66959751380227595167435399)
          ·
            refine ⟨100439627070341392751153099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66959751380227595167435399 100439627070341392751153099)
            ·
              refine ⟨150659440605512089126729649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100439627070341392751153099 150659440605512089126729649)
              ·
                refine ⟨112994580454134066845047237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150659440605512089126729649 112994580454134066845047237)
                ·
                  refine ⟨21186483835150137533446357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112994580454134066845047237 21186483835150137533446357)
                  ·
                    refine ⟨496558214886331348440149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21186483835150137533446357 496558214886331348440149)
                    ·
                      rfl

theorem cell23_2901131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 7].length) (baseStart_2901131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901131 prefixEnd_2901131 := by exact prefixLift 2901131
  have htrace : WordTrace (prefixWord ++ tailWord_2901131) baseStart_2901131 baseEnd_2901131 := by
    simpa [prefixWord, tailWord_2901131, baseEnd_2901131] using wordTrace_append hprefix tailTrace_2901131
  have hstable : (prefixWord ++ tailWord_2901131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901131).length < 2 ^ (prefixWord ++ tailWord_2901131).sum := by decide
  have hdescent : baseEnd_2901131 < baseStart_2901131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901146 : List Nat := [3, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2]
def baseStart_2901146 : Nat := 118140960795 + 2901146 * 2 ^ 59
def prefixEnd_2901146 : Nat := 4983230072969 + 3 ^ 40 * 2901146 * 2
def baseEnd_2901146 : Nat := 1489682346868811486632879

theorem tailTrace_2901146 : CollatzResearch.WordTrace tailWord_2901146 prefixEnd_2901146 1489682346868811486632879 := by
  unfold tailWord_2901146
  simp only [CollatzResearch.WordTrace]
  refine ⟨26453371886912748283756823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70542325031767328756684861 26453371886912748283756823)
  ·
    refine ⟨39680057830369122425635235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26453371886912748283756823 39680057830369122425635235)
    ·
      refine ⟨59520086745553683638452853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39680057830369122425635235 59520086745553683638452853)
      ·
        refine ⟨5580008132395657841104955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59520086745553683638452853 5580008132395657841104955)
        ·
          refine ⟨8370012198593486761657433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5580008132395657841104955 8370012198593486761657433)
          ·
            refine ⟨6277509148945115071243075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8370012198593486761657433 6277509148945115071243075)
            ·
              refine ⟨9416263723417672606864613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6277509148945115071243075 9416263723417672606864613)
              ·
                refine ⟨1765549448140813613787115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9416263723417672606864613 1765549448140813613787115)
                ·
                  refine ⟨2648324172211220420680673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1765549448140813613787115 2648324172211220420680673)
                  ·
                    refine ⟨1986243129158415315510505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2648324172211220420680673 1986243129158415315510505)
                    ·
                      refine ⟨1489682346868811486632879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1986243129158415315510505 1489682346868811486632879)
                      ·
                        rfl

theorem cell23_2901146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_2901146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901146 prefixEnd_2901146 := by exact prefixLift 2901146
  have htrace : WordTrace (prefixWord ++ tailWord_2901146) baseStart_2901146 baseEnd_2901146 := by
    simpa [prefixWord, tailWord_2901146, baseEnd_2901146] using wordTrace_append hprefix tailTrace_2901146
  have hstable : (prefixWord ++ tailWord_2901146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901146).length < 2 ^ (prefixWord ++ tailWord_2901146).sum := by decide
  have hdescent : baseEnd_2901146 < baseStart_2901146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901148 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 2, 7]
def baseStart_2901148 : Nat := 118140960795 + 2901148 * 2 ^ 59
def prefixEnd_2901148 : Nat := 4983230072969 + 3 ^ 40 * 2901148 * 2
def baseEnd_2901148 : Nat := 496561124610040159602623

theorem tailTrace_2901148 : CollatzResearch.WordTrace tailWord_2901148 prefixEnd_2901148 496561124610040159602623 := by
  unfold tailWord_2901148
  simp only [CollatzResearch.WordTrace]
  refine ⟨52906780246821873738300049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70542373662429164984400065 52906780246821873738300049)
  ·
    refine ⟨39680085185116405303725037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52906780246821873738300049 39680085185116405303725037)
    ·
      refine ⟨14880031944418651988896889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39680085185116405303725037 14880031944418651988896889)
      ·
        refine ⟨11160023958313988991672667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14880031944418651988896889 11160023958313988991672667)
        ·
          refine ⟨16740035937470983487509001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11160023958313988991672667 16740035937470983487509001)
          ·
            refine ⟨12555026953103237615631751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16740035937470983487509001 12555026953103237615631751)
            ·
              refine ⟨18832540429654856423447627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12555026953103237615631751 18832540429654856423447627)
              ·
                refine ⟨28248810644482284635171441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18832540429654856423447627 28248810644482284635171441)
                ·
                  refine ⟨21186607983361713476378581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28248810644482284635171441 21186607983361713476378581)
                  ·
                    refine ⟨496561124610040159602623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21186607983361713476378581 496561124610040159602623)
                    ·
                      rfl

theorem cell23_2901148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_2901148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901148 prefixEnd_2901148 := by exact prefixLift 2901148
  have htrace : WordTrace (prefixWord ++ tailWord_2901148) baseStart_2901148 baseEnd_2901148 := by
    simpa [prefixWord, tailWord_2901148, baseEnd_2901148] using wordTrace_append hprefix tailTrace_2901148
  have hstable : (prefixWord ++ tailWord_2901148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901148).length < 2 ^ (prefixWord ++ tailWord_2901148).sum := by decide
  have hdescent : baseEnd_2901148 < baseStart_2901148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901162 : List Nat := [3, 1, 5, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_2901162 : Nat := 118140960795 + 2901162 * 2 ^ 59
def prefixEnd_2901162 : Nat := 4983230072969 + 3 ^ 40 * 2901162 * 2
def baseEnd_2901162 : Nat := 1489690562559283424032805

theorem tailTrace_2901162 : CollatzResearch.WordTrace tailWord_2901162 prefixEnd_2901162 1489690562559283424032805 := by
  unfold tailWord_2901162
  simp only [CollatzResearch.WordTrace]
  refine ⟨26453517778898256966902435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70542714077062018578406493 26453517778898256966902435)
  ·
    refine ⟨39680276668347385450353653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26453517778898256966902435 39680276668347385450353653)
    ·
      refine ⟨3720025937657567385970655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39680276668347385450353653 3720025937657567385970655)
      ·
        refine ⟨5580038906486351078955983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3720025937657567385970655 5580038906486351078955983)
        ·
          refine ⟨8370058359729526618433975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5580038906486351078955983 8370058359729526618433975)
          ·
            refine ⟨12555087539594289927650963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8370058359729526618433975 12555087539594289927650963)
            ·
              refine ⟨18832631309391434891476445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12555087539594289927650963 18832631309391434891476445)
              ·
                refine ⟨7062236741021788084303667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18832631309391434891476445 7062236741021788084303667)
                ·
                  refine ⟨10593355111532682126455501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7062236741021788084303667 10593355111532682126455501)
                  ·
                    refine ⟨3972508166824755797420813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10593355111532682126455501 3972508166824755797420813)
                    ·
                      refine ⟨1489690562559283424032805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3972508166824755797420813 1489690562559283424032805)
                      ·
                        rfl

theorem cell23_2901162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_2901162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901162 prefixEnd_2901162 := by exact prefixLift 2901162
  have htrace : WordTrace (prefixWord ++ tailWord_2901162) baseStart_2901162 baseEnd_2901162 := by
    simpa [prefixWord, tailWord_2901162, baseEnd_2901162] using wordTrace_append hprefix tailTrace_2901162
  have hstable : (prefixWord ++ tailWord_2901162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901162).length < 2 ^ (prefixWord ++ tailWord_2901162).sum := by decide
  have hdescent : baseEnd_2901162 < baseStart_2901162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901190 : List Nat := [6, 1, 2, 2, 2, 1, 1, 2, 2, 4]
def baseStart_2901190 : Nat := 118140960795 + 2901190 * 2 ^ 59
def prefixEnd_2901190 : Nat := 4983230072969 + 3 ^ 40 * 2901190 * 2
def baseEnd_2901190 : Nat := 496568313339203104827559

theorem tailTrace_2901190 : CollatzResearch.WordTrace tailWord_2901190 prefixEnd_2901190 496568313339203104827559 := by
  unfold tailWord_2901190
  simp only [CollatzResearch.WordTrace]
  refine ⟨3306721636234112145300907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 70543394906327725766419349 3306721636234112145300907)
  ·
    refine ⟨4960082454351168217951361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3306721636234112145300907 4960082454351168217951361)
    ·
      refine ⟨3720061840763376163463521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4960082454351168217951361 3720061840763376163463521)
      ·
        refine ⟨2790046380572532122597641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3720061840763376163463521 2790046380572532122597641)
        ·
          refine ⟨2092534785429399091948231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2790046380572532122597641 2092534785429399091948231)
          ·
            refine ⟨3138802178144098637922347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2092534785429399091948231 3138802178144098637922347)
            ·
              refine ⟨4708203267216147956883521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3138802178144098637922347 4708203267216147956883521)
              ·
                refine ⟨3531152450412110967662641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4708203267216147956883521 3531152450412110967662641)
                ·
                  refine ⟨2648364337809083225746981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3531152450412110967662641 2648364337809083225746981)
                  ·
                    refine ⟨496568313339203104827559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2648364337809083225746981 496568313339203104827559)
                    ·
                      rfl

theorem cell23_2901190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_2901190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901190 prefixEnd_2901190 := by exact prefixLift 2901190
  have htrace : WordTrace (prefixWord ++ tailWord_2901190) baseStart_2901190 baseEnd_2901190 := by
    simpa [prefixWord, tailWord_2901190, baseEnd_2901190] using wordTrace_append hprefix tailTrace_2901190
  have hstable : (prefixWord ++ tailWord_2901190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901190).length < 2 ^ (prefixWord ++ tailWord_2901190).sum := by decide
  have hdescent : baseEnd_2901190 < baseStart_2901190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901245 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 3, 7, 2]
def baseStart_2901245 : Nat := 118140960795 + 2901245 * 2 ^ 59
def prefixEnd_2901245 : Nat := 4983230072969 + 3 ^ 40 * 2901245 * 2
def baseEnd_2901245 : Nat := 1489733181453606599294923

theorem tailTrace_2901245 : CollatzResearch.WordTrace tailWord_2901245 prefixEnd_2901245 1489733181453606599294923 := by
  unfold tailWord_2901245
  simp only [CollatzResearch.WordTrace]
  refine ⟨105817098374292333042881189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70544732249528222028587459 105817098374292333042881189)
  ·
    refine ⟨19840705945179812445540223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105817098374292333042881189 19840705945179812445540223)
    ·
      refine ⟨29761058917769718668310335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19840705945179812445540223 29761058917769718668310335)
      ·
        refine ⟨44641588376654578002465503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29761058917769718668310335 44641588376654578002465503)
        ·
          refine ⟨66962382564981867003698255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44641588376654578002465503 66962382564981867003698255)
          ·
            refine ⟨100443573847472800505547383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66962382564981867003698255 100443573847472800505547383)
            ·
              refine ⟨150665360771209200758321075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100443573847472800505547383 150665360771209200758321075)
              ·
                refine ⟨225998041156813801137481613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150665360771209200758321075 225998041156813801137481613)
                ·
                  refine ⟨84749265433805175426555605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225998041156813801137481613 84749265433805175426555605)
                  ·
                    refine ⟨1986310908604808799059897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 84749265433805175426555605 1986310908604808799059897)
                    ·
                      refine ⟨1489733181453606599294923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1986310908604808799059897 1489733181453606599294923)
                      ·
                        rfl

theorem cell23_2901245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 7, 2].length) (baseStart_2901245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901245 prefixEnd_2901245 := by exact prefixLift 2901245
  have htrace : WordTrace (prefixWord ++ tailWord_2901245) baseStart_2901245 baseEnd_2901245 := by
    simpa [prefixWord, tailWord_2901245, baseEnd_2901245] using wordTrace_append hprefix tailTrace_2901245
  have hstable : (prefixWord ++ tailWord_2901245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901245).length < 2 ^ (prefixWord ++ tailWord_2901245).sum := by decide
  have hdescent : baseEnd_2901245 < baseStart_2901245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901248 : List Nat := [2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 5]
def baseStart_2901248 : Nat := 118140960795 + 2901248 * 2 ^ 59
def prefixEnd_2901248 : Nat := 4983230072969 + 3 ^ 40 * 2901248 * 2
def baseEnd_2901248 : Nat := 1489734721895570087557409

theorem tailTrace_2901248 : CollatzResearch.WordTrace tailWord_2901248 prefixEnd_2901248 1489734721895570087557409 := by
  unfold tailWord_2901248
  simp only [CollatzResearch.WordTrace]
  refine ⟨52908603896640732277620199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70544805195520976370160265 52908603896640732277620199)
  ·
    refine ⟨79362905844961098416430299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52908603896640732277620199 79362905844961098416430299)
    ·
      refine ⟨119044358767441647624645449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79362905844961098416430299 119044358767441647624645449)
      ·
        refine ⟨89283269075581235718484087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119044358767441647624645449 89283269075581235718484087)
        ·
          refine ⟨133924903613371853577726131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89283269075581235718484087 133924903613371853577726131)
          ·
            refine ⟨200887355420057780366589197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133924903613371853577726131 200887355420057780366589197)
            ·
              refine ⟨75332758282521667637470949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200887355420057780366589197 75332758282521667637470949)
              ·
                refine ⟨14124892177972812682025803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75332758282521667637470949 14124892177972812682025803)
                ·
                  refine ⟨21187338266959219023038705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14124892177972812682025803 21187338266959219023038705)
                  ·
                    refine ⟨15890503700219414267279029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21187338266959219023038705 15890503700219414267279029)
                    ·
                      refine ⟨1489734721895570087557409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15890503700219414267279029 1489734721895570087557409)
                      ·
                        rfl

theorem cell23_2901248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_2901248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901248 prefixEnd_2901248 := by exact prefixLift 2901248
  have htrace : WordTrace (prefixWord ++ tailWord_2901248) baseStart_2901248 baseEnd_2901248 := by
    simpa [prefixWord, tailWord_2901248, baseEnd_2901248] using wordTrace_append hprefix tailTrace_2901248
  have hstable : (prefixWord ++ tailWord_2901248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901248).length < 2 ^ (prefixWord ++ tailWord_2901248).sum := by decide
  have hdescent : baseEnd_2901248 < baseStart_2901248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901275 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 1, 6, 2]
def baseStart_2901275 : Nat := 118140960795 + 2901275 * 2 ^ 59
def prefixEnd_2901275 : Nat := 4983230072969 + 3 ^ 40 * 2901275 * 2
def baseEnd_2901275 : Nat := 1489748585873241481919785

theorem tailTrace_2901275 : CollatzResearch.WordTrace tailWord_2901275 prefixEnd_2901275 1489748585873241481919785 := by
  unfold tailWord_2901275
  simp only [CollatzResearch.WordTrace]
  refine ⟨105818192564183648166473279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70545461709455765444315519 105818192564183648166473279)
  ·
    refine ⟨158727288846275472249709919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105818192564183648166473279 158727288846275472249709919)
    ·
      refine ⟨238090933269413208374564879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158727288846275472249709919 238090933269413208374564879)
      ·
        refine ⟨357136399904119812561847319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238090933269413208374564879 357136399904119812561847319)
        ·
          refine ⟨535704599856179718842770979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357136399904119812561847319 535704599856179718842770979)
          ·
            refine ⟨803556899784269578264156469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535704599856179718842770979 803556899784269578264156469)
            ·
              refine ⟨75333459354775272962264669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 803556899784269578264156469 75333459354775272962264669)
              ·
                refine ⟨28250047258040727360849251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75333459354775272962264669 28250047258040727360849251)
                ·
                  refine ⟨42375070887061091041273877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28250047258040727360849251 42375070887061091041273877)
                  ·
                    refine ⟨1986331447830988642559713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42375070887061091041273877 1986331447830988642559713)
                    ·
                      refine ⟨1489748585873241481919785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1986331447830988642559713 1489748585873241481919785)
                      ·
                        rfl

theorem cell23_2901275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 6, 2].length) (baseStart_2901275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901275 prefixEnd_2901275 := by exact prefixLift 2901275
  have htrace : WordTrace (prefixWord ++ tailWord_2901275) baseStart_2901275 baseEnd_2901275 := by
    simpa [prefixWord, tailWord_2901275, baseEnd_2901275] using wordTrace_append hprefix tailTrace_2901275
  have hstable : (prefixWord ++ tailWord_2901275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901275).length < 2 ^ (prefixWord ++ tailWord_2901275).sum := by decide
  have hdescent : baseEnd_2901275 < baseStart_2901275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901319 : List Nat := [1, 1, 4, 1, 2, 4, 1, 4, 1, 4]
def baseStart_2901319 : Nat := 118140960795 + 2901319 * 2 ^ 59
def prefixEnd_2901319 : Nat := 4983230072969 + 3 ^ 40 * 2901319 * 2
def baseEnd_2901319 : Nat := 496590393007346436589861

theorem tailTrace_2901319 : CollatzResearch.WordTrace tailWord_2901319 prefixEnd_2901319 496590393007346436589861 := by
  unfold tailWord_2901319
  simp only [CollatzResearch.WordTrace]
  refine ⟨105819797376024243681075011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70546531584016162454050007 105819797376024243681075011)
  ·
    refine ⟨158729696064036365521612517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105819797376024243681075011 158729696064036365521612517)
    ·
      refine ⟨29761818012006818535302347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158729696064036365521612517 29761818012006818535302347)
      ·
        refine ⟨44642727018010227802953521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29761818012006818535302347 44642727018010227802953521)
        ·
          refine ⟨33482045263507670852215141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44642727018010227802953521 33482045263507670852215141)
          ·
            refine ⟨6277883486907688284790339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33482045263507670852215141 6277883486907688284790339)
            ·
              refine ⟨9416825230361532427185509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6277883486907688284790339 9416825230361532427185509)
              ·
                refine ⟨1765654730692787330097283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9416825230361532427185509 1765654730692787330097283)
                ·
                  refine ⟨2648482096039180995145925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1765654730692787330097283 2648482096039180995145925)
                  ·
                    refine ⟨496590393007346436589861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2648482096039180995145925 496590393007346436589861)
                    ·
                      rfl

theorem cell23_2901319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_2901319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901319 prefixEnd_2901319 := by exact prefixLift 2901319
  have htrace : WordTrace (prefixWord ++ tailWord_2901319) baseStart_2901319 baseEnd_2901319 := by
    simpa [prefixWord, tailWord_2901319, baseEnd_2901319] using wordTrace_append hprefix tailTrace_2901319
  have hstable : (prefixWord ++ tailWord_2901319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901319).length < 2 ^ (prefixWord ++ tailWord_2901319).sum := by decide
  have hdescent : baseEnd_2901319 < baseStart_2901319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901362 : List Nat := [3, 2, 1, 2, 1, 2, 3, 3, 1, 5]
def baseStart_2901362 : Nat := 118140960795 + 2901362 * 2 ^ 59
def prefixEnd_2901362 : Nat := 4983230072969 + 3 ^ 40 * 2901362 * 2
def baseEnd_2901362 : Nat := 496597752896727547177295

theorem tailTrace_2901362 : CollatzResearch.WordTrace tailWord_2901362 prefixEnd_2901362 496597752896727547177295 := by
  unfold tailWord_2901362
  simp only [CollatzResearch.WordTrace]
  refine ⟨26455341428717115506222585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70547577143245641349926893 26455341428717115506222585)
  ·
    refine ⟨19841506071537836629666939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26455341428717115506222585 19841506071537836629666939)
    ·
      refine ⟨29762259107306754944500409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19841506071537836629666939 29762259107306754944500409)
      ·
        refine ⟨22321694330480066208375307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29762259107306754944500409 22321694330480066208375307)
        ·
          refine ⟨33482541495720099312562961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22321694330480066208375307 33482541495720099312562961)
          ·
            refine ⟨25111906121790074484422221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33482541495720099312562961 25111906121790074484422221)
            ·
              refine ⟨9416964795671277931658333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25111906121790074484422221 9416964795671277931658333)
              ·
                refine ⟨3531361798376729224371875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9416964795671277931658333 3531361798376729224371875)
                ·
                  refine ⟨5297042697565093836557813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3531361798376729224371875 5297042697565093836557813)
                  ·
                    refine ⟨496597752896727547177295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5297042697565093836557813 496597752896727547177295)
                    ·
                      rfl

theorem cell23_2901362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_2901362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901362 prefixEnd_2901362 := by exact prefixLift 2901362
  have htrace : WordTrace (prefixWord ++ tailWord_2901362) baseStart_2901362 baseEnd_2901362 := by
    simpa [prefixWord, tailWord_2901362, baseEnd_2901362] using wordTrace_append hprefix tailTrace_2901362
  have hstable : (prefixWord ++ tailWord_2901362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901362).length < 2 ^ (prefixWord ++ tailWord_2901362).sum := by decide
  have hdescent : baseEnd_2901362 < baseStart_2901362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901433 : List Nat := [1, 2, 1, 4, 4, 2, 1, 1, 3, 2, 2]
def baseStart_2901433 : Nat := 118140960795 + 2901433 * 2 ^ 59
def prefixEnd_2901433 : Nat := 4983230072969 + 3 ^ 40 * 2901433 * 2
def baseEnd_2901433 : Nat := 1489829715816651863744059

theorem tailTrace_2901433 : CollatzResearch.WordTrace tailWord_2901433 prefixEnd_2901433 1489829715816651863744059 := by
  unfold tailWord_2901433
  simp only [CollatzResearch.WordTrace]
  refine ⟨105823955297611241150724953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70549303531740827433816635 105823955297611241150724953)
  ·
    refine ⟨79367966473208430863043715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105823955297611241150724953 79367966473208430863043715)
    ·
      refine ⟨119051949709812646294565573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79367966473208430863043715 119051949709812646294565573)
      ·
        refine ⟨22322240570589871180231045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119051949709812646294565573 22322240570589871180231045)
        ·
          refine ⟨4185420106985600846293321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22322240570589871180231045 4185420106985600846293321)
          ·
            refine ⟨3139065080239200634719991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4185420106985600846293321 3139065080239200634719991)
            ·
              refine ⟨4708597620358800952079987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3139065080239200634719991 4708597620358800952079987)
              ·
                refine ⟨7062896430538201428119981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4708597620358800952079987 7062896430538201428119981)
                ·
                  refine ⟨2648586161451825535544993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7062896430538201428119981 2648586161451825535544993)
                  ·
                    refine ⟨1986439621088869151658745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2648586161451825535544993 1986439621088869151658745)
                    ·
                      refine ⟨1489829715816651863744059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1986439621088869151658745 1489829715816651863744059)
                      ·
                        rfl

theorem cell23_2901433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_2901433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901433 prefixEnd_2901433 := by exact prefixLift 2901433
  have htrace : WordTrace (prefixWord ++ tailWord_2901433) baseStart_2901433 baseEnd_2901433 := by
    simpa [prefixWord, tailWord_2901433, baseEnd_2901433] using wordTrace_append hprefix tailTrace_2901433
  have hstable : (prefixWord ++ tailWord_2901433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901433).length < 2 ^ (prefixWord ++ tailWord_2901433).sum := by decide
  have hdescent : baseEnd_2901433 < baseStart_2901433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901534 : List Nat := [4, 3, 3, 1, 1, 2, 1, 2, 2, 1, 3]
def baseStart_2901534 : Nat := 118140960795 + 2901534 * 2 ^ 59
def prefixEnd_2901534 : Nat := 4983230072969 + 3 ^ 40 * 2901534 * 2
def baseEnd_2901534 : Nat := 1489881577362755968581095

theorem tailTrace_2901534 : CollatzResearch.WordTrace tailWord_2901534 prefixEnd_2901534 1489881577362755968581095 := by
  unfold tailWord_2901534
  simp only [CollatzResearch.WordTrace]
  refine ⟨13228454883780666925018957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70551759380163556933434437 13228454883780666925018957)
  ·
    refine ⟨4960670581417750096882109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13228454883780666925018957 4960670581417750096882109)
    ·
      refine ⟨1860251468031656286330791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4960670581417750096882109 1860251468031656286330791)
      ·
        refine ⟨2790377202047484429496187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1860251468031656286330791 2790377202047484429496187)
        ·
          refine ⟨4185565803071226644244281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2790377202047484429496187 4185565803071226644244281)
          ·
            refine ⟨3139174352303419983183211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4185565803071226644244281 3139174352303419983183211)
            ·
              refine ⟨4708761528455129974774817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3139174352303419983183211 4708761528455129974774817)
              ·
                refine ⟨3531571146341347481081113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4708761528455129974774817 3531571146341347481081113)
                ·
                  refine ⟨2648678359756010610810835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3531571146341347481081113 2648678359756010610810835)
                  ·
                    refine ⟨3973017539634015916216253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2648678359756010610810835 3973017539634015916216253)
                    ·
                      refine ⟨1489881577362755968581095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3973017539634015916216253 1489881577362755968581095)
                      ·
                        rfl

theorem cell23_2901534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_2901534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901534 prefixEnd_2901534 := by exact prefixLift 2901534
  have htrace : WordTrace (prefixWord ++ tailWord_2901534) baseStart_2901534 baseEnd_2901534 := by
    simpa [prefixWord, tailWord_2901534, baseEnd_2901534] using wordTrace_append hprefix tailTrace_2901534
  have hstable : (prefixWord ++ tailWord_2901534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901534).length < 2 ^ (prefixWord ++ tailWord_2901534).sum := by decide
  have hdescent : baseEnd_2901534 < baseStart_2901534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901562 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4]
def baseStart_2901562 : Nat := 118140960795 + 2901562 * 2 ^ 59
def prefixEnd_2901562 : Nat := 4983230072969 + 3 ^ 40 * 2901562 * 2
def baseEnd_2901562 : Nat := 1489895954821081859030965

theorem tailTrace_2901562 : CollatzResearch.WordTrace tailWord_2901562 prefixEnd_2901562 1489895954821081859030965 := by
  unfold tailWord_2901562
  simp only [CollatzResearch.WordTrace]
  refine ⟨26457165078535974045542735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70552440209429264121447293 26457165078535974045542735)
  ·
    refine ⟨39685747617803961068314103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26457165078535974045542735 39685747617803961068314103)
    ·
      refine ⟨59528621426705941602471155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39685747617803961068314103 59528621426705941602471155)
      ·
        refine ⟨89292932140058912403706733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59528621426705941602471155 89292932140058912403706733)
        ·
          refine ⟨33484849552522092151390025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89292932140058912403706733 33484849552522092151390025)
          ·
            refine ⟨25113637164391569113542519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33484849552522092151390025 25113637164391569113542519)
            ·
              refine ⟨37670455746587353670313779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25113637164391569113542519 37670455746587353670313779)
              ·
                refine ⟨56505683619881030505470669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37670455746587353670313779 56505683619881030505470669)
                ·
                  refine ⟨21189631357455386439551501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56505683619881030505470669 21189631357455386439551501)
                  ·
                    refine ⟨7946111759045769914831813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21189631357455386439551501 7946111759045769914831813)
                    ·
                      refine ⟨1489895954821081859030965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7946111759045769914831813 1489895954821081859030965)
                      ·
                        rfl

theorem cell23_2901562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_2901562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901562 prefixEnd_2901562 := by exact prefixLift 2901562
  have htrace : WordTrace (prefixWord ++ tailWord_2901562) baseStart_2901562 baseEnd_2901562 := by
    simpa [prefixWord, tailWord_2901562, baseEnd_2901562] using wordTrace_append hprefix tailTrace_2901562
  have hstable : (prefixWord ++ tailWord_2901562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901562).length < 2 ^ (prefixWord ++ tailWord_2901562).sum := by decide
  have hdescent : baseEnd_2901562 < baseStart_2901562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901582 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5]
def baseStart_2901582 : Nat := 118140960795 + 2901582 * 2 ^ 59
def prefixEnd_2901582 : Nat := 4983230072969 + 3 ^ 40 * 2901582 * 2
def baseEnd_2901582 : Nat := 1489906224434171780780873

theorem tailTrace_2901582 : CollatzResearch.WordTrace tailWord_2901582 prefixEnd_2901582 1489906224434171780780873 := by
  unfold tailWord_2901582
  simp only [CollatzResearch.WordTrace]
  refine ⟨13228673721758929949737375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70552926516047626398599333 13228673721758929949737375)
  ·
    refine ⟨19843010582638394924606063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13228673721758929949737375 19843010582638394924606063)
    ·
      refine ⟨29764515873957592386909095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19843010582638394924606063 29764515873957592386909095)
      ·
        refine ⟨44646773810936388580363643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29764515873957592386909095 44646773810936388580363643)
        ·
          refine ⟨66970160716404582870545465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44646773810936388580363643 66970160716404582870545465)
          ·
            refine ⟨50227620537303437152909099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66970160716404582870545465 50227620537303437152909099)
            ·
              refine ⟨75341430805955155729363649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50227620537303437152909099 75341430805955155729363649)
              ·
                refine ⟨56506073104466366797022737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75341430805955155729363649 56506073104466366797022737)
                ·
                  refine ⟨42379554828349775097767053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56506073104466366797022737 42379554828349775097767053)
                  ·
                    refine ⟨15892333060631165661662645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42379554828349775097767053 15892333060631165661662645)
                    ·
                      refine ⟨1489906224434171780780873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15892333060631165661662645 1489906224434171780780873)
                      ·
                        rfl

theorem cell23_2901582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_2901582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901582 prefixEnd_2901582 := by exact prefixLift 2901582
  have htrace : WordTrace (prefixWord ++ tailWord_2901582) baseStart_2901582 baseEnd_2901582 := by
    simpa [prefixWord, tailWord_2901582, baseEnd_2901582] using wordTrace_append hprefix tailTrace_2901582
  have hstable : (prefixWord ++ tailWord_2901582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901582).length < 2 ^ (prefixWord ++ tailWord_2901582).sum := by decide
  have hdescent : baseEnd_2901582 < baseStart_2901582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901596 : List Nat := [2, 2, 4, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_2901596 : Nat := 118140960795 + 2901596 * 2 ^ 59
def prefixEnd_2901596 : Nat := 4983230072969 + 3 ^ 40 * 2901596 * 2
def baseEnd_2901596 : Nat := 1489913413163334726005809

theorem tailTrace_2901596 : CollatzResearch.WordTrace tailWord_2901596 prefixEnd_2901596 1489913413163334726005809 := by
  unfold tailWord_2901596
  simp only [CollatzResearch.WordTrace]
  refine ⟨52914950198010359994454321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70553266930680479992605761 52914950198010359994454321)
  ·
    refine ⟨39686212648507769995840741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52914950198010359994454321 39686212648507769995840741)
    ·
      refine ⟨7441164871595206874220139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39686212648507769995840741 7441164871595206874220139)
      ·
        refine ⟨11161747307392810311330209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7441164871595206874220139 11161747307392810311330209)
        ·
          refine ⟨8371310480544607733497657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11161747307392810311330209 8371310480544607733497657)
          ·
            refine ⟨6278482860408455800123243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8371310480544607733497657 6278482860408455800123243)
            ·
              refine ⟨9417724290612683700184865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6278482860408455800123243 9417724290612683700184865)
              ·
                refine ⟨7063293217959512775138649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9417724290612683700184865 7063293217959512775138649)
                ·
                  refine ⟨5297469913469634581353987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7063293217959512775138649 5297469913469634581353987)
                  ·
                    refine ⟨7946204870204451872030981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5297469913469634581353987 7946204870204451872030981)
                    ·
                      refine ⟨1489913413163334726005809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7946204870204451872030981 1489913413163334726005809)
                      ·
                        rfl

theorem cell23_2901596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_2901596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901596 prefixEnd_2901596 := by exact prefixLift 2901596
  have htrace : WordTrace (prefixWord ++ tailWord_2901596) baseStart_2901596 baseEnd_2901596 := by
    simpa [prefixWord, tailWord_2901596, baseEnd_2901596] using wordTrace_append hprefix tailTrace_2901596
  have hstable : (prefixWord ++ tailWord_2901596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901596).length < 2 ^ (prefixWord ++ tailWord_2901596).sum := by decide
  have hdescent : baseEnd_2901596 < baseStart_2901596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901669 : List Nat := [1, 3, 1, 2, 1, 2, 3, 2, 3, 1, 4]
def baseStart_2901669 : Nat := 118140960795 + 2901669 * 2 ^ 59
def prefixEnd_2901669 : Nat := 4983230072969 + 3 ^ 40 * 2901669 * 2
def baseEnd_2901669 : Nat := 1489950897251112940392973

theorem tailTrace_2901669 : CollatzResearch.WordTrace tailWord_2901669 prefixEnd_2901669 1489950897251112940392973 := by
  unfold tailWord_2901669
  simp only [CollatzResearch.WordTrace]
  refine ⟨105832562924756253456316061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70555041949837502304210707 105832562924756253456316061)
  ·
    refine ⟨39687211096783595046118523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105832562924756253456316061 39687211096783595046118523)
    ·
      refine ⟨59530816645175392569177785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39687211096783595046118523 59530816645175392569177785)
      ·
        refine ⟨44648112483881544426883339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59530816645175392569177785 44648112483881544426883339)
        ·
          refine ⟨66972168725822316640325009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44648112483881544426883339 66972168725822316640325009)
          ·
            refine ⟨50229126544366737480243757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66972168725822316640325009 50229126544366737480243757)
            ·
              refine ⟨18835922454137526555091409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50229126544366737480243757 18835922454137526555091409)
              ·
                refine ⟨14126941840603144916318557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18835922454137526555091409 14126941840603144916318557)
                ·
                  refine ⟨5297603190226179343619459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14126941840603144916318557 5297603190226179343619459)
                  ·
                    refine ⟨7946404785339269015429189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5297603190226179343619459 7946404785339269015429189)
                    ·
                      refine ⟨1489950897251112940392973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7946404785339269015429189 1489950897251112940392973)
                      ·
                        rfl

theorem cell23_2901669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_2901669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901669 prefixEnd_2901669 := by exact prefixLift 2901669
  have htrace : WordTrace (prefixWord ++ tailWord_2901669) baseStart_2901669 baseEnd_2901669 := by
    simpa [prefixWord, tailWord_2901669, baseEnd_2901669] using wordTrace_append hprefix tailTrace_2901669
  have hstable : (prefixWord ++ tailWord_2901669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901669).length < 2 ^ (prefixWord ++ tailWord_2901669).sum := by decide
  have hdescent : baseEnd_2901669 < baseStart_2901669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901679 : List Nat := [1, 1, 2, 1, 2, 4, 4, 1, 1, 6]
def baseStart_2901679 : Nat := 118140960795 + 2901679 * 2 ^ 59
def prefixEnd_2901679 : Nat := 4983230072969 + 3 ^ 40 * 2901679 * 2
def baseEnd_2901679 : Nat := 496652010685885967089309

theorem tailTrace_2901679 : CollatzResearch.WordTrace tailWord_2901679 prefixEnd_2901679 496652010685885967089309 := by
  unfold tailWord_2901679
  simp only [CollatzResearch.WordTrace]
  refine ⟨105832927654720025164180091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70555285103146683442786727 105832927654720025164180091)
  ·
    refine ⟨158749391482080037746270137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105832927654720025164180091 158749391482080037746270137)
    ·
      refine ⟨119062043611560028309702603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158749391482080037746270137 119062043611560028309702603)
      ·
        refine ⟨178593065417340042464553905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119062043611560028309702603 178593065417340042464553905)
        ·
          refine ⟨133944799063005031848415429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178593065417340042464553905 133944799063005031848415429)
          ·
            refine ⟨25114649824313443471577893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133944799063005031848415429 25114649824313443471577893)
            ·
              refine ⟨4708996842058770650920855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25114649824313443471577893 4708996842058770650920855)
              ·
                refine ⟨7063495263088155976381283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4708996842058770650920855 7063495263088155976381283)
                ·
                  refine ⟨10595242894632233964571925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7063495263088155976381283 10595242894632233964571925)
                  ·
                    refine ⟨496652010685885967089309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10595242894632233964571925 496652010685885967089309)
                    ·
                      rfl

theorem cell23_2901679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 6].length) (baseStart_2901679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901679 prefixEnd_2901679 := by exact prefixLift 2901679
  have htrace : WordTrace (prefixWord ++ tailWord_2901679) baseStart_2901679 baseEnd_2901679 := by
    simpa [prefixWord, tailWord_2901679, baseEnd_2901679] using wordTrace_append hprefix tailTrace_2901679
  have hstable : (prefixWord ++ tailWord_2901679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901679).length < 2 ^ (prefixWord ++ tailWord_2901679).sum := by decide
  have hdescent : baseEnd_2901679 < baseStart_2901679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901713 : List Nat := [1, 2, 2, 1, 2, 6, 1, 2, 2, 4]
def baseStart_2901713 : Nat := 118140960795 + 2901713 * 2 ^ 59
def prefixEnd_2901713 : Nat := 4983230072969 + 3 ^ 40 * 2901713 * 2
def baseEnd_2901713 : Nat := 496657830133303589414257

theorem tailTrace_2901713 : CollatzResearch.WordTrace tailWord_2901713 prefixEnd_2901713 496657830133303589414257 := by
  unfold tailWord_2901713
  simp only [CollatzResearch.WordTrace]
  refine ⟨105834167736596848970917793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70556111824397899313945195 105834167736596848970917793)
  ·
    refine ⟨79375625802447636728188345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105834167736596848970917793 79375625802447636728188345)
    ·
      refine ⟨59531719351835727546141259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79375625802447636728188345 59531719351835727546141259)
      ·
        refine ⟨89297579027753591319211889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59531719351835727546141259 89297579027753591319211889)
        ·
          refine ⟨66973184270815193489408917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89297579027753591319211889 66973184270815193489408917)
          ·
            refine ⟨3139368012694462194816043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 66973184270815193489408917 3139368012694462194816043)
            ·
              refine ⟨4709052019041693292224065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3139368012694462194816043 4709052019041693292224065)
              ·
                refine ⟨3531789014281269969168049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4709052019041693292224065 3531789014281269969168049)
                ·
                  refine ⟨2648841760710952476876037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3531789014281269969168049 2648841760710952476876037)
                  ·
                    refine ⟨496657830133303589414257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2648841760710952476876037 496657830133303589414257)
                    ·
                      rfl

theorem cell23_2901713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2, 4].length) (baseStart_2901713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901713 prefixEnd_2901713 := by exact prefixLift 2901713
  have htrace : WordTrace (prefixWord ++ tailWord_2901713) baseStart_2901713 baseEnd_2901713 := by
    simpa [prefixWord, tailWord_2901713, baseEnd_2901713] using wordTrace_append hprefix tailTrace_2901713
  have hstable : (prefixWord ++ tailWord_2901713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901713).length < 2 ^ (prefixWord ++ tailWord_2901713).sum := by decide
  have hdescent : baseEnd_2901713 < baseStart_2901713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901720 : List Nat := [2, 1, 2, 2, 3, 1, 1, 6, 1, 2, 2]
def baseStart_2901720 : Nat := 118140960795 + 2901720 * 2 ^ 59
def prefixEnd_2901720 : Nat := 4983230072969 + 3 ^ 40 * 2901720 * 2
def baseEnd_2901720 : Nat := 1489977084764492240855239

theorem tailTrace_2901720 : CollatzResearch.WordTrace tailWord_2901720 prefixEnd_2901720 1489977084764492240855239 := by
  unfold tailWord_2901720
  simp only [CollatzResearch.WordTrace]
  refine ⟨52917211523785744583211307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70556282031714326110948409 52917211523785744583211307)
  ·
    refine ⟨79375817285678616874816961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52917211523785744583211307 79375817285678616874816961)
    ·
      refine ⟨59531862964258962656112721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79375817285678616874816961 59531862964258962656112721)
      ·
        refine ⟨44648897223194221992084541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59531862964258962656112721 44648897223194221992084541)
        ·
          refine ⟨16743336458697833247031703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44648897223194221992084541 16743336458697833247031703)
          ·
            refine ⟨25115004688046749870547555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16743336458697833247031703 25115004688046749870547555)
            ·
              refine ⟨37672507032070124805821333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25115004688046749870547555 37672507032070124805821333)
              ·
                refine ⟨1765898767128287100272875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37672507032070124805821333 1765898767128287100272875)
                ·
                  refine ⟨2648848150692430650409313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1765898767128287100272875 2648848150692430650409313)
                  ·
                    refine ⟨1986636113019322987806985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2648848150692430650409313 1986636113019322987806985)
                    ·
                      refine ⟨1489977084764492240855239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1986636113019322987806985 1489977084764492240855239)
                      ·
                        rfl

theorem cell23_2901720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6, 1, 2, 2].length) (baseStart_2901720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901720 prefixEnd_2901720 := by exact prefixLift 2901720
  have htrace : WordTrace (prefixWord ++ tailWord_2901720) baseStart_2901720 baseEnd_2901720 := by
    simpa [prefixWord, tailWord_2901720, baseEnd_2901720] using wordTrace_append hprefix tailTrace_2901720
  have hstable : (prefixWord ++ tailWord_2901720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901720).length < 2 ^ (prefixWord ++ tailWord_2901720).sum := by decide
  have hdescent : baseEnd_2901720 < baseStart_2901720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901763 : List Nat := [1, 1, 1, 3, 2, 2, 4, 3, 1, 3, 2]
def baseStart_2901763 : Nat := 118140960795 + 2901763 * 2 ^ 59
def prefixEnd_2901763 : Nat := 4983230072969 + 3 ^ 40 * 2901763 * 2
def baseEnd_2901763 : Nat := 1489999164432635572617541

theorem tailTrace_2901763 : CollatzResearch.WordTrace tailWord_2901763 prefixEnd_2901763 1489999164432635572617541 := by
  unfold tailWord_2901763
  simp only [CollatzResearch.WordTrace]
  refine ⟨105835991386415707510237943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70557327590943805006825295 105835991386415707510237943)
  ·
    refine ⟨158753987079623561265356915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105835991386415707510237943 158753987079623561265356915)
    ·
      refine ⟨238130980619435341898035373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158753987079623561265356915 238130980619435341898035373)
      ·
        refine ⟨89299117732288253211763265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238130980619435341898035373 89299117732288253211763265)
        ·
          refine ⟨66974338299216189908822449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89299117732288253211763265 66974338299216189908822449)
          ·
            refine ⟨50230753724412142431616837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66974338299216189908822449 50230753724412142431616837)
            ·
              refine ⟨9418266323327276705928157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50230753724412142431616837 9418266323327276705928157)
              ·
                refine ⟨3531849871247728764723059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9418266323327276705928157 3531849871247728764723059)
                ·
                  refine ⟨5297774806871593147084589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3531849871247728764723059 5297774806871593147084589)
                  ·
                    refine ⟨1986665552576847430156721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5297774806871593147084589 1986665552576847430156721)
                    ·
                      refine ⟨1489999164432635572617541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1986665552576847430156721 1489999164432635572617541)
                      ·
                        rfl

theorem cell23_2901763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 3, 2].length) (baseStart_2901763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901763 prefixEnd_2901763 := by exact prefixLift 2901763
  have htrace : WordTrace (prefixWord ++ tailWord_2901763) baseStart_2901763 baseEnd_2901763 := by
    simpa [prefixWord, tailWord_2901763, baseEnd_2901763] using wordTrace_append hprefix tailTrace_2901763
  have hstable : (prefixWord ++ tailWord_2901763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901763).length < 2 ^ (prefixWord ++ tailWord_2901763).sum := by decide
  have hdescent : baseEnd_2901763 < baseStart_2901763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901796 : List Nat := [2, 3, 1, 3, 2, 1, 1, 2, 2, 1, 5]
def baseStart_2901796 : Nat := 118140960795 + 2901796 * 2 ^ 59
def prefixEnd_2901796 : Nat := 4983230072969 + 3 ^ 40 * 2901796 * 2
def baseEnd_2901796 : Nat := 1490016109294233943504889

theorem tailTrace_2901796 : CollatzResearch.WordTrace tailWord_2901796 prefixEnd_2901796 1490016109294233943504889 := by
  unfold tailWord_2901796
  simp only [CollatzResearch.WordTrace]
  refine ⟨52918597497648077073094621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70558129996864102764126161 52918597497648077073094621)
  ·
    refine ⟨19844474061618028902410483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52918597497648077073094621 19844474061618028902410483)
    ·
      refine ⟨29766711092427043353615725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19844474061618028902410483 29766711092427043353615725)
      ·
        refine ⟨11162516659660141257605897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29766711092427043353615725 11162516659660141257605897)
        ·
          refine ⟨8371887494745105943204423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11162516659660141257605897 8371887494745105943204423)
          ·
            refine ⟨12557831242117658914806635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8371887494745105943204423 12557831242117658914806635)
            ·
              refine ⟨18836746863176488372209953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12557831242117658914806635 18836746863176488372209953)
              ·
                refine ⟨14127560147382366279157465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18836746863176488372209953 14127560147382366279157465)
                ·
                  refine ⟨10595670110536774709368099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14127560147382366279157465 10595670110536774709368099)
                  ·
                    refine ⟨15893505165805162064052149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10595670110536774709368099 15893505165805162064052149)
                    ·
                      refine ⟨1490016109294233943504889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15893505165805162064052149 1490016109294233943504889)
                      ·
                        rfl

theorem cell23_2901796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_2901796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901796 prefixEnd_2901796 := by exact prefixLift 2901796
  have htrace : WordTrace (prefixWord ++ tailWord_2901796) baseStart_2901796 baseEnd_2901796 := by
    simpa [prefixWord, tailWord_2901796, baseEnd_2901796] using wordTrace_append hprefix tailTrace_2901796
  have hstable : (prefixWord ++ tailWord_2901796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901796).length < 2 ^ (prefixWord ++ tailWord_2901796).sum := by decide
  have hdescent : baseEnd_2901796 < baseStart_2901796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901814 : List Nat := [5, 1, 2, 2, 1, 2, 3, 1, 1, 3, 2]
def baseStart_2901814 : Nat := 118140960795 + 2901814 * 2 ^ 59
def prefixEnd_2901814 : Nat := 4983230072969 + 3 ^ 40 * 2901814 * 2
def baseEnd_2901814 : Nat := 1490025351946014873079807

theorem tailTrace_2901814 : CollatzResearch.WordTrace tailWord_2901814 prefixEnd_2901814 1490025351946014873079807 := by
  unfold tailWord_2901814
  simp only [CollatzResearch.WordTrace]
  refine ⟨6614865719326933951271531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70558567672820628813562997 6614865719326933951271531)
  ·
    refine ⟨9922298578990400926907297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6614865719326933951271531 9922298578990400926907297)
    ·
      refine ⟨7441723934242800695180473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9922298578990400926907297 7441723934242800695180473)
      ·
        refine ⟨5581292950682100521385355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7441723934242800695180473 5581292950682100521385355)
        ·
          refine ⟨8371939426023150782078033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5581292950682100521385355 8371939426023150782078033)
          ·
            refine ⟨6278954569517363086558525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8371939426023150782078033 6278954569517363086558525)
            ·
              refine ⟨2354607963569011157459447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6278954569517363086558525 2354607963569011157459447)
              ·
                refine ⟨3531911945353516736189171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2354607963569011157459447 3531911945353516736189171)
                ·
                  refine ⟨5297867918030275104283757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3531911945353516736189171 5297867918030275104283757)
                  ·
                    refine ⟨1986700469261353164106409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5297867918030275104283757 1986700469261353164106409)
                    ·
                      refine ⟨1490025351946014873079807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1986700469261353164106409 1490025351946014873079807)
                      ·
                        rfl

theorem cell23_2901814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_2901814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901814 prefixEnd_2901814 := by exact prefixLift 2901814
  have htrace : WordTrace (prefixWord ++ tailWord_2901814) baseStart_2901814 baseEnd_2901814 := by
    simpa [prefixWord, tailWord_2901814, baseEnd_2901814] using wordTrace_append hprefix tailTrace_2901814
  have hstable : (prefixWord ++ tailWord_2901814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901814).length < 2 ^ (prefixWord ++ tailWord_2901814).sum := by decide
  have hdescent : baseEnd_2901814 < baseStart_2901814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901830 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_2901830 : Nat := 118140960795 + 2901830 * 2 ^ 59
def prefixEnd_2901830 : Nat := 4983230072969 + 3 ^ 40 * 2901830 * 2
def baseEnd_2901830 : Nat := 1490033567636486810479733

theorem tailTrace_2901830 : CollatzResearch.WordTrace tailWord_2901830 prefixEnd_2901830 1490033567636486810479733 := by
  unfold tailWord_2901830
  simp only [CollatzResearch.WordTrace]
  refine ⟨3307451096161655561028967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 70558956718115318635284629 3307451096161655561028967)
  ·
    refine ⟨4961176644242483341543451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3307451096161655561028967 4961176644242483341543451)
    ·
      refine ⟨7441764966363725012315177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4961176644242483341543451 7441764966363725012315177)
      ·
        refine ⟨5581323724772793759236383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7441764966363725012315177 5581323724772793759236383)
        ·
          refine ⟨8371985587159190638854575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5581323724772793759236383 8371985587159190638854575)
          ·
            refine ⟨12557978380738785958281863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8371985587159190638854575 12557978380738785958281863)
            ·
              refine ⟨18836967571108178937422795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12557978380738785958281863 18836967571108178937422795)
              ·
                refine ⟨28255451356662268406134193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18836967571108178937422795 28255451356662268406134193)
                ·
                  refine ⟨21191588517496701304600645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28255451356662268406134193 21191588517496701304600645)
                  ·
                    refine ⟨3973422847030631494612621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21191588517496701304600645 3973422847030631494612621)
                    ·
                      refine ⟨1490033567636486810479733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3973422847030631494612621 1490033567636486810479733)
                      ·
                        rfl

theorem cell23_2901830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_2901830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901830 prefixEnd_2901830 := by exact prefixLift 2901830
  have htrace : WordTrace (prefixWord ++ tailWord_2901830) baseStart_2901830 baseEnd_2901830 := by
    simpa [prefixWord, tailWord_2901830, baseEnd_2901830] using wordTrace_append hprefix tailTrace_2901830
  have hstable : (prefixWord ++ tailWord_2901830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901830).length < 2 ^ (prefixWord ++ tailWord_2901830).sum := by decide
  have hdescent : baseEnd_2901830 < baseStart_2901830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901893 : List Nat := [1, 3, 1, 1, 3, 2, 4, 1, 3, 4]
def baseStart_2901893 : Nat := 118140960795 + 2901893 * 2 ^ 59
def prefixEnd_2901893 : Nat := 4983230072969 + 3 ^ 40 * 2901893 * 2
def baseEnd_2901893 : Nat := 496688638972573354663981

theorem tailTrace_2901893 : CollatzResearch.WordTrace tailWord_2901893 prefixEnd_2901893 496688638972573354663981 := by
  unfold tailWord_2901893
  simp only [CollatzResearch.WordTrace]
  refine ⟨105840732875944739712470333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70560488583963159808313555 105840732875944739712470333)
  ·
    refine ⟨39690274828479277392176375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105840732875944739712470333 39690274828479277392176375)
    ·
      refine ⟨59535412242718916088264563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39690274828479277392176375 59535412242718916088264563)
      ·
        refine ⟨89303118364078374132396845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59535412242718916088264563 89303118364078374132396845)
        ·
          refine ⟨33488669386529390299648817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89303118364078374132396845 33488669386529390299648817)
          ·
            refine ⟨25116502039897042724736613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33488669386529390299648817 25116502039897042724736613)
            ·
              refine ⟨4709344132480695510888115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25116502039897042724736613 4709344132480695510888115)
              ·
                refine ⟨7064016198721043266332173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4709344132480695510888115 7064016198721043266332173)
                ·
                  refine ⟨2649006074520391224874565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7064016198721043266332173 2649006074520391224874565)
                  ·
                    refine ⟨496688638972573354663981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2649006074520391224874565 496688638972573354663981)
                    ·
                      rfl

theorem cell23_2901893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3, 4].length) (baseStart_2901893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901893 prefixEnd_2901893 := by exact prefixLift 2901893
  have htrace : WordTrace (prefixWord ++ tailWord_2901893) baseStart_2901893 baseEnd_2901893 := by
    simpa [prefixWord, tailWord_2901893, baseEnd_2901893] using wordTrace_append hprefix tailTrace_2901893
  have hstable : (prefixWord ++ tailWord_2901893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901893).length < 2 ^ (prefixWord ++ tailWord_2901893).sum := by decide
  have hdescent : baseEnd_2901893 < baseStart_2901893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901927 : List Nat := [1, 1, 6, 1, 2, 1, 3, 3, 1, 4]
def baseStart_2901927 : Nat := 118140960795 + 2901927 * 2 ^ 59
def prefixEnd_2901927 : Nat := 4983230072969 + 3 ^ 40 * 2901927 * 2
def baseEnd_2901927 : Nat := 496694458419990976988929

theorem tailTrace_2901927 : CollatzResearch.WordTrace tailWord_2901927 prefixEnd_2901927 496694458419990976988929 := by
  unfold tailWord_2901927
  simp only [CollatzResearch.WordTrace]
  refine ⟨105841972957821563519208035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70561315305214375679472023 105841972957821563519208035)
  ·
    refine ⟨158762959436732345278812053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105841972957821563519208035 158762959436732345278812053)
    ·
      refine ⟨7442013723596828684944315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 158762959436732345278812053 7442013723596828684944315)
      ·
        refine ⟨11163020585395243027416473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7442013723596828684944315 11163020585395243027416473)
        ·
          refine ⟨8372265439046432270562355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11163020585395243027416473 8372265439046432270562355)
          ·
            refine ⟨12558398158569648405843533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8372265439046432270562355 12558398158569648405843533)
            ·
              refine ⟨4709399309463618152191325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12558398158569648405843533 4709399309463618152191325)
              ·
                refine ⟨1766024741048856807071747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4709399309463618152191325 1766024741048856807071747)
                ·
                  refine ⟨2649037111573285210607621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1766024741048856807071747 2649037111573285210607621)
                  ·
                    refine ⟨496694458419990976988929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2649037111573285210607621 496694458419990976988929)
                    ·
                      rfl

theorem cell23_2901927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_2901927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901927 prefixEnd_2901927 := by exact prefixLift 2901927
  have htrace : WordTrace (prefixWord ++ tailWord_2901927) baseStart_2901927 baseEnd_2901927 := by
    simpa [prefixWord, tailWord_2901927, baseEnd_2901927] using wordTrace_append hprefix tailTrace_2901927
  have hstable : (prefixWord ++ tailWord_2901927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901927).length < 2 ^ (prefixWord ++ tailWord_2901927).sum := by decide
  have hdescent : baseEnd_2901927 < baseStart_2901927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901934 : List Nat := [4, 1, 5, 1, 1, 1, 1, 2, 2, 1, 4]
def baseStart_2901934 : Nat := 118140960795 + 2901934 * 2 ^ 59
def prefixEnd_2901934 : Nat := 4983230072969 + 3 ^ 40 * 2901934 * 2
def baseEnd_2901934 : Nat := 1490086969624554403579255

theorem tailTrace_2901934 : CollatzResearch.WordTrace tailWord_2901934 prefixEnd_2901934 1490086969624554403579255 := by
  unfold tailWord_2901934
  simp only [CollatzResearch.WordTrace]
  refine ⟨13230278533599525464339107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70561485512530802476475237 13230278533599525464339107)
  ·
    refine ⟨19845417800399288196508661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13230278533599525464339107 19845417800399288196508661)
    ·
      refine ⟨1860507918787433268422687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19845417800399288196508661 1860507918787433268422687)
      ·
        refine ⟨2790761878181149902634031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1860507918787433268422687 2790761878181149902634031)
        ·
          refine ⟨4186142817271724853951047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2790761878181149902634031 4186142817271724853951047)
          ·
            refine ⟨6279214225907587280926571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4186142817271724853951047 6279214225907587280926571)
            ·
              refine ⟨9418821338861380921389857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6279214225907587280926571 9418821338861380921389857)
              ·
                refine ⟨7064116004146035691042393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9418821338861380921389857 7064116004146035691042393)
                ·
                  refine ⟨5298087003109526768281795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7064116004146035691042393 5298087003109526768281795)
                  ·
                    refine ⟨7947130504664290152422693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5298087003109526768281795 7947130504664290152422693)
                    ·
                      refine ⟨1490086969624554403579255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7947130504664290152422693 1490086969624554403579255)
                      ·
                        rfl

theorem cell23_2901934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_2901934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901934 prefixEnd_2901934 := by exact prefixLift 2901934
  have htrace : WordTrace (prefixWord ++ tailWord_2901934) baseStart_2901934 baseEnd_2901934 := by
    simpa [prefixWord, tailWord_2901934, baseEnd_2901934] using wordTrace_append hprefix tailTrace_2901934
  have hstable : (prefixWord ++ tailWord_2901934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901934).length < 2 ^ (prefixWord ++ tailWord_2901934).sum := by decide
  have hdescent : baseEnd_2901934 < baseStart_2901934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901970 : List Nat := [3, 2, 2, 3, 2, 1, 1, 1, 3, 5]
def baseStart_2901970 : Nat := 118140960795 + 2901970 * 2 ^ 59
def prefixEnd_2901970 : Nat := 4983230072969 + 3 ^ 40 * 2901970 * 2
def baseEnd_2901970 : Nat := 496701818309372087576363

theorem tailTrace_2901970 : CollatzResearch.WordTrace tailWord_2901970 prefixEnd_2901970 496701818309372087576363 := by
  unfold tailWord_2901970
  simp only [CollatzResearch.WordTrace]
  refine ⟨26460885324166445465755841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70562360864443854575348909 26460885324166445465755841)
  ·
    refine ⟨19845663993124834099316881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26460885324166445465755841 19845663993124834099316881)
    ·
      refine ⟨14884247994843625574487661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19845663993124834099316881 14884247994843625574487661)
      ·
        refine ⟨5581592998066359590432873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14884247994843625574487661 5581592998066359590432873)
        ·
          refine ⟨4186194748549769692824655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5581592998066359590432873 4186194748549769692824655)
          ·
            refine ⟨6279292122824654539236983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4186194748549769692824655 6279292122824654539236983)
            ·
              refine ⟨9418938184236981808855475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6279292122824654539236983 9418938184236981808855475)
              ·
                refine ⟨14128407276355472713283213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9418938184236981808855475 14128407276355472713283213)
                ·
                  refine ⟨5298152728633302267481205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14128407276355472713283213 5298152728633302267481205)
                  ·
                    refine ⟨496701818309372087576363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5298152728633302267481205 496701818309372087576363)
                    ·
                      rfl

theorem cell23_2901970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_2901970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901970 prefixEnd_2901970 := by exact prefixLift 2901970
  have htrace : WordTrace (prefixWord ++ tailWord_2901970) baseStart_2901970 baseEnd_2901970 := by
    simpa [prefixWord, tailWord_2901970, baseEnd_2901970] using wordTrace_append hprefix tailTrace_2901970
  have hstable : (prefixWord ++ tailWord_2901970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901970).length < 2 ^ (prefixWord ++ tailWord_2901970).sum := by decide
  have hdescent : baseEnd_2901970 < baseStart_2901970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901977 : List Nat := [1, 2, 1, 2, 6, 1, 2, 1, 2, 3, 2]
def baseStart_2901977 : Nat := 118140960795 + 2901977 * 2 ^ 59
def prefixEnd_2901977 : Nat := 4983230072969 + 3 ^ 40 * 2901977 * 2
def baseEnd_2901977 : Nat := 1490109049292697735341557

theorem tailTrace_2901977 : CollatzResearch.WordTrace tailWord_2901977 prefixEnd_2901977 1490109049292697735341557 := by
  unfold tailWord_2901977
  simp only [CollatzResearch.WordTrace]
  refine ⟨105843796607640422058528185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70562531071760281372352123 105843796607640422058528185)
  ·
    refine ⟨79382847455730316543896139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105843796607640422058528185 79382847455730316543896139)
    ·
      refine ⟨119074271183595474815844209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79382847455730316543896139 119074271183595474815844209)
      ·
        refine ⟨89305703387696606111883157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119074271183595474815844209 89305703387696606111883157)
        ·
          refine ⟨4186204846298278411494523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 89305703387696606111883157 4186204846298278411494523)
          ·
            refine ⟨6279307269447417617241785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4186204846298278411494523 6279307269447417617241785)
            ·
              refine ⟨4709480452085563212931339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6279307269447417617241785 4709480452085563212931339)
              ·
                refine ⟨7064220678128344819397009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4709480452085563212931339 7064220678128344819397009)
                ·
                  refine ⟨5298165508596258614547757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7064220678128344819397009 5298165508596258614547757)
                  ·
                    refine ⟨1986812065723596980455409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5298165508596258614547757 1986812065723596980455409)
                    ·
                      refine ⟨1490109049292697735341557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1986812065723596980455409 1490109049292697735341557)
                      ·
                        rfl

theorem cell23_2901977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 3, 2].length) (baseStart_2901977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901977 prefixEnd_2901977 := by exact prefixLift 2901977
  have htrace : WordTrace (prefixWord ++ tailWord_2901977) baseStart_2901977 baseEnd_2901977 := by
    simpa [prefixWord, tailWord_2901977, baseEnd_2901977] using wordTrace_append hprefix tailTrace_2901977
  have hstable : (prefixWord ++ tailWord_2901977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901977).length < 2 ^ (prefixWord ++ tailWord_2901977).sum := by decide
  have hdescent : baseEnd_2901977 < baseStart_2901977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2901983 : List Nat := [1, 1, 2, 3, 4, 2, 1, 2, 1, 6]
def baseStart_2901983 : Nat := 118140960795 + 2901983 * 2 ^ 59
def prefixEnd_2901983 : Nat := 4983230072969 + 3 ^ 40 * 2901983 * 2
def baseEnd_2901983 : Nat := 496704043392208237288843

theorem tailTrace_2901983 : CollatzResearch.WordTrace tailWord_2901983 prefixEnd_2901983 496704043392208237288843 := by
  unfold tailWord_2901983
  simp only [CollatzResearch.WordTrace]
  refine ⟨105844015445618685083246603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70562676963745790055497735 105844015445618685083246603)
  ·
    refine ⟨158766023168428027624869905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105844015445618685083246603 158766023168428027624869905)
    ·
      refine ⟨119074517376321020718652429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158766023168428027624869905 119074517376321020718652429)
      ·
        refine ⟨44652944016120382769494661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119074517376321020718652429 44652944016120382769494661)
        ·
          refine ⟨8372427003022571769280249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44652944016120382769494661 8372427003022571769280249)
          ·
            refine ⟨6279320252266928826960187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8372427003022571769280249 6279320252266928826960187)
            ·
              refine ⟨9418980378400393240440281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6279320252266928826960187 9418980378400393240440281)
              ·
                refine ⟨7064235283800294930330211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9418980378400393240440281 7064235283800294930330211)
                ·
                  refine ⟨10596352925700442395495317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7064235283800294930330211 10596352925700442395495317)
                  ·
                    refine ⟨496704043392208237288843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10596352925700442395495317 496704043392208237288843)
                    ·
                      rfl

theorem cell23_2901983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 6].length) (baseStart_2901983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2901983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2901983 prefixEnd_2901983 := by exact prefixLift 2901983
  have htrace : WordTrace (prefixWord ++ tailWord_2901983) baseStart_2901983 baseEnd_2901983 := by
    simpa [prefixWord, tailWord_2901983, baseEnd_2901983] using wordTrace_append hprefix tailTrace_2901983
  have hstable : (prefixWord ++ tailWord_2901983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2901983).length < 2 ^ (prefixWord ++ tailWord_2901983).sum := by decide
  have hdescent : baseEnd_2901983 < baseStart_2901983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2901983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902001 : List Nat := [1, 2, 2, 2, 5, 2, 2, 2, 1, 1, 3]
def baseStart_2902001 : Nat := 118140960795 + 2902001 * 2 ^ 59
def prefixEnd_2902001 : Nat := 4983230072969 + 3 ^ 40 * 2902001 * 2
def baseEnd_2902001 : Nat := 1490121372828405641441447

theorem tailTrace_2902001 : CollatzResearch.WordTrace tailWord_2902001 prefixEnd_2902001 1490121372828405641441447 := by
  unfold tailWord_2902001
  simp only [CollatzResearch.WordTrace]
  refine ⟨105844671959553474157401857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70563114639702316104934571 105844671959553474157401857)
  ·
    refine ⟨79383503969665105618051393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105844671959553474157401857 79383503969665105618051393)
    ·
      refine ⟨59537627977248829213538545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79383503969665105618051393 59537627977248829213538545)
      ·
        refine ⟨44653220982936621910153909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59537627977248829213538545 44653220982936621910153909)
        ·
          refine ⟨4186239467150308304076929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44653220982936621910153909 4186239467150308304076929)
          ·
            refine ⟨3139679600362731228057697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4186239467150308304076929 3139679600362731228057697)
            ·
              refine ⟨2354759700272048421043273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3139679600362731228057697 2354759700272048421043273)
              ·
                refine ⟨1766069775204036315782455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2354759700272048421043273 1766069775204036315782455)
                ·
                  refine ⟨2649104662806054473673683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1766069775204036315782455 2649104662806054473673683)
                  ·
                    refine ⟨3973656994209081710510525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2649104662806054473673683 3973656994209081710510525)
                    ·
                      refine ⟨1490121372828405641441447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3973656994209081710510525 1490121372828405641441447)
                      ·
                        rfl

theorem cell23_2902001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2, 1, 1, 3].length) (baseStart_2902001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902001 prefixEnd_2902001 := by exact prefixLift 2902001
  have htrace : WordTrace (prefixWord ++ tailWord_2902001) baseStart_2902001 baseEnd_2902001 := by
    simpa [prefixWord, tailWord_2902001, baseEnd_2902001] using wordTrace_append hprefix tailTrace_2902001
  have hstable : (prefixWord ++ tailWord_2902001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902001).length < 2 ^ (prefixWord ++ tailWord_2902001).sum := by decide
  have hdescent : baseEnd_2902001 < baseStart_2902001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902040 : List Nat := [2, 1, 2, 3, 2, 1, 2, 2, 4, 1, 3]
def baseStart_2902040 : Nat := 118140960795 + 2902040 * 2 ^ 59
def prefixEnd_2902040 : Nat := 4983230072969 + 3 ^ 40 * 2902040 * 2
def baseEnd_2902040 : Nat := 1490141398573930988853767

theorem tailTrace_2902040 : CollatzResearch.WordTrace tailWord_2902040 prefixEnd_2902040 1490141398573930988853767 := by
  unfold tailWord_2902040
  simp only [CollatzResearch.WordTrace]
  refine ⟨52923047203206091909035787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70564062937608122545381049 52923047203206091909035787)
  ·
    refine ⟨79384570804809137863553681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52923047203206091909035787 79384570804809137863553681)
    ·
      refine ⟨59538428103606853397665261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79384570804809137863553681 59538428103606853397665261)
      ·
        refine ⟨22326910538852570024124473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59538428103606853397665261 22326910538852570024124473)
        ·
          refine ⟨16745182904139427518093355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22326910538852570024124473 16745182904139427518093355)
          ·
            refine ⟨25117774356209141277140033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16745182904139427518093355 25117774356209141277140033)
            ·
              refine ⟨18838330767156855957855025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25117774356209141277140033 18838330767156855957855025)
              ·
                refine ⟨14128748075367641968391269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18838330767156855957855025 14128748075367641968391269)
                ·
                  refine ⟨2649140264131432869073363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14128748075367641968391269 2649140264131432869073363)
                  ·
                    refine ⟨3973710396197149303610045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2649140264131432869073363 3973710396197149303610045)
                    ·
                      refine ⟨1490141398573930988853767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3973710396197149303610045 1490141398573930988853767)
                      ·
                        rfl

theorem cell23_2902040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_2902040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902040 prefixEnd_2902040 := by exact prefixLift 2902040
  have htrace : WordTrace (prefixWord ++ tailWord_2902040) baseStart_2902040 baseEnd_2902040 := by
    simpa [prefixWord, tailWord_2902040, baseEnd_2902040] using wordTrace_append hprefix tailTrace_2902040
  have hstable : (prefixWord ++ tailWord_2902040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902040).length < 2 ^ (prefixWord ++ tailWord_2902040).sum := by decide
  have hdescent : baseEnd_2902040 < baseStart_2902040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902044 : List Nat := [2, 2, 3, 1, 3, 3, 2, 1, 1, 2, 3]
def baseStart_2902044 : Nat := 118140960795 + 2902044 * 2 ^ 59
def prefixEnd_2902044 : Nat := 4983230072969 + 3 ^ 40 * 2902044 * 2
def baseEnd_2902044 : Nat := 1490143452496548973203749

theorem tailTrace_2902044 : CollatzResearch.WordTrace tailWord_2902044 prefixEnd_2902044 1490143452496548973203749 := by
  unfold tailWord_2902044
  simp only [CollatzResearch.WordTrace]
  refine ⟨52923120149198846250608593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70564160198931795000811457 52923120149198846250608593)
  ·
    refine ⟨39692340111899134687956445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52923120149198846250608593 39692340111899134687956445)
    ·
      refine ⟨14884627541962175507983667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39692340111899134687956445 14884627541962175507983667)
      ·
        refine ⟨22326941312943263261975501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14884627541962175507983667 22326941312943263261975501)
        ·
          refine ⟨8372602992353723723240813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22326941312943263261975501 8372602992353723723240813)
          ·
            refine ⟨3139726122132646396215305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8372602992353723723240813 3139726122132646396215305)
            ·
              refine ⟨2354794591599484797161479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3139726122132646396215305 2354794591599484797161479)
              ·
                refine ⟨3532191887399227195742219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2354794591599484797161479 3532191887399227195742219)
                ·
                  refine ⟨5298287831098840793613329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3532191887399227195742219 5298287831098840793613329)
                  ·
                    refine ⟨3973715873324130595209997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5298287831098840793613329 3973715873324130595209997)
                    ·
                      refine ⟨1490143452496548973203749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3973715873324130595209997 1490143452496548973203749)
                      ·
                        rfl

theorem cell23_2902044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_2902044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902044 prefixEnd_2902044 := by exact prefixLift 2902044
  have htrace : WordTrace (prefixWord ++ tailWord_2902044) baseStart_2902044 baseEnd_2902044 := by
    simpa [prefixWord, tailWord_2902044, baseEnd_2902044] using wordTrace_append hprefix tailTrace_2902044
  have hstable : (prefixWord ++ tailWord_2902044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902044).length < 2 ^ (prefixWord ++ tailWord_2902044).sum := by decide
  have hdescent : baseEnd_2902044 < baseStart_2902044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902204 : List Nat := [2, 2, 2, 3, 3, 2, 1, 1, 2, 1, 4]
def baseStart_2902204 : Nat := 118140960795 + 2902204 * 2 ^ 59
def prefixEnd_2902204 : Nat := 4983230072969 + 3 ^ 40 * 2902204 * 2
def baseEnd_2902204 : Nat := 1490225609401268347203013

theorem tailTrace_2902204 : CollatzResearch.WordTrace tailWord_2902204 prefixEnd_2902204 1490225609401268347203013 := by
  unfold tailWord_2902204
  simp only [CollatzResearch.WordTrace]
  refine ⟨52926037988909019913520833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70568050651878693218027777 52926037988909019913520833)
  ·
    refine ⟨39694528491681764935140625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52926037988909019913520833 39694528491681764935140625)
    ·
      refine ⟨29770896368761323701355469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39694528491681764935140625 29770896368761323701355469)
      ·
        refine ⟨11164086138285496388008301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29770896368761323701355469 11164086138285496388008301)
        ·
          refine ⟨4186532301857061145503113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11164086138285496388008301 4186532301857061145503113)
          ·
            refine ⟨3139899226392795859127335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4186532301857061145503113 3139899226392795859127335)
            ·
              refine ⟨4709848839589193788691003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3139899226392795859127335 4709848839589193788691003)
              ·
                refine ⟨7064773259383790683036505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4709848839589193788691003 7064773259383790683036505)
                ·
                  refine ⟨5298579944537843012277379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7064773259383790683036505 5298579944537843012277379)
                  ·
                    refine ⟨7947869916806764518416069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5298579944537843012277379 7947869916806764518416069)
                    ·
                      refine ⟨1490225609401268347203013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7947869916806764518416069 1490225609401268347203013)
                      ·
                        rfl

theorem cell23_2902204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_2902204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902204 prefixEnd_2902204 := by exact prefixLift 2902204
  have htrace : WordTrace (prefixWord ++ tailWord_2902204) baseStart_2902204 baseEnd_2902204 := by
    simpa [prefixWord, tailWord_2902204, baseEnd_2902204] using wordTrace_append hprefix tailTrace_2902204
  have hstable : (prefixWord ++ tailWord_2902204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902204).length < 2 ^ (prefixWord ++ tailWord_2902204).sum := by decide
  have hdescent : baseEnd_2902204 < baseStart_2902204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902274 : List Nat := [3, 4, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_2902274 : Nat := 118140960795 + 2902274 * 2 ^ 59
def prefixEnd_2902274 : Nat := 4983230072969 + 3 ^ 40 * 2902274 * 2
def baseEnd_2902274 : Nat := 496753851015694357775897

theorem tailTrace_2902274 : CollatzResearch.WordTrace tailWord_2902274 prefixEnd_2902274 496753851015694357775897 := by
  unfold tailWord_2902274
  simp only [CollatzResearch.WordTrace]
  refine ⟨26463657271891110445522469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70569752725042961188059917 26463657271891110445522469)
  ·
    refine ⟨4961935738479583208535463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26463657271891110445522469 4961935738479583208535463)
    ·
      refine ⟨7442903607719374812803195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4961935738479583208535463 7442903607719374812803195)
      ·
        refine ⟨11164355411579062219204793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7442903607719374812803195 11164355411579062219204793)
        ·
          refine ⟨8373266558684296664403595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11164355411579062219204793 8373266558684296664403595)
          ·
            refine ⟨12559899838026444996605393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8373266558684296664403595 12559899838026444996605393)
            ·
              refine ⟨9419924878519833747454045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12559899838026444996605393 9419924878519833747454045)
              ·
                refine ⟨3532471829444937655295267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9419924878519833747454045 3532471829444937655295267)
                ·
                  refine ⟨5298707744167406482942901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3532471829444937655295267 5298707744167406482942901)
                  ·
                    refine ⟨496753851015694357775897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5298707744167406482942901 496753851015694357775897)
                    ·
                      rfl

theorem cell23_2902274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_2902274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902274 prefixEnd_2902274 := by exact prefixLift 2902274
  have htrace : WordTrace (prefixWord ++ tailWord_2902274) baseStart_2902274 baseEnd_2902274 := by
    simpa [prefixWord, tailWord_2902274, baseEnd_2902274] using wordTrace_append hprefix tailTrace_2902274
  have hstable : (prefixWord ++ tailWord_2902274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902274).length < 2 ^ (prefixWord ++ tailWord_2902274).sum := by decide
  have hdescent : baseEnd_2902274 < baseStart_2902274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902304 : List Nat := [2, 1, 1, 5, 2, 2, 1, 3, 2, 4]
def baseStart_2902304 : Nat := 118140960795 + 2902304 * 2 ^ 59
def prefixEnd_2902304 : Nat := 4983230072969 + 3 ^ 40 * 2902304 * 2
def baseEnd_2902304 : Nat := 496758985822239318650851

theorem tailTrace_2902304 : CollatzResearch.WordTrace tailWord_2902304 prefixEnd_2902304 496758985822239318650851 := by
  unfold tailWord_2902304
  simp only [CollatzResearch.WordTrace]
  refine ⟨52927861638727878452840983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70570482184970504603787977 52927861638727878452840983)
  ·
    refine ⟨79391792458091817679261475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52927861638727878452840983 79391792458091817679261475)
    ·
      refine ⟨119087688687137726518892213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79391792458091817679261475 119087688687137726518892213)
      ·
        refine ⟨11164470814419161861146145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119087688687137726518892213 11164470814419161861146145)
        ·
          refine ⟨8373353110814371395859609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11164470814419161861146145 8373353110814371395859609)
          ·
            refine ⟨6280014833110778546894707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8373353110814371395859609 6280014833110778546894707)
            ·
              refine ⟨9420022249666167820342061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6280014833110778546894707 9420022249666167820342061)
              ·
                refine ⟨3532508343624812932628273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9420022249666167820342061 3532508343624812932628273)
                ·
                  refine ⟨2649381257718609699471205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3532508343624812932628273 2649381257718609699471205)
                  ·
                    refine ⟨496758985822239318650851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2649381257718609699471205 496758985822239318650851)
                    ·
                      rfl

theorem cell23_2902304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 2, 4].length) (baseStart_2902304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902304 prefixEnd_2902304 := by exact prefixLift 2902304
  have htrace : WordTrace (prefixWord ++ tailWord_2902304) baseStart_2902304 baseEnd_2902304 := by
    simpa [prefixWord, tailWord_2902304, baseEnd_2902304] using wordTrace_append hprefix tailTrace_2902304
  have hstable : (prefixWord ++ tailWord_2902304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902304).length < 2 ^ (prefixWord ++ tailWord_2902304).sum := by decide
  have hdescent : baseEnd_2902304 < baseStart_2902304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902324 : List Nat := [2, 5, 1, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_2902324 : Nat := 118140960795 + 2902324 * 2 ^ 59
def prefixEnd_2902324 : Nat := 4983230072969 + 3 ^ 40 * 2902324 * 2
def baseEnd_2902324 : Nat := 1490287227079807877702461

theorem tailTrace_2902324 : CollatzResearch.WordTrace tailWord_2902324 prefixEnd_2902324 1490287227079807877702461 := by
  unfold tailWord_2902324
  simp only [CollatzResearch.WordTrace]
  refine ⟨52928226368691650160705013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70570968491588866880940017 52928226368691650160705013)
  ·
    refine ⟨4962021222064842202566095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52928226368691650160705013 4962021222064842202566095)
    ·
      refine ⟨7443031833097263303849143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4962021222064842202566095 7443031833097263303849143)
      ·
        refine ⟨11164547749645894955773715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7443031833097263303849143 11164547749645894955773715)
        ·
          refine ⟨16746821624468842433660573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11164547749645894955773715 16746821624468842433660573)
          ·
            refine ⟨6280058109175815912622715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16746821624468842433660573 6280058109175815912622715)
            ·
              refine ⟨9420087163763723868934073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6280058109175815912622715 9420087163763723868934073)
              ·
                refine ⟨7065065372822792901700555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9420087163763723868934073 7065065372822792901700555)
                ·
                  refine ⟨10597598059234189352550833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7065065372822792901700555 10597598059234189352550833)
                  ·
                    refine ⟨7948198544425642014413125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10597598059234189352550833 7948198544425642014413125)
                    ·
                      refine ⟨1490287227079807877702461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7948198544425642014413125 1490287227079807877702461)
                      ·
                        rfl

theorem cell23_2902324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_2902324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902324 prefixEnd_2902324 := by exact prefixLift 2902324
  have htrace : WordTrace (prefixWord ++ tailWord_2902324) baseStart_2902324 baseEnd_2902324 := by
    simpa [prefixWord, tailWord_2902324, baseEnd_2902324] using wordTrace_append hprefix tailTrace_2902324
  have hstable : (prefixWord ++ tailWord_2902324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902324).length < 2 ^ (prefixWord ++ tailWord_2902324).sum := by decide
  have hdescent : baseEnd_2902324 < baseStart_2902324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902327 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 6, 1, 3]
def baseStart_2902327 : Nat := 118140960795 + 2902327 * 2 ^ 59
def prefixEnd_2902327 : Nat := 4983230072969 + 3 ^ 40 * 2902327 * 2
def baseEnd_2902327 : Nat := 1490288767521771365964947

theorem tailTrace_2902327 : CollatzResearch.WordTrace tailWord_2902327 prefixEnd_2902327 1490288767521771365964947 := by
  unfold tailWord_2902327
  simp only [CollatzResearch.WordTrace]
  refine ⟨105856562156372431833769235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70571041437581621222512823 105856562156372431833769235)
  ·
    refine ⟨158784843234558647750653853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105856562156372431833769235 158784843234558647750653853)
    ·
      refine ⟨59544316212959492906495195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158784843234558647750653853 59544316212959492906495195)
      ·
        refine ⟨89316474319439239359742793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59544316212959492906495195 89316474319439239359742793)
        ·
          refine ⟨66987355739579429519807095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89316474319439239359742793 66987355739579429519807095)
          ·
            refine ⟨100481033609369144279710643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66987355739579429519807095 100481033609369144279710643)
            ·
              refine ⟨150721550414053716419565965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100481033609369144279710643 150721550414053716419565965)
              ·
                refine ⟨56520581405270143657337237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150721550414053716419565965 56520581405270143657337237)
                ·
                  refine ⟨2649402253372037983937683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56520581405270143657337237 2649402253372037983937683)
                  ·
                    refine ⟨3974103380058056975906525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2649402253372037983937683 3974103380058056975906525)
                    ·
                      refine ⟨1490288767521771365964947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3974103380058056975906525 1490288767521771365964947)
                      ·
                        rfl

theorem cell23_2902327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6, 1, 3].length) (baseStart_2902327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902327 prefixEnd_2902327 := by exact prefixLift 2902327
  have htrace : WordTrace (prefixWord ++ tailWord_2902327) baseStart_2902327 baseEnd_2902327 := by
    simpa [prefixWord, tailWord_2902327, baseEnd_2902327] using wordTrace_append hprefix tailTrace_2902327
  have hstable : (prefixWord ++ tailWord_2902327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902327).length < 2 ^ (prefixWord ++ tailWord_2902327).sum := by decide
  have hdescent : baseEnd_2902327 < baseStart_2902327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902344 : List Nat := [2, 1, 3, 1, 1, 2, 3, 4, 2, 1, 3]
def baseStart_2902344 : Nat := 118140960795 + 2902344 * 2 ^ 59
def prefixEnd_2902344 : Nat := 4983230072969 + 3 ^ 40 * 2902344 * 2
def baseEnd_2902344 : Nat := 1490297496692897799452369

theorem tailTrace_2902344 : CollatzResearch.WordTrace tailWord_2902344 prefixEnd_2902344 1490297496692897799452369 := by
  unfold tailWord_2902344
  simp only [CollatzResearch.WordTrace]
  refine ⟨52928591098655421868569043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70571454798207229158092057 52928591098655421868569043)
  ·
    refine ⟨79392886647983132802853565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52928591098655421868569043 79392886647983132802853565)
    ·
      refine ⟨29772332492993674801070087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79392886647983132802853565 29772332492993674801070087)
      ·
        refine ⟨44658498739490512201605131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29772332492993674801070087 44658498739490512201605131)
        ·
          refine ⟨66987748109235768302407697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44658498739490512201605131 66987748109235768302407697)
          ·
            refine ⟨50240811081926826226805773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66987748109235768302407697 50240811081926826226805773)
            ·
              refine ⟨18840304155722559835052165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50240811081926826226805773 18840304155722559835052165)
              ·
                refine ⟨3532557029197979969072281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18840304155722559835052165 3532557029197979969072281)
                ·
                  refine ⟨2649417771898484976804211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3532557029197979969072281 2649417771898484976804211)
                  ·
                    refine ⟨3974126657847727465206317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2649417771898484976804211 3974126657847727465206317)
                    ·
                      refine ⟨1490297496692897799452369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3974126657847727465206317 1490297496692897799452369)
                      ·
                        rfl

theorem cell23_2902344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_2902344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902344 prefixEnd_2902344 := by exact prefixLift 2902344
  have htrace : WordTrace (prefixWord ++ tailWord_2902344) baseStart_2902344 baseEnd_2902344 := by
    simpa [prefixWord, tailWord_2902344, baseEnd_2902344] using wordTrace_append hprefix tailTrace_2902344
  have hstable : (prefixWord ++ tailWord_2902344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902344).length < 2 ^ (prefixWord ++ tailWord_2902344).sum := by decide
  have hdescent : baseEnd_2902344 < baseStart_2902344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902354 : List Nat := [3, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2]
def baseStart_2902354 : Nat := 118140960795 + 2902354 * 2 ^ 59
def prefixEnd_2902354 : Nat := 4983230072969 + 3 ^ 40 * 2902354 * 2
def baseEnd_2902354 : Nat := 1490302631499442760327323

theorem tailTrace_2902354 : CollatzResearch.WordTrace tailWord_2902354 prefixEnd_2902354 1490302631499442760327323 := by
  unfold tailWord_2902354
  simp only [CollatzResearch.WordTrace]
  refine ⟨26464386731818653861250529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70571697951516410296668077 26464386731818653861250529)
  ·
    refine ⟨19848290048863990395937897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26464386731818653861250529 19848290048863990395937897)
    ·
      refine ⟨14886217536647992796953423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19848290048863990395937897 14886217536647992796953423)
      ·
        refine ⟨22329326304971989195430135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14886217536647992796953423 22329326304971989195430135)
        ·
          refine ⟨33493989457457983793145203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22329326304971989195430135 33493989457457983793145203)
          ·
            refine ⟨50240984186186975689717805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33493989457457983793145203 50240984186186975689717805)
            ·
              refine ⟨18840369069820115883644177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50240984186186975689717805 18840369069820115883644177)
              ·
                refine ⟨14130276802365086912733133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18840369069820115883644177 14130276802365086912733133)
                ·
                  refine ⟨5298853800886907592274925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14130276802365086912733133 5298853800886907592274925)
                  ·
                    refine ⟨1987070175332590347103097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5298853800886907592274925 1987070175332590347103097)
                    ·
                      refine ⟨1490302631499442760327323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1987070175332590347103097 1490302631499442760327323)
                      ·
                        rfl

theorem cell23_2902354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_2902354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902354 prefixEnd_2902354 := by exact prefixLift 2902354
  have htrace : WordTrace (prefixWord ++ tailWord_2902354) baseStart_2902354 baseEnd_2902354 := by
    simpa [prefixWord, tailWord_2902354, baseEnd_2902354] using wordTrace_append hprefix tailTrace_2902354
  have hstable : (prefixWord ++ tailWord_2902354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902354).length < 2 ^ (prefixWord ++ tailWord_2902354).sum := by decide
  have hdescent : baseEnd_2902354 < baseStart_2902354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902384 : List Nat := [2, 1, 1, 1, 4, 3, 2, 2, 1, 4, 2]
def baseStart_2902384 : Nat := 118140960795 + 2902384 * 2 ^ 59
def prefixEnd_2902384 : Nat := 4983230072969 + 3 ^ 40 * 2902384 * 2
def baseEnd_2902384 : Nat := 1490318035919077642952185

theorem tailTrace_2902384 : CollatzResearch.WordTrace tailWord_2902384 prefixEnd_2902384 1490318035919077642952185 := by
  unfold tailWord_2902384
  simp only [CollatzResearch.WordTrace]
  refine ⟨52929320558582965284297103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70572427411443953712396137 52929320558582965284297103)
  ·
    refine ⟨79393980837874447926445655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52929320558582965284297103 79393980837874447926445655)
    ·
      refine ⟨119090971256811671889668483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79393980837874447926445655 119090971256811671889668483)
      ·
        refine ⟨178636456885217507834502725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119090971256811671889668483 178636456885217507834502725)
        ·
          refine ⟨33494335665978282718969261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178636456885217507834502725 33494335665978282718969261)
          ·
            refine ⟨12560375874741856019613473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33494335665978282718969261 12560375874741856019613473)
            ·
              refine ⟨9420281906056392014710105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12560375874741856019613473 9420281906056392014710105)
              ·
                refine ⟨7065211429542294011032579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9420281906056392014710105 7065211429542294011032579)
                ·
                  refine ⟨10597817144313441016548869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7065211429542294011032579 10597817144313441016548869)
                  ·
                    refine ⟨1987090714558770190602913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10597817144313441016548869 1987090714558770190602913)
                    ·
                      refine ⟨1490318035919077642952185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1987090714558770190602913 1490318035919077642952185)
                      ·
                        rfl

theorem cell23_2902384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 1, 4, 2].length) (baseStart_2902384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902384 prefixEnd_2902384 := by exact prefixLift 2902384
  have htrace : WordTrace (prefixWord ++ tailWord_2902384) baseStart_2902384 baseEnd_2902384 := by
    simpa [prefixWord, tailWord_2902384, baseEnd_2902384] using wordTrace_append hprefix tailTrace_2902384
  have hstable : (prefixWord ++ tailWord_2902384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902384).length < 2 ^ (prefixWord ++ tailWord_2902384).sum := by decide
  have hdescent : baseEnd_2902384 < baseStart_2902384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902397 : List Nat := [1, 4, 1, 1, 2, 3, 1, 2, 2, 2, 4]
def baseStart_2902397 : Nat := 118140960795 + 2902397 * 2 ^ 59
def prefixEnd_2902397 : Nat := 4983230072969 + 3 ^ 40 * 2902397 * 2
def baseEnd_2902397 : Nat := 1490324711167586092089625

theorem tailTrace_2902397 : CollatzResearch.WordTrace tailWord_2902397 prefixEnd_2902397 1490324711167586092089625 := by
  unfold tailWord_2902397
  simp only [CollatzResearch.WordTrace]
  refine ⟨105859115266118833788817445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70572743510745889192544963 105859115266118833788817445)
  ·
    refine ⟨19848584112397281335403271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105859115266118833788817445 19848584112397281335403271)
    ·
      refine ⟨29772876168595922003104907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19848584112397281335403271 29772876168595922003104907)
      ·
        refine ⟨44659314252893883004657361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29772876168595922003104907 44659314252893883004657361)
        ·
          refine ⟨33494485689670412253493021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44659314252893883004657361 33494485689670412253493021)
          ·
            refine ⟨12560432133626404595059883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33494485689670412253493021 12560432133626404595059883)
            ·
              refine ⟨18840648200439606892589825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12560432133626404595059883 18840648200439606892589825)
              ·
                refine ⟨14130486150329705169442369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18840648200439606892589825 14130486150329705169442369)
                ·
                  refine ⟨10597864612747278877081777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14130486150329705169442369 10597864612747278877081777)
                  ·
                    refine ⟨7948398459560459157811333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10597864612747278877081777 7948398459560459157811333)
                    ·
                      refine ⟨1490324711167586092089625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7948398459560459157811333 1490324711167586092089625)
                      ·
                        rfl

theorem cell23_2902397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_2902397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902397 prefixEnd_2902397 := by exact prefixLift 2902397
  have htrace : WordTrace (prefixWord ++ tailWord_2902397) baseStart_2902397 baseEnd_2902397 := by
    simpa [prefixWord, tailWord_2902397, baseEnd_2902397] using wordTrace_append hprefix tailTrace_2902397
  have hstable : (prefixWord ++ tailWord_2902397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902397).length < 2 ^ (prefixWord ++ tailWord_2902397).sum := by decide
  have hdescent : baseEnd_2902397 < baseStart_2902397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902407 : List Nat := [1, 1, 4, 2, 2, 1, 4, 1, 7]
def baseStart_2902407 : Nat := 118140960795 + 2902407 * 2 ^ 59
def prefixEnd_2902407 : Nat := 4983230072969 + 3 ^ 40 * 2902407 * 2
def baseEnd_2902407 : Nat := 165592205108236783662731

theorem tailTrace_2902407 : CollatzResearch.WordTrace tailWord_2902407 prefixEnd_2902407 165592205108236783662731 := by
  unfold tailWord_2902407
  simp only [CollatzResearch.WordTrace]
  refine ⟨105859479996082605496681475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70572986664055070331120983 105859479996082605496681475)
  ·
    refine ⟨158789219994123908245022213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105859479996082605496681475 158789219994123908245022213)
    ·
      refine ⟨29772978748898232795941665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158789219994123908245022213 29772978748898232795941665)
      ·
        refine ⟨22329734061673674596956249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29772978748898232795941665 22329734061673674596956249)
        ·
          refine ⟨16747300546255255947717187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22329734061673674596956249 16747300546255255947717187)
          ·
            refine ⟨25120950819382883921575781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16747300546255255947717187 25120950819382883921575781)
            ·
              refine ⟨4710178278634290735295459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25120950819382883921575781 4710178278634290735295459)
              ·
                refine ⟨7065267417951436102943189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4710178278634290735295459 7065267417951436102943189)
                ·
                  refine ⟨165592205108236783662731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7065267417951436102943189 165592205108236783662731)
                  ·
                    rfl

theorem cell23_2902407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 7].length) (baseStart_2902407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902407 prefixEnd_2902407 := by exact prefixLift 2902407
  have htrace : WordTrace (prefixWord ++ tailWord_2902407) baseStart_2902407 baseEnd_2902407 := by
    simpa [prefixWord, tailWord_2902407, baseEnd_2902407] using wordTrace_append hprefix tailTrace_2902407
  have hstable : (prefixWord ++ tailWord_2902407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902407).length < 2 ^ (prefixWord ++ tailWord_2902407).sum := by decide
  have hdescent : baseEnd_2902407 < baseStart_2902407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902414 : List Nat := [4, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4]
def baseStart_2902414 : Nat := 118140960795 + 2902414 * 2 ^ 59
def prefixEnd_2902414 : Nat := 4983230072969 + 3 ^ 40 * 2902414 * 2
def baseEnd_2902414 : Nat := 1490333440338712525577047

theorem tailTrace_2902414 : CollatzResearch.WordTrace tailWord_2902414 prefixEnd_2902414 1490333440338712525577047 := by
  unfold tailWord_2902414
  simp only [CollatzResearch.WordTrace]
  refine ⟨13232466913382155711523287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70573156871371497128124197 13232466913382155711523287)
  ·
    refine ⟨19848700370073233567284931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13232466913382155711523287 19848700370073233567284931)
    ·
      refine ⟨29773050555109850350927397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19848700370073233567284931 29773050555109850350927397)
      ·
        refine ⟨5582446979083096940798887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29773050555109850350927397 5582446979083096940798887)
        ·
          refine ⟨8373670468624645411198331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5582446979083096940798887 8373670468624645411198331)
          ·
            refine ⟨12560505702936968116797497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8373670468624645411198331 12560505702936968116797497)
            ·
              refine ⟨9420379277202726087598123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12560505702936968116797497 9420379277202726087598123)
              ·
                refine ⟨14130568915804089131397185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9420379277202726087598123 14130568915804089131397185)
                ·
                  refine ⟨10597926686853066848547889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14130568915804089131397185 10597926686853066848547889)
                  ·
                    refine ⟨7948445015139800136410917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10597926686853066848547889 7948445015139800136410917)
                    ·
                      refine ⟨1490333440338712525577047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7948445015139800136410917 1490333440338712525577047)
                      ·
                        rfl

theorem cell23_2902414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_2902414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902414 prefixEnd_2902414 := by exact prefixLift 2902414
  have htrace : WordTrace (prefixWord ++ tailWord_2902414) baseStart_2902414 baseEnd_2902414 := by
    simpa [prefixWord, tailWord_2902414, baseEnd_2902414] using wordTrace_append hprefix tailTrace_2902414
  have hstable : (prefixWord ++ tailWord_2902414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902414).length < 2 ^ (prefixWord ++ tailWord_2902414).sum := by decide
  have hdescent : baseEnd_2902414 < baseStart_2902414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902437 : List Nat := [1, 3, 1, 2, 1, 1, 4, 3, 2, 5]
def baseStart_2902437 : Nat := 118140960795 + 2902437 * 2 ^ 59
def prefixEnd_2902437 : Nat := 4983230072969 + 3 ^ 40 * 2902437 * 2
def baseEnd_2902437 : Nat := 496781750131255311863147

theorem tailTrace_2902437 : CollatzResearch.WordTrace tailWord_2902437 prefixEnd_2902437 496781750131255311863147 := by
  unfold tailWord_2902437
  simp only [CollatzResearch.WordTrace]
  refine ⟨105860574185973920620273565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70573716123982613746849043 105860574185973920620273565)
  ·
    refine ⟨39697715319740220232602587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105860574185973920620273565 39697715319740220232602587)
    ·
      refine ⟨59546572979610330348903881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39697715319740220232602587 59546572979610330348903881)
      ·
        refine ⟨44659929734707747761677911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59546572979610330348903881 44659929734707747761677911)
        ·
          refine ⟨66989894602061621642516867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44659929734707747761677911 66989894602061621642516867)
          ·
            refine ⟨100484841903092432463775301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66989894602061621642516867 100484841903092432463775301)
            ·
              refine ⟨18840907856829831086957869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100484841903092432463775301 18840907856829831086957869)
              ·
                refine ⟨7065340446311186657609201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18840907856829831086957869 7065340446311186657609201)
                ·
                  refine ⟨5299005334733389993206901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7065340446311186657609201 5299005334733389993206901)
                  ·
                    refine ⟨496781750131255311863147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5299005334733389993206901 496781750131255311863147)
                    ·
                      rfl

theorem cell23_2902437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 5].length) (baseStart_2902437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902437 prefixEnd_2902437 := by exact prefixLift 2902437
  have htrace : WordTrace (prefixWord ++ tailWord_2902437) baseStart_2902437 baseEnd_2902437 := by
    simpa [prefixWord, tailWord_2902437, baseEnd_2902437] using wordTrace_append hprefix tailTrace_2902437
  have hstable : (prefixWord ++ tailWord_2902437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902437).length < 2 ^ (prefixWord ++ tailWord_2902437).sum := by decide
  have hdescent : baseEnd_2902437 < baseStart_2902437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902474 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 1, 6, 2]
def baseStart_2902474 : Nat := 118140960795 + 2902474 * 2 ^ 59
def prefixEnd_2902474 : Nat := 4983230072969 + 3 ^ 40 * 2902474 * 2
def baseEnd_2902474 : Nat := 1490364249177982290826771

theorem tailTrace_2902474 : CollatzResearch.WordTrace tailWord_2902474 prefixEnd_2902474 1490364249177982290826771 := by
  unfold tailWord_2902474
  simp only [CollatzResearch.WordTrace]
  refine ⟨26465480921709968984842619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70574615791226583959580317 26465480921709968984842619)
  ·
    refine ⟨39698221382564953477263929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26465480921709968984842619 39698221382564953477263929)
    ·
      refine ⟨29773666036923715107947947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39698221382564953477263929 29773666036923715107947947)
      ·
        refine ⟨44660499055385572661921921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29773666036923715107947947 44660499055385572661921921)
        ·
          refine ⟨33495374291539179496441441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44660499055385572661921921 33495374291539179496441441)
          ·
            refine ⟨25121530718654384622331081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33495374291539179496441441 25121530718654384622331081)
            ·
              refine ⟨18841148038990788466748311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25121530718654384622331081 18841148038990788466748311)
              ·
                refine ⟨28261722058486182700122467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18841148038990788466748311 28261722058486182700122467)
                ·
                  refine ⟨42392583087729274050183701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28261722058486182700122467 42392583087729274050183701)
                  ·
                    refine ⟨1987152332237309721102361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42392583087729274050183701 1987152332237309721102361)
                    ·
                      refine ⟨1490364249177982290826771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1987152332237309721102361 1490364249177982290826771)
                      ·
                        rfl

theorem cell23_2902474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 1, 6, 2].length) (baseStart_2902474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902474 prefixEnd_2902474 := by exact prefixLift 2902474
  have htrace : WordTrace (prefixWord ++ tailWord_2902474) baseStart_2902474 baseEnd_2902474 := by
    simpa [prefixWord, tailWord_2902474, baseEnd_2902474] using wordTrace_append hprefix tailTrace_2902474
  have hstable : (prefixWord ++ tailWord_2902474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902474).length < 2 ^ (prefixWord ++ tailWord_2902474).sum := by decide
  have hdescent : baseEnd_2902474 < baseStart_2902474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902518 : List Nat := [5, 1, 1, 1, 2, 1, 3, 4, 1, 4]
def baseStart_2902518 : Nat := 118140960795 + 2902518 * 2 ^ 59
def prefixEnd_2902518 : Nat := 4983230072969 + 3 ^ 40 * 2902518 * 2
def baseEnd_2902518 : Nat := 496795614108926706225523

theorem tailTrace_2902518 : CollatzResearch.WordTrace tailWord_2902518 prefixEnd_2902518 496795614108926706225523 := by
  unfold tailWord_2902518
  simp only [CollatzResearch.WordTrace]
  refine ⟨6616470531167529465873263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70575685665786980969314805 6616470531167529465873263)
  ·
    refine ⟨9924705796751294198809895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6616470531167529465873263 9924705796751294198809895)
    ·
      refine ⟨14887058695126941298214843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9924705796751294198809895 14887058695126941298214843)
      ·
        refine ⟨22330588042690411947322265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14887058695126941298214843 22330588042690411947322265)
        ·
          refine ⟨16747941032017808960491699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22330588042690411947322265 16747941032017808960491699)
          ·
            refine ⟨25121911548026713440737549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16747941032017808960491699 25121911548026713440737549)
            ·
              refine ⟨9420716830510017540276581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25121911548026713440737549 9420716830510017540276581)
              ·
                refine ⟨1766384405720628288801859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9420716830510017540276581 1766384405720628288801859)
                ·
                  refine ⟨2649576608580942433202789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1766384405720628288801859 2649576608580942433202789)
                  ·
                    refine ⟨496795614108926706225523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2649576608580942433202789 496795614108926706225523)
                    ·
                      rfl

theorem cell23_2902518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_2902518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902518 prefixEnd_2902518 := by exact prefixLift 2902518
  have htrace : WordTrace (prefixWord ++ tailWord_2902518) baseStart_2902518 baseEnd_2902518 := by
    simpa [prefixWord, tailWord_2902518, baseEnd_2902518] using wordTrace_append hprefix tailTrace_2902518
  have hstable : (prefixWord ++ tailWord_2902518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902518).length < 2 ^ (prefixWord ++ tailWord_2902518).sum := by decide
  have hdescent : baseEnd_2902518 < baseStart_2902518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902527 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 5, 5]
def baseStart_2902527 : Nat := 118140960795 + 2902527 * 2 ^ 59
def prefixEnd_2902527 : Nat := 4983230072969 + 3 ^ 40 * 2902527 * 2
def baseEnd_2902527 : Nat := 496797154550890194488009

theorem tailTrace_2902527 : CollatzResearch.WordTrace tailWord_2902527 prefixEnd_2902527 496797154550890194488009 := by
  unfold tailWord_2902527
  simp only [CollatzResearch.WordTrace]
  refine ⟨105863856755647865991049835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70575904503765243994033223 105863856755647865991049835)
  ·
    refine ⟨158795785133471798986574753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105863856755647865991049835 158795785133471798986574753)
    ·
      refine ⟨119096838850103849239931065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158795785133471798986574753 119096838850103849239931065)
      ·
        refine ⟨89322629137577886929948299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119096838850103849239931065 89322629137577886929948299)
        ·
          refine ⟨133983943706366830394922449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89322629137577886929948299 133983943706366830394922449)
          ·
            refine ⟨100487957779775122796191837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133983943706366830394922449 100487957779775122796191837)
            ·
              refine ⟨37682984167415671048571939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100487957779775122796191837 37682984167415671048571939)
              ·
                refine ⟨56524476251123506572857909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37682984167415671048571939 56524476251123506572857909)
                ·
                  refine ⟨5299169648542828741205429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56524476251123506572857909 5299169648542828741205429)
                  ·
                    refine ⟨496797154550890194488009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5299169648542828741205429 496797154550890194488009)
                    ·
                      rfl

theorem cell23_2902527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 5].length) (baseStart_2902527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902527 prefixEnd_2902527 := by exact prefixLift 2902527
  have htrace : WordTrace (prefixWord ++ tailWord_2902527) baseStart_2902527 baseEnd_2902527 := by
    simpa [prefixWord, tailWord_2902527, baseEnd_2902527] using wordTrace_append hprefix tailTrace_2902527
  have hstable : (prefixWord ++ tailWord_2902527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902527).length < 2 ^ (prefixWord ++ tailWord_2902527).sum := by decide
  have hdescent : baseEnd_2902527 < baseStart_2902527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902584 : List Nat := [2, 1, 2, 1, 4, 1, 3, 2, 1, 1, 5]
def baseStart_2902584 : Nat := 118140960795 + 2902584 * 2 ^ 59
def prefixEnd_2902584 : Nat := 4983230072969 + 3 ^ 40 * 2902584 * 2
def baseEnd_2902584 : Nat := 1490420732049976860451265

theorem tailTrace_2902584 : CollatzResearch.WordTrace tailWord_2902584 prefixEnd_2902584 1490420732049976860451265 := by
  unfold tailWord_2902584
  simp only [CollatzResearch.WordTrace]
  refine ⟨52932967858220682362937403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70577290477627576483916537 52932967858220682362937403)
  ·
    refine ⟨79399451787331023544406105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52932967858220682362937403 79399451787331023544406105)
    ·
      refine ⟨59549588840498267658304579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79399451787331023544406105 59549588840498267658304579)
      ·
        refine ⟨89324383260747401487456869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59549588840498267658304579 89324383260747401487456869)
        ·
          refine ⟨16748321861390137778898163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89324383260747401487456869 16748321861390137778898163)
          ·
            refine ⟨25122482792085206668347245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16748321861390137778898163 25122482792085206668347245)
            ·
              refine ⟨9420931047031952500630217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25122482792085206668347245 9420931047031952500630217)
              ·
                refine ⟨7065698285273964375472663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9420931047031952500630217 7065698285273964375472663)
                ·
                  refine ⟨10598547427910946563208995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7065698285273964375472663 10598547427910946563208995)
                  ·
                    refine ⟨15897821141866419844813493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10598547427910946563208995 15897821141866419844813493)
                    ·
                      refine ⟨1490420732049976860451265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15897821141866419844813493 1490420732049976860451265)
                      ·
                        rfl

theorem cell23_2902584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_2902584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902584 prefixEnd_2902584 := by exact prefixLift 2902584
  have htrace : WordTrace (prefixWord ++ tailWord_2902584) baseStart_2902584 baseEnd_2902584 := by
    simpa [prefixWord, tailWord_2902584, baseEnd_2902584] using wordTrace_append hprefix tailTrace_2902584
  have hstable : (prefixWord ++ tailWord_2902584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902584).length < 2 ^ (prefixWord ++ tailWord_2902584).sum := by decide
  have hdescent : baseEnd_2902584 < baseStart_2902584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902617 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 3, 9]
def baseStart_2902617 : Nat := 118140960795 + 2902617 * 2 ^ 59
def prefixEnd_2902617 : Nat := 4983230072969 + 3 ^ 40 * 2902617 * 2
def baseEnd_2902617 : Nat := 496812558970525077112871

theorem tailTrace_2902617 : CollatzResearch.WordTrace tailWord_2902617 prefixEnd_2902617 496812558970525077112871 := by
  unfold tailWord_2902617
  simp only [CollatzResearch.WordTrace]
  refine ⟨105867139325321811361826105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70578092883547874241217403 105867139325321811361826105)
  ·
    refine ⟨79400354493991358521369579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105867139325321811361826105 79400354493991358521369579)
    ·
      refine ⟨119100531740987037782054369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79400354493991358521369579 119100531740987037782054369)
      ·
        refine ⟨89325398805740278336540777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119100531740987037782054369 89325398805740278336540777)
        ·
          refine ⟨66994049104305208752405583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89325398805740278336540777 66994049104305208752405583)
          ·
            refine ⟨100491073656457813128608375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66994049104305208752405583 100491073656457813128608375)
            ·
              refine ⟨150736610484686719692912563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100491073656457813128608375 150736610484686719692912563)
              ·
                refine ⟨226104915727030079539368845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150736610484686719692912563 226104915727030079539368845)
                ·
                  refine ⟨84789343397636279827263317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226104915727030079539368845 84789343397636279827263317)
                  ·
                    refine ⟨496812558970525077112871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 84789343397636279827263317 496812558970525077112871)
                    ·
                      rfl

theorem cell23_2902617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 9].length) (baseStart_2902617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902617 prefixEnd_2902617 := by exact prefixLift 2902617
  have htrace : WordTrace (prefixWord ++ tailWord_2902617) baseStart_2902617 baseEnd_2902617 := by
    simpa [prefixWord, tailWord_2902617, baseEnd_2902617] using wordTrace_append hprefix tailTrace_2902617
  have hstable : (prefixWord ++ tailWord_2902617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902617).length < 2 ^ (prefixWord ++ tailWord_2902617).sum := by decide
  have hdescent : baseEnd_2902617 < baseStart_2902617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902632 : List Nat := [2, 1, 4, 3, 2, 2, 1, 1, 3, 2, 2]
def baseStart_2902632 : Nat := 118140960795 + 2902632 * 2 ^ 59
def prefixEnd_2902632 : Nat := 4983230072969 + 3 ^ 40 * 2902632 * 2
def baseEnd_2902632 : Nat := 1490445379121392672651045

theorem tailTrace_2902632 : CollatzResearch.WordTrace tailWord_2902632 prefixEnd_2902632 1490445379121392672651045 := by
  unfold tailWord_2902632
  simp only [CollatzResearch.WordTrace]
  refine ⟨52933843210133734461811075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70578457613511645949081433 52933843210133734461811075)
  ·
    refine ⟨79400764815200601692716613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52933843210133734461811075 79400764815200601692716613)
    ·
      refine ⟨14887643402850112817384365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79400764815200601692716613 14887643402850112817384365)
      ·
        refine ⟨5582866276068792306519137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14887643402850112817384365 5582866276068792306519137)
        ·
          refine ⟨4187149707051594229889353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5582866276068792306519137 4187149707051594229889353)
          ·
            refine ⟨3140362280288695672417015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4187149707051594229889353 3140362280288695672417015)
            ·
              refine ⟨4710543420433043508625523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3140362280288695672417015 4710543420433043508625523)
              ·
                refine ⟨7065815130649565262938285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4710543420433043508625523 7065815130649565262938285)
                ·
                  refine ⟨2649680673993586973601857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7065815130649565262938285 2649680673993586973601857)
                  ·
                    refine ⟨1987260505495190230201393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2649680673993586973601857 1987260505495190230201393)
                    ·
                      refine ⟨1490445379121392672651045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1987260505495190230201393 1490445379121392672651045)
                      ·
                        rfl

theorem cell23_2902632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_2902632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902632 prefixEnd_2902632 := by exact prefixLift 2902632
  have htrace : WordTrace (prefixWord ++ tailWord_2902632) baseStart_2902632 baseEnd_2902632 := by
    simpa [prefixWord, tailWord_2902632, baseEnd_2902632] using wordTrace_append hprefix tailTrace_2902632
  have hstable : (prefixWord ++ tailWord_2902632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902632).length < 2 ^ (prefixWord ++ tailWord_2902632).sum := by decide
  have hdescent : baseEnd_2902632 < baseStart_2902632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902634 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 2, 7]
def baseStart_2902634 : Nat := 118140960795 + 2902634 * 2 ^ 59
def prefixEnd_2902634 : Nat := 4983230072969 + 3 ^ 40 * 2902634 * 2
def baseEnd_2902634 : Nat := 496815468694233888275345

theorem tailTrace_2902634 : CollatzResearch.WordTrace tailWord_2902634 prefixEnd_2902634 496815468694233888275345 := by
  unfold tailWord_2902634
  simp only [CollatzResearch.WordTrace]
  refine ⟨26466939841565055816298739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70578506244173482176796637 26466939841565055816298739)
  ·
    refine ⟨39700409762347583724448109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26466939841565055816298739 39700409762347583724448109)
    ·
      refine ⟨14887653660880343896668041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39700409762347583724448109 14887653660880343896668041)
      ·
        refine ⟨11165740245660257922501031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14887653660880343896668041 11165740245660257922501031)
        ·
          refine ⟨16748610368490386883751547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11165740245660257922501031 16748610368490386883751547)
          ·
            refine ⟨25122915552735580325627321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16748610368490386883751547 25122915552735580325627321)
            ·
              refine ⟨18842186664551685244220491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25122915552735580325627321 18842186664551685244220491)
              ·
                refine ⟨28263279996827527866330737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18842186664551685244220491 28263279996827527866330737)
                ·
                  refine ⟨21197459997620645899748053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28263279996827527866330737 21197459997620645899748053)
                  ·
                    refine ⟨496815468694233888275345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21197459997620645899748053 496815468694233888275345)
                    ·
                      rfl

theorem cell23_2902634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_2902634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902634 prefixEnd_2902634 := by exact prefixLift 2902634
  have htrace : WordTrace (prefixWord ++ tailWord_2902634) baseStart_2902634 baseEnd_2902634 := by
    simpa [prefixWord, tailWord_2902634, baseEnd_2902634] using wordTrace_append hprefix tailTrace_2902634
  have hstable : (prefixWord ++ tailWord_2902634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902634).length < 2 ^ (prefixWord ++ tailWord_2902634).sum := by decide
  have hdescent : baseEnd_2902634 < baseStart_2902634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902642 : List Nat := [3, 2, 1, 2, 5, 1, 2, 1, 2, 4]
def baseStart_2902642 : Nat := 118140960795 + 2902642 * 2 ^ 59
def prefixEnd_2902642 : Nat := 4983230072969 + 3 ^ 40 * 2902642 * 2
def baseEnd_2902642 : Nat := 496816837975979211175333

theorem tailTrace_2902642 : CollatzResearch.WordTrace tailWord_2902642 prefixEnd_2902642 496816837975979211175333 := by
  unfold tailWord_2902642
  simp only [CollatzResearch.WordTrace]
  refine ⟨26467012787557810157871545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70578700766820827087657453 26467012787557810157871545)
  ·
    refine ⟨19850259590668357618403659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26467012787557810157871545 19850259590668357618403659)
    ·
      refine ⟨29775389386002536427605489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19850259590668357618403659 29775389386002536427605489)
      ·
        refine ⟨22331542039501902320704117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29775389386002536427605489 22331542039501902320704117)
        ·
          refine ⟨2093582066203303342566011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22331542039501902320704117 2093582066203303342566011)
          ·
            refine ⟨3140373099304955013849017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2093582066203303342566011 3140373099304955013849017)
            ·
              refine ⟨2355279824478716260386763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3140373099304955013849017 2355279824478716260386763)
              ·
                refine ⟨3532919736718074390580145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2355279824478716260386763 3532919736718074390580145)
                ·
                  refine ⟨2649689802538555792935109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3532919736718074390580145 2649689802538555792935109)
                  ·
                    refine ⟨496816837975979211175333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2649689802538555792935109 496816837975979211175333)
                    ·
                      rfl

theorem cell23_2902642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_2902642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902642 prefixEnd_2902642 := by exact prefixLift 2902642
  have htrace : WordTrace (prefixWord ++ tailWord_2902642) baseStart_2902642 baseEnd_2902642 := by
    simpa [prefixWord, tailWord_2902642, baseEnd_2902642] using wordTrace_append hprefix tailTrace_2902642
  have hstable : (prefixWord ++ tailWord_2902642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902642).length < 2 ^ (prefixWord ++ tailWord_2902642).sum := by decide
  have hdescent : baseEnd_2902642 < baseStart_2902642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902671 : List Nat := [1, 1, 2, 1, 1, 1, 1, 8, 1, 4, 2]
def baseStart_2902671 : Nat := 118140960795 + 2902671 * 2 ^ 59
def prefixEnd_2902671 : Nat := 4983230072969 + 3 ^ 40 * 2902671 * 2
def baseEnd_2902671 : Nat := 1490465404866918020063365

theorem tailTrace_2902671 : CollatzResearch.WordTrace tailWord_2902671 prefixEnd_2902671 1490465404866918020063365 := by
  unfold tailWord_2902671
  simp only [CollatzResearch.WordTrace]
  refine ⟨105869108867126178584291867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70579405911417452389527911 105869108867126178584291867)
  ·
    refine ⟨158803663300689267876437801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105869108867126178584291867 158803663300689267876437801)
    ·
      refine ⟨119102747475516950907328351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158803663300689267876437801 119102747475516950907328351)
      ·
        refine ⟨178654121213275426360992527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119102747475516950907328351 178654121213275426360992527)
        ·
          refine ⟨267981181819913139541488791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178654121213275426360992527 267981181819913139541488791)
          ·
            refine ⟨401971772729869709312233187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267981181819913139541488791 401971772729869709312233187)
            ·
              refine ⟨602957659094804563968349781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401971772729869709312233187 602957659094804563968349781)
              ·
                refine ⟨7065910067517240984004099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 602957659094804563968349781 7065910067517240984004099)
                ·
                  refine ⟨10598865101275861476006149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7065910067517240984004099 10598865101275861476006149)
                  ·
                    refine ⟨1987287206489224026751153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10598865101275861476006149 1987287206489224026751153)
                    ·
                      refine ⟨1490465404866918020063365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1987287206489224026751153 1490465404866918020063365)
                      ·
                        rfl

theorem cell23_2902671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 4, 2].length) (baseStart_2902671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902671 prefixEnd_2902671 := by exact prefixLift 2902671
  have htrace : WordTrace (prefixWord ++ tailWord_2902671) baseStart_2902671 baseEnd_2902671 := by
    simpa [prefixWord, tailWord_2902671, baseEnd_2902671] using wordTrace_append hprefix tailTrace_2902671
  have hstable : (prefixWord ++ tailWord_2902671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902671).length < 2 ^ (prefixWord ++ tailWord_2902671).sum := by decide
  have hdescent : baseEnd_2902671 < baseStart_2902671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902682 : List Nat := [3, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3]
def baseStart_2902682 : Nat := 118140960795 + 2902682 * 2 ^ 59
def prefixEnd_2902682 : Nat := 4983230072969 + 3 ^ 40 * 2902682 * 2
def baseEnd_2902682 : Nat := 1490471053154117477025815

theorem tailTrace_2902682 : CollatzResearch.WordTrace tailWord_2902682 prefixEnd_2902682 1490471053154117477025815 := by
  unfold tailWord_2902682
  simp only [CollatzResearch.WordTrace]
  refine ⟨26467377517521581865735575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70579673380057551641961533 26467377517521581865735575)
  ·
    refine ⟨39701066276282372798603363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26467377517521581865735575 39701066276282372798603363)
    ·
      refine ⟨59551599414423559197905045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39701066276282372798603363 59551599414423559197905045)
      ·
        refine ⟨2791481222551104337401799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59551599414423559197905045 2791481222551104337401799)
        ·
          refine ⟨4187221833826656506102699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2791481222551104337401799 4187221833826656506102699)
          ·
            refine ⟨6280832750739984759154049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4187221833826656506102699 6280832750739984759154049)
            ·
              refine ⟨4710624563054988569365537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6280832750739984759154049 4710624563054988569365537)
              ·
                refine ⟨3532968422291241427024153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4710624563054988569365537 3532968422291241427024153)
                ·
                  refine ⟨2649726316718431070268115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3532968422291241427024153 2649726316718431070268115)
                  ·
                    refine ⟨3974589475077646605402173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2649726316718431070268115 3974589475077646605402173)
                    ·
                      refine ⟨1490471053154117477025815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3974589475077646605402173 1490471053154117477025815)
                      ·
                        rfl

theorem cell23_2902682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_2902682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902682 prefixEnd_2902682 := by exact prefixLift 2902682
  have htrace : WordTrace (prefixWord ++ tailWord_2902682) baseStart_2902682 baseEnd_2902682 := by
    simpa [prefixWord, tailWord_2902682, baseEnd_2902682] using wordTrace_append hprefix tailTrace_2902682
  have hstable : (prefixWord ++ tailWord_2902682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902682).length < 2 ^ (prefixWord ++ tailWord_2902682).sum := by decide
  have hdescent : baseEnd_2902682 < baseStart_2902682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902701 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_2902701 : Nat := 118140960795 + 2902701 * 2 ^ 59
def prefixEnd_2902701 : Nat := 4983230072969 + 3 ^ 40 * 2902701 * 2
def baseEnd_2902701 : Nat := 1490480809286552902688227

theorem tailTrace_2902701 : CollatzResearch.WordTrace tailWord_2902701 prefixEnd_2902701 1490480809286552902688227 := by
  unfold tailWord_2902701
  simp only [CollatzResearch.WordTrace]
  refine ⟨105870203057017493707883957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70580135371344995805255971 105870203057017493707883957)
  ·
    refine ⟨9925331536595390035114121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105870203057017493707883957 9925331536595390035114121)
    ·
      refine ⟨7443998652446542526335591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9925331536595390035114121 7443998652446542526335591)
      ·
        refine ⟨11165997978669813789503387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7443998652446542526335591 11165997978669813789503387)
        ·
          refine ⟨16748996968004720684255081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11165997978669813789503387 16748996968004720684255081)
          ·
            refine ⟨12561747726003540513191311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16748996968004720684255081 12561747726003540513191311)
            ·
              refine ⟨18842621589005310769786967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12561747726003540513191311 18842621589005310769786967)
              ·
                refine ⟨28263932383507966154680451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18842621589005310769786967 28263932383507966154680451)
                ·
                  refine ⟨42395898575261949232020677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28263932383507966154680451 42395898575261949232020677)
                  ·
                    refine ⟨7949230982861615481003877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42395898575261949232020677 7949230982861615481003877)
                    ·
                      refine ⟨1490480809286552902688227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7949230982861615481003877 1490480809286552902688227)
                      ·
                        rfl

theorem cell23_2902701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_2902701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902701 prefixEnd_2902701 := by exact prefixLift 2902701
  have htrace : WordTrace (prefixWord ++ tailWord_2902701) baseStart_2902701 baseEnd_2902701 := by
    simpa [prefixWord, tailWord_2902701, baseEnd_2902701] using wordTrace_append hprefix tailTrace_2902701
  have hstable : (prefixWord ++ tailWord_2902701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902701).length < 2 ^ (prefixWord ++ tailWord_2902701).sum := by decide
  have hdescent : baseEnd_2902701 < baseStart_2902701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902711 : List Nat := [1, 1, 3, 1, 6, 1, 1, 2, 7]
def baseStart_2902711 : Nat := 118140960795 + 2902711 * 2 ^ 59
def prefixEnd_2902711 : Nat := 4983230072969 + 3 ^ 40 * 2902711 * 2
def baseEnd_2902711 : Nat := 165609549343677540395909

theorem tailTrace_2902711 : CollatzResearch.WordTrace tailWord_2902711 prefixEnd_2902711 165609549343677540395909 := by
  unfold tailWord_2902711
  simp only [CollatzResearch.WordTrace]
  refine ⟨105870567786981265415747987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70580378524654176943831991 105870567786981265415747987)
  ·
    refine ⟨158805851680471898123621981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105870567786981265415747987 158805851680471898123621981)
    ·
      refine ⟨59552194380176961796358243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158805851680471898123621981 59552194380176961796358243)
      ·
        refine ⟨89328291570265442694537365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59552194380176961796358243 89328291570265442694537365)
        ·
          refine ⟨4187263667356192626306439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 89328291570265442694537365 4187263667356192626306439)
          ·
            refine ⟨6280895501034288939459659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4187263667356192626306439 6280895501034288939459659)
            ·
              refine ⟨9421343251551433409189489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6280895501034288939459659 9421343251551433409189489)
              ·
                refine ⟨7066007438663575056892117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9421343251551433409189489 7066007438663575056892117)
                ·
                  refine ⟨165609549343677540395909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7066007438663575056892117 165609549343677540395909)
                  ·
                    rfl

theorem cell23_2902711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 7].length) (baseStart_2902711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902711 prefixEnd_2902711 := by exact prefixLift 2902711
  have htrace : WordTrace (prefixWord ++ tailWord_2902711) baseStart_2902711 baseEnd_2902711 := by
    simpa [prefixWord, tailWord_2902711, baseEnd_2902711] using wordTrace_append hprefix tailTrace_2902711
  have hstable : (prefixWord ++ tailWord_2902711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902711).length < 2 ^ (prefixWord ++ tailWord_2902711).sum := by decide
  have hdescent : baseEnd_2902711 < baseStart_2902711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902728 : List Nat := [2, 1, 3, 1, 2, 4, 2, 3, 5]
def baseStart_2902728 : Nat := 118140960795 + 2902728 * 2 ^ 59
def prefixEnd_2902728 : Nat := 4983230072969 + 3 ^ 40 * 2902728 * 2
def baseEnd_2902728 : Nat := 165610519251580477450067

theorem tailTrace_2902728 : CollatzResearch.WordTrace tailWord_2902728 prefixEnd_2902728 165610519251580477450067 := by
  unfold tailWord_2902728
  simp only [CollatzResearch.WordTrace]
  refine ⟨52935593913959838659558419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70580791885279784879411225 52935593913959838659558419)
  ·
    refine ⟨79403390870939757989337629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52935593913959838659558419 79403390870939757989337629)
    ·
      refine ⟨29776271576602409246001611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79403390870939757989337629 29776271576602409246001611)
      ·
        refine ⟨44664407364903613869002417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29776271576602409246001611 44664407364903613869002417)
        ·
          refine ⟨33498305523677710401751813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44664407364903613869002417 33498305523677710401751813)
          ·
            refine ⟨6280932285689570700328465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33498305523677710401751813 6280932285689570700328465)
            ·
              refine ⟨4710699214267178025246349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6280932285689570700328465 4710699214267178025246349)
              ·
                refine ⟨1766512205350191759467381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4710699214267178025246349 1766512205350191759467381)
                ·
                  refine ⟨165610519251580477450067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1766512205350191759467381 165610519251580477450067)
                  ·
                    rfl

theorem cell23_2902728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3, 5].length) (baseStart_2902728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902728 prefixEnd_2902728 := by exact prefixLift 2902728
  have htrace : WordTrace (prefixWord ++ tailWord_2902728) baseStart_2902728 baseEnd_2902728 := by
    simpa [prefixWord, tailWord_2902728, baseEnd_2902728] using wordTrace_append hprefix tailTrace_2902728
  have hstable : (prefixWord ++ tailWord_2902728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902728).length < 2 ^ (prefixWord ++ tailWord_2902728).sum := by decide
  have hdescent : baseEnd_2902728 < baseStart_2902728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902781 : List Nat := [1, 4, 1, 1, 1, 1, 3, 3, 1, 4, 3]
def baseStart_2902781 : Nat := 118140960795 + 2902781 * 2 ^ 59
def prefixEnd_2902781 : Nat := 4983230072969 + 3 ^ 40 * 2902781 * 2
def baseEnd_2902781 : Nat := 1490521887738912589687859

theorem tailTrace_2902781 : CollatzResearch.WordTrace tailWord_2902781 prefixEnd_2902781 1490521887738912589687859 := by
  unfold tailWord_2902781
  simp only [CollatzResearch.WordTrace]
  refine ⟨105873120896727667370796197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70582080597818444913864131 105873120896727667370796197)
  ·
    refine ⟨19851210168136437632024287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105873120896727667370796197 19851210168136437632024287)
    ·
      refine ⟨29776815252204656448036431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19851210168136437632024287 29776815252204656448036431)
      ·
        refine ⟨44665222878306984672054647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29776815252204656448036431 44665222878306984672054647)
        ·
          refine ⟨66997834317460477008081971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44665222878306984672054647 66997834317460477008081971)
          ·
            refine ⟨100496751476190715512122957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66997834317460477008081971 100496751476190715512122957)
            ·
              refine ⟨37686281803571518317046109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100496751476190715512122957 37686281803571518317046109)
              ·
                refine ⟨14132355676339319368892291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37686281803571518317046109 14132355676339319368892291)
                ·
                  refine ⟨21198533514508979053338437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14132355676339319368892291 21198533514508979053338437)
                  ·
                    refine ⟨3974725033970433572500957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21198533514508979053338437 3974725033970433572500957)
                    ·
                      refine ⟨1490521887738912589687859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3974725033970433572500957 1490521887738912589687859)
                      ·
                        rfl

theorem cell23_2902781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_2902781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902781 prefixEnd_2902781 := by exact prefixLift 2902781
  have htrace : WordTrace (prefixWord ++ tailWord_2902781) baseStart_2902781 baseEnd_2902781 := by
    simpa [prefixWord, tailWord_2902781, baseEnd_2902781] using wordTrace_append hprefix tailTrace_2902781
  have hstable : (prefixWord ++ tailWord_2902781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902781).length < 2 ^ (prefixWord ++ tailWord_2902781).sum := by decide
  have hdescent : baseEnd_2902781 < baseStart_2902781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902818 : List Nat := [3, 3, 1, 1, 2, 3, 1, 3, 6]
def baseStart_2902818 : Nat := 118140960795 + 2902818 * 2 ^ 59
def prefixEnd_2902818 : Nat := 4983230072969 + 3 ^ 40 * 2902818 * 2
def baseEnd_2902818 : Nat := 165615654058125438325021

theorem tailTrace_2902818 : CollatzResearch.WordTrace tailWord_2902818 prefixEnd_2902818 165615654058125438325021 := by
  unfold tailWord_2902818
  simp only [CollatzResearch.WordTrace]
  refine ⟨26468617599398405672473277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70582980265062415126595405 26468617599398405672473277)
  ·
    refine ⟨9925731599774402127177479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26468617599398405672473277 9925731599774402127177479)
    ·
      refine ⟨14888597399661603190766219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9925731599774402127177479 14888597399661603190766219)
      ·
        refine ⟨22332896099492404786149329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14888597399661603190766219 22332896099492404786149329)
        ·
          refine ⟨16749672074619303589611997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22332896099492404786149329 16749672074619303589611997)
          ·
            refine ⟨6281127027982238846104499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16749672074619303589611997 6281127027982238846104499)
            ·
              refine ⟨9421690541973358269156749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6281127027982238846104499 9421690541973358269156749)
              ·
                refine ⟨3533133953240009350933781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9421690541973358269156749 3533133953240009350933781)
                ·
                  refine ⟨165615654058125438325021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3533133953240009350933781 165615654058125438325021)
                  ·
                    rfl

theorem cell23_2902818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_2902818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902818 prefixEnd_2902818 := by exact prefixLift 2902818
  have htrace : WordTrace (prefixWord ++ tailWord_2902818) baseStart_2902818 baseEnd_2902818 := by
    simpa [prefixWord, tailWord_2902818, baseEnd_2902818] using wordTrace_append hprefix tailTrace_2902818
  have hstable : (prefixWord ++ tailWord_2902818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902818).length < 2 ^ (prefixWord ++ tailWord_2902818).sum := by decide
  have hdescent : baseEnd_2902818 < baseStart_2902818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902828 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 3]
def baseStart_2902828 : Nat := 118140960795 + 2902828 * 2 ^ 59
def prefixEnd_2902828 : Nat := 4983230072969 + 3 ^ 40 * 2902828 * 2
def baseEnd_2902828 : Nat := 1490546021329673905800143

theorem tailTrace_2902828 : CollatzResearch.WordTrace tailWord_2902828 prefixEnd_2902828 1490546021329673905800143 := by
  unfold tailWord_2902828
  simp only [CollatzResearch.WordTrace]
  refine ⟨52937417563778697198878569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70583223418371596265171425 52937417563778697198878569)
  ·
    refine ⟨39703063172834022899158927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52937417563778697198878569 39703063172834022899158927)
    ·
      refine ⟨59554594759251034348738391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39703063172834022899158927 59554594759251034348738391)
      ·
        refine ⟨89331892138876551523107587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59554594759251034348738391 89331892138876551523107587)
        ·
          refine ⟨133997838208314827284661381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89331892138876551523107587 133997838208314827284661381)
          ·
            refine ⟨25124594664059030115874009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133997838208314827284661381 25124594664059030115874009)
            ·
              refine ⟨18843445998044272586905507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25124594664059030115874009 18843445998044272586905507)
              ·
                refine ⟨28265168997066408880358261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18843445998044272586905507 28265168997066408880358261)
                ·
                  refine ⟨2649859593474975832533587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28265168997066408880358261 2649859593474975832533587)
                  ·
                    refine ⟨3974789390212463748800381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2649859593474975832533587 3974789390212463748800381)
                    ·
                      refine ⟨1490546021329673905800143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3974789390212463748800381 1490546021329673905800143)
                      ·
                        rfl

theorem cell23_2902828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 3].length) (baseStart_2902828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902828 prefixEnd_2902828 := by exact prefixLift 2902828
  have htrace : WordTrace (prefixWord ++ tailWord_2902828) baseStart_2902828 baseEnd_2902828 := by
    simpa [prefixWord, tailWord_2902828, baseEnd_2902828] using wordTrace_append hprefix tailTrace_2902828
  have hstable : (prefixWord ++ tailWord_2902828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902828).length < 2 ^ (prefixWord ++ tailWord_2902828).sum := by decide
  have hdescent : baseEnd_2902828 < baseStart_2902828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902852 : List Nat := [2, 3, 4, 2, 1, 1, 2, 2, 6]
def baseStart_2902852 : Nat := 118140960795 + 2902852 * 2 ^ 59
def prefixEnd_2902852 : Nat := 4983230072969 + 3 ^ 40 * 2902852 * 2
def baseEnd_2902852 : Nat := 165617593873931312433337

theorem tailTrace_2902852 : CollatzResearch.WordTrace tailWord_2902852 prefixEnd_2902852 165617593873931312433337 := by
  unfold tailWord_2902852
  simp only [CollatzResearch.WordTrace]
  refine ⟨52937855239735223248315405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70583806986313630997753873 52937855239735223248315405)
  ·
    refine ⟨19851695714900708718118277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52937855239735223248315405 19851695714900708718118277)
    ·
      refine ⟨3722192946543882884647177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19851695714900708718118277 3722192946543882884647177)
      ·
        refine ⟨2791644709907912163485383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3722192946543882884647177 2791644709907912163485383)
        ·
          refine ⟨4187467064861868245228075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2791644709907912163485383 4187467064861868245228075)
          ·
            refine ⟨6281200597292802367842113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4187467064861868245228075 6281200597292802367842113)
            ·
              refine ⟨4710900447969601775881585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6281200597292802367842113 4710900447969601775881585)
              ·
                refine ⟨3533175335977201331911189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4710900447969601775881585 3533175335977201331911189)
                ·
                  refine ⟨165617593873931312433337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3533175335977201331911189 165617593873931312433337)
                  ·
                    rfl

theorem cell23_2902852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 6].length) (baseStart_2902852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902852 prefixEnd_2902852 := by exact prefixLift 2902852
  have htrace : WordTrace (prefixWord ++ tailWord_2902852) baseStart_2902852 baseEnd_2902852 := by
    simpa [prefixWord, tailWord_2902852, baseEnd_2902852] using wordTrace_append hprefix tailTrace_2902852
  have hstable : (prefixWord ++ tailWord_2902852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902852).length < 2 ^ (prefixWord ++ tailWord_2902852).sum := by decide
  have hdescent : baseEnd_2902852 < baseStart_2902852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902885 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 5, 2, 2]
def baseStart_2902885 : Nat := 118140960795 + 2902885 * 2 ^ 59
def prefixEnd_2902885 : Nat := 4983230072969 + 3 ^ 40 * 2902885 * 2
def baseEnd_2902885 : Nat := 1490575289726980182787381

theorem tailTrace_2902885 : CollatzResearch.WordTrace tailWord_2902885 prefixEnd_2902885 1490575289726980182787381 := by
  unfold tailWord_2902885
  simp only [CollatzResearch.WordTrace]
  refine ⟨105876914088350893132582109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70584609392233928755054739 105876914088350893132582109)
  ·
    refine ⟨39703842783131584924718291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105876914088350893132582109 39703842783131584924718291)
    ·
      refine ⟨59555764174697377387077437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39703842783131584924718291 59555764174697377387077437)
      ·
        refine ⟨22333411565511516520154039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59555764174697377387077437 22333411565511516520154039)
        ·
          refine ⟨33500117348267274780231059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22333411565511516520154039 33500117348267274780231059)
          ·
            refine ⟨50250176022400912170346589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33500117348267274780231059 50250176022400912170346589)
            ·
              refine ⟨18843816008400342063879971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50250176022400912170346589 18843816008400342063879971)
              ·
                refine ⟨28265724012600513095819957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18843816008400342063879971 28265724012600513095819957)
                ·
                  refine ⟨2649911626181298102733121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28265724012600513095819957 2649911626181298102733121)
                  ·
                    refine ⟨1987433719635973577049841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2649911626181298102733121 1987433719635973577049841)
                    ·
                      refine ⟨1490575289726980182787381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1987433719635973577049841 1490575289726980182787381)
                      ·
                        rfl

theorem cell23_2902885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_2902885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902885 prefixEnd_2902885 := by exact prefixLift 2902885
  have htrace : WordTrace (prefixWord ++ tailWord_2902885) baseStart_2902885 baseEnd_2902885 := by
    simpa [prefixWord, tailWord_2902885, baseEnd_2902885] using wordTrace_append hprefix tailTrace_2902885
  have hstable : (prefixWord ++ tailWord_2902885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902885).length < 2 ^ (prefixWord ++ tailWord_2902885).sum := by decide
  have hdescent : baseEnd_2902885 < baseStart_2902885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902898 : List Nat := [3, 2, 1, 2, 1, 1, 4, 2, 1, 2, 4]
def baseStart_2902898 : Nat := 118140960795 + 2902898 * 2 ^ 59
def prefixEnd_2902898 : Nat := 4983230072969 + 3 ^ 40 * 2902898 * 2
def baseEnd_2902898 : Nat := 1490581964975488631924821

theorem tailTrace_2902898 : CollatzResearch.WordTrace tailWord_2902898 prefixEnd_2902898 1490581964975488631924821 := by
  unfold tailWord_2902898
  simp only [CollatzResearch.WordTrace]
  refine ⟨26469347059325949088201337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70584925491535864235203565 26469347059325949088201337)
  ·
    refine ⟨19852010294494461816151003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26469347059325949088201337 19852010294494461816151003)
    ·
      refine ⟨29778015441741692724226505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19852010294494461816151003 29778015441741692724226505)
      ·
        refine ⟨22333511581306269543169879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29778015441741692724226505 22333511581306269543169879)
        ·
          refine ⟨33500267371959404314754819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22333511581306269543169879 33500267371959404314754819)
          ·
            refine ⟨50250401057939106472132229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33500267371959404314754819 50250401057939106472132229)
            ·
              refine ⟨9421950198363582463524793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50250401057939106472132229 9421950198363582463524793)
              ·
                refine ⟨7066462648772686847643595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9421950198363582463524793 7066462648772686847643595)
                ·
                  refine ⟨10599693973159030271465393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7066462648772686847643595 10599693973159030271465393)
                  ·
                    refine ⟨7949770479869272703599045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10599693973159030271465393 7949770479869272703599045)
                    ·
                      refine ⟨1490581964975488631924821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7949770479869272703599045 1490581964975488631924821)
                      ·
                        rfl

theorem cell23_2902898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_2902898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902898 prefixEnd_2902898 := by exact prefixLift 2902898
  have htrace : WordTrace (prefixWord ++ tailWord_2902898) baseStart_2902898 baseEnd_2902898 := by
    simpa [prefixWord, tailWord_2902898, baseEnd_2902898] using wordTrace_append hprefix tailTrace_2902898
  have hstable : (prefixWord ++ tailWord_2902898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902898).length < 2 ^ (prefixWord ++ tailWord_2902898).sum := by decide
  have hdescent : baseEnd_2902898 < baseStart_2902898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902902 : List Nat := [5, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4]
def baseStart_2902902 : Nat := 118140960795 + 2902902 * 2 ^ 59
def prefixEnd_2902902 : Nat := 4983230072969 + 3 ^ 40 * 2902902 * 2
def baseEnd_2902902 : Nat := 1490584018898106616274803

theorem tailTrace_2902902 : CollatzResearch.WordTrace tailWord_2902902 prefixEnd_2902902 1490584018898106616274803 := by
  unfold tailWord_2902902
  simp only [CollatzResearch.WordTrace]
  refine ⟨6617345883080581564746935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70585022752859536690633973 6617345883080581564746935)
  ·
    refine ⟨9926018824620872347120403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6617345883080581564746935 9926018824620872347120403)
    ·
      refine ⟨14889028236931308520680605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9926018824620872347120403 14889028236931308520680605)
      ·
        refine ⟨5583385588849240695255227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14889028236931308520680605 5583385588849240695255227)
        ·
          refine ⟨8375078383273861042882841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5583385588849240695255227 8375078383273861042882841)
          ·
            refine ⟨6281308787455395782162131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8375078383273861042882841 6281308787455395782162131)
            ·
              refine ⟨9421963181183093673243197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6281308787455395782162131 9421963181183093673243197)
              ·
                refine ⟨3533236192943660127466199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9421963181183093673243197 3533236192943660127466199)
                ·
                  refine ⟨5299854289415490191199299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3533236192943660127466199 5299854289415490191199299)
                  ·
                    refine ⟨7949781434123235286798949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5299854289415490191199299 7949781434123235286798949)
                    ·
                      refine ⟨1490584018898106616274803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7949781434123235286798949 1490584018898106616274803)
                      ·
                        rfl

theorem cell23_2902902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_2902902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902902 prefixEnd_2902902 := by exact prefixLift 2902902
  have htrace : WordTrace (prefixWord ++ tailWord_2902902) baseStart_2902902 baseEnd_2902902 := by
    simpa [prefixWord, tailWord_2902902, baseEnd_2902902] using wordTrace_append hprefix tailTrace_2902902
  have hstable : (prefixWord ++ tailWord_2902902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902902).length < 2 ^ (prefixWord ++ tailWord_2902902).sum := by decide
  have hdescent : baseEnd_2902902 < baseStart_2902902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902905 : List Nat := [1, 2, 1, 3, 2, 4, 1, 3, 1, 2, 3]
def baseStart_2902905 : Nat := 118140960795 + 2902905 * 2 ^ 59
def prefixEnd_2902905 : Nat := 4983230072969 + 3 ^ 40 * 2902905 * 2
def baseEnd_2902905 : Nat := 1490585559340070104537289

theorem tailTrace_2902905 : CollatzResearch.WordTrace tailWord_2902905 prefixEnd_2902905 1490585559340070104537289 := by
  unfold tailWord_2902905
  simp only [CollatzResearch.WordTrace]
  refine ⟨105877643548278436548310169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70585095698852291032206779 105877643548278436548310169)
  ·
    refine ⟨79408232661208827411232627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105877643548278436548310169 79408232661208827411232627)
    ·
      refine ⟨119112348991813241116848941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79408232661208827411232627 119112348991813241116848941)
      ·
        refine ⟨44667130871929965418818353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119112348991813241116848941 44667130871929965418818353)
        ·
          refine ⟨33500348153947474064113765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44667130871929965418818353 33500348153947474064113765)
          ·
            refine ⟨6281315278865151387021331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33500348153947474064113765 6281315278865151387021331)
            ·
              refine ⟨9421972918297727080531997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6281315278865151387021331 9421972918297727080531997)
              ·
                refine ⟨3533239844361647655199499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9421972918297727080531997 3533239844361647655199499)
                ·
                  refine ⟨5299859766542471482799249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3533239844361647655199499 5299859766542471482799249)
                  ·
                    refine ⟨3974894824906853612099437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5299859766542471482799249 3974894824906853612099437)
                    ·
                      refine ⟨1490585559340070104537289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3974894824906853612099437 1490585559340070104537289)
                      ·
                        rfl

theorem cell23_2902905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_2902905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902905 prefixEnd_2902905 := by exact prefixLift 2902905
  have htrace : WordTrace (prefixWord ++ tailWord_2902905) baseStart_2902905 baseEnd_2902905 := by
    simpa [prefixWord, tailWord_2902905, baseEnd_2902905] using wordTrace_append hprefix tailTrace_2902905
  have hstable : (prefixWord ++ tailWord_2902905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902905).length < 2 ^ (prefixWord ++ tailWord_2902905).sum := by decide
  have hdescent : baseEnd_2902905 < baseStart_2902905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902919 : List Nat := [1, 1, 4, 2, 3, 1, 2, 4, 1, 2, 2]
def baseStart_2902919 : Nat := 118140960795 + 2902919 * 2 ^ 59
def prefixEnd_2902919 : Nat := 4983230072969 + 3 ^ 40 * 2902919 * 2
def baseEnd_2902919 : Nat := 1490592748069233049762225

theorem tailTrace_2902919 : CollatzResearch.WordTrace tailWord_2902919 prefixEnd_2902919 1490592748069233049762225 := by
  unfold tailWord_2902919
  simp only [CollatzResearch.WordTrace]
  refine ⟨105878154170227716939319811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70585436113485144626213207 105878154170227716939319811)
  ·
    refine ⟨158817231255341575408979717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105878154170227716939319811 158817231255341575408979717)
    ·
      refine ⟨29778230860376545389183697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158817231255341575408979717 29778230860376545389183697)
      ·
        refine ⟨22333673145282409041887773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29778230860376545389183697 22333673145282409041887773)
        ·
          refine ⟨8375127429480903390707915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22333673145282409041887773 8375127429480903390707915)
          ·
            refine ⟨12562691144221355086061873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8375127429480903390707915 12562691144221355086061873)
            ·
              refine ⟨9422018358166016314546405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12562691144221355086061873 9422018358166016314546405)
              ·
                refine ⟨1766628442156128058977451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9422018358166016314546405 1766628442156128058977451)
                ·
                  refine ⟨2649942663234192088466177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1766628442156128058977451 2649942663234192088466177)
                  ·
                    refine ⟨1987456997425644066349633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2649942663234192088466177 1987456997425644066349633)
                    ·
                      refine ⟨1490592748069233049762225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1987456997425644066349633 1490592748069233049762225)
                      ·
                        rfl

theorem cell23_2902919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_2902919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902919 prefixEnd_2902919 := by exact prefixLift 2902919
  have htrace : WordTrace (prefixWord ++ tailWord_2902919) baseStart_2902919 baseEnd_2902919 := by
    simpa [prefixWord, tailWord_2902919, baseEnd_2902919] using wordTrace_append hprefix tailTrace_2902919
  have hstable : (prefixWord ++ tailWord_2902919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902919).length < 2 ^ (prefixWord ++ tailWord_2902919).sum := by decide
  have hdescent : baseEnd_2902919 < baseStart_2902919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2902988 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 1, 4, 4]
def baseStart_2902988 : Nat := 118140960795 + 2902988 * 2 ^ 59
def prefixEnd_2902988 : Nat := 4983230072969 + 3 ^ 40 * 2902988 * 2
def baseEnd_2902988 : Nat := 1490628178234393279799407

theorem tailTrace_2902988 : CollatzResearch.WordTrace tailWord_2902988 prefixEnd_2902988 1490628178234393279799407 := by
  unfold tailWord_2902988
  simp only [CollatzResearch.WordTrace]
  refine ⟨52940335403488870861790809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70587113871318494482387745 52940335403488870861790809)
  ·
    refine ⟨39705251552616653146343107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52940335403488870861790809 39705251552616653146343107)
    ·
      refine ⟨59557877328924979719514661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39705251552616653146343107 59557877328924979719514661)
      ·
        refine ⟨11167101999173433697408999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59557877328924979719514661 11167101999173433697408999)
        ·
          refine ⟨16750652998760150546113499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11167101999173433697408999 16750652998760150546113499)
          ·
            refine ⟨25125979498140225819170249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16750652998760150546113499 25125979498140225819170249)
            ·
              refine ⟨18844484623605169364377687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25125979498140225819170249 18844484623605169364377687)
              ·
                refine ⟨28266726935407754046566531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18844484623605169364377687 28266726935407754046566531)
                ·
                  refine ⟨42400090403111631069849797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28266726935407754046566531 42400090403111631069849797)
                  ·
                    refine ⟨7950016950583430825596837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42400090403111631069849797 7950016950583430825596837)
                    ·
                      refine ⟨1490628178234393279799407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7950016950583430825596837 1490628178234393279799407)
                      ·
                        rfl

theorem cell23_2902988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_2902988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2902988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2902988 prefixEnd_2902988 := by exact prefixLift 2902988
  have htrace : WordTrace (prefixWord ++ tailWord_2902988) baseStart_2902988 baseEnd_2902988 := by
    simpa [prefixWord, tailWord_2902988, baseEnd_2902988] using wordTrace_append hprefix tailTrace_2902988
  have hstable : (prefixWord ++ tailWord_2902988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2902988).length < 2 ^ (prefixWord ++ tailWord_2902988).sum := by decide
  have hdescent : baseEnd_2902988 < baseStart_2902988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2902988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903008 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 3]
def baseStart_2903008 : Nat := 118140960795 + 2903008 * 2 ^ 59
def prefixEnd_2903008 : Nat := 4983230072969 + 3 ^ 40 * 2903008 * 2
def baseEnd_2903008 : Nat := 1490638447847483201549315

theorem tailTrace_2903008 : CollatzResearch.WordTrace tailWord_2903008 prefixEnd_2903008 1490638447847483201549315 := by
  unfold tailWord_2903008
  simp only [CollatzResearch.WordTrace]
  refine ⟨52940700133452642569654839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70587600177936856759539785 52940700133452642569654839)
  ·
    refine ⟨79411050200178963854482259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52940700133452642569654839 79411050200178963854482259)
    ·
      refine ⟨119116575300268445781723389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79411050200178963854482259 119116575300268445781723389)
      ·
        refine ⟨44668715737600667168146271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119116575300268445781723389 44668715737600667168146271)
        ·
          refine ⟨67003073606401000752219407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44668715737600667168146271 67003073606401000752219407)
          ·
            refine ⟨100504610409601501128329111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67003073606401000752219407 100504610409601501128329111)
            ·
              refine ⟨150756915614402251692493667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100504610409601501128329111 150756915614402251692493667)
              ·
                refine ⟨226135373421603377538740501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150756915614402251692493667 226135373421603377538740501)
                ·
                  refine ⟨10600095629137658322128461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 226135373421603377538740501 10600095629137658322128461)
                  ·
                    refine ⟨3975035860926621870798173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10600095629137658322128461 3975035860926621870798173)
                    ·
                      refine ⟨1490638447847483201549315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3975035860926621870798173 1490638447847483201549315)
                      ·
                        rfl

theorem cell23_2903008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_2903008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903008 prefixEnd_2903008 := by exact prefixLift 2903008
  have htrace : WordTrace (prefixWord ++ tailWord_2903008) baseStart_2903008 baseEnd_2903008 := by
    simpa [prefixWord, tailWord_2903008, baseEnd_2903008] using wordTrace_append hprefix tailTrace_2903008
  have hstable : (prefixWord ++ tailWord_2903008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903008).length < 2 ^ (prefixWord ++ tailWord_2903008).sum := by decide
  have hdescent : baseEnd_2903008 < baseStart_2903008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903065 : List Nat := [1, 2, 1, 2, 1, 1, 7, 1, 2, 1, 4]
def baseStart_2903065 : Nat := 118140960795 + 2903065 * 2 ^ 59
def prefixEnd_2903065 : Nat := 4983230072969 + 3 ^ 40 * 2903065 * 2
def baseEnd_2903065 : Nat := 1490667716244789478536553

theorem tailTrace_2903065 : CollatzResearch.WordTrace tailWord_2903065 prefixEnd_2903065 1490667716244789478536553 := by
  unfold tailWord_2903065
  simp only [CollatzResearch.WordTrace]
  refine ⟨105883479227698783874134649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70588986151799189249423099 105883479227698783874134649)
  ·
    refine ⟨79412609420774087905600987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105883479227698783874134649 79412609420774087905600987)
    ·
      refine ⟨119118914131161131858401481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79412609420774087905600987 119118914131161131858401481)
      ·
        refine ⟨89339185598370848893801111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119118914131161131858401481 89339185598370848893801111)
        ·
          refine ⟨134008778397556273340701667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89339185598370848893801111 134008778397556273340701667)
          ·
            refine ⟨201013167596334410011052501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134008778397556273340701667 201013167596334410011052501)
            ·
              refine ⟨4711246115539087734634043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 201013167596334410011052501 4711246115539087734634043)
              ·
                refine ⟨7066869173308631601951065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4711246115539087734634043 7066869173308631601951065)
                ·
                  refine ⟨5300151879981473701463299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7066869173308631601951065 5300151879981473701463299)
                  ·
                    refine ⟨7950227819972210552194949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5300151879981473701463299 7950227819972210552194949)
                    ·
                      refine ⟨1490667716244789478536553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7950227819972210552194949 1490667716244789478536553)
                      ·
                        rfl

theorem cell23_2903065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 1, 4].length) (baseStart_2903065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903065 prefixEnd_2903065 := by exact prefixLift 2903065
  have htrace : WordTrace (prefixWord ++ tailWord_2903065) baseStart_2903065 baseEnd_2903065 := by
    simpa [prefixWord, tailWord_2903065, baseEnd_2903065] using wordTrace_append hprefix tailTrace_2903065
  have hstable : (prefixWord ++ tailWord_2903065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903065).length < 2 ^ (prefixWord ++ tailWord_2903065).sum := by decide
  have hdescent : baseEnd_2903065 < baseStart_2903065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903088 : List Nat := [2, 1, 1, 1, 2, 4, 3, 1, 8]
def baseStart_2903088 : Nat := 118140960795 + 2903088 * 2 ^ 59
def prefixEnd_2903088 : Nat := 4983230072969 + 3 ^ 40 * 2903088 * 2
def baseEnd_2903088 : Nat := 165631058477760320949883

theorem tailTrace_2903088 : CollatzResearch.WordTrace tailWord_2903088 prefixEnd_2903088 165631058477760320949883 := by
  unfold tailWord_2903088
  simp only [CollatzResearch.WordTrace]
  refine ⟨52942159053307729401110959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70589545404410305868147945 52942159053307729401110959)
  ·
    refine ⟨79413238579961594101666439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52942159053307729401110959 79413238579961594101666439)
    ·
      refine ⟨119119857869942391152499659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79413238579961594101666439 119119857869942391152499659)
      ·
        refine ⟨178679786804913586728749489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119119857869942391152499659 178679786804913586728749489)
        ·
          refine ⟨134009840103685190046562117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178679786804913586728749489 134009840103685190046562117)
          ·
            refine ⟨25126845019440973133730397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134009840103685190046562117 25126845019440973133730397)
            ·
              refine ⟨9422566882290364925148899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25126845019440973133730397 9422566882290364925148899)
              ·
                refine ⟨14133850323435547387723349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9422566882290364925148899 14133850323435547387723349)
                ·
                  refine ⟨165631058477760320949883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14133850323435547387723349 165631058477760320949883)
                  ·
                    rfl

theorem cell23_2903088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 8].length) (baseStart_2903088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903088 prefixEnd_2903088 := by exact prefixLift 2903088
  have htrace : WordTrace (prefixWord ++ tailWord_2903088) baseStart_2903088 baseEnd_2903088 := by
    simpa [prefixWord, tailWord_2903088, baseEnd_2903088] using wordTrace_append hprefix tailTrace_2903088
  have hstable : (prefixWord ++ tailWord_2903088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903088).length < 2 ^ (prefixWord ++ tailWord_2903088).sum := by decide
  have hdescent : baseEnd_2903088 < baseStart_2903088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903102 : List Nat := [4, 2, 1, 3, 1, 1, 1, 2, 1, 4, 3]
def baseStart_2903102 : Nat := 118140960795 + 2903102 * 2 ^ 59
def prefixEnd_2903102 : Nat := 4983230072969 + 3 ^ 40 * 2903102 * 2
def baseEnd_2903102 : Nat := 1490686715029005833773883

theorem tailTrace_2903102 : CollatzResearch.WordTrace tailWord_2903102 prefixEnd_2903102 1490686715029005833773883 := by
  unfold tailWord_2903102
  simp only [CollatzResearch.WordTrace]
  refine ⟨13235603591070592399153945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70589885819043159462154373 13235603591070592399153945)
  ·
    refine ⟨9926702693302944299365459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13235603591070592399153945 9926702693302944299365459)
    ·
      refine ⟨14890054039954416449048189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9926702693302944299365459 14890054039954416449048189)
      ·
        refine ⟨5583770264982906168393071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14890054039954416449048189 5583770264982906168393071)
        ·
          refine ⟨8375655397474359252589607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5583770264982906168393071 8375655397474359252589607)
          ·
            refine ⟨12563483096211538878884411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8375655397474359252589607 12563483096211538878884411)
            ·
              refine ⟨18845224644317308318326617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12563483096211538878884411 18845224644317308318326617)
              ·
                refine ⟨14133918483237981238744963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18845224644317308318326617 14133918483237981238744963)
                ·
                  refine ⟨21200877724856971858117445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14133918483237981238744963 21200877724856971858117445)
                  ·
                    refine ⟨3975164573410682223397021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21200877724856971858117445 3975164573410682223397021)
                    ·
                      refine ⟨1490686715029005833773883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3975164573410682223397021 1490686715029005833773883)
                      ·
                        rfl

theorem cell23_2903102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_2903102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903102 prefixEnd_2903102 := by exact prefixLift 2903102
  have htrace : WordTrace (prefixWord ++ tailWord_2903102) baseStart_2903102 baseEnd_2903102 := by
    simpa [prefixWord, tailWord_2903102, baseEnd_2903102] using wordTrace_append hprefix tailTrace_2903102
  have hstable : (prefixWord ++ tailWord_2903102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903102).length < 2 ^ (prefixWord ++ tailWord_2903102).sum := by decide
  have hdescent : baseEnd_2903102 < baseStart_2903102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903135 : List Nat := [1, 1, 2, 3, 1, 1, 3, 5, 1, 5]
def baseStart_2903135 : Nat := 118140960795 + 2903135 * 2 ^ 59
def prefixEnd_2903135 : Nat := 4983230072969 + 3 ^ 40 * 2903135 * 2
def baseEnd_2903135 : Nat := 496901219963534734887077

theorem tailTrace_2903135 : CollatzResearch.WordTrace tailWord_2903135 prefixEnd_2903135 496901219963534734887077 := by
  unfold tailWord_2903135
  simp only [CollatzResearch.WordTrace]
  refine ⟨105886032337445185829182859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70590688224963457219455239 105886032337445185829182859)
  ·
    refine ⟨158829048506167778743774289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105886032337445185829182859 158829048506167778743774289)
    ·
      refine ⟨119121786379625834057830717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158829048506167778743774289 119121786379625834057830717)
      ·
        refine ⟨44670669892359687771686519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119121786379625834057830717 44670669892359687771686519)
        ·
          refine ⟨67006004838539531657529779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44670669892359687771686519 67006004838539531657529779)
          ·
            refine ⟨100509007257809297486294669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67006004838539531657529779 100509007257809297486294669)
            ·
              refine ⟨37690877721678486557360501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100509007257809297486294669 37690877721678486557360501)
              ·
                refine ⟨3533519786407358114752547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37690877721678486557360501 3533519786407358114752547)
                ·
                  refine ⟨5300279679611037172128821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3533519786407358114752547 5300279679611037172128821)
                  ·
                    refine ⟨496901219963534734887077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5300279679611037172128821 496901219963534734887077)
                    ·
                      rfl

theorem cell23_2903135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 5].length) (baseStart_2903135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903135 prefixEnd_2903135 := by exact prefixLift 2903135
  have htrace : WordTrace (prefixWord ++ tailWord_2903135) baseStart_2903135 baseEnd_2903135 := by
    simpa [prefixWord, tailWord_2903135, baseEnd_2903135] using wordTrace_append hprefix tailTrace_2903135
  have hstable : (prefixWord ++ tailWord_2903135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903135).length < 2 ^ (prefixWord ++ tailWord_2903135).sum := by decide
  have hdescent : baseEnd_2903135 < baseStart_2903135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903149 : List Nat := [1, 5, 1, 1, 2, 2, 3, 1, 3, 1, 3]
def baseStart_2903149 : Nat := 118140960795 + 2903149 * 2 ^ 59
def prefixEnd_2903149 : Nat := 4983230072969 + 3 ^ 40 * 2903149 * 2
def baseEnd_2903149 : Nat := 1490710848619767149886167

theorem tailTrace_2903149 : CollatzResearch.WordTrace tailWord_2903149 prefixEnd_2903149 1490710848619767149886167 := by
  unfold tailWord_2903149
  simp only [CollatzResearch.WordTrace]
  refine ⟨105886542959394466220192501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70591028639596310813461667 105886542959394466220192501)
  ·
    refine ⟨9926863402443231208143047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105886542959394466220192501 9926863402443231208143047)
    ·
      refine ⟨14890295103664846812214571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9926863402443231208143047 14890295103664846812214571)
      ·
        refine ⟨22335442655497270218321857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14890295103664846812214571 22335442655497270218321857)
        ·
          refine ⟨16751581991622952663741393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22335442655497270218321857 16751581991622952663741393)
          ·
            refine ⟨12563686493717214497806045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16751581991622952663741393 12563686493717214497806045)
            ·
              refine ⟨4711382435143955436677267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12563686493717214497806045 4711382435143955436677267)
              ·
                refine ⟨7067073652715933155015901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4711382435143955436677267 7067073652715933155015901)
                ·
                  refine ⟨2650152619768474933130963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7067073652715933155015901 2650152619768474933130963)
                  ·
                    refine ⟨3975228929652712399696445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2650152619768474933130963 3975228929652712399696445)
                    ·
                      refine ⟨1490710848619767149886167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3975228929652712399696445 1490710848619767149886167)
                      ·
                        rfl

theorem cell23_2903149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_2903149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903149 prefixEnd_2903149 := by exact prefixLift 2903149
  have htrace : WordTrace (prefixWord ++ tailWord_2903149) baseStart_2903149 baseEnd_2903149 := by
    simpa [prefixWord, tailWord_2903149, baseEnd_2903149] using wordTrace_append hprefix tailTrace_2903149
  have hstable : (prefixWord ++ tailWord_2903149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903149).length < 2 ^ (prefixWord ++ tailWord_2903149).sum := by decide
  have hdescent : baseEnd_2903149 < baseStart_2903149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903165 : List Nat := [1, 4, 1, 1, 3, 1, 2, 3, 1, 6]
def baseStart_2903165 : Nat := 118140960795 + 2903165 * 2 ^ 59
def prefixEnd_2903165 : Nat := 4983230072969 + 3 ^ 40 * 2903165 * 2
def baseEnd_2903165 : Nat := 496906354770079695762031

theorem tailTrace_2903165 : CollatzResearch.WordTrace tailWord_2903165 prefixEnd_2903165 496906354770079695762031 := by
  unfold tailWord_2903165
  simp only [CollatzResearch.WordTrace]
  refine ⟨105887126527336500952774949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70591417684891000635183299 105887126527336500952774949)
  ·
    refine ⟨19853836223875593928645303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105887126527336500952774949 19853836223875593928645303)
    ·
      refine ⟨29780754335813390892967955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19853836223875593928645303 29780754335813390892967955)
      ·
        refine ⟨44671131503720086339451933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29780754335813390892967955 44671131503720086339451933)
        ·
          refine ⟨16751674313895032377294475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44671131503720086339451933 16751674313895032377294475)
          ·
            refine ⟨25127511470842548565941713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16751674313895032377294475 25127511470842548565941713)
            ·
              refine ⟨18845633603131911424456285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25127511470842548565941713 18845633603131911424456285)
              ·
                refine ⟨7067112601174466784171107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18845633603131911424456285 7067112601174466784171107)
                ·
                  refine ⟨10600668901761700176256661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7067112601174466784171107 10600668901761700176256661)
                  ·
                    refine ⟨496906354770079695762031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10600668901761700176256661 496906354770079695762031)
                    ·
                      rfl

theorem cell23_2903165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_2903165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903165 prefixEnd_2903165 := by exact prefixLift 2903165
  have htrace : WordTrace (prefixWord ++ tailWord_2903165) baseStart_2903165 baseEnd_2903165 := by
    simpa [prefixWord, tailWord_2903165, baseEnd_2903165] using wordTrace_append hprefix tailTrace_2903165
  have hstable : (prefixWord ++ tailWord_2903165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903165).length < 2 ^ (prefixWord ++ tailWord_2903165).sum := by decide
  have hdescent : baseEnd_2903165 < baseStart_2903165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903169 : List Nat := [1, 2, 4, 2, 2, 3, 1, 2, 1, 5]
def baseStart_2903169 : Nat := 118140960795 + 2903169 * 2 ^ 59
def prefixEnd_2903169 : Nat := 4983230072969 + 3 ^ 40 * 2903169 * 2
def baseEnd_2903169 : Nat := 496907039410952357212025

theorem tailTrace_2903169 : CollatzResearch.WordTrace tailWord_2903169 prefixEnd_2903169 496907039410952357212025 := by
  unfold tailWord_2903169
  simp only [CollatzResearch.WordTrace]
  refine ⟨105887272419322009635920561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70591514946214673090613707 105887272419322009635920561)
  ·
    refine ⟨79415454314491507226940421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105887272419322009635920561 79415454314491507226940421)
    ·
      refine ⟨14890397683967157605051329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79415454314491507226940421 14890397683967157605051329)
      ·
        refine ⟨11167798262975368203788497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14890397683967157605051329 11167798262975368203788497)
        ·
          refine ⟨8375848697231526152841373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11167798262975368203788497 8375848697231526152841373)
          ·
            refine ⟨3140943261461822307315515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8375848697231526152841373 3140943261461822307315515)
            ·
              refine ⟨4711414892192733460973273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3140943261461822307315515 4711414892192733460973273)
              ·
                refine ⟨3533561169144550095729955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4711414892192733460973273 3533561169144550095729955)
                ·
                  refine ⟨5300341753716825143594933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3533561169144550095729955 5300341753716825143594933)
                  ·
                    refine ⟨496907039410952357212025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5300341753716825143594933 496907039410952357212025)
                    ·
                      rfl

theorem cell23_2903169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_2903169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903169 prefixEnd_2903169 := by exact prefixLift 2903169
  have htrace : WordTrace (prefixWord ++ tailWord_2903169) baseStart_2903169 baseEnd_2903169 := by
    simpa [prefixWord, tailWord_2903169, baseEnd_2903169] using wordTrace_append hprefix tailTrace_2903169
  have hstable : (prefixWord ++ tailWord_2903169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903169).length < 2 ^ (prefixWord ++ tailWord_2903169).sum := by decide
  have hdescent : baseEnd_2903169 < baseStart_2903169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903172 : List Nat := [2, 3, 2, 1, 2, 3, 1, 1, 3, 1, 4]
def baseStart_2903172 : Nat := 118140960795 + 2903172 * 2 ^ 59
def prefixEnd_2903172 : Nat := 4983230072969 + 3 ^ 40 * 2903172 * 2
def baseEnd_2903172 : Nat := 1490722658674820559898561

theorem tailTrace_2903172 : CollatzResearch.WordTrace tailWord_2903172 prefixEnd_2903172 1490722658674820559898561 := by
  unfold tailWord_2903172
  simp only [CollatzResearch.WordTrace]
  refine ⟨52943690919155570574139885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70591587892207427432186513 52943690919155570574139885)
  ·
    refine ⟨19853884094683338965302457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52943690919155570574139885 19853884094683338965302457)
    ·
      refine ⟨14890413071012504223976843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19853884094683338965302457 14890413071012504223976843)
      ·
        refine ⟨22335619606518756335965265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14890413071012504223976843 22335619606518756335965265)
        ·
          refine ⟨16751714704889067251973949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22335619606518756335965265 16751714704889067251973949)
          ·
            refine ⟨6281893014333400219490231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16751714704889067251973949 6281893014333400219490231)
            ·
              refine ⟨9422839521500100329235347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6281893014333400219490231 9422839521500100329235347)
              ·
                refine ⟨14134259282250150493853021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9422839521500100329235347 14134259282250150493853021)
                ·
                  refine ⟨5300347230843806435194883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14134259282250150493853021 5300347230843806435194883)
                  ·
                    refine ⟨7950520846265709652792325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5300347230843806435194883 7950520846265709652792325)
                    ·
                      refine ⟨1490722658674820559898561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7950520846265709652792325 1490722658674820559898561)
                      ·
                        rfl

theorem cell23_2903172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_2903172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903172 prefixEnd_2903172 := by exact prefixLift 2903172
  have htrace : WordTrace (prefixWord ++ tailWord_2903172) baseStart_2903172 baseEnd_2903172 := by
    simpa [prefixWord, tailWord_2903172, baseEnd_2903172] using wordTrace_append hprefix tailTrace_2903172
  have hstable : (prefixWord ++ tailWord_2903172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903172).length < 2 ^ (prefixWord ++ tailWord_2903172).sum := by decide
  have hdescent : baseEnd_2903172 < baseStart_2903172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903176 : List Nat := [2, 1, 3, 4, 2, 1, 2, 1, 2, 3, 2]
def baseStart_2903176 : Nat := 118140960795 + 2903176 * 2 ^ 59
def prefixEnd_2903176 : Nat := 4983230072969 + 3 ^ 40 * 2903176 * 2
def baseEnd_2903176 : Nat := 1490724712597438544248543

theorem tailTrace_2903176 : CollatzResearch.WordTrace tailWord_2903176 prefixEnd_2903176 1490724712597438544248543 := by
  unfold tailWord_2903176
  simp only [CollatzResearch.WordTrace]
  refine ⟨52943763865148324915712691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70591685153531099887616921 52943763865148324915712691)
  ·
    refine ⟨79415645797722487373569037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52943763865148324915712691 79415645797722487373569037)
    ·
      refine ⟨29780867174145932765088389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79415645797722487373569037 29780867174145932765088389)
      ·
        refine ⟨5583912595152362393454073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29780867174145932765088389 5583912595152362393454073)
        ·
          refine ⟨4187934446364271795090555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5583912595152362393454073 4187934446364271795090555)
          ·
            refine ⟨6281901669546407692635833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4187934446364271795090555 6281901669546407692635833)
            ·
              refine ⟨4711426252159805769476875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6281901669546407692635833 4711426252159805769476875)
              ·
                refine ⟨7067139378239708654215313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4711426252159805769476875 7067139378239708654215313)
                ·
                  refine ⟨5300354533679781490661485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7067139378239708654215313 5300354533679781490661485)
                  ·
                    refine ⟨1987632950129918058998057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5300354533679781490661485 1987632950129918058998057)
                    ·
                      refine ⟨1490724712597438544248543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1987632950129918058998057 1490724712597438544248543)
                      ·
                        rfl

theorem cell23_2903176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_2903176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903176 prefixEnd_2903176 := by exact prefixLift 2903176
  have htrace : WordTrace (prefixWord ++ tailWord_2903176) baseStart_2903176 baseEnd_2903176 := by
    simpa [prefixWord, tailWord_2903176, baseEnd_2903176] using wordTrace_append hprefix tailTrace_2903176
  have hstable : (prefixWord ++ tailWord_2903176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903176).length < 2 ^ (prefixWord ++ tailWord_2903176).sum := by decide
  have hdescent : baseEnd_2903176 < baseStart_2903176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903182 : List Nat := [4, 1, 1, 3, 2, 2, 1, 2, 1, 6]
def baseStart_2903182 : Nat := 118140960795 + 2903182 * 2 ^ 59
def prefixEnd_2903182 : Nat := 4983230072969 + 3 ^ 40 * 2903182 * 2
def baseEnd_2903182 : Nat := 496909264493788506924505

theorem tailTrace_2903182 : CollatzResearch.WordTrace tailWord_2903182 prefixEnd_2903182 496909264493788506924505 := by
  unfold tailWord_2903182
  simp only [CollatzResearch.WordTrace]
  refine ⟨13235968321034364107017975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70591831045516608570762533 13235968321034364107017975)
  ·
    refine ⟨19853952481551546160526963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13235968321034364107017975 19853952481551546160526963)
    ·
      refine ⟨29780928722327319240790445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19853952481551546160526963 29780928722327319240790445)
      ·
        refine ⟨11167848270872744715296417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29780928722327319240790445 11167848270872744715296417)
        ·
          refine ⟨8375886203154558536472313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11167848270872744715296417 8375886203154558536472313)
          ·
            refine ⟨6281914652365918902354235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8375886203154558536472313 6281914652365918902354235)
            ·
              refine ⟨9422871978548878353531353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6281914652365918902354235 9422871978548878353531353)
              ·
                refine ⟨7067153983911658765148515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9422871978548878353531353 7067153983911658765148515)
                ·
                  refine ⟨10600730975867488147722773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7067153983911658765148515 10600730975867488147722773)
                  ·
                    refine ⟨496909264493788506924505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10600730975867488147722773 496909264493788506924505)
                    ·
                      rfl

theorem cell23_2903182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_2903182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903182 prefixEnd_2903182 := by exact prefixLift 2903182
  have htrace : WordTrace (prefixWord ++ tailWord_2903182) baseStart_2903182 baseEnd_2903182 := by
    simpa [prefixWord, tailWord_2903182, baseEnd_2903182] using wordTrace_append hprefix tailTrace_2903182
  have hstable : (prefixWord ++ tailWord_2903182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903182).length < 2 ^ (prefixWord ++ tailWord_2903182).sum := by decide
  have hdescent : baseEnd_2903182 < baseStart_2903182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903192 : List Nat := [2, 1, 2, 4, 2, 1, 3, 1, 1, 1, 5]
def baseStart_2903192 : Nat := 118140960795 + 2903192 * 2 ^ 59
def prefixEnd_2903192 : Nat := 4983230072969 + 3 ^ 40 * 2903192 * 2
def baseEnd_2903192 : Nat := 1490732928287910481648469

theorem tailTrace_2903192 : CollatzResearch.WordTrace tailWord_2903192 prefixEnd_2903192 1490732928287910481648469 := by
  unfold tailWord_2903192
  simp only [CollatzResearch.WordTrace]
  refine ⟨52944055649119342282003915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70592074198825789709338553 52944055649119342282003915)
  ·
    refine ⟨79416083473679013423005873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52944055649119342282003915 79416083473679013423005873)
    ·
      refine ⟨59562062605259260067254405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79416083473679013423005873 59562062605259260067254405)
      ·
        refine ⟨11167886738486111262610201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59562062605259260067254405 11167886738486111262610201)
        ·
          refine ⟨8375915053864583446957651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11167886738486111262610201 8375915053864583446957651)
          ·
            refine ⟨12563872580796875170436477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8375915053864583446957651 12563872580796875170436477)
            ·
              refine ⟨4711452217798828188913679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12563872580796875170436477 4711452217798828188913679)
              ·
                refine ⟨7067178326698242283370519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4711452217798828188913679 7067178326698242283370519)
                ·
                  refine ⟨10600767490047363425055779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7067178326698242283370519 10600767490047363425055779)
                  ·
                    refine ⟨15901151235071045137583669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10600767490047363425055779 15901151235071045137583669)
                    ·
                      refine ⟨1490732928287910481648469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15901151235071045137583669 1490732928287910481648469)
                      ·
                        rfl

theorem cell23_2903192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_2903192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903192 prefixEnd_2903192 := by exact prefixLift 2903192
  have htrace : WordTrace (prefixWord ++ tailWord_2903192) baseStart_2903192 baseEnd_2903192 := by
    simpa [prefixWord, tailWord_2903192, baseEnd_2903192] using wordTrace_append hprefix tailTrace_2903192
  have hstable : (prefixWord ++ tailWord_2903192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903192).length < 2 ^ (prefixWord ++ tailWord_2903192).sum := by decide
  have hdescent : baseEnd_2903192 < baseStart_2903192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903255 : List Nat := [1, 1, 3, 2, 1, 2, 3, 2, 2, 6]
def baseStart_2903255 : Nat := 118140960795 + 2903255 * 2 ^ 59
def prefixEnd_2903255 : Nat := 4983230072969 + 3 ^ 40 * 2903255 * 2
def baseEnd_2903255 : Nat := 496921759189714578386893

theorem tailTrace_2903255 : CollatzResearch.WordTrace tailWord_2903255 prefixEnd_2903255 496921759189714578386893 := by
  unfold tailWord_2903255
  simp only [CollatzResearch.WordTrace]
  refine ⟨105890409097010446323551219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70593606064673630882367479 105890409097010446323551219)
  ·
    refine ⟨158835613645515669485326829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105890409097010446323551219 158835613645515669485326829)
    ·
      refine ⟨59563355117068376056997561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158835613645515669485326829 59563355117068376056997561)
      ·
        refine ⟨44672516337801282042748171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59563355117068376056997561 44672516337801282042748171)
        ·
          refine ⟨67008774506701923064122257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44672516337801282042748171 67008774506701923064122257)
          ·
            refine ⟨50256580880026442298091693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67008774506701923064122257 50256580880026442298091693)
            ·
              refine ⟨18846217830009915861784385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50256580880026442298091693 18846217830009915861784385)
              ·
                refine ⟨14134663372507436896338289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18846217830009915861784385 14134663372507436896338289)
                ·
                  refine ⟨10600997529380577672253717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14134663372507436896338289 10600997529380577672253717)
                  ·
                    refine ⟨496921759189714578386893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10600997529380577672253717 496921759189714578386893)
                    ·
                      rfl

theorem cell23_2903255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 6].length) (baseStart_2903255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903255 prefixEnd_2903255 := by exact prefixLift 2903255
  have htrace : WordTrace (prefixWord ++ tailWord_2903255) baseStart_2903255 baseEnd_2903255 := by
    simpa [prefixWord, tailWord_2903255, baseEnd_2903255] using wordTrace_append hprefix tailTrace_2903255
  have hstable : (prefixWord ++ tailWord_2903255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903255).length < 2 ^ (prefixWord ++ tailWord_2903255).sum := by decide
  have hdescent : baseEnd_2903255 < baseStart_2903255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903332 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 4, 5]
def baseStart_2903332 : Nat := 118140960795 + 2903332 * 2 ^ 59
def prefixEnd_2903332 : Nat := 4983230072969 + 3 ^ 40 * 2903332 * 2
def baseEnd_2903332 : Nat := 496934938526513311299275

theorem tailTrace_2903332 : CollatzResearch.WordTrace tailWord_2903332 prefixEnd_2903332 496934938526513311299275 := by
  unfold tailWord_2903332
  simp only [CollatzResearch.WordTrace]
  refine ⟨52946608758865744237052125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70595478345154325649402833 52946608758865744237052125)
  ·
    refine ⟨19854978284574654088894547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52946608758865744237052125 19854978284574654088894547)
    ·
      refine ⟨29782467426861981133341821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19854978284574654088894547 29782467426861981133341821)
      ·
        refine ⟨11168425285073242925003183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29782467426861981133341821 11168425285073242925003183)
        ·
          refine ⟨16752637927609864387504775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11168425285073242925003183 16752637927609864387504775)
          ·
            refine ⟨25128956891414796581257163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16752637927609864387504775 25128956891414796581257163)
            ·
              refine ⟨37693435337122194871885745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25128956891414796581257163 37693435337122194871885745)
              ·
                refine ⟨28270076502841646153914309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37693435337122194871885745 28270076502841646153914309)
                ·
                  refine ⟨5300639344282808653858933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28270076502841646153914309 5300639344282808653858933)
                  ·
                    refine ⟨496934938526513311299275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5300639344282808653858933 496934938526513311299275)
                    ·
                      rfl

theorem cell23_2903332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_2903332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903332 prefixEnd_2903332 := by exact prefixLift 2903332
  have htrace : WordTrace (prefixWord ++ tailWord_2903332) baseStart_2903332 baseEnd_2903332 := by
    simpa [prefixWord, tailWord_2903332, baseEnd_2903332] using wordTrace_append hprefix tailTrace_2903332
  have hstable : (prefixWord ++ tailWord_2903332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903332).length < 2 ^ (prefixWord ++ tailWord_2903332).sum := by decide
  have hdescent : baseEnd_2903332 < baseStart_2903332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903349 : List Nat := [1, 3, 3, 1, 2, 3, 2, 1, 2, 5]
def baseStart_2903349 : Nat := 118140960795 + 2903349 * 2 ^ 59
def prefixEnd_2903349 : Nat := 4983230072969 + 3 ^ 40 * 2903349 * 2
def baseEnd_2903349 : Nat := 496937848250222122461749

theorem tailTrace_2903349 : CollatzResearch.WordTrace tailWord_2903349 prefixEnd_2903349 496937848250222122461749 := by
  unfold tailWord_2903349
  simp only [CollatzResearch.WordTrace]
  refine ⟨105893837558669900377473101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70595891705779933584982067 105893837558669900377473101)
  ·
    refine ⟨39710189084501212641552413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105893837558669900377473101 39710189084501212641552413)
    ·
      refine ⟨14891320906687954740582155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39710189084501212641552413 14891320906687954740582155)
      ·
        refine ⟨22336981360031932110873233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14891320906687954740582155 22336981360031932110873233)
        ·
          refine ⟨16752736020023949083154925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22336981360031932110873233 16752736020023949083154925)
          ·
            refine ⟨6282276007508980906183097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16752736020023949083154925 6282276007508980906183097)
            ·
              refine ⟨4711707005631735679637323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6282276007508980906183097 4711707005631735679637323)
              ·
                refine ⟨7067560508447603519455985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4711707005631735679637323 7067560508447603519455985)
                ·
                  refine ⟨5300670381335702639591989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7067560508447603519455985 5300670381335702639591989)
                  ·
                    refine ⟨496937848250222122461749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5300670381335702639591989 496937848250222122461749)
                    ·
                      rfl

theorem cell23_2903349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_2903349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903349 prefixEnd_2903349 := by exact prefixLift 2903349
  have htrace : WordTrace (prefixWord ++ tailWord_2903349) baseStart_2903349 baseEnd_2903349 := by
    simpa [prefixWord, tailWord_2903349, baseEnd_2903349] using wordTrace_append hprefix tailTrace_2903349
  have hstable : (prefixWord ++ tailWord_2903349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903349).length < 2 ^ (prefixWord ++ tailWord_2903349).sum := by decide
  have hdescent : baseEnd_2903349 < baseStart_2903349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903375 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 12]
def baseStart_2903375 : Nat := 118140960795 + 2903375 * 2 ^ 59
def prefixEnd_2903375 : Nat := 4983230072969 + 3 ^ 40 * 2903375 * 2
def baseEnd_2903375 : Nat := 165647432805298140628903

theorem tailTrace_2903375 : CollatzResearch.WordTrace tailWord_2903375 prefixEnd_2903375 165647432805298140628903 := by
  unfold tailWord_2903375
  simp only [CollatzResearch.WordTrace]
  refine ⟨105894785856575706817919579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70596523904383804545279719 105894785856575706817919579)
  ·
    refine ⟨158842178784863560226879369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105894785856575706817919579 158842178784863560226879369)
    ·
      refine ⟨119131634088647670170159527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158842178784863560226879369 119131634088647670170159527)
      ·
        refine ⟨178697451132971505255239291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119131634088647670170159527 178697451132971505255239291)
        ·
          refine ⟨268046176699457257882858937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178697451132971505255239291 268046176699457257882858937)
          ·
            refine ⟨201034632524592943412144203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268046176699457257882858937 201034632524592943412144203)
            ·
              refine ⟨301551948786889415118216305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201034632524592943412144203 301551948786889415118216305)
              ·
                refine ⟨226163961590167061338662229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301551948786889415118216305 226163961590167061338662229)
                ·
                  refine ⟨165647432805298140628903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 226163961590167061338662229 165647432805298140628903)
                  ·
                    rfl

theorem cell23_2903375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 12].length) (baseStart_2903375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903375 prefixEnd_2903375 := by exact prefixLift 2903375
  have htrace : WordTrace (prefixWord ++ tailWord_2903375) baseStart_2903375 baseEnd_2903375 := by
    simpa [prefixWord, tailWord_2903375, baseEnd_2903375] using wordTrace_append hprefix tailTrace_2903375
  have hstable : (prefixWord ++ tailWord_2903375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903375).length < 2 ^ (prefixWord ++ tailWord_2903375).sum := by decide
  have hdescent : baseEnd_2903375 < baseStart_2903375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903419 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 5, 1, 3]
def baseStart_2903419 : Nat := 118140960795 + 2903419 * 2 ^ 59
def prefixEnd_2903419 : Nat := 4983230072969 + 3 ^ 40 * 2903419 * 2
def baseEnd_2903419 : Nat := 1490849488396481093509925

theorem tailTrace_2903419 : CollatzResearch.WordTrace tailWord_2903419 prefixEnd_2903419 1490849488396481093509925 := by
  unfold tailWord_2903419
  simp only [CollatzResearch.WordTrace]
  refine ⟨105896390668416302332521311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70597593778944201555014207 105896390668416302332521311)
  ·
    refine ⟨158844586002624453498781967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105896390668416302332521311 158844586002624453498781967)
    ·
      refine ⟨238266879003936680248172951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158844586002624453498781967 238266879003936680248172951)
      ·
        refine ⟨357400318505905020372259427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238266879003936680248172951 357400318505905020372259427)
        ·
          refine ⟨536100477758857530558389141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357400318505905020372259427 536100477758857530558389141)
          ·
            refine ⟨25129709894946446744924491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 536100477758857530558389141 25129709894946446744924491)
            ·
              refine ⟨37694564842419670117386737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25129709894946446744924491 37694564842419670117386737)
              ·
                refine ⟨28270923631814752588040053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37694564842419670117386737 28270923631814752588040053)
                ·
                  refine ⟨2650399090482633055128755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28270923631814752588040053 2650399090482633055128755)
                  ·
                    refine ⟨3975598635723949582693133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2650399090482633055128755 3975598635723949582693133)
                    ·
                      refine ⟨1490849488396481093509925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3975598635723949582693133 1490849488396481093509925)
                      ·
                        rfl

theorem cell23_2903419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5, 1, 3].length) (baseStart_2903419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903419 prefixEnd_2903419 := by exact prefixLift 2903419
  have htrace : WordTrace (prefixWord ++ tailWord_2903419) baseStart_2903419 baseEnd_2903419 := by
    simpa [prefixWord, tailWord_2903419, baseEnd_2903419] using wordTrace_append hprefix tailTrace_2903419
  have hstable : (prefixWord ++ tailWord_2903419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903419).length < 2 ^ (prefixWord ++ tailWord_2903419).sum := by decide
  have hdescent : baseEnd_2903419 < baseStart_2903419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903426 : List Nat := [3, 4, 2, 1, 1, 2, 1, 1, 8]
def baseStart_2903426 : Nat := 118140960795 + 2903426 * 2 ^ 59
def prefixEnd_2903426 : Nat := 4983230072969 + 3 ^ 40 * 2903426 * 2
def baseEnd_2903426 : Nat := 165650342529006951791377

theorem tailTrace_2903426 : CollatzResearch.WordTrace tailWord_2903426 prefixEnd_2903426 165650342529006951791377 := by
  unfold tailWord_2903426
  simp only [CollatzResearch.WordTrace]
  refine ⟨26474161494847735632006533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70597763986260628352017421 26474161494847735632006533)
  ·
    refine ⟨4963905280283950431001225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26474161494847735632006533 4963905280283950431001225)
    ·
      refine ⟨3722928960212962823250919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4963905280283950431001225 3722928960212962823250919)
      ·
        refine ⟨5584393440319444234876379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3722928960212962823250919 5584393440319444234876379)
        ·
          refine ⟨8376590160479166352314569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5584393440319444234876379 8376590160479166352314569)
          ·
            refine ⟨6282442620359374764235927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8376590160479166352314569 6282442620359374764235927)
            ·
              refine ⟨9423663930539062146353891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6282442620359374764235927 9423663930539062146353891)
              ·
                refine ⟨14135495895808593219530837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9423663930539062146353891 14135495895808593219530837)
                ·
                  refine ⟨165650342529006951791377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14135495895808593219530837 165650342529006951791377)
                  ·
                    rfl

theorem cell23_2903426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_2903426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903426 prefixEnd_2903426 := by exact prefixLift 2903426
  have htrace : WordTrace (prefixWord ++ tailWord_2903426) baseStart_2903426 baseEnd_2903426 := by
    simpa [prefixWord, tailWord_2903426, baseEnd_2903426] using wordTrace_append hprefix tailTrace_2903426
  have hstable : (prefixWord ++ tailWord_2903426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903426).length < 2 ^ (prefixWord ++ tailWord_2903426).sum := by decide
  have hdescent : baseEnd_2903426 < baseStart_2903426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903436 : List Nat := [2, 2, 1, 2, 1, 3, 4, 1, 3, 1, 3]
def baseStart_2903436 : Nat := 118140960795 + 2903436 * 2 ^ 59
def prefixEnd_2903436 : Nat := 4983230072969 + 3 ^ 40 * 2903436 * 2
def baseEnd_2903436 : Nat := 1490858217567607526997347

theorem tailTrace_2903436 : CollatzResearch.WordTrace tailWord_2903436 prefixEnd_2903436 1490858217567607526997347 := by
  unfold tailWord_2903436
  simp only [CollatzResearch.WordTrace]
  refine ⟨52948505354677357117945081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70598007139569809490593441 52948505354677357117945081)
  ·
    refine ⟨39711379016008017838458811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52948505354677357117945081 39711379016008017838458811)
    ·
      refine ⟨59567068524012026757688217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39711379016008017838458811 59567068524012026757688217)
      ·
        refine ⟨44675301393009020068266163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59567068524012026757688217 44675301393009020068266163)
        ·
          refine ⟨67012952089513530102399245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44675301393009020068266163 67012952089513530102399245)
          ·
            refine ⟨25129857033567573788399717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67012952089513530102399245 25129857033567573788399717)
            ·
              refine ⟨4711848193793920085324947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25129857033567573788399717 4711848193793920085324947)
              ·
                refine ⟨7067772290690880127987421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4711848193793920085324947 7067772290690880127987421)
                ·
                  refine ⟨2650414609009080047995283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7067772290690880127987421 2650414609009080047995283)
                  ·
                    refine ⟨3975621913513620071992925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2650414609009080047995283 3975621913513620071992925)
                    ·
                      refine ⟨1490858217567607526997347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3975621913513620071992925 1490858217567607526997347)
                      ·
                        rfl

theorem cell23_2903436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_2903436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903436 prefixEnd_2903436 := by exact prefixLift 2903436
  have htrace : WordTrace (prefixWord ++ tailWord_2903436) baseStart_2903436 baseEnd_2903436 := by
    simpa [prefixWord, tailWord_2903436, baseEnd_2903436] using wordTrace_append hprefix tailTrace_2903436
  have hstable : (prefixWord ++ tailWord_2903436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903436).length < 2 ^ (prefixWord ++ tailWord_2903436).sum := by decide
  have hdescent : baseEnd_2903436 < baseStart_2903436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903459 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 2, 6, 2]
def baseStart_2903459 : Nat := 118140960795 + 2903459 * 2 ^ 59
def prefixEnd_2903459 : Nat := 4983230072969 + 3 ^ 40 * 2903459 * 2
def baseEnd_2903459 : Nat := 1490870027622660937009741

theorem tailTrace_2903459 : CollatzResearch.WordTrace tailWord_2903459 prefixEnd_2903459 1490870027622660937009741 := by
  unfold tailWord_2903459
  simp only [CollatzResearch.WordTrace]
  refine ⟨105897849588271389163977431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70598566392180926109318287 105897849588271389163977431)
  ·
    refine ⟨158846774382407083745966147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105897849588271389163977431 158846774382407083745966147)
    ·
      refine ⟨238270161573610625618949221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158846774382407083745966147 238270161573610625618949221)
      ·
        refine ⟨44675655295051992303552979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 238270161573610625618949221 44675655295051992303552979)
        ·
          refine ⟨67013482942577988455329469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44675655295051992303552979 67013482942577988455329469)
          ·
            refine ⟨25130056103466745670748551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67013482942577988455329469 25130056103466745670748551)
            ·
              refine ⟨37695084155200118506122827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25130056103466745670748551 37695084155200118506122827)
              ·
                refine ⟨56542626232800177759184241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37695084155200118506122827 56542626232800177759184241)
                ·
                  refine ⟨42406969674600133319388181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56542626232800177759184241 42406969674600133319388181)
                  ·
                    refine ⟨1987826703496881249346321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42406969674600133319388181 1987826703496881249346321)
                    ·
                      refine ⟨1490870027622660937009741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1987826703496881249346321 1490870027622660937009741)
                      ·
                        rfl

theorem cell23_2903459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 6, 2].length) (baseStart_2903459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903459 prefixEnd_2903459 := by exact prefixLift 2903459
  have htrace : WordTrace (prefixWord ++ tailWord_2903459) baseStart_2903459 baseEnd_2903459 := by
    simpa [prefixWord, tailWord_2903459, baseEnd_2903459] using wordTrace_append hprefix tailTrace_2903459
  have hstable : (prefixWord ++ tailWord_2903459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903459).length < 2 ^ (prefixWord ++ tailWord_2903459).sum := by decide
  have hdescent : baseEnd_2903459 < baseStart_2903459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903479 : List Nat := [1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 5]
def baseStart_2903479 : Nat := 118140960795 + 2903479 * 2 ^ 59
def prefixEnd_2903479 : Nat := 4983230072969 + 3 ^ 40 * 2903479 * 2
def baseEnd_2903479 : Nat := 1490880297235750858759649

theorem tailTrace_2903479 : CollatzResearch.WordTrace tailWord_2903479 prefixEnd_2903479 1490880297235750858759649 := by
  unfold tailWord_2903479
  simp only [CollatzResearch.WordTrace]
  refine ⟨105898579048198932579705491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70599052698799288386470327 105898579048198932579705491)
  ·
    refine ⟨158847868572298398869558237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105898579048198932579705491 158847868572298398869558237)
    ·
      refine ⟨59567950714611899576084339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158847868572298398869558237 59567950714611899576084339)
      ·
        refine ⟨89351926071917849364126509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59567950714611899576084339 89351926071917849364126509)
        ·
          refine ⟨33506972276969193511547441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89351926071917849364126509 33506972276969193511547441)
          ·
            refine ⟨25130229207726895133660581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33506972276969193511547441 25130229207726895133660581)
            ·
              refine ⟨4711917976448792837561359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25130229207726895133660581 4711917976448792837561359)
              ·
                refine ⟨7067876964673189256342039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4711917976448792837561359 7067876964673189256342039)
                ·
                  refine ⟨10601815447009783884513059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7067876964673189256342039 10601815447009783884513059)
                  ·
                    refine ⟨15902723170514675826769589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10601815447009783884513059 15902723170514675826769589)
                    ·
                      refine ⟨1490880297235750858759649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15902723170514675826769589 1490880297235750858759649)
                      ·
                        rfl

theorem cell23_2903479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 5].length) (baseStart_2903479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903479 prefixEnd_2903479 := by exact prefixLift 2903479
  have htrace : WordTrace (prefixWord ++ tailWord_2903479) baseStart_2903479 baseEnd_2903479 := by
    simpa [prefixWord, tailWord_2903479, baseEnd_2903479] using wordTrace_append hprefix tailTrace_2903479
  have hstable : (prefixWord ++ tailWord_2903479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903479).length < 2 ^ (prefixWord ++ tailWord_2903479).sum := by decide
  have hdescent : baseEnd_2903479 < baseStart_2903479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903486 : List Nat := [4, 2, 1, 1, 1, 1, 1, 6, 2, 4]
def baseStart_2903486 : Nat := 118140960795 + 2903486 * 2 ^ 59
def prefixEnd_2903486 : Nat := 4983230072969 + 3 ^ 40 * 2903486 * 2
def baseEnd_2903486 : Nat := 496961297200110777124039

theorem tailTrace_2903486 : CollatzResearch.WordTrace tailWord_2903486 prefixEnd_2903486 496961297200110777124039 := by
  unfold tailWord_2903486
  simp only [CollatzResearch.WordTrace]
  refine ⟨13237354294896696596901289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70599222906115715183473541 13237354294896696596901289)
  ·
    refine ⟨9928015721172522447675967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13237354294896696596901289 9928015721172522447675967)
    ·
      refine ⟨14892023581758783671513951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9928015721172522447675967 14892023581758783671513951)
      ·
        refine ⟨22338035372638175507270927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14892023581758783671513951 22338035372638175507270927)
        ·
          refine ⟨33507053058957263260906391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22338035372638175507270927 33507053058957263260906391)
          ·
            refine ⟨50260579588435894891359587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33507053058957263260906391 50260579588435894891359587)
            ·
              refine ⟨75390869382653842337039381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50260579588435894891359587 75390869382653842337039381)
              ·
                refine ⟨3533947002311898859548721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75390869382653842337039381 3533947002311898859548721)
                ·
                  refine ⟨2650460251733924144661541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3533947002311898859548721 2650460251733924144661541)
                  ·
                    refine ⟨496961297200110777124039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2650460251733924144661541 496961297200110777124039)
                    ·
                      rfl

theorem cell23_2903486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_2903486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903486 prefixEnd_2903486 := by exact prefixLift 2903486
  have htrace : WordTrace (prefixWord ++ tailWord_2903486) baseStart_2903486 baseEnd_2903486 := by
    simpa [prefixWord, tailWord_2903486, baseEnd_2903486] using wordTrace_append hprefix tailTrace_2903486
  have hstable : (prefixWord ++ tailWord_2903486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903486).length < 2 ^ (prefixWord ++ tailWord_2903486).sum := by decide
  have hdescent : baseEnd_2903486 < baseStart_2903486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903510 : List Nat := [5, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4]
def baseStart_2903510 : Nat := 118140960795 + 2903510 * 2 ^ 59
def prefixEnd_2903510 : Nat := 4983230072969 + 3 ^ 40 * 2903510 * 2
def baseEnd_2903510 : Nat := 1490896215136040237472007

theorem tailTrace_2903510 : CollatzResearch.WordTrace tailWord_2903510 prefixEnd_2903510 1490896215136040237472007 := by
  unfold tailWord_2903510
  simp only [CollatzResearch.WordTrace]
  refine ⟨6618731856942914054630249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70599806474057749916055989 6618731856942914054630249)
  ·
    refine ⟨4964048892707185540972687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6618731856942914054630249 4964048892707185540972687)
    ·
      refine ⟨7446073339060778311459031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4964048892707185540972687 7446073339060778311459031)
      ·
        refine ⟨11169110008591167467188547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7446073339060778311459031 11169110008591167467188547)
        ·
          refine ⟨16753665012886751200782821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11169110008591167467188547 16753665012886751200782821)
          ·
            refine ⟨3141312189916265850146779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16753665012886751200782821 3141312189916265850146779)
            ·
              refine ⟨4711968284874398775220169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3141312189916265850146779 4711968284874398775220169)
              ·
                refine ⟨3533976213655799081415127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4711968284874398775220169 3533976213655799081415127)
                ·
                  refine ⟨5300964320483698622122691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3533976213655799081415127 5300964320483698622122691)
                  ·
                    refine ⟨7951446480725547933184037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5300964320483698622122691 7951446480725547933184037)
                    ·
                      refine ⟨1490896215136040237472007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7951446480725547933184037 1490896215136040237472007)
                      ·
                        rfl

theorem cell23_2903510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_2903510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903510 prefixEnd_2903510 := by exact prefixLift 2903510
  have htrace : WordTrace (prefixWord ++ tailWord_2903510) baseStart_2903510 baseEnd_2903510 := by
    simpa [prefixWord, tailWord_2903510, baseEnd_2903510] using wordTrace_append hprefix tailTrace_2903510
  have hstable : (prefixWord ++ tailWord_2903510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903510).length < 2 ^ (prefixWord ++ tailWord_2903510).sum := by decide
  have hdescent : baseEnd_2903510 < baseStart_2903510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903513 : List Nat := [1, 2, 1, 2, 4, 4, 1, 2, 1, 2, 3]
def baseStart_2903513 : Nat := 118140960795 + 2903513 * 2 ^ 59
def prefixEnd_2903513 : Nat := 4983230072969 + 3 ^ 40 * 2903513 * 2
def baseEnd_2903513 : Nat := 1490897755578003725734493

theorem tailTrace_2903513 : CollatzResearch.WordTrace tailWord_2903513 prefixEnd_2903513 1490897755578003725734493 := by
  unfold tailWord_2903513
  simp only [CollatzResearch.WordTrace]
  refine ⟨105899819130075756386443193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70599879420050504257628795 105899819130075756386443193)
  ·
    refine ⟨79424864347556817289832395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105899819130075756386443193 79424864347556817289832395)
    ·
      refine ⟨119137296521335225934748593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79424864347556817289832395 119137296521335225934748593)
      ·
        refine ⟨89352972391001419451061445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119137296521335225934748593 89352972391001419451061445)
        ·
          refine ⟨16753682323312766147074021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89352972391001419451061445 16753682323312766147074021)
          ·
            refine ⟨3141315435621143652576379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16753682323312766147074021 3141315435621143652576379)
            ·
              refine ⟨4711973153431715478864569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3141315435621143652576379 4711973153431715478864569)
              ·
                refine ⟨3533979865073786609148427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4711973153431715478864569 3533979865073786609148427)
                ·
                  refine ⟨5300969797610679913722641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3533979865073786609148427 5300969797610679913722641)
                  ·
                    refine ⟨3975727348208009935291981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5300969797610679913722641 3975727348208009935291981)
                    ·
                      refine ⟨1490897755578003725734493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3975727348208009935291981 1490897755578003725734493)
                      ·
                        rfl

theorem cell23_2903513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 2, 3].length) (baseStart_2903513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903513 prefixEnd_2903513 := by exact prefixLift 2903513
  have htrace : WordTrace (prefixWord ++ tailWord_2903513) baseStart_2903513 baseEnd_2903513 := by
    simpa [prefixWord, tailWord_2903513, baseEnd_2903513] using wordTrace_append hprefix tailTrace_2903513
  have hstable : (prefixWord ++ tailWord_2903513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903513).length < 2 ^ (prefixWord ++ tailWord_2903513).sum := by decide
  have hdescent : baseEnd_2903513 < baseStart_2903513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903530 : List Nat := [3, 1, 3, 1, 4, 1, 3, 1, 1, 2, 3]
def baseStart_2903530 : Nat := 118140960795 + 2903530 * 2 ^ 59
def prefixEnd_2903530 : Nat := 4983230072969 + 3 ^ 40 * 2903530 * 2
def baseEnd_2903530 : Nat := 1490906484749130159221915

theorem tailTrace_2903530 : CollatzResearch.WordTrace tailWord_2903530 prefixEnd_2903530 1490906484749130159221915 := by
  unfold tailWord_2903530
  simp only [CollatzResearch.WordTrace]
  refine ⟨26475109792753542072453011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70600292780676112193208029 26475109792753542072453011)
  ·
    refine ⟨39712664689130313108679517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26475109792753542072453011 39712664689130313108679517)
    ·
      refine ⟨14892249258423867415754819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39712664689130313108679517 14892249258423867415754819)
      ·
        refine ⟨22338373887635801123632229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14892249258423867415754819 22338373887635801123632229)
        ·
          refine ⟨4188445103931712710681043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22338373887635801123632229 4188445103931712710681043)
          ·
            refine ⟨6282667655897569066021565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4188445103931712710681043 6282667655897569066021565)
            ·
              refine ⟨2356000370961588399758087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6282667655897569066021565 2356000370961588399758087)
              ·
                refine ⟨3534000556442382599637131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2356000370961588399758087 3534000556442382599637131)
                ·
                  refine ⟨5301000834663573899455697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3534000556442382599637131 5301000834663573899455697)
                  ·
                    refine ⟨3975750625997680424591773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5301000834663573899455697 3975750625997680424591773)
                    ·
                      refine ⟨1490906484749130159221915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3975750625997680424591773 1490906484749130159221915)
                      ·
                        rfl

theorem cell23_2903530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_2903530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903530 prefixEnd_2903530 := by exact prefixLift 2903530
  have htrace : WordTrace (prefixWord ++ tailWord_2903530) baseStart_2903530 baseEnd_2903530 := by
    simpa [prefixWord, tailWord_2903530, baseEnd_2903530] using wordTrace_append hprefix tailTrace_2903530
  have hstable : (prefixWord ++ tailWord_2903530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903530).length < 2 ^ (prefixWord ++ tailWord_2903530).sum := by decide
  have hdescent : baseEnd_2903530 < baseStart_2903530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903549 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 2, 3, 4]
def baseStart_2903549 : Nat := 118140960795 + 2903549 * 2 ^ 59
def prefixEnd_2903549 : Nat := 4983230072969 + 3 ^ 40 * 2903549 * 2
def baseEnd_2903549 : Nat := 1490916240881565584884327

theorem tailTrace_2903549 : CollatzResearch.WordTrace tailWord_2903549 prefixEnd_2903549 1490916240881565584884327 := by
  unfold tailWord_2903549
  simp only [CollatzResearch.WordTrace]
  refine ⟨105901132157945334534753701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70600754771963556356502467 105901132157945334534753701)
  ·
    refine ⟨19856462279614750225266319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105901132157945334534753701 19856462279614750225266319)
    ·
      refine ⟨29784693419422125337899479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19856462279614750225266319 29784693419422125337899479)
      ·
        refine ⟨44677040129133188006849219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29784693419422125337899479 44677040129133188006849219)
        ·
          refine ⟨67015560193699782010273829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44677040129133188006849219 67015560193699782010273829)
          ·
            refine ⟨12565417536318709126926343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67015560193699782010273829 12565417536318709126926343)
            ·
              refine ⟨18848126304478063690389515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12565417536318709126926343 18848126304478063690389515)
              ·
                refine ⟨28272189456717095535584273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18848126304478063690389515 28272189456717095535584273)
                ·
                  refine ⟨21204142092537821651688205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28272189456717095535584273 21204142092537821651688205)
                  ·
                    refine ⟨7951553284701683119383077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21204142092537821651688205 7951553284701683119383077)
                    ·
                      refine ⟨1490916240881565584884327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7951553284701683119383077 1490916240881565584884327)
                      ·
                        rfl

theorem cell23_2903549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_2903549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903549 prefixEnd_2903549 := by exact prefixLift 2903549
  have htrace : WordTrace (prefixWord ++ tailWord_2903549) baseStart_2903549 baseEnd_2903549 := by
    simpa [prefixWord, tailWord_2903549, baseEnd_2903549] using wordTrace_append hprefix tailTrace_2903549
  have hstable : (prefixWord ++ tailWord_2903549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903549).length < 2 ^ (prefixWord ++ tailWord_2903549).sum := by decide
  have hdescent : baseEnd_2903549 < baseStart_2903549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903550 : List Nat := [4, 2, 2, 3, 2, 1, 1, 8]
def baseStart_2903550 : Nat := 118140960795 + 2903550 * 2 ^ 59
def prefixEnd_2903550 : Nat := 4983230072969 + 3 ^ 40 * 2903550 * 2
def baseEnd_2903550 : Nat := 55219139050452595591549

theorem tailTrace_2903550 : CollatzResearch.WordTrace tailWord_2903550 prefixEnd_2903550 55219139050452595591549 := by
  unfold tailWord_2903550
  simp only [CollatzResearch.WordTrace]
  refine ⟨13237646078867713963192513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70600779087294474470360069 13237646078867713963192513)
  ·
    refine ⟨9928234559150785472394385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13237646078867713963192513 9928234559150785472394385)
    ·
      refine ⟨7446175919363089104295789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9928234559150785472394385 7446175919363089104295789)
      ·
        refine ⟨2792315969761158414110921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7446175919363089104295789 2792315969761158414110921)
        ·
          refine ⟨2094236977320868810583191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2792315969761158414110921 2094236977320868810583191)
          ·
            refine ⟨3141355465981303215874787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2094236977320868810583191 3141355465981303215874787)
            ·
              refine ⟨4712033198971954823812181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3141355465981303215874787 4712033198971954823812181)
              ·
                refine ⟨55219139050452595591549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4712033198971954823812181 55219139050452595591549)
                ·
                  rfl

theorem cell23_2903550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 8].length) (baseStart_2903550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903550 prefixEnd_2903550 := by exact prefixLift 2903550
  have htrace : WordTrace (prefixWord ++ tailWord_2903550) baseStart_2903550 baseEnd_2903550 := by
    simpa [prefixWord, tailWord_2903550, baseEnd_2903550] using wordTrace_append hprefix tailTrace_2903550
  have hstable : (prefixWord ++ tailWord_2903550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903550).length < 2 ^ (prefixWord ++ tailWord_2903550).sum := by decide
  have hdescent : baseEnd_2903550 < baseStart_2903550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903559 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 1, 8]
def baseStart_2903559 : Nat := 118140960795 + 2903559 * 2 ^ 59
def prefixEnd_2903559 : Nat := 4983230072969 + 3 ^ 40 * 2903559 * 2
def baseEnd_2903559 : Nat := 496973791896036848586427

theorem tailTrace_2903559 : CollatzResearch.WordTrace tailWord_2903559 prefixEnd_2903559 496973791896036848586427 := by
  unfold tailWord_2903559
  simp only [CollatzResearch.WordTrace]
  refine ⟨105901496887909106242617731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70600997925272737495078487 105901496887909106242617731)
  ·
    refine ⟨158852245331863659363926597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105901496887909106242617731 158852245331863659363926597)
    ·
      refine ⟨29784795999724436130736237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158852245331863659363926597 29784795999724436130736237)
      ·
        refine ⟨11169298499896663549026089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29784795999724436130736237 11169298499896663549026089)
        ·
          refine ⟨8376973874922497661769567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11169298499896663549026089 8376973874922497661769567)
          ·
            refine ⟨12565460812383746492654351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8376973874922497661769567 12565460812383746492654351)
            ·
              refine ⟨18848191218575619738981527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12565460812383746492654351 18848191218575619738981527)
              ·
                refine ⟨28272286827863429608472291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18848191218575619738981527 28272286827863429608472291)
                ·
                  refine ⟨42408430241795144412708437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28272286827863429608472291 42408430241795144412708437)
                  ·
                    refine ⟨496973791896036848586427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42408430241795144412708437 496973791896036848586427)
                    ·
                      rfl

theorem cell23_2903559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_2903559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903559 prefixEnd_2903559 := by exact prefixLift 2903559
  have htrace : WordTrace (prefixWord ++ tailWord_2903559) baseStart_2903559 baseEnd_2903559 := by
    simpa [prefixWord, tailWord_2903559, baseEnd_2903559] using wordTrace_append hprefix tailTrace_2903559
  have hstable : (prefixWord ++ tailWord_2903559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903559).length < 2 ^ (prefixWord ++ tailWord_2903559).sum := by decide
  have hdescent : baseEnd_2903559 < baseStart_2903559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903569 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 3]
def baseStart_2903569 : Nat := 118140960795 + 2903569 * 2 ^ 59
def prefixEnd_2903569 : Nat := 4983230072969 + 3 ^ 40 * 2903569 * 2
def baseEnd_2903569 : Nat := 1490926510494655506634235

theorem tailTrace_2903569 : CollatzResearch.WordTrace tailWord_2903569 prefixEnd_2903569 1490926510494655506634235 := by
  unfold tailWord_2903569
  simp only [CollatzResearch.WordTrace]
  refine ⟨105901861617872877950481761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70601241078581918633654507 105901861617872877950481761)
  ·
    refine ⟨79426396213404658462861321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105901861617872877950481761 79426396213404658462861321)
    ·
      refine ⟨59569797160053493847145991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79426396213404658462861321 59569797160053493847145991)
      ·
        refine ⟨89354695740080240770718987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59569797160053493847145991 89354695740080240770718987)
        ·
          refine ⟨134032043610120361156078481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89354695740080240770718987 134032043610120361156078481)
          ·
            refine ⟨100524032707590270867058861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134032043610120361156078481 100524032707590270867058861)
            ·
              refine ⟨37696512265346351575147073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100524032707590270867058861 37696512265346351575147073)
              ·
                refine ⟨28272384199009763681360305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37696512265346351575147073 28272384199009763681360305)
                ·
                  refine ⟨21204288149257322761020229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28272384199009763681360305 21204288149257322761020229)
                  ·
                    refine ⟨3975804027985748017691293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21204288149257322761020229 3975804027985748017691293)
                    ·
                      refine ⟨1490926510494655506634235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3975804027985748017691293 1490926510494655506634235)
                      ·
                        rfl

theorem cell23_2903569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 3].length) (baseStart_2903569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903569 prefixEnd_2903569 := by exact prefixLift 2903569
  have htrace : WordTrace (prefixWord ++ tailWord_2903569) baseStart_2903569 baseEnd_2903569 := by
    simpa [prefixWord, tailWord_2903569, baseEnd_2903569] using wordTrace_append hprefix tailTrace_2903569
  have hstable : (prefixWord ++ tailWord_2903569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903569).length < 2 ^ (prefixWord ++ tailWord_2903569).sum := by decide
  have hdescent : baseEnd_2903569 < baseStart_2903569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903587 : List Nat := [1, 1, 1, 4, 5, 2, 2, 1, 1, 3, 2]
def baseStart_2903587 : Nat := 118140960795 + 2903587 * 2 ^ 59
def prefixEnd_2903587 : Nat := 4983230072969 + 3 ^ 40 * 2903587 * 2
def baseEnd_2903587 : Nat := 1490935753146436436209153

theorem tailTrace_2903587 : CollatzResearch.WordTrace tailWord_2903587 prefixEnd_2903587 1490935753146436436209153 := by
  unfold tailWord_2903587
  simp only [CollatzResearch.WordTrace]
  refine ⟨105902518131807667024637015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70601678754538444683091343 105902518131807667024637015)
  ·
    refine ⟨158853777197711500536955523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105902518131807667024637015 158853777197711500536955523)
    ·
      refine ⟨238280665796567250805433285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158853777197711500536955523 238280665796567250805433285)
      ·
        refine ⟨44677624836856359526018741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 238280665796567250805433285 44677624836856359526018741)
        ·
          refine ⟨4188527328455283705564257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44677624836856359526018741 4188527328455283705564257)
          ·
            refine ⟨3141395496341462779173193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4188527328455283705564257 3141395496341462779173193)
            ·
              refine ⟨2356046622256097084379895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3141395496341462779173193 2356046622256097084379895)
              ·
                refine ⟨3534069933384145626569843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2356046622256097084379895 3534069933384145626569843)
                ·
                  refine ⟨5301104900076218439854765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3534069933384145626569843 5301104900076218439854765)
                  ·
                    refine ⟨1987914337528581914945537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5301104900076218439854765 1987914337528581914945537)
                    ·
                      refine ⟨1490935753146436436209153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1987914337528581914945537 1490935753146436436209153)
                      ·
                        rfl

theorem cell23_2903587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 1, 3, 2].length) (baseStart_2903587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903587 prefixEnd_2903587 := by exact prefixLift 2903587
  have htrace : WordTrace (prefixWord ++ tailWord_2903587) baseStart_2903587 baseEnd_2903587 := by
    simpa [prefixWord, tailWord_2903587, baseEnd_2903587] using wordTrace_append hprefix tailTrace_2903587
  have hstable : (prefixWord ++ tailWord_2903587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903587).length < 2 ^ (prefixWord ++ tailWord_2903587).sum := by decide
  have hdescent : baseEnd_2903587 < baseStart_2903587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903617 : List Nat := [1, 2, 5, 1, 1, 1, 5, 1, 2, 2, 2]
def baseStart_2903617 : Nat := 118140960795 + 2903617 * 2 ^ 59
def prefixEnd_2903617 : Nat := 4983230072969 + 3 ^ 40 * 2903617 * 2
def baseEnd_2903617 : Nat := 1490951157566071318834015

theorem tailTrace_2903617 : CollatzResearch.WordTrace tailWord_2903617 prefixEnd_2903617 1490951157566071318834015 := by
  unfold tailWord_2903617
  simp only [CollatzResearch.WordTrace]
  refine ⟨105903612321698982148229105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70602408214465988098819403 105903612321698982148229105)
  ·
    refine ⟨79427709241274236611171829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105903612321698982148229105 79427709241274236611171829)
    ·
      refine ⟨7446347741369459682297359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79427709241274236611171829 7446347741369459682297359)
      ·
        refine ⟨11169521612054189523446039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7446347741369459682297359 11169521612054189523446039)
        ·
          refine ⟨16754282418081284285169059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11169521612054189523446039 16754282418081284285169059)
          ·
            refine ⟨25131423627121926427753589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16754282418081284285169059 25131423627121926427753589)
            ·
              refine ⟨2356070965042680602601899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25131423627121926427753589 2356070965042680602601899)
              ·
                refine ⟨3534106447564020903902849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2356070965042680602601899 3534106447564020903902849)
                ·
                  refine ⟨2650579835673015677927137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3534106447564020903902849 2650579835673015677927137)
                  ·
                    refine ⟨1987934876754761758445353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2650579835673015677927137 1987934876754761758445353)
                    ·
                      refine ⟨1490951157566071318834015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1987934876754761758445353 1490951157566071318834015)
                      ·
                        rfl

theorem cell23_2903617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_2903617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903617 prefixEnd_2903617 := by exact prefixLift 2903617
  have htrace : WordTrace (prefixWord ++ tailWord_2903617) baseStart_2903617 baseEnd_2903617 := by
    simpa [prefixWord, tailWord_2903617, baseEnd_2903617] using wordTrace_append hprefix tailTrace_2903617
  have hstable : (prefixWord ++ tailWord_2903617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903617).length < 2 ^ (prefixWord ++ tailWord_2903617).sum := by decide
  have hdescent : baseEnd_2903617 < baseStart_2903617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903636 : List Nat := [2, 4, 1, 1, 1, 2, 2, 3, 2, 5]
def baseStart_2903636 : Nat := 118140960795 + 2903636 * 2 ^ 59
def prefixEnd_2903636 : Nat := 4983230072969 + 3 ^ 40 * 2903636 * 2
def baseEnd_2903636 : Nat := 496986971232835581498809

theorem tailTrace_2903636 : CollatzResearch.WordTrace tailWord_2903636 prefixEnd_2903636 496986971232835581498809 := by
  unfold tailWord_2903636
  simp only [CollatzResearch.WordTrace]
  refine ⟨52952152654315074196585381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70602870205753432262113841 52952152654315074196585381)
  ·
    refine ⟨9928528622684076411859759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52952152654315074196585381 9928528622684076411859759)
    ·
      refine ⟨14892792934026114617789639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9928528622684076411859759 14892792934026114617789639)
      ·
        refine ⟨22339189401039171926684459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14892792934026114617789639 22339189401039171926684459)
        ·
          refine ⟨33508784101558757890026689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22339189401039171926684459 33508784101558757890026689)
          ·
            refine ⟨25131588076169068417520017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33508784101558757890026689 25131588076169068417520017)
            ·
              refine ⟨18848691057126801313140013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25131588076169068417520017 18848691057126801313140013)
              ·
                refine ⟨7068259146422550492427505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18848691057126801313140013 7068259146422550492427505)
                ·
                  refine ⟨5301194359816912869320629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7068259146422550492427505 5301194359816912869320629)
                  ·
                    refine ⟨496986971232835581498809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5301194359816912869320629 496986971232835581498809)
                    ·
                      rfl

theorem cell23_2903636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_2903636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903636 prefixEnd_2903636 := by exact prefixLift 2903636
  have htrace : WordTrace (prefixWord ++ tailWord_2903636) baseStart_2903636 baseEnd_2903636 := by
    simpa [prefixWord, tailWord_2903636, baseEnd_2903636] using wordTrace_append hprefix tailTrace_2903636
  have hstable : (prefixWord ++ tailWord_2903636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903636).length < 2 ^ (prefixWord ++ tailWord_2903636).sum := by decide
  have hdescent : baseEnd_2903636 < baseStart_2903636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903676 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 6, 2, 3]
def baseStart_2903676 : Nat := 118140960795 + 2903676 * 2 ^ 59
def prefixEnd_2903676 : Nat := 4983230072969 + 3 ^ 40 * 2903676 * 2
def baseEnd_2903676 : Nat := 1490981452924686587996243

theorem tailTrace_2903676 : CollatzResearch.WordTrace tailWord_2903676 prefixEnd_2903676 1490981452924686587996243 := by
  unfold tailWord_2903676
  simp only [CollatzResearch.WordTrace]
  refine ⟨52952882114242617612313441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70603842818990156816417921 52952882114242617612313441)
  ·
    refine ⟨39714661585681963209235081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52952882114242617612313441 39714661585681963209235081)
    ·
      refine ⟨29785996189261472406926311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39714661585681963209235081 29785996189261472406926311)
      ·
        refine ⟨44678994283892208610389467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29785996189261472406926311 44678994283892208610389467)
        ·
          refine ⟨67018491425838312915584201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44678994283892208610389467 67018491425838312915584201)
          ·
            refine ⟨50263868569378734686688151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67018491425838312915584201 50263868569378734686688151)
            ·
              refine ⟨75395802854068102030032227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50263868569378734686688151 75395802854068102030032227)
              ·
                refine ⟨113093704281102153045048341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75395802854068102030032227 113093704281102153045048341)
                ·
                  refine ⟨5301267388176663423986641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 113093704281102153045048341 5301267388176663423986641)
                  ·
                    refine ⟨3975950541132497567989981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5301267388176663423986641 3975950541132497567989981)
                    ·
                      refine ⟨1490981452924686587996243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3975950541132497567989981 1490981452924686587996243)
                      ·
                        rfl

theorem cell23_2903676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_2903676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903676 prefixEnd_2903676 := by exact prefixLift 2903676
  have htrace : WordTrace (prefixWord ++ tailWord_2903676) baseStart_2903676 baseEnd_2903676 := by
    simpa [prefixWord, tailWord_2903676, baseEnd_2903676] using wordTrace_append hprefix tailTrace_2903676
  have hstable : (prefixWord ++ tailWord_2903676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903676).length < 2 ^ (prefixWord ++ tailWord_2903676).sum := by decide
  have hdescent : baseEnd_2903676 < baseStart_2903676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903710 : List Nat := [4, 3, 1, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_2903710 : Nat := 118140960795 + 2903710 * 2 ^ 59
def prefixEnd_2903710 : Nat := 4983230072969 + 3 ^ 40 * 2903710 * 2
def baseEnd_2903710 : Nat := 1490998911266939454971087

theorem tailTrace_2903710 : CollatzResearch.WordTrace tailWord_2903710 prefixEnd_2903710 1490998911266939454971087 := by
  unfold tailWord_2903710
  simp only [CollatzResearch.WordTrace]
  refine ⟨13238375538795257378920573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70604669540241372687576389 13238375538795257378920573)
  ·
    refine ⟨4964390827048221517095215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13238375538795257378920573 4964390827048221517095215)
    ·
      refine ⟨7446586240572332275642823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4964390827048221517095215 7446586240572332275642823)
      ·
        refine ⟨11169879360858498413464235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7446586240572332275642823 11169879360858498413464235)
        ·
          refine ⟨16754819041287747620196353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11169879360858498413464235 16754819041287747620196353)
          ·
            refine ⟨12566114280965810715147265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16754819041287747620196353 12566114280965810715147265)
            ·
              refine ⟨9424585710724358036360449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12566114280965810715147265 9424585710724358036360449)
              ·
                refine ⟨7068439283043268527270337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9424585710724358036360449 7068439283043268527270337)
                ·
                  refine ⟨5301329462282451395452753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7068439283043268527270337 5301329462282451395452753)
                  ·
                    refine ⟨3975997096711838546589565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5301329462282451395452753 3975997096711838546589565)
                    ·
                      refine ⟨1490998911266939454971087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3975997096711838546589565 1490998911266939454971087)
                      ·
                        rfl

theorem cell23_2903710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_2903710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903710 prefixEnd_2903710 := by exact prefixLift 2903710
  have htrace : WordTrace (prefixWord ++ tailWord_2903710) baseStart_2903710 baseEnd_2903710 := by
    simpa [prefixWord, tailWord_2903710, baseEnd_2903710] using wordTrace_append hprefix tailTrace_2903710
  have hstable : (prefixWord ++ tailWord_2903710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903710).length < 2 ^ (prefixWord ++ tailWord_2903710).sum := by decide
  have hdescent : baseEnd_2903710 < baseStart_2903710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903713 : List Nat := [1, 2, 3, 3, 2, 2, 2, 2, 6]
def baseStart_2903713 : Nat := 118140960795 + 2903713 * 2 ^ 59
def prefixEnd_2903713 : Nat := 4983230072969 + 3 ^ 40 * 2903713 * 2
def baseEnd_2903713 : Nat := 165666716856544771470397

theorem tailTrace_2903713 : CollatzResearch.WordTrace tailWord_2903713 prefixEnd_2903713 165666716856544771470397 := by
  unfold tailWord_2903713
  simp only [CollatzResearch.WordTrace]
  refine ⟨105907113729351190543723793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70604742486234127029149195 105907113729351190543723793)
  ·
    refine ⟨79430335297013392907792845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105907113729351190543723793 79430335297013392907792845)
    ·
      refine ⟨29786375736380022340422317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79430335297013392907792845 29786375736380022340422317)
      ·
        refine ⟨11169890901142508377658369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29786375736380022340422317 11169890901142508377658369)
        ·
          refine ⟨8377418175856881283243777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11169890901142508377658369 8377418175856881283243777)
          ·
            refine ⟨6283063631892660962432833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8377418175856881283243777 6283063631892660962432833)
            ·
              refine ⟨4712297723919495721824625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6283063631892660962432833 4712297723919495721824625)
              ·
                refine ⟨3534223292939621791368469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4712297723919495721824625 3534223292939621791368469)
                ·
                  refine ⟨165666716856544771470397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3534223292939621791368469 165666716856544771470397)
                  ·
                    rfl

theorem cell23_2903713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 6].length) (baseStart_2903713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903713 prefixEnd_2903713 := by exact prefixLift 2903713
  have htrace : WordTrace (prefixWord ++ tailWord_2903713) baseStart_2903713 baseEnd_2903713 := by
    simpa [prefixWord, tailWord_2903713, baseEnd_2903713] using wordTrace_append hprefix tailTrace_2903713
  have hstable : (prefixWord ++ tailWord_2903713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903713).length < 2 ^ (prefixWord ++ tailWord_2903713).sum := by decide
  have hdescent : baseEnd_2903713 < baseStart_2903713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903740 : List Nat := [2, 2, 2, 3, 1, 3, 1, 2, 3, 1, 3]
def baseStart_2903740 : Nat := 118140960795 + 2903740 * 2 ^ 59
def prefixEnd_2903740 : Nat := 4983230072969 + 3 ^ 40 * 2903740 * 2
def baseEnd_2903740 : Nat := 1491014315686574337595949

theorem tailTrace_2903740 : CollatzResearch.WordTrace tailWord_2903740 prefixEnd_2903740 1491014315686574337595949 := by
  unfold tailWord_2903740
  simp only [CollatzResearch.WordTrace]
  refine ⟨52954049250126687077478337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70605399000168916103304449 52954049250126687077478337)
  ·
    refine ⟨39715536937595015308108753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52954049250126687077478337 39715536937595015308108753)
    ·
      refine ⟨29786652703196261481081565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39715536937595015308108753 29786652703196261481081565)
      ·
        refine ⟨11169994763698598055405587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29786652703196261481081565 11169994763698598055405587)
        ·
          refine ⟨16754992145547897083108381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11169994763698598055405587 16754992145547897083108381)
          ·
            refine ⟨6283122054580461406165643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16754992145547897083108381 6283122054580461406165643)
            ·
              refine ⟨9424683081870692109248465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6283122054580461406165643 9424683081870692109248465)
              ·
                refine ⟨7068512311403019081936349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9424683081870692109248465 7068512311403019081936349)
                ·
                  refine ⟨2650692116776132155726131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7068512311403019081936349 2650692116776132155726131)
                  ·
                    refine ⟨3976038175164198233589197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2650692116776132155726131 3976038175164198233589197)
                    ·
                      refine ⟨1491014315686574337595949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3976038175164198233589197 1491014315686574337595949)
                      ·
                        rfl

theorem cell23_2903740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_2903740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903740 prefixEnd_2903740 := by exact prefixLift 2903740
  have htrace : WordTrace (prefixWord ++ tailWord_2903740) baseStart_2903740 baseEnd_2903740 := by
    simpa [prefixWord, tailWord_2903740, baseEnd_2903740] using wordTrace_append hprefix tailTrace_2903740
  have hstable : (prefixWord ++ tailWord_2903740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903740).length < 2 ^ (prefixWord ++ tailWord_2903740).sum := by decide
  have hdescent : baseEnd_2903740 < baseStart_2903740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903776 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 4]
def baseStart_2903776 : Nat := 118140960795 + 2903776 * 2 ^ 59
def prefixEnd_2903776 : Nat := 4983230072969 + 3 ^ 40 * 2903776 * 2
def baseEnd_2903776 : Nat := 1491032800990136196745783

theorem tailTrace_2903776 : CollatzResearch.WordTrace tailWord_2903776 prefixEnd_2903776 1491032800990136196745783 := by
  unfold tailWord_2903776
  simp only [CollatzResearch.WordTrace]
  refine ⟨52954705764061476151633591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70606274352081968202178121 52954705764061476151633591)
  ·
    refine ⟨79432058646092214227450387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52954705764061476151633591 79432058646092214227450387)
    ·
      refine ⟨119148087969138321341175581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79432058646092214227450387 119148087969138321341175581)
      ·
        refine ⟨44680532988426870502940843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119148087969138321341175581 44680532988426870502940843)
        ·
          refine ⟨67020799482640305754411265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44680532988426870502940843 67020799482640305754411265)
          ·
            refine ⟨50265599611980229315808449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67020799482640305754411265 50265599611980229315808449)
            ·
              refine ⟨37699199708985171986856337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50265599611980229315808449 37699199708985171986856337)
              ·
                refine ⟨28274399781738878990142253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37699199708985171986856337 28274399781738878990142253)
                ·
                  refine ⟨10602899918152079621303345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28274399781738878990142253 10602899918152079621303345)
                  ·
                    refine ⟨7952174938614059715977509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10602899918152079621303345 7952174938614059715977509)
                    ·
                      refine ⟨1491032800990136196745783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7952174938614059715977509 1491032800990136196745783)
                      ·
                        rfl

theorem cell23_2903776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_2903776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903776 prefixEnd_2903776 := by exact prefixLift 2903776
  have htrace : WordTrace (prefixWord ++ tailWord_2903776) baseStart_2903776 baseEnd_2903776 := by
    simpa [prefixWord, tailWord_2903776, baseEnd_2903776] using wordTrace_append hprefix tailTrace_2903776
  have hstable : (prefixWord ++ tailWord_2903776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903776).length < 2 ^ (prefixWord ++ tailWord_2903776).sum := by decide
  have hdescent : baseEnd_2903776 < baseStart_2903776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903793 : List Nat := [1, 2, 2, 2, 2, 3, 3, 1, 1, 2, 4]
def baseStart_2903793 : Nat := 118140960795 + 2903793 * 2 ^ 59
def prefixEnd_2903793 : Nat := 4983230072969 + 3 ^ 40 * 2903793 * 2
def baseEnd_2903793 : Nat := 1491041530161262630233205

theorem tailTrace_2903793 : CollatzResearch.WordTrace tailWord_2903793 prefixEnd_2903793 1491041530161262630233205 := by
  unfold tailWord_2903793
  simp only [CollatzResearch.WordTrace]
  refine ⟨105910031569061364206636033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70606687712707576137757355 105910031569061364206636033)
  ·
    refine ⟨79432523676796023154977025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105910031569061364206636033 79432523676796023154977025)
    ·
      refine ⟨59574392757597017366232769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79432523676796023154977025 59574392757597017366232769)
      ·
        refine ⟨44680794568197763024674577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59574392757597017366232769 44680794568197763024674577)
        ·
          refine ⟨33510595926148322268505933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44680794568197763024674577 33510595926148322268505933)
          ·
            refine ⟨12566473472305620850689725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33510595926148322268505933 12566473472305620850689725)
            ·
              refine ⟨4712427552114607819008647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12566473472305620850689725 4712427552114607819008647)
              ·
                refine ⟨7068641328171911728512971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4712427552114607819008647 7068641328171911728512971)
                ·
                  refine ⟨10602961992257867592769457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7068641328171911728512971 10602961992257867592769457)
                  ·
                    refine ⟨7952221494193400694577093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10602961992257867592769457 7952221494193400694577093)
                    ·
                      refine ⟨1491041530161262630233205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7952221494193400694577093 1491041530161262630233205)
                      ·
                        rfl

theorem cell23_2903793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_2903793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903793 prefixEnd_2903793 := by exact prefixLift 2903793
  have htrace : WordTrace (prefixWord ++ tailWord_2903793) baseStart_2903793 baseEnd_2903793 := by
    simpa [prefixWord, tailWord_2903793, baseEnd_2903793] using wordTrace_append hprefix tailTrace_2903793
  have hstable : (prefixWord ++ tailWord_2903793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903793).length < 2 ^ (prefixWord ++ tailWord_2903793).sum := by decide
  have hdescent : baseEnd_2903793 < baseStart_2903793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903831 : List Nat := [1, 1, 3, 4, 2, 2, 3, 2, 1, 2, 2]
def baseStart_2903831 : Nat := 118140960795 + 2903831 * 2 ^ 59
def prefixEnd_2903831 : Nat := 4983230072969 + 3 ^ 40 * 2903831 * 2
def baseEnd_2903831 : Nat := 1491061042426133481558031

theorem tailTrace_2903831 : CollatzResearch.WordTrace tailWord_2903831 prefixEnd_2903831 1491061042426133481558031 := by
  unfold tailWord_2903831
  simp only [CollatzResearch.WordTrace]
  refine ⟨105911417542923696696519347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70607611695282464464346231 105911417542923696696519347)
  ·
    refine ⟨158867126314385545044779021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105911417542923696696519347 158867126314385545044779021)
    ·
      refine ⟨59575172367894579391792133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158867126314385545044779021 59575172367894579391792133)
      ·
        refine ⟨11170344818980233635961025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59575172367894579391792133 11170344818980233635961025)
        ·
          refine ⟨8377758614235175226970769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11170344818980233635961025 8377758614235175226970769)
          ·
            refine ⟨6283318960676381420228077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8377758614235175226970769 6283318960676381420228077)
            ·
              refine ⟨2356244610253643032585529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6283318960676381420228077 2356244610253643032585529)
              ·
                refine ⟨1767183457690232274439147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2356244610253643032585529 1767183457690232274439147)
                ·
                  refine ⟨2650775186535348411658721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1767183457690232274439147 2650775186535348411658721)
                  ·
                    refine ⟨1988081389901511308744041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2650775186535348411658721 1988081389901511308744041)
                    ·
                      refine ⟨1491061042426133481558031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1988081389901511308744041 1491061042426133481558031)
                      ·
                        rfl

theorem cell23_2903831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_2903831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903831 prefixEnd_2903831 := by exact prefixLift 2903831
  have htrace : WordTrace (prefixWord ++ tailWord_2903831) baseStart_2903831 baseEnd_2903831 := by
    simpa [prefixWord, tailWord_2903831, baseEnd_2903831] using wordTrace_append hprefix tailTrace_2903831
  have hstable : (prefixWord ++ tailWord_2903831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903831).length < 2 ^ (prefixWord ++ tailWord_2903831).sum := by decide
  have hdescent : baseEnd_2903831 < baseStart_2903831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903840 : List Nat := [2, 1, 1, 5, 1, 1, 2, 2, 3, 3, 2]
def baseStart_2903840 : Nat := 118140960795 + 2903840 * 2 ^ 59
def prefixEnd_2903840 : Nat := 4983230072969 + 3 ^ 40 * 2903840 * 2
def baseEnd_2903840 : Nat := 1491065663752023946345489

theorem tailTrace_2903840 : CollatzResearch.WordTrace tailWord_2903840 prefixEnd_2903840 1491065663752023946345489 := by
  unfold tailWord_2903840
  simp only [CollatzResearch.WordTrace]
  refine ⟨52955872899945545616798487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70607830533260727489064649 52955872899945545616798487)
  ·
    refine ⟨79433809349918318425197731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52955872899945545616798487 79433809349918318425197731)
    ·
      refine ⟨119150714024877477637796597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79433809349918318425197731 119150714024877477637796597)
      ·
        refine ⟨11170379439832263528543431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119150714024877477637796597 11170379439832263528543431)
        ·
          refine ⟨16755569159748395292815147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11170379439832263528543431 16755569159748395292815147)
          ·
            refine ⟨25133353739622592939222721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16755569159748395292815147 25133353739622592939222721)
            ·
              refine ⟨18850015304716944704417041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25133353739622592939222721 18850015304716944704417041)
              ·
                refine ⟨14137511478537708528312781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18850015304716944704417041 14137511478537708528312781)
                ·
                  refine ⟨5301566804451640698117293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14137511478537708528312781 5301566804451640698117293)
                  ·
                    refine ⟨1988087551669365261793985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5301566804451640698117293 1988087551669365261793985)
                    ·
                      refine ⟨1491065663752023946345489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1988087551669365261793985 1491065663752023946345489)
                      ·
                        rfl

theorem cell23_2903840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_2903840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903840 prefixEnd_2903840 := by exact prefixLift 2903840
  have htrace : WordTrace (prefixWord ++ tailWord_2903840) baseStart_2903840 baseEnd_2903840 := by
    simpa [prefixWord, tailWord_2903840, baseEnd_2903840] using wordTrace_append hprefix tailTrace_2903840
  have hstable : (prefixWord ++ tailWord_2903840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903840).length < 2 ^ (prefixWord ++ tailWord_2903840).sum := by decide
  have hdescent : baseEnd_2903840 < baseStart_2903840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903857 : List Nat := [1, 2, 2, 3, 2, 2, 3, 2, 1, 3, 2]
def baseStart_2903857 : Nat := 118140960795 + 2903857 * 2 ^ 59
def prefixEnd_2903857 : Nat := 4983230072969 + 3 ^ 40 * 2903857 * 2
def baseEnd_2903857 : Nat := 1491074392923150379832911

theorem tailTrace_2903857 : CollatzResearch.WordTrace tailWord_2903857 prefixEnd_2903857 1491074392923150379832911 := by
  unfold tailWord_2903857
  simp only [CollatzResearch.WordTrace]
  refine ⟨105912365840829503136965825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70608243893886335424643883 105912365840829503136965825)
  ·
    refine ⟨79434274380622127352724369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105912365840829503136965825 79434274380622127352724369)
    ·
      refine ⟨59575705785466595514543277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79434274380622127352724369 59575705785466595514543277)
      ·
        refine ⟨22340889669549973317953729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59575705785466595514543277 22340889669549973317953729)
        ·
          refine ⟨16755667252162479988465297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22340889669549973317953729 16755667252162479988465297)
          ·
            refine ⟨12566750439121859991348973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16755667252162479988465297 12566750439121859991348973)
            ·
              refine ⟨4712531414670697496755865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12566750439121859991348973 4712531414670697496755865)
              ·
                refine ⟨3534398561003023122566899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4712531414670697496755865 3534398561003023122566899)
                ·
                  refine ⟨5301597841504534683850349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3534398561003023122566899 5301597841504534683850349)
                  ·
                    refine ⟨1988099190564200506443881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5301597841504534683850349 1988099190564200506443881)
                    ·
                      refine ⟨1491074392923150379832911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1988099190564200506443881 1491074392923150379832911)
                      ·
                        rfl

theorem cell23_2903857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_2903857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903857 prefixEnd_2903857 := by exact prefixLift 2903857
  have htrace : WordTrace (prefixWord ++ tailWord_2903857) baseStart_2903857 baseEnd_2903857 := by
    simpa [prefixWord, tailWord_2903857, baseEnd_2903857] using wordTrace_append hprefix tailTrace_2903857
  have hstable : (prefixWord ++ tailWord_2903857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903857).length < 2 ^ (prefixWord ++ tailWord_2903857).sum := by decide
  have hdescent : baseEnd_2903857 < baseStart_2903857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903896 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 1, 3, 8]
def baseStart_2903896 : Nat := 118140960795 + 2903896 * 2 ^ 59
def prefixEnd_2903896 : Nat := 4983230072969 + 3 ^ 40 * 2903896 * 2
def baseEnd_2903896 : Nat := 1491094418668675727245231

theorem tailTrace_2903896 : CollatzResearch.WordTrace tailWord_2903896 prefixEnd_2903896 1491094418668675727245231 := by
  unfold tailWord_2903896
  simp only [CollatzResearch.WordTrace]
  refine ⟨52956894143844106398817771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70609192191792141865090361 52956894143844106398817771)
  ·
    refine ⟨79435341215766159598226657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52956894143844106398817771 79435341215766159598226657)
    ·
      refine ⟨59576505911824619698669993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79435341215766159598226657 59576505911824619698669993)
      ·
        refine ⟨44682379433868464774002495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59576505911824619698669993 44682379433868464774002495)
        ·
          refine ⟨67023569150802697161003743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44682379433868464774002495 67023569150802697161003743)
          ·
            refine ⟨100535353726204045741505615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67023569150802697161003743 100535353726204045741505615)
            ·
              refine ⟨150803030589306068612258423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100535353726204045741505615 150803030589306068612258423)
              ·
                refine ⟨226204545883959102918387635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150803030589306068612258423 226204545883959102918387635)
                ·
                  refine ⟨339306818825938654377581453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 226204545883959102918387635 339306818825938654377581453)
                  ·
                    refine ⟨127240057059726995391593045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 339306818825938654377581453 127240057059726995391593045)
                    ·
                      refine ⟨1491094418668675727245231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 127240057059726995391593045 1491094418668675727245231)
                      ·
                        rfl

theorem cell23_2903896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_2903896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903896 prefixEnd_2903896 := by exact prefixLift 2903896
  have htrace : WordTrace (prefixWord ++ tailWord_2903896) baseStart_2903896 baseEnd_2903896 := by
    simpa [prefixWord, tailWord_2903896, baseEnd_2903896] using wordTrace_append hprefix tailTrace_2903896
  have hstable : (prefixWord ++ tailWord_2903896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903896).length < 2 ^ (prefixWord ++ tailWord_2903896).sum := by decide
  have hdescent : baseEnd_2903896 < baseStart_2903896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903903 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 3]
def baseStart_2903903 : Nat := 118140960795 + 2903903 * 2 ^ 59
def prefixEnd_2903903 : Nat := 4983230072969 + 3 ^ 40 * 2903903 * 2
def baseEnd_2903903 : Nat := 1491098013033257199857699

theorem tailTrace_2903903 : CollatzResearch.WordTrace tailWord_2903903 prefixEnd_2903903 1491098013033257199857699 := by
  unfold tailWord_2903903
  simp only [CollatzResearch.WordTrace]
  refine ⟨105914043598662852993140363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70609362399108568662093575 105914043598662852993140363)
  ·
    refine ⟨158871065397994279489710545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105914043598662852993140363 158871065397994279489710545)
    ·
      refine ⟨119153299048495709617282909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158871065397994279489710545 119153299048495709617282909)
      ·
        refine ⟨44682487143185891106481091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119153299048495709617282909 44682487143185891106481091)
        ·
          refine ⟨67023730714778836659721637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44682487143185891106481091 67023730714778836659721637)
          ·
            refine ⟨12566949509021031873697807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67023730714778836659721637 12566949509021031873697807)
            ·
              refine ⟨18850424263531547810546711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12566949509021031873697807 18850424263531547810546711)
              ·
                refine ⟨28275636395297321715820067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18850424263531547810546711 28275636395297321715820067)
                ·
                  refine ⟨42413454592945982573730101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28275636395297321715820067 42413454592945982573730101)
                  ·
                    refine ⟨3976261368088685866287197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42413454592945982573730101 3976261368088685866287197)
                    ·
                      refine ⟨1491098013033257199857699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3976261368088685866287197 1491098013033257199857699)
                      ·
                        rfl

theorem cell23_2903903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_2903903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903903 prefixEnd_2903903 := by exact prefixLift 2903903
  have htrace : WordTrace (prefixWord ++ tailWord_2903903) baseStart_2903903 baseEnd_2903903 := by
    simpa [prefixWord, tailWord_2903903, baseEnd_2903903] using wordTrace_append hprefix tailTrace_2903903
  have hstable : (prefixWord ++ tailWord_2903903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903903).length < 2 ^ (prefixWord ++ tailWord_2903903).sum := by decide
  have hdescent : baseEnd_2903903 < baseStart_2903903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903997 : List Nat := [1, 4, 1, 2, 3, 2, 1, 2, 2, 2, 3]
def baseStart_2903997 : Nat := 118140960795 + 2903997 * 2 ^ 59
def prefixEnd_2903997 : Nat := 4983230072969 + 3 ^ 40 * 2903997 * 2
def baseEnd_2903997 : Nat := 1491146280214779832082267

theorem tailTrace_2903997 : CollatzResearch.WordTrace tailWord_2903997 prefixEnd_2903997 1491146280214779832082267 := by
  unfold tailWord_2903997
  simp only [CollatzResearch.WordTrace]
  refine ⟨105917472060322307047062245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70611648040214871364708163 105917472060322307047062245)
  ·
    refine ⟨19859526011310432571324171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105917472060322307047062245 19859526011310432571324171)
    ·
      refine ⟨29789289016965648856986257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19859526011310432571324171 29789289016965648856986257)
      ·
        refine ⟨22341966762724236642739693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29789289016965648856986257 22341966762724236642739693)
        ·
          refine ⟨8378237536021588741027385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22341966762724236642739693 8378237536021588741027385)
          ·
            refine ⟨6283678152016191555770539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8378237536021588741027385 6283678152016191555770539)
            ·
              refine ⟨9425517228024287333655809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6283678152016191555770539 9425517228024287333655809)
              ·
                refine ⟨7069137921018215500241857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9425517228024287333655809 7069137921018215500241857)
                ·
                  refine ⟨5301853440763661625181393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7069137921018215500241857 5301853440763661625181393)
                  ·
                    refine ⟨3976390080572746218886045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5301853440763661625181393 3976390080572746218886045)
                    ·
                      refine ⟨1491146280214779832082267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3976390080572746218886045 1491146280214779832082267)
                      ·
                        rfl

theorem cell23_2903997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_2903997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2903997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2903997 prefixEnd_2903997 := by exact prefixLift 2903997
  have htrace : WordTrace (prefixWord ++ tailWord_2903997) baseStart_2903997 baseEnd_2903997 := by
    simpa [prefixWord, tailWord_2903997, baseEnd_2903997] using wordTrace_append hprefix tailTrace_2903997
  have hstable : (prefixWord ++ tailWord_2903997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903997).length < 2 ^ (prefixWord ++ tailWord_2903997).sum := by decide
  have hdescent : baseEnd_2903997 < baseStart_2903997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904047 : List Nat := [1, 1, 2, 1, 4, 2, 5, 1, 1, 5]
def baseStart_2904047 : Nat := 118140960795 + 2904047 * 2 ^ 59
def prefixEnd_2904047 : Nat := 4983230072969 + 3 ^ 40 * 2904047 * 2
def baseEnd_2904047 : Nat := 497057318082501545485679

theorem tailTrace_2904047 : CollatzResearch.WordTrace tailWord_2904047 prefixEnd_2904047 497057318082501545485679 := by
  unfold tailWord_2904047
  simp only [CollatzResearch.WordTrace]
  refine ⟨105919295710141165586382395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70612863806760777057588263 105919295710141165586382395)
  ·
    refine ⟨158878943565211748379573593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105919295710141165586382395 158878943565211748379573593)
    ·
      refine ⟨119159207673908811284680195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158878943565211748379573593 119159207673908811284680195)
      ·
        refine ⟨178738811510863216927020293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119159207673908811284680195 178738811510863216927020293)
        ·
          refine ⟨33513527158286853173816305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178738811510863216927020293 33513527158286853173816305)
          ·
            refine ⟨25135145368715139880362229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33513527158286853173816305 25135145368715139880362229)
            ·
              refine ⟨2356419878317044363783959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25135145368715139880362229 2356419878317044363783959)
              ·
                refine ⟨3534629817475566545675939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2356419878317044363783959 3534629817475566545675939)
                ·
                  refine ⟨5301944726213349818513909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3534629817475566545675939 5301944726213349818513909)
                  ·
                    refine ⟨497057318082501545485679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5301944726213349818513909 497057318082501545485679)
                    ·
                      rfl

theorem cell23_2904047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 1, 5].length) (baseStart_2904047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904047 prefixEnd_2904047 := by exact prefixLift 2904047
  have htrace : WordTrace (prefixWord ++ tailWord_2904047) baseStart_2904047 baseEnd_2904047 := by
    simpa [prefixWord, tailWord_2904047, baseEnd_2904047] using wordTrace_append hprefix tailTrace_2904047
  have hstable : (prefixWord ++ tailWord_2904047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904047).length < 2 ^ (prefixWord ++ tailWord_2904047).sum := by decide
  have hdescent : baseEnd_2904047 < baseStart_2904047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904061 : List Nat := [1, 4, 1, 1, 1, 2, 6, 2, 1, 1, 3]
def baseStart_2904061 : Nat := 118140960795 + 2904061 * 2 ^ 59
def prefixEnd_2904061 : Nat := 4983230072969 + 3 ^ 40 * 2904061 * 2
def baseEnd_2904061 : Nat := 1491179142976667581681973

theorem tailTrace_2904061 : CollatzResearch.WordTrace tailWord_2904061 prefixEnd_2904061 1491179142976667581681973 := by
  unfold tailWord_2904061
  simp only [CollatzResearch.WordTrace]
  refine ⟨105919806332090445977392037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70613204221393630651594691 105919806332090445977392037)
  ·
    refine ⟨19859963687266958620761007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105919806332090445977392037 19859963687266958620761007)
    ·
      refine ⟨29789945530900437931141511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19859963687266958620761007 29789945530900437931141511)
      ·
        refine ⟨44684918296350656896712267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29789945530900437931141511 44684918296350656896712267)
        ·
          refine ⟨67027377444525985345068401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44684918296350656896712267 67027377444525985345068401)
          ·
            refine ⟨50270533083394489008801301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67027377444525985345068401 50270533083394489008801301)
            ·
              refine ⟨2356431238284116672287561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50270533083394489008801301 2356431238284116672287561)
              ·
                refine ⟨1767323428713087504215671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2356431238284116672287561 1767323428713087504215671)
                ·
                  refine ⟨2650985143069631256323507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1767323428713087504215671 2650985143069631256323507)
                  ·
                    refine ⟨3976477714604446884485261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2650985143069631256323507 3976477714604446884485261)
                    ·
                      refine ⟨1491179142976667581681973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3976477714604446884485261 1491179142976667581681973)
                      ·
                        rfl

theorem cell23_2904061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2, 1, 1, 3].length) (baseStart_2904061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904061 prefixEnd_2904061 := by exact prefixLift 2904061
  have htrace : WordTrace (prefixWord ++ tailWord_2904061) baseStart_2904061 baseEnd_2904061 := by
    simpa [prefixWord, tailWord_2904061, baseEnd_2904061] using wordTrace_append hprefix tailTrace_2904061
  have hstable : (prefixWord ++ tailWord_2904061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904061).length < 2 ^ (prefixWord ++ tailWord_2904061).sum := by decide
  have hdescent : baseEnd_2904061 < baseStart_2904061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904063 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 6]
def baseStart_2904063 : Nat := 118140960795 + 2904063 * 2 ^ 59
def prefixEnd_2904063 : Nat := 4983230072969 + 3 ^ 40 * 2904063 * 2
def baseEnd_2904063 : Nat := 1491180169937976573856963

theorem tailTrace_2904063 : CollatzResearch.WordTrace tailWord_2904063 prefixEnd_2904063 1491180169937976573856963 := by
  unfold tailWord_2904063
  simp only [CollatzResearch.WordTrace]
  refine ⟨105919879278083200318964843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70613252852055466879309895 105919879278083200318964843)
  ·
    refine ⟨158879818917124800478447265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105919879278083200318964843 158879818917124800478447265)
    ·
      refine ⟨119159864187843600358835449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158879818917124800478447265 119159864187843600358835449)
      ·
        refine ⟨89369898140882700269126587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119159864187843600358835449 89369898140882700269126587)
        ·
          refine ⟨134054847211324050403689881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89369898140882700269126587 134054847211324050403689881)
          ·
            refine ⟨100541135408493037802767411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134054847211324050403689881 100541135408493037802767411)
            ·
              refine ⟨150811703112739556704151117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100541135408493037802767411 150811703112739556704151117)
              ·
                refine ⟨56554388667277333764056669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150811703112739556704151117 56554388667277333764056669)
                ·
                  refine ⟨21207895750229000161521251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56554388667277333764056669 21207895750229000161521251)
                  ·
                    refine ⟨31811843625343500242281877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21207895750229000161521251 31811843625343500242281877)
                    ·
                      refine ⟨1491180169937976573856963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31811843625343500242281877 1491180169937976573856963)
                      ·
                        rfl

theorem cell23_2904063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_2904063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904063 prefixEnd_2904063 := by exact prefixLift 2904063
  have htrace : WordTrace (prefixWord ++ tailWord_2904063) baseStart_2904063 baseEnd_2904063 := by
    simpa [prefixWord, tailWord_2904063, baseEnd_2904063] using wordTrace_append hprefix tailTrace_2904063
  have hstable : (prefixWord ++ tailWord_2904063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904063).length < 2 ^ (prefixWord ++ tailWord_2904063).sum := by decide
  have hdescent : baseEnd_2904063 < baseStart_2904063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904067 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 7, 2, 2]
def baseStart_2904067 : Nat := 118140960795 + 2904067 * 2 ^ 59
def prefixEnd_2904067 : Nat := 4983230072969 + 3 ^ 40 * 2904067 * 2
def baseEnd_2904067 : Nat := 1491182223860594558206945

theorem tailTrace_2904067 : CollatzResearch.WordTrace tailWord_2904067 prefixEnd_2904067 1491182223860594558206945 := by
  unfold tailWord_2904067
  simp only [CollatzResearch.WordTrace]
  refine ⟨105920025170068709002110455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70613350113379139334740303 105920025170068709002110455)
  ·
    refine ⟨158880037755103063503165683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105920025170068709002110455 158880037755103063503165683)
    ·
      refine ⟨238320056632654595254748525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158880037755103063503165683 238320056632654595254748525)
      ·
        refine ⟨89370021237245473220530697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238320056632654595254748525 89370021237245473220530697)
        ·
          refine ⟨67027515927934104915398023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89370021237245473220530697 67027515927934104915398023)
          ·
            refine ⟨100541273891901157373097035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67027515927934104915398023 100541273891901157373097035)
            ·
              refine ⟨150811910837851736059645553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100541273891901157373097035 150811910837851736059645553)
              ·
                refine ⟨113108933128388802044734165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150811910837851736059645553 113108933128388802044734165)
                ·
                  refine ⟨2650990620196612547923457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 113108933128388802044734165 2650990620196612547923457)
                  ·
                    refine ⟨1988242965147459410942593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2650990620196612547923457 1988242965147459410942593)
                    ·
                      refine ⟨1491182223860594558206945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1988242965147459410942593 1491182223860594558206945)
                      ·
                        rfl

theorem cell23_2904067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7, 2, 2].length) (baseStart_2904067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904067 prefixEnd_2904067 := by exact prefixLift 2904067
  have htrace : WordTrace (prefixWord ++ tailWord_2904067) baseStart_2904067 baseEnd_2904067 := by
    simpa [prefixWord, tailWord_2904067, baseEnd_2904067] using wordTrace_append hprefix tailTrace_2904067
  have hstable : (prefixWord ++ tailWord_2904067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904067).length < 2 ^ (prefixWord ++ tailWord_2904067).sum := by decide
  have hdescent : baseEnd_2904067 < baseStart_2904067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904101 : List Nat := [1, 3, 1, 2, 2, 3, 1, 5, 1, 2, 2]
def baseStart_2904101 : Nat := 118140960795 + 2904101 * 2 ^ 59
def prefixEnd_2904101 : Nat := 4983230072969 + 3 ^ 40 * 2904101 * 2
def baseEnd_2904101 : Nat := 1491199682202847425181789

theorem tailTrace_2904101 : CollatzResearch.WordTrace tailWord_2904101 prefixEnd_2904101 1491199682202847425181789 := by
  unfold tailWord_2904101
  simp only [CollatzResearch.WordTrace]
  refine ⟨105921265251945532808848157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70614176834630355205898771 105921265251945532808848157)
  ·
    refine ⟨39720474469479574803318059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105921265251945532808848157 39720474469479574803318059)
    ·
      refine ⟨59580711704219362204977089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39720474469479574803318059 59580711704219362204977089)
      ·
        refine ⟨44685533778164521653732817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59580711704219362204977089 44685533778164521653732817)
        ·
          refine ⟨33514150333623391240299613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44685533778164521653732817 33514150333623391240299613)
          ·
            refine ⟨12567806375108771715112355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33514150333623391240299613 12567806375108771715112355)
            ·
              refine ⟨18851709562663157572668533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12567806375108771715112355 18851709562663157572668533)
              ·
                refine ⟨1767347771499671022437675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18851709562663157572668533 1767347771499671022437675)
                ·
                  refine ⟨2651021657249506533656513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1767347771499671022437675 2651021657249506533656513)
                  ·
                    refine ⟨1988266242937129900242385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2651021657249506533656513 1988266242937129900242385)
                    ·
                      refine ⟨1491199682202847425181789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1988266242937129900242385 1491199682202847425181789)
                      ·
                        rfl

theorem cell23_2904101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5, 1, 2, 2].length) (baseStart_2904101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904101 prefixEnd_2904101 := by exact prefixLift 2904101
  have htrace : WordTrace (prefixWord ++ tailWord_2904101) baseStart_2904101 baseEnd_2904101 := by
    simpa [prefixWord, tailWord_2904101, baseEnd_2904101] using wordTrace_append hprefix tailTrace_2904101
  have hstable : (prefixWord ++ tailWord_2904101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904101).length < 2 ^ (prefixWord ++ tailWord_2904101).sum := by decide
  have hdescent : baseEnd_2904101 < baseStart_2904101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904118 : List Nat := [5, 1, 2, 1, 1, 1, 1, 6, 1, 2, 2]
def baseStart_2904118 : Nat := 118140960795 + 2904118 * 2 ^ 59
def prefixEnd_2904118 : Nat := 4983230072969 + 3 ^ 40 * 2904118 * 2
def baseEnd_2904118 : Nat := 1491208411373973858669211

theorem tailTrace_2904118 : CollatzResearch.WordTrace tailWord_2904118 prefixEnd_2904118 1491208411373973858669211 := by
  unfold tailWord_2904118
  simp only [CollatzResearch.WordTrace]
  refine ⟨6620117830805246544513563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70614590195255963141478005 6620117830805246544513563)
  ·
    refine ⟨9930176746207869816770345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6620117830805246544513563 9930176746207869816770345)
    ·
      refine ⟨7447632559655902362577759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9930176746207869816770345 7447632559655902362577759)
      ·
        refine ⟨11171448839483853543866639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7447632559655902362577759 11171448839483853543866639)
        ·
          refine ⟨16757173259225780315799959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11171448839483853543866639 16757173259225780315799959)
          ·
            refine ⟨25135759888838670473699939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16757173259225780315799959 25135759888838670473699939)
            ·
              refine ⟨37703639833258005710549909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25135759888838670473699939 37703639833258005710549909)
              ·
                refine ⟨1767358117183969017682027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37703639833258005710549909 1767358117183969017682027)
                ·
                  refine ⟨2651037175775953526523041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1767358117183969017682027 2651037175775953526523041)
                  ·
                    refine ⟨1988277881831965144892281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2651037175775953526523041 1988277881831965144892281)
                    ·
                      refine ⟨1491208411373973858669211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1988277881831965144892281 1491208411373973858669211)
                      ·
                        rfl

theorem cell23_2904118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_2904118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904118 prefixEnd_2904118 := by exact prefixLift 2904118
  have htrace : WordTrace (prefixWord ++ tailWord_2904118) baseStart_2904118 baseEnd_2904118 := by
    simpa [prefixWord, tailWord_2904118, baseEnd_2904118] using wordTrace_append hprefix tailTrace_2904118
  have hstable : (prefixWord ++ tailWord_2904118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904118).length < 2 ^ (prefixWord ++ tailWord_2904118).sum := by decide
  have hdescent : baseEnd_2904118 < baseStart_2904118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904127 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 5, 3, 2]
def baseStart_2904127 : Nat := 118140960795 + 2904127 * 2 ^ 59
def prefixEnd_2904127 : Nat := 4983230072969 + 3 ^ 40 * 2904127 * 2
def baseEnd_2904127 : Nat := 1491213032699864323456669

theorem tailTrace_2904127 : CollatzResearch.WordTrace tailWord_2904127 prefixEnd_2904127 1491213032699864323456669 := by
  unfold tailWord_2904127
  simp only [CollatzResearch.WordTrace]
  refine ⟨105922213549851339249294635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70614809033234226166196423 105922213549851339249294635)
  ·
    refine ⟨158883320324777008873941953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105922213549851339249294635 158883320324777008873941953)
    ·
      refine ⟨119162490243582756655456465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158883320324777008873941953 119162490243582756655456465)
      ·
        refine ⟨89371867682687067491592349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119162490243582756655456465 89371867682687067491592349)
        ·
          refine ⟨33514450381007650309347131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89371867682687067491592349 33514450381007650309347131)
          ·
            refine ⟨50271675571511475464020697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33514450381007650309347131 50271675571511475464020697)
            ·
              refine ⟨37703756678633606598015523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50271675571511475464020697 37703756678633606598015523)
              ·
                refine ⟨56555635017950409897023285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37703756678633606598015523 56555635017950409897023285)
                ·
                  refine ⟨5302090782932850927845933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56555635017950409897023285 5302090782932850927845933)
                  ·
                    refine ⟨1988284043599819097942225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5302090782932850927845933 1988284043599819097942225)
                    ·
                      refine ⟨1491213032699864323456669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1988284043599819097942225 1491213032699864323456669)
                      ·
                        rfl

theorem cell23_2904127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 3, 2].length) (baseStart_2904127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904127 prefixEnd_2904127 := by exact prefixLift 2904127
  have htrace : WordTrace (prefixWord ++ tailWord_2904127) baseStart_2904127 baseEnd_2904127 := by
    simpa [prefixWord, tailWord_2904127, baseEnd_2904127] using wordTrace_append hprefix tailTrace_2904127
  have hstable : (prefixWord ++ tailWord_2904127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904127).length < 2 ^ (prefixWord ++ tailWord_2904127).sum := by decide
  have hdescent : baseEnd_2904127 < baseStart_2904127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904140 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 2, 3, 4]
def baseStart_2904140 : Nat := 118140960795 + 2904140 * 2 ^ 59
def prefixEnd_2904140 : Nat := 4983230072969 + 3 ^ 40 * 2904140 * 2
def baseEnd_2904140 : Nat := 1491219707948372772594109

theorem tailTrace_2904140 : CollatzResearch.WordTrace tailWord_2904140 prefixEnd_2904140 1491219707948372772594109 := by
  unfold tailWord_2904140
  simp only [CollatzResearch.WordTrace]
  refine ⟨52961343849402121234758937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70615125132536161646345249 52961343849402121234758937)
  ·
    refine ⟨39721007887051590926069203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52961343849402121234758937 39721007887051590926069203)
    ·
      refine ⟨59581511830577386389103805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39721007887051590926069203 59581511830577386389103805)
      ·
        refine ⟨22343066936466519895913927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59581511830577386389103805 22343066936466519895913927)
        ·
          refine ⟨33514600404699779843870891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22343066936466519895913927 33514600404699779843870891)
          ·
            refine ⟨50271900607049669765806337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33514600404699779843870891 50271900607049669765806337)
            ·
              refine ⟨37703925455287252324354753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50271900607049669765806337 37703925455287252324354753)
              ·
                refine ⟨28277944091465439243266065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37703925455287252324354753 28277944091465439243266065)
                ·
                  refine ⟨21208458068599079432449549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28277944091465439243266065 21208458068599079432449549)
                  ·
                    refine ⟨7953171775724654787168581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21208458068599079432449549 7953171775724654787168581)
                    ·
                      refine ⟨1491219707948372772594109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7953171775724654787168581 1491219707948372772594109)
                      ·
                        rfl

theorem cell23_2904140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_2904140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904140 prefixEnd_2904140 := by exact prefixLift 2904140
  have htrace : WordTrace (prefixWord ++ tailWord_2904140) baseStart_2904140 baseEnd_2904140 := by
    simpa [prefixWord, tailWord_2904140, baseEnd_2904140] using wordTrace_append hprefix tailTrace_2904140
  have hstable : (prefixWord ++ tailWord_2904140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904140).length < 2 ^ (prefixWord ++ tailWord_2904140).sum := by decide
  have hdescent : baseEnd_2904140 < baseStart_2904140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904160 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 5]
def baseStart_2904160 : Nat := 118140960795 + 2904160 * 2 ^ 59
def prefixEnd_2904160 : Nat := 4983230072969 + 3 ^ 40 * 2904160 * 2
def baseEnd_2904160 : Nat := 1491229977561462694344017

theorem tailTrace_2904160 : CollatzResearch.WordTrace tailWord_2904160 prefixEnd_2904160 1491229977561462694344017 := by
  unfold tailWord_2904160
  simp only [CollatzResearch.WordTrace]
  refine ⟨52961708579365892942622967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70615611439154523923497289 52961708579365892942622967)
  ·
    refine ⟨79442562869048839413934451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52961708579365892942622967 79442562869048839413934451)
    ·
      refine ⟨119163844303573259120901677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79442562869048839413934451 119163844303573259120901677)
      ·
        refine ⟨44686441613839972170338129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119163844303573259120901677 44686441613839972170338129)
        ·
          refine ⟨33514831210379979127753597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44686441613839972170338129 33514831210379979127753597)
          ·
            refine ⟨12568061703892492172907599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33514831210379979127753597 12568061703892492172907599)
            ·
              refine ⟨18852092555838738259361399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12568061703892492172907599 18852092555838738259361399)
              ·
                refine ⟨28278138833758107389042099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18852092555838738259361399 28278138833758107389042099)
                ·
                  refine ⟨42417208250637161083563149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28278138833758107389042099 42417208250637161083563149)
                  ·
                    refine ⟨15906453093988935406336181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42417208250637161083563149 15906453093988935406336181)
                    ·
                      refine ⟨1491229977561462694344017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15906453093988935406336181 1491229977561462694344017)
                      ·
                        rfl

theorem cell23_2904160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_2904160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904160 prefixEnd_2904160 := by exact prefixLift 2904160
  have htrace : WordTrace (prefixWord ++ tailWord_2904160) baseStart_2904160 baseEnd_2904160 := by
    simpa [prefixWord, tailWord_2904160, baseEnd_2904160] using wordTrace_append hprefix tailTrace_2904160
  have hstable : (prefixWord ++ tailWord_2904160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904160).length < 2 ^ (prefixWord ++ tailWord_2904160).sum := by decide
  have hdescent : baseEnd_2904160 < baseStart_2904160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904217 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 4, 5, 2]
def baseStart_2904217 : Nat := 118140960795 + 2904217 * 2 ^ 59
def prefixEnd_2904217 : Nat := 4983230072969 + 3 ^ 40 * 2904217 * 2
def baseEnd_2904217 : Nat := 1491259245958768971331255

theorem tailTrace_2904217 : CollatzResearch.WordTrace tailWord_2904217 prefixEnd_2904217 1491259245958768971331255 := by
  unfold tailWord_2904217
  simp only [CollatzResearch.WordTrace]
  refine ⟨105925496119525284620070905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70616997413016856413380603 105925496119525284620070905)
  ·
    refine ⟨79444122089643963465053179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105925496119525284620070905 79444122089643963465053179)
    ·
      refine ⟨119166183134465945197579769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79444122089643963465053179 119166183134465945197579769)
      ·
        refine ⟨89374637350849458898184827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119166183134465945197579769 89374637350849458898184827)
        ·
          refine ⟨134061956026274188347277241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89374637350849458898184827 134061956026274188347277241)
          ·
            refine ⟨100546467019705641260457931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134061956026274188347277241 100546467019705641260457931)
            ·
              refine ⟨150819700529558461890686897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100546467019705641260457931 150819700529558461890686897)
              ·
                refine ⟨113114775397168846418015173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150819700529558461890686897 113114775397168846418015173)
                ·
                  refine ⟨21209020386969158703377845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113114775397168846418015173 21209020386969158703377845)
                  ·
                    refine ⟨1988345661278358628441673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21209020386969158703377845 1988345661278358628441673)
                    ·
                      refine ⟨1491259245958768971331255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1988345661278358628441673 1491259245958768971331255)
                      ·
                        rfl

theorem cell23_2904217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 5, 2].length) (baseStart_2904217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904217 prefixEnd_2904217 := by exact prefixLift 2904217
  have htrace : WordTrace (prefixWord ++ tailWord_2904217) baseStart_2904217 baseEnd_2904217 := by
    simpa [prefixWord, tailWord_2904217, baseEnd_2904217] using wordTrace_append hprefix tailTrace_2904217
  have hstable : (prefixWord ++ tailWord_2904217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904217).length < 2 ^ (prefixWord ++ tailWord_2904217).sum := by decide
  have hdescent : baseEnd_2904217 < baseStart_2904217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904231 : List Nat := [1, 1, 6, 2, 2, 1, 1, 4, 5]
def baseStart_2904231 : Nat := 118140960795 + 2904231 * 2 ^ 59
def prefixEnd_2904231 : Nat := 4983230072969 + 3 ^ 40 * 2904231 * 2
def baseEnd_2904231 : Nat := 165696270520881324061799

theorem tailTrace_2904231 : CollatzResearch.WordTrace tailWord_2904231 prefixEnd_2904231 165696270520881324061799 := by
  unfold tailWord_2904231
  simp only [CollatzResearch.WordTrace]
  refine ⟨105926006741474565011080547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70617337827649710007387031 105926006741474565011080547)
  ·
    refine ⟨158889010112211847516620821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105926006741474565011080547 158889010112211847516620821)
    ·
      refine ⟨7447922349009930352341601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 158889010112211847516620821 7447922349009930352341601)
      ·
        refine ⟨5585941761757447764256201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7447922349009930352341601 5585941761757447764256201)
        ·
          refine ⟨4189456321318085823192151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5585941761757447764256201 4189456321318085823192151)
          ·
            refine ⟨6284184481977128734788227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4189456321318085823192151 6284184481977128734788227)
            ·
              refine ⟨9426276722965693102182341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6284184481977128734788227 9426276722965693102182341)
              ·
                refine ⟨1767426885556067456659189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9426276722965693102182341 1767426885556067456659189)
                ·
                  refine ⟨165696270520881324061799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1767426885556067456659189 165696270520881324061799)
                  ·
                    rfl

theorem cell23_2904231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4, 5].length) (baseStart_2904231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904231 prefixEnd_2904231 := by exact prefixLift 2904231
  have htrace : WordTrace (prefixWord ++ tailWord_2904231) baseStart_2904231 baseEnd_2904231 := by
    simpa [prefixWord, tailWord_2904231, baseEnd_2904231] using wordTrace_append hprefix tailTrace_2904231
  have hstable : (prefixWord ++ tailWord_2904231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904231).length < 2 ^ (prefixWord ++ tailWord_2904231).sum := by decide
  have hdescent : baseEnd_2904231 < baseStart_2904231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904267 : List Nat := [1, 1, 1, 1, 3, 2, 5, 1, 1, 4, 3]
def baseStart_2904267 : Nat := 118140960795 + 2904267 * 2 ^ 59
def prefixEnd_2904267 : Nat := 4983230072969 + 3 ^ 40 * 2904267 * 2
def baseEnd_2904267 : Nat := 1491284919991493775706025

theorem tailTrace_2904267 : CollatzResearch.WordTrace tailWord_2904267 prefixEnd_2904267 1491284919991493775706025 := by
  unfold tailWord_2904267
  simp only [CollatzResearch.WordTrace]
  refine ⟨105927319769344143159391055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70618213179562762106260703 105927319769344143159391055)
  ·
    refine ⟨158890979654016214739086583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105927319769344143159391055 158890979654016214739086583)
    ·
      refine ⟨238336469481024322108629875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158890979654016214739086583 238336469481024322108629875)
      ·
        refine ⟨357504704221536483162944813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238336469481024322108629875 357504704221536483162944813)
        ·
          refine ⟨134064264083076181186104305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 357504704221536483162944813 134064264083076181186104305)
          ·
            refine ⟨100548198062307135889578229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134064264083076181186104305 100548198062307135889578229)
            ·
              refine ⟨9426393568341293989647959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100548198062307135889578229 9426393568341293989647959)
              ·
                refine ⟨14139590352511940984471939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9426393568341293989647959 14139590352511940984471939)
                ·
                  refine ⟨21209385528767911476707909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14139590352511940984471939 21209385528767911476707909)
                  ·
                    refine ⟨3976759786643983401882733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21209385528767911476707909 3976759786643983401882733)
                    ·
                      refine ⟨1491284919991493775706025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3976759786643983401882733 1491284919991493775706025)
                      ·
                        rfl

theorem cell23_2904267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4, 3].length) (baseStart_2904267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904267 prefixEnd_2904267 := by exact prefixLift 2904267
  have htrace : WordTrace (prefixWord ++ tailWord_2904267) baseStart_2904267 baseEnd_2904267 := by
    simpa [prefixWord, tailWord_2904267, baseEnd_2904267] using wordTrace_append hprefix tailTrace_2904267
  have hstable : (prefixWord ++ tailWord_2904267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904267).length < 2 ^ (prefixWord ++ tailWord_2904267).sum := by decide
  have hdescent : baseEnd_2904267 < baseStart_2904267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904317 : List Nat := [1, 4, 1, 1, 1, 1, 1, 5, 3, 5]
def baseStart_2904317 : Nat := 118140960795 + 2904317 * 2 ^ 59
def prefixEnd_2904317 : Nat := 4983230072969 + 3 ^ 40 * 2904317 * 2
def baseEnd_2904317 : Nat := 497103531341406193360265

theorem tailTrace_2904317 : CollatzResearch.WordTrace tailWord_2904317 prefixEnd_2904317 497103531341406193360265 := by
  unfold tailWord_2904317
  simp only [CollatzResearch.WordTrace]
  refine ⟨105929143419163001698711205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70619428946108667799140803 105929143419163001698711205)
  ·
    refine ⟨19861714391093062818508351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105929143419163001698711205 19861714391093062818508351)
    ·
      refine ⟨29792571586639594227762527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19861714391093062818508351 29792571586639594227762527)
      ·
        refine ⟨44688857379959391341643791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29792571586639594227762527 44688857379959391341643791)
        ·
          refine ⟨67033286069939087012465687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44688857379959391341643791 67033286069939087012465687)
          ·
            refine ⟨100549929104908630518698531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67033286069939087012465687 100549929104908630518698531)
            ·
              refine ⟨150824893657362945778047797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100549929104908630518698531 150824893657362945778047797)
              ·
                refine ⟨14139833780377776166691981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150824893657362945778047797 14139833780377776166691981)
                ·
                  refine ⟨5302437667641666062509493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14139833780377776166691981 5302437667641666062509493)
                  ·
                    refine ⟨497103531341406193360265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5302437667641666062509493 497103531341406193360265)
                    ·
                      rfl

theorem cell23_2904317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_2904317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904317 prefixEnd_2904317 := by exact prefixLift 2904317
  have htrace : WordTrace (prefixWord ++ tailWord_2904317) baseStart_2904317 baseEnd_2904317 := by
    simpa [prefixWord, tailWord_2904317, baseEnd_2904317] using wordTrace_append hprefix tailTrace_2904317
  have hstable : (prefixWord ++ tailWord_2904317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904317).length < 2 ^ (prefixWord ++ tailWord_2904317).sum := by decide
  have hdescent : baseEnd_2904317 < baseStart_2904317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904334 : List Nat := [4, 1, 1, 2, 1, 2, 1, 5, 1, 5]
def baseStart_2904334 : Nat := 118140960795 + 2904334 * 2 ^ 59
def prefixEnd_2904334 : Nat := 4983230072969 + 3 ^ 40 * 2904334 * 2
def baseEnd_2904334 : Nat := 497106441065115004522739

theorem tailTrace_2904334 : CollatzResearch.WordTrace tailWord_2904334 prefixEnd_2904334 497106441065115004522739 := by
  unfold tailWord_2904334
  simp only [CollatzResearch.WordTrace]
  refine ⟨13241220432512676700260007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70619842306734275734720037 13241220432512676700260007)
  ·
    refine ⟨19861830648769015050390011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13241220432512676700260007 19861830648769015050390011)
    ·
      refine ⟨29792745973153522575585017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19861830648769015050390011 29792745973153522575585017)
      ·
        refine ⟨22344559479865141931688763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29792745973153522575585017 22344559479865141931688763)
        ·
          refine ⟨33516839219797712897533145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22344559479865141931688763 33516839219797712897533145)
          ·
            refine ⟨25137629414848284673149859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33516839219797712897533145 25137629414848284673149859)
            ·
              refine ⟨37706444122272427009724789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25137629414848284673149859 37706444122272427009724789)
              ·
                refine ⟨3534979136463040032161699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37706444122272427009724789 3534979136463040032161699)
                ·
                  refine ⟨5302468704694560048242549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3534979136463040032161699 5302468704694560048242549)
                  ·
                    refine ⟨497106441065115004522739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5302468704694560048242549 497106441065115004522739)
                    ·
                      rfl

theorem cell23_2904334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_2904334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904334 prefixEnd_2904334 := by exact prefixLift 2904334
  have htrace : WordTrace (prefixWord ++ tailWord_2904334) baseStart_2904334 baseEnd_2904334 := by
    simpa [prefixWord, tailWord_2904334, baseEnd_2904334] using wordTrace_append hprefix tailTrace_2904334
  have hstable : (prefixWord ++ tailWord_2904334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904334).length < 2 ^ (prefixWord ++ tailWord_2904334).sum := by decide
  have hdescent : baseEnd_2904334 < baseStart_2904334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904367 : List Nat := [1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 6]
def baseStart_2904367 : Nat := 118140960795 + 2904367 * 2 ^ 59
def prefixEnd_2904367 : Nat := 4983230072969 + 3 ^ 40 * 2904367 * 2
def baseEnd_2904367 : Nat := 1491336268056943384455565

theorem tailTrace_2904367 : CollatzResearch.WordTrace tailWord_2904367 prefixEnd_2904367 1491336268056943384455565 := by
  unfold tailWord_2904367
  simp only [CollatzResearch.WordTrace]
  refine ⟨105930967068981860238031355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70620644712654573492020903 105930967068981860238031355)
  ·
    refine ⟨158896450603472790357047033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105930967068981860238031355 158896450603472790357047033)
    ·
      refine ⟨119172337952604592767785275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158896450603472790357047033 119172337952604592767785275)
      ·
        refine ⟨178758506928906889151677913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119172337952604592767785275 178758506928906889151677913)
        ·
          refine ⟨134068880196680166863758435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178758506928906889151677913 134068880196680166863758435)
          ·
            refine ⟨201103320295020250295637653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134068880196680166863758435 201103320295020250295637653)
            ·
              refine ⟨9426718138829074232608015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 201103320295020250295637653 9426718138829074232608015)
              ·
                refine ⟨14140077208243611348912023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9426718138829074232608015 14140077208243611348912023)
                ·
                  refine ⟨21210115812365417023368035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14140077208243611348912023 21210115812365417023368035)
                  ·
                    refine ⟨31815173718548125535052053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21210115812365417023368035 31815173718548125535052053)
                    ·
                      refine ⟨1491336268056943384455565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31815173718548125535052053 1491336268056943384455565)
                      ·
                        rfl

theorem cell23_2904367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 6].length) (baseStart_2904367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904367 prefixEnd_2904367 := by exact prefixLift 2904367
  have htrace : WordTrace (prefixWord ++ tailWord_2904367) baseStart_2904367 baseEnd_2904367 := by
    simpa [prefixWord, tailWord_2904367, baseEnd_2904367] using wordTrace_append hprefix tailTrace_2904367
  have hstable : (prefixWord ++ tailWord_2904367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904367).length < 2 ^ (prefixWord ++ tailWord_2904367).sum := by decide
  have hdescent : baseEnd_2904367 < baseStart_2904367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904371 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 5, 2, 2]
def baseStart_2904371 : Nat := 118140960795 + 2904371 * 2 ^ 59
def prefixEnd_2904371 : Nat := 4983230072969 + 3 ^ 40 * 2904371 * 2
def baseEnd_2904371 : Nat := 1491338321979561368805547

theorem tailTrace_2904371 : CollatzResearch.WordTrace tailWord_2904371 prefixEnd_2904371 1491338321979561368805547 := by
  unfold tailWord_2904371
  simp only [CollatzResearch.WordTrace]
  refine ⟨105931112960967368921176967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70620741973978245947451311 105931112960967368921176967)
  ·
    refine ⟨158896669441451053381765451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105931112960967368921176967 158896669441451053381765451)
    ·
      refine ⟨238345004162176580072648177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158896669441451053381765451 238345004162176580072648177)
      ·
        refine ⟨178758753121632435054486133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238345004162176580072648177 178758753121632435054486133)
        ·
          refine ⟨16758633105153040786358075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 178758753121632435054486133 16758633105153040786358075)
          ·
            refine ⟨25137949657729561179537113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16758633105153040786358075 25137949657729561179537113)
            ·
              refine ⟨18853462243297170884652835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25137949657729561179537113 18853462243297170884652835)
              ·
                refine ⟨28280193364945756326979253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18853462243297170884652835 28280193364945756326979253)
                ·
                  refine ⟨2651268127963664655654305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28280193364945756326979253 2651268127963664655654305)
                  ·
                    refine ⟨1988451095972748491740729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2651268127963664655654305 1988451095972748491740729)
                    ·
                      refine ⟨1491338321979561368805547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1988451095972748491740729 1491338321979561368805547)
                      ·
                        rfl

theorem cell23_2904371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5, 2, 2].length) (baseStart_2904371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904371 prefixEnd_2904371 := by exact prefixLift 2904371
  have htrace : WordTrace (prefixWord ++ tailWord_2904371) baseStart_2904371 baseEnd_2904371 := by
    simpa [prefixWord, tailWord_2904371, baseEnd_2904371] using wordTrace_append hprefix tailTrace_2904371
  have hstable : (prefixWord ++ tailWord_2904371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904371).length < 2 ^ (prefixWord ++ tailWord_2904371).sum := by decide
  have hdescent : baseEnd_2904371 < baseStart_2904371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904407 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 1, 9]
def baseStart_2904407 : Nat := 118140960795 + 2904407 * 2 ^ 59
def prefixEnd_2904407 : Nat := 4983230072969 + 3 ^ 40 * 2904407 * 2
def baseEnd_2904407 : Nat := 497118935761041075985127

theorem tailTrace_2904407 : CollatzResearch.WordTrace tailWord_2904407 prefixEnd_2904407 497118935761041075985127 := by
  unfold tailWord_2904407
  simp only [CollatzResearch.WordTrace]
  refine ⟨105932425988836947069487475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70621617325891298046324983 105932425988836947069487475)
  ·
    refine ⟨158898638983255420604231213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105932425988836947069487475 158898638983255420604231213)
    ·
      refine ⟨59586989618720782726586705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158898638983255420604231213 59586989618720782726586705)
      ·
        refine ⟨44690242214040587044940029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59586989618720782726586705 44690242214040587044940029)
        ·
          refine ⟨16758840830265220141852511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44690242214040587044940029 16758840830265220141852511)
          ·
            refine ⟨25138261245397830212778767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16758840830265220141852511 25138261245397830212778767)
            ·
              refine ⟨37707391868096745319168151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25138261245397830212778767 37707391868096745319168151)
              ·
                refine ⟨56561087802145117978752227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37707391868096745319168151 56561087802145117978752227)
                ·
                  refine ⟨84841631703217676968128341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56561087802145117978752227 84841631703217676968128341)
                  ·
                    refine ⟨497118935761041075985127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 84841631703217676968128341 497118935761041075985127)
                    ·
                      rfl

theorem cell23_2904407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 9].length) (baseStart_2904407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904407 prefixEnd_2904407 := by exact prefixLift 2904407
  have htrace : WordTrace (prefixWord ++ tailWord_2904407) baseStart_2904407 baseEnd_2904407 := by
    simpa [prefixWord, tailWord_2904407, baseEnd_2904407] using wordTrace_append hprefix tailTrace_2904407
  have hstable : (prefixWord ++ tailWord_2904407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904407).length < 2 ^ (prefixWord ++ tailWord_2904407).sum := by decide
  have hdescent : baseEnd_2904407 < baseStart_2904407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904417 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 3, 4, 5]
def baseStart_2904417 : Nat := 118140960795 + 2904417 * 2 ^ 59
def prefixEnd_2904417 : Nat := 4983230072969 + 3 ^ 40 * 2904417 * 2
def baseEnd_2904417 : Nat := 1491361942089668188830335

theorem tailTrace_2904417 : CollatzResearch.WordTrace tailWord_2904417 prefixEnd_2904417 1491361942089668188830335 := by
  unfold tailWord_2904417
  simp only [CollatzResearch.WordTrace]
  refine ⟨105932790718800718777351505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70621860479200479184901003 105932790718800718777351505)
  ·
    refine ⟨79449593039100539083013629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105932790718800718777351505 79449593039100539083013629)
    ·
      refine ⟨29793597389662702156130111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79449593039100539083013629 29793597389662702156130111)
      ·
        refine ⟨44690396084494053234195167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29793597389662702156130111 44690396084494053234195167)
        ·
          refine ⟨67035594126741079851292751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44690396084494053234195167 67035594126741079851292751)
          ·
            refine ⟨100553391190111619776939127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67035594126741079851292751 100553391190111619776939127)
            ·
              refine ⟨150830086785167429665408691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100553391190111619776939127 150830086785167429665408691)
              ·
                refine ⟨226245130177751144498113037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150830086785167429665408691 226245130177751144498113037)
                ·
                  refine ⟨84841923816656679186792389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226245130177751144498113037 84841923816656679186792389)
                  ·
                    refine ⟨15907860715623127347523573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84841923816656679186792389 15907860715623127347523573)
                    ·
                      refine ⟨1491361942089668188830335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15907860715623127347523573 1491361942089668188830335)
                      ·
                        rfl

theorem cell23_2904417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_2904417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904417 prefixEnd_2904417 := by exact prefixLift 2904417
  have htrace : WordTrace (prefixWord ++ tailWord_2904417) baseStart_2904417 baseEnd_2904417 := by
    simpa [prefixWord, tailWord_2904417, baseEnd_2904417] using wordTrace_append hprefix tailTrace_2904417
  have hstable : (prefixWord ++ tailWord_2904417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904417).length < 2 ^ (prefixWord ++ tailWord_2904417).sum := by decide
  have hdescent : baseEnd_2904417 < baseStart_2904417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904421 : List Nat := [1, 3, 1, 3, 1, 4, 2, 1, 1, 3, 3]
def baseStart_2904421 : Nat := 118140960795 + 2904421 * 2 ^ 59
def prefixEnd_2904421 : Nat := 4983230072969 + 3 ^ 40 * 2904421 * 2
def baseEnd_2904421 : Nat := 1491363996012286173180317

theorem tailTrace_2904421 : CollatzResearch.WordTrace tailWord_2904421 prefixEnd_2904421 1491363996012286173180317 := by
  unfold tailWord_2904421
  simp only [CollatzResearch.WordTrace]
  refine ⟨105932936610786227460497117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70621957740524151640331411 105932936610786227460497117)
  ·
    refine ⟨39724851229044835297686419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105932936610786227460497117 39724851229044835297686419)
    ·
      refine ⟨59587276843567252946529629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39724851229044835297686419 59587276843567252946529629)
      ·
        refine ⟨22345228816337719854948611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59587276843567252946529629 22345228816337719854948611)
        ·
          refine ⟨33517843224506579782422917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22345228816337719854948611 33517843224506579782422917)
          ·
            refine ⟨6284595604594983709204297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33517843224506579782422917 6284595604594983709204297)
            ·
              refine ⟨4713446703446237781903223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6284595604594983709204297 4713446703446237781903223)
              ·
                refine ⟨7070170055169356672854835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4713446703446237781903223 7070170055169356672854835)
                ·
                  refine ⟨10605255082754035009282253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7070170055169356672854835 10605255082754035009282253)
                  ·
                    refine ⟨3976970656032763128480845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10605255082754035009282253 3976970656032763128480845)
                    ·
                      refine ⟨1491363996012286173180317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3976970656032763128480845 1491363996012286173180317)
                      ·
                        rfl

theorem cell23_2904421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_2904421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904421 prefixEnd_2904421 := by exact prefixLift 2904421
  have htrace : WordTrace (prefixWord ++ tailWord_2904421) baseStart_2904421 baseEnd_2904421 := by
    simpa [prefixWord, tailWord_2904421, baseEnd_2904421] using wordTrace_append hprefix tailTrace_2904421
  have hstable : (prefixWord ++ tailWord_2904421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904421).length < 2 ^ (prefixWord ++ tailWord_2904421).sum := by decide
  have hdescent : baseEnd_2904421 < baseStart_2904421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904484 : List Nat := [2, 3, 1, 2, 1, 1, 4, 2, 7]
def baseStart_2904484 : Nat := 118140960795 + 2904484 * 2 ^ 59
def prefixEnd_2904484 : Nat := 4983230072969 + 3 ^ 40 * 2904484 * 2
def baseEnd_2904484 : Nat := 165710705032613269632503

theorem tailTrace_2904484 : CollatzResearch.WordTrace tailWord_2904484 prefixEnd_2904484 165710705032613269632503 := by
  unfold tailWord_2904484
  simp only [CollatzResearch.WordTrace]
  refine ⟨52967617204778994610020253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70623489606371992813360337 52967617204778994610020253)
  ·
    refine ⟨19862856451792122978757595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52967617204778994610020253 19862856451792122978757595)
    ·
      refine ⟨29794284677688184468136393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19862856451792122978757595 29794284677688184468136393)
      ·
        refine ⟨22345713508266138351102295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29794284677688184468136393 22345713508266138351102295)
        ·
          refine ⟨33518570262399207526653443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22345713508266138351102295 33518570262399207526653443)
          ·
            refine ⟨50277855393598811289980165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33518570262399207526653443 50277855393598811289980165)
            ·
              refine ⟨9427097886299777116871281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50277855393598811289980165 9427097886299777116871281)
              ·
                refine ⟨7070323414724832837653461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9427097886299777116871281 7070323414724832837653461)
                ·
                  refine ⟨165710705032613269632503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7070323414724832837653461 165710705032613269632503)
                  ·
                    rfl

theorem cell23_2904484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 7].length) (baseStart_2904484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904484 prefixEnd_2904484 := by exact prefixLift 2904484
  have htrace : WordTrace (prefixWord ++ tailWord_2904484) baseStart_2904484 baseEnd_2904484 := by
    simpa [prefixWord, tailWord_2904484, baseEnd_2904484] using wordTrace_append hprefix tailTrace_2904484
  have hstable : (prefixWord ++ tailWord_2904484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904484).length < 2 ^ (prefixWord ++ tailWord_2904484).sum := by decide
  have hdescent : baseEnd_2904484 < baseStart_2904484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904605 : List Nat := [1, 4, 2, 2, 1, 4, 1, 1, 2, 2, 3]
def baseStart_2904605 : Nat := 118140960795 + 2904605 * 2 ^ 59
def prefixEnd_2904605 : Nat := 4983230072969 + 3 ^ 40 * 2904605 * 2
def baseEnd_2904605 : Nat := 1491458476452713453279471

theorem tailTrace_2904605 : CollatzResearch.WordTrace tailWord_2904605 prefixEnd_2904605 1491458476452713453279471 := by
  unfold tailWord_2904605
  simp only [CollatzResearch.WordTrace]
  refine ⟨105939647642119626885195269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70626431761413084590130179 105939647642119626885195269)
  ·
    refine ⟨19863683932897430040974113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105939647642119626885195269 19863683932897430040974113)
    ·
      refine ⟨14897762949673072530730585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19863683932897430040974113 14897762949673072530730585)
      ·
        refine ⟨11173322212254804398047939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14897762949673072530730585 11173322212254804398047939)
        ·
          refine ⟨16759983318382206597071909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11173322212254804398047939 16759983318382206597071909)
          ·
            refine ⟨3142496872196663736950983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16759983318382206597071909 3142496872196663736950983)
            ·
              refine ⟨4713745308294995605426475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3142496872196663736950983 4713745308294995605426475)
              ·
                refine ⟨7070617962442493408139713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4713745308294995605426475 7070617962442493408139713)
                ·
                  refine ⟨5302963471831870056104785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7070617962442493408139713 5302963471831870056104785)
                  ·
                    refine ⟨3977222603873902542078589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5302963471831870056104785 3977222603873902542078589)
                    ·
                      refine ⟨1491458476452713453279471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3977222603873902542078589 1491458476452713453279471)
                      ·
                        rfl

theorem cell23_2904605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_2904605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904605 prefixEnd_2904605 := by exact prefixLift 2904605
  have htrace : WordTrace (prefixWord ++ tailWord_2904605) baseStart_2904605 baseEnd_2904605 := by
    simpa [prefixWord, tailWord_2904605, baseEnd_2904605] using wordTrace_append hprefix tailTrace_2904605
  have hstable : (prefixWord ++ tailWord_2904605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904605).length < 2 ^ (prefixWord ++ tailWord_2904605).sum := by decide
  have hdescent : baseEnd_2904605 < baseStart_2904605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904651 : List Nat := [1, 1, 1, 1, 3, 1, 7, 1, 1, 6]
def baseStart_2904651 : Nat := 118140960795 + 2904651 * 2 ^ 59
def prefixEnd_2904651 : Nat := 4983230072969 + 3 ^ 40 * 2904651 * 2
def baseEnd_2904651 : Nat := 497160698854273424434753

theorem tailTrace_2904651 : CollatzResearch.WordTrace tailWord_2904651 prefixEnd_2904651 497160698854273424434753 := by
  unfold tailWord_2904651
  simp only [CollatzResearch.WordTrace]
  refine ⟨105941325399952976741369807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70627550266635317827579871 105941325399952976741369807)
  ·
    refine ⟨158911988099929465112054711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105941325399952976741369807 158911988099929465112054711)
    ·
      refine ⟨238367982149894197668082067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158911988099929465112054711 238367982149894197668082067)
      ·
        refine ⟨357551973224841296502123101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238367982149894197668082067 357551973224841296502123101)
        ·
          refine ⟨134081989959315486188296163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 357551973224841296502123101 134081989959315486188296163)
          ·
            refine ⟨201122984938973229282444245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134081989959315486188296163 201122984938973229282444245)
            ·
              refine ⟨4713819959507185061307287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 201122984938973229282444245 4713819959507185061307287)
              ·
                refine ⟨7070729939260777591960931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4713819959507185061307287 7070729939260777591960931)
                ·
                  refine ⟨10606094908891166387941397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7070729939260777591960931 10606094908891166387941397)
                  ·
                    refine ⟨497160698854273424434753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10606094908891166387941397 497160698854273424434753)
                    ·
                      rfl

theorem cell23_2904651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 6].length) (baseStart_2904651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904651 prefixEnd_2904651 := by exact prefixLift 2904651
  have htrace : WordTrace (prefixWord ++ tailWord_2904651) baseStart_2904651 baseEnd_2904651 := by
    simpa [prefixWord, tailWord_2904651, baseEnd_2904651] using wordTrace_append hprefix tailTrace_2904651
  have hstable : (prefixWord ++ tailWord_2904651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904651).length < 2 ^ (prefixWord ++ tailWord_2904651).sum := by decide
  have hdescent : baseEnd_2904651 < baseStart_2904651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904658 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 2, 6, 2]
def baseStart_2904658 : Nat := 118140960795 + 2904658 * 2 ^ 59
def prefixEnd_2904658 : Nat := 4983230072969 + 3 ^ 40 * 2904658 * 2
def baseEnd_2904658 : Nat := 1491485690927401745916727

theorem tailTrace_2904658 : CollatzResearch.WordTrace tailWord_2904658 prefixEnd_2904658 1491485690927401745916727 := by
  unfold tailWord_2904658
  simp only [CollatzResearch.WordTrace]
  refine ⟨26485395177731904234218657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70627720473951744624583085 26485395177731904234218657)
  ·
    refine ⟨19864046383298928175663993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26485395177731904234218657 19864046383298928175663993)
    ·
      refine ⟨14898034787474196131747995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19864046383298928175663993 14898034787474196131747995)
      ·
        refine ⟨22347052181211294197621993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14898034787474196131747995 22347052181211294197621993)
        ·
          refine ⟨16760289135908470648216495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22347052181211294197621993 16760289135908470648216495)
          ·
            refine ⟨25140433703862705972324743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16760289135908470648216495 25140433703862705972324743)
            ·
              refine ⟨37710650555794058958487115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25140433703862705972324743 37710650555794058958487115)
              ·
                refine ⟨56565975833691088437730673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37710650555794058958487115 56565975833691088437730673)
                ·
                  refine ⟨42424481875268316328298005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56565975833691088437730673 42424481875268316328298005)
                  ·
                    refine ⟨1988647587903202327888969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42424481875268316328298005 1988647587903202327888969)
                    ·
                      refine ⟨1491485690927401745916727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1988647587903202327888969 1491485690927401745916727)
                      ·
                        rfl

theorem cell23_2904658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_2904658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904658 prefixEnd_2904658 := by exact prefixLift 2904658
  have htrace : WordTrace (prefixWord ++ tailWord_2904658) baseStart_2904658 baseEnd_2904658 := by
    simpa [prefixWord, tailWord_2904658, baseEnd_2904658] using wordTrace_append hprefix tailTrace_2904658
  have hstable : (prefixWord ++ tailWord_2904658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904658).length < 2 ^ (prefixWord ++ tailWord_2904658).sum := by decide
  have hdescent : baseEnd_2904658 < baseStart_2904658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904671 : List Nat := [1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 4]
def baseStart_2904671 : Nat := 118140960795 + 2904671 * 2 ^ 59
def prefixEnd_2904671 : Nat := 4983230072969 + 3 ^ 40 * 2904671 * 2
def baseEnd_2904671 : Nat := 1491492366175910195054167

theorem tailTrace_2904671 : CollatzResearch.WordTrace tailWord_2904671 prefixEnd_2904671 1491492366175910195054167 := by
  unfold tailWord_2904671
  simp only [CollatzResearch.WordTrace]
  refine ⟨105942054859880520157097867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70628036573253680104731911 105942054859880520157097867)
  ·
    refine ⟨158913082289820780235646801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105942054859880520157097867 158913082289820780235646801)
    ·
      refine ⟨119184811717365585176735101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158913082289820780235646801 119184811717365585176735101)
      ·
        refine ⟨44694304394012094441275663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119184811717365585176735101 44694304394012094441275663)
        ·
          refine ⟨67041456591018141661913495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44694304394012094441275663 67041456591018141661913495)
          ·
            refine ⟨100562184886527212492870243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67041456591018141661913495 100562184886527212492870243)
            ·
              refine ⟨150843277329790818739305365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100562184886527212492870243 150843277329790818739305365)
              ·
                refine ⟨7070778624833944628404939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 150843277329790818739305365 7070778624833944628404939)
                ·
                  refine ⟨10606167937250916942607409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7070778624833944628404939 10606167937250916942607409)
                  ·
                    refine ⟨7954625952938187706955557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10606167937250916942607409 7954625952938187706955557)
                    ·
                      refine ⟨1491492366175910195054167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7954625952938187706955557 1491492366175910195054167)
                      ·
                        rfl

theorem cell23_2904671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_2904671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904671 prefixEnd_2904671 := by exact prefixLift 2904671
  have htrace : WordTrace (prefixWord ++ tailWord_2904671) baseStart_2904671 baseEnd_2904671 := by
    simpa [prefixWord, tailWord_2904671, baseEnd_2904671] using wordTrace_append hprefix tailTrace_2904671
  have hstable : (prefixWord ++ tailWord_2904671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904671).length < 2 ^ (prefixWord ++ tailWord_2904671).sum := by decide
  have hdescent : baseEnd_2904671 < baseStart_2904671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904691 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 5, 3, 3]
def baseStart_2904691 : Nat := 118140960795 + 2904691 * 2 ^ 59
def prefixEnd_2904691 : Nat := 4983230072969 + 3 ^ 40 * 2904691 * 2
def baseEnd_2904691 : Nat := 1491502635789000116804075

theorem tailTrace_2904691 : CollatzResearch.WordTrace tailWord_2904691 prefixEnd_2904691 1491502635789000116804075 := by
  unfold tailWord_2904691
  simp only [CollatzResearch.WordTrace]
  refine ⟨105942784319808063572825927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70628522879872042381883951 105942784319808063572825927)
  ·
    refine ⟨158914176479712095359238891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105942784319808063572825927 158914176479712095359238891)
    ·
      refine ⟨238371264719568143038858337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158914176479712095359238891 238371264719568143038858337)
      ·
        refine ⟨178778448539676107279143753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238371264719568143038858337 178778448539676107279143753)
        ·
          refine ⟨134083836404757080459357815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178778448539676107279143753 134083836404757080459357815)
          ·
            refine ⟨201125754607135620689036723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134083836404757080459357815 201125754607135620689036723)
            ·
              refine ⟨301688631910703431033555085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201125754607135620689036723 301688631910703431033555085)
              ·
                refine ⟨113133236966513786637583157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 301688631910703431033555085 113133236966513786637583157)
                ·
                  refine ⟨10606240965610667497273421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113133236966513786637583157 10606240965610667497273421)
                  ·
                    refine ⟨3977340362104000311477533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10606240965610667497273421 3977340362104000311477533)
                    ·
                      refine ⟨1491502635789000116804075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3977340362104000311477533 1491502635789000116804075)
                      ·
                        rfl

theorem cell23_2904691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3, 3].length) (baseStart_2904691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904691 prefixEnd_2904691 := by exact prefixLift 2904691
  have htrace : WordTrace (prefixWord ++ tailWord_2904691) baseStart_2904691 baseEnd_2904691 := by
    simpa [prefixWord, tailWord_2904691, baseEnd_2904691] using wordTrace_append hprefix tailTrace_2904691
  have hstable : (prefixWord ++ tailWord_2904691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904691).length < 2 ^ (prefixWord ++ tailWord_2904691).sum := by decide
  have hdescent : baseEnd_2904691 < baseStart_2904691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904706 : List Nat := [3, 4, 3, 1, 1, 2, 1, 2, 1, 5]
def baseStart_2904706 : Nat := 118140960795 + 2904706 * 2 ^ 59
def prefixEnd_2904706 : Nat := 4983230072969 + 3 ^ 40 * 2904706 * 2
def baseEnd_2904706 : Nat := 497170112666272519372169

theorem tailTrace_2904706 : CollatzResearch.WordTrace tailWord_2904706 prefixEnd_2904706 497170112666272519372169 := by
  unfold tailWord_2904706
  simp only [CollatzResearch.WordTrace]
  refine ⟨26485832853688430283655493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70628887609835814089747981 26485832853688430283655493)
  ·
    refine ⟨4966093660066580678185405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26485832853688430283655493 4966093660066580678185405)
    ·
      refine ⟨1862285122524967754319527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4966093660066580678185405 1862285122524967754319527)
      ·
        refine ⟨2793427683787451631479291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1862285122524967754319527 2793427683787451631479291)
        ·
          refine ⟨4190141525681177447218937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2793427683787451631479291 4190141525681177447218937)
          ·
            refine ⟨3142606144260883085414203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4190141525681177447218937 3142606144260883085414203)
            ·
              refine ⟨4713909216391324628121305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3142606144260883085414203 4713909216391324628121305)
              ·
                refine ⟨3535431912293493471090979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4713909216391324628121305 3535431912293493471090979)
                ·
                  refine ⟨5303147868440240206636469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3535431912293493471090979 5303147868440240206636469)
                  ·
                    refine ⟨497170112666272519372169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5303147868440240206636469 497170112666272519372169)
                    ·
                      rfl

theorem cell23_2904706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_2904706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904706 prefixEnd_2904706 := by exact prefixLift 2904706
  have htrace : WordTrace (prefixWord ++ tailWord_2904706) baseStart_2904706 baseEnd_2904706 := by
    simpa [prefixWord, tailWord_2904706, baseEnd_2904706] using wordTrace_append hprefix tailTrace_2904706
  have hstable : (prefixWord ++ tailWord_2904706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904706).length < 2 ^ (prefixWord ++ tailWord_2904706).sum := by decide
  have hdescent : baseEnd_2904706 < baseStart_2904706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904741 : List Nat := [1, 3, 1, 2, 1, 2, 1, 4, 2, 6]
def baseStart_2904741 : Nat := 118140960795 + 2904741 * 2 ^ 59
def prefixEnd_2904741 : Nat := 4983230072969 + 3 ^ 40 * 2904741 * 2
def baseEnd_2904741 : Nat := 497176103273908307059615

theorem tailTrace_2904741 : CollatzResearch.WordTrace tailWord_2904741 prefixEnd_2904741 497176103273908307059615 := by
  unfold tailWord_2904741
  simp only [CollatzResearch.WordTrace]
  refine ⟨105944607969626922112146077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70629738646417948074764051 105944607969626922112146077)
  ·
    refine ⟨39729227988610095792054779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105944607969626922112146077 39729227988610095792054779)
    ·
      refine ⟨59593841982915143688082169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39729227988610095792054779 59593841982915143688082169)
      ·
        refine ⟨44695381487186357766061627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59593841982915143688082169 44695381487186357766061627)
        ·
          refine ⟨67043072230779536649092441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44695381487186357766061627 67043072230779536649092441)
          ·
            refine ⟨50282304173084652486819331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67043072230779536649092441 50282304173084652486819331)
            ·
              refine ⟨75423456259626978730228997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50282304173084652486819331 75423456259626978730228997)
              ·
                refine ⟨14141898048680058511917937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75423456259626978730228997 14141898048680058511917937)
                ·
                  refine ⟨10606423536510043883938453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14141898048680058511917937 10606423536510043883938453)
                  ·
                    refine ⟨497176103273908307059615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10606423536510043883938453 497176103273908307059615)
                    ·
                      rfl

theorem cell23_2904741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 6].length) (baseStart_2904741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904741 prefixEnd_2904741 := by exact prefixLift 2904741
  have htrace : WordTrace (prefixWord ++ tailWord_2904741) baseStart_2904741 baseEnd_2904741 := by
    simpa [prefixWord, tailWord_2904741, baseEnd_2904741] using wordTrace_append hprefix tailTrace_2904741
  have hstable : (prefixWord ++ tailWord_2904741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904741).length < 2 ^ (prefixWord ++ tailWord_2904741).sum := by decide
  have hdescent : baseEnd_2904741 < baseStart_2904741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904765 : List Nat := [1, 4, 1, 2, 1, 3, 1, 3, 1, 4, 2]
def baseStart_2904765 : Nat := 118140960795 + 2904765 * 2 ^ 59
def prefixEnd_2904765 : Nat := 4983230072969 + 3 ^ 40 * 2904765 * 2
def baseEnd_2904765 : Nat := 1491540633357432827278735

theorem tailTrace_2904765 : CollatzResearch.WordTrace tailWord_2904765 prefixEnd_2904765 1491540633357432827278735 := by
  unfold tailWord_2904765
  simp only [CollatzResearch.WordTrace]
  refine ⟨105945483321539974211019749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70630322214359982807346499 105945483321539974211019749)
  ·
    refine ⟨19864778122788745164566203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105945483321539974211019749 19864778122788745164566203)
    ·
      refine ⟨29797167184183117746849305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19864778122788745164566203 29797167184183117746849305)
      ·
        refine ⟨22347875388137338310136979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29797167184183117746849305 22347875388137338310136979)
        ·
          refine ⟨33521813082206007465205469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22347875388137338310136979 33521813082206007465205469)
          ·
            refine ⟨12570679905827252799452051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33521813082206007465205469 12570679905827252799452051)
            ·
              refine ⟨18856019858740879199178077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12570679905827252799452051 18856019858740879199178077)
              ·
                refine ⟨7071007447027829699691779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18856019858740879199178077 7071007447027829699691779)
                ·
                  refine ⟨10606511170541744549537669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7071007447027829699691779 10606511170541744549537669)
                  ·
                    refine ⟨1988720844476577103038313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10606511170541744549537669 1988720844476577103038313)
                    ·
                      refine ⟨1491540633357432827278735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1988720844476577103038313 1491540633357432827278735)
                      ·
                        rfl

theorem cell23_2904765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_2904765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904765 prefixEnd_2904765 := by exact prefixLift 2904765
  have htrace : WordTrace (prefixWord ++ tailWord_2904765) baseStart_2904765 baseEnd_2904765 := by
    simpa [prefixWord, tailWord_2904765, baseEnd_2904765] using wordTrace_append hprefix tailTrace_2904765
  have hstable : (prefixWord ++ tailWord_2904765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904765).length < 2 ^ (prefixWord ++ tailWord_2904765).sum := by decide
  have hdescent : baseEnd_2904765 < baseStart_2904765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904786 : List Nat := [3, 2, 2, 2, 3, 2, 2, 1, 1, 3, 2]
def baseStart_2904786 : Nat := 118140960795 + 2904786 * 2 ^ 59
def prefixEnd_2904786 : Nat := 4983230072969 + 3 ^ 40 * 2904786 * 2
def baseEnd_2904786 : Nat := 1491551416451177245116139

theorem tailTrace_2904786 : CollatzResearch.WordTrace tailWord_2904786 prefixEnd_2904786 1491551416451177245116139 := by
  unfold tailWord_2904786
  simp only [CollatzResearch.WordTrace]
  refine ⟨26486562313615973699383553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70630832836309263198356141 26486562313615973699383553)
  ·
    refine ⟨19864921735211980274537665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26486562313615973699383553 19864921735211980274537665)
    ·
      refine ⟨14898691301408985205903249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19864921735211980274537665 14898691301408985205903249)
      ·
        refine ⟨11174018476056738904427437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14898691301408985205903249 11174018476056738904427437)
        ·
          refine ⟨4190256928521277089160289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11174018476056738904427437 4190256928521277089160289)
          ·
            refine ⟨3142692696390957816870217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4190256928521277089160289 3142692696390957816870217)
            ·
              refine ⟨2357019522293218362652663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3142692696390957816870217 2357019522293218362652663)
              ·
                refine ⟨3535529283439827543978995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2357019522293218362652663 3535529283439827543978995)
                ·
                  refine ⟨5303293925159741315968493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3535529283439827543978995 5303293925159741315968493)
                  ·
                    refine ⟨1988735221934902993488185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5303293925159741315968493 1988735221934902993488185)
                    ·
                      refine ⟨1491551416451177245116139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1988735221934902993488185 1491551416451177245116139)
                      ·
                        rfl

theorem cell23_2904786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_2904786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904786 prefixEnd_2904786 := by exact prefixLift 2904786
  have htrace : WordTrace (prefixWord ++ tailWord_2904786) baseStart_2904786 baseEnd_2904786 := by
    simpa [prefixWord, tailWord_2904786, baseEnd_2904786] using wordTrace_append hprefix tailTrace_2904786
  have hstable : (prefixWord ++ tailWord_2904786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904786).length < 2 ^ (prefixWord ++ tailWord_2904786).sum := by decide
  have hdescent : baseEnd_2904786 < baseStart_2904786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2904799 : List Nat := [1, 1, 2, 3, 2, 5, 1, 2, 2, 2, 2]
def baseStart_2904799 : Nat := 118140960795 + 2904799 * 2 ^ 59
def prefixEnd_2904799 : Nat := 4983230072969 + 3 ^ 40 * 2904799 * 2
def baseEnd_2904799 : Nat := 1491558091699685694253579

theorem tailTrace_2904799 : CollatzResearch.WordTrace tailWord_2904799 prefixEnd_2904799 1491558091699685694253579 := by
  unfold tailWord_2904799
  simp only [CollatzResearch.WordTrace]
  refine ⟨105946723403416798017757451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70631148935611198678504967 105946723403416798017757451)
  ·
    refine ⟨158920085105125197026636177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105946723403416798017757451 158920085105125197026636177)
    ·
      refine ⟨119190063828843897769977133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158920085105125197026636177 119190063828843897769977133)
      ·
        refine ⟨44696273935816461663741425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119190063828843897769977133 44696273935816461663741425)
        ·
          refine ⟨33522205451862346247806069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44696273935816461663741425 33522205451862346247806069)
          ·
            refine ⟨3142706761112094960731819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33522205451862346247806069 3142706761112094960731819)
            ·
              refine ⟨4714060141668142441097729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3142706761112094960731819 4714060141668142441097729)
              ·
                refine ⟨3535545106251106830823297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4714060141668142441097729 3535545106251106830823297)
                ·
                  refine ⟨2651658829688330123117473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3535545106251106830823297 2651658829688330123117473)
                  ·
                    refine ⟨1988744122266247592338105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2651658829688330123117473 1988744122266247592338105)
                    ·
                      refine ⟨1491558091699685694253579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1988744122266247592338105 1491558091699685694253579)
                      ·
                        rfl

theorem cell23_2904799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2, 2, 2].length) (baseStart_2904799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2904799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2904799 prefixEnd_2904799 := by exact prefixLift 2904799
  have htrace : WordTrace (prefixWord ++ tailWord_2904799) baseStart_2904799 baseEnd_2904799 := by
    simpa [prefixWord, tailWord_2904799, baseEnd_2904799] using wordTrace_append hprefix tailTrace_2904799
  have hstable : (prefixWord ++ tailWord_2904799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2904799).length < 2 ^ (prefixWord ++ tailWord_2904799).sum := by decide
  have hdescent : baseEnd_2904799 < baseStart_2904799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2904799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
