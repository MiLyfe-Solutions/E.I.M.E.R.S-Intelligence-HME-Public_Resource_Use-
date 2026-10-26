import V185TrunkScan23Chunk0507

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3004889 : List Nat := [1, 2, 1, 2, 4, 1, 1, 5, 2, 4]
def baseStart_3004889 : Nat := 118140960795 + 3004889 * 2 ^ 59
def prefixEnd_3004889 : Nat := 4983230072969 + 3 ^ 40 * 3004889 * 2
def baseEnd_3004889 : Nat := 514317456802733030556091

theorem tailTrace_3004889 : CollatzResearch.WordTrace tailWord_3004889 prefixEnd_3004889 514317456802733030556091 := by
  unfold tailWord_3004889
  simp only [CollatzResearch.WordTrace]
  refine ⟨109597305610807822028833721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73064870407205214685889147 109597305610807822028833721)
  ·
    refine ⟨82197979208105866521625291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109597305610807822028833721 82197979208105866521625291)
    ·
      refine ⟨123296968812158799782437937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82197979208105866521625291 123296968812158799782437937)
      ·
        refine ⟨92472726609119099836828453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123296968812158799782437937 92472726609119099836828453)
        ·
          refine ⟨17338636239209831219405335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92472726609119099836828453 17338636239209831219405335)
          ·
            refine ⟨26007954358814746829108003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17338636239209831219405335 26007954358814746829108003)
            ·
              refine ⟨39011931538222120243662005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26007954358814746829108003 39011931538222120243662005)
              ·
                refine ⟨3657368581708323772843313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39011931538222120243662005 3657368581708323772843313)
                ·
                  refine ⟨2743026436281242829632485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3657368581708323772843313 2743026436281242829632485)
                  ·
                    refine ⟨514317456802733030556091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2743026436281242829632485 514317456802733030556091)
                    ·
                      rfl

theorem cell23_3004889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2, 4].length) (baseStart_3004889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004889 prefixEnd_3004889 := by exact prefixLift 3004889
  have htrace : WordTrace (prefixWord ++ tailWord_3004889) baseStart_3004889 baseEnd_3004889 := by
    simpa [prefixWord, tailWord_3004889, baseEnd_3004889] using wordTrace_append hprefix tailTrace_3004889
  have hstable : (prefixWord ++ tailWord_3004889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004889).length < 2 ^ (prefixWord ++ tailWord_3004889).sum := by decide
  have hdescent : baseEnd_3004889 < baseStart_3004889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004896 : List Nat := [2, 1, 1, 3, 1, 1, 5, 2, 3, 2, 2]
def baseStart_3004896 : Nat := 118140960795 + 3004896 * 2 ^ 59
def prefixEnd_3004896 : Nat := 4983230072969 + 3 ^ 40 * 3004896 * 2
def baseEnd_3004896 : Nat := 1542955964772780564280741

theorem tailTrace_3004896 : CollatzResearch.WordTrace tailWord_3004896 prefixEnd_3004896 1542955964772780564280741 := by
  unfold tailWord_3004896
  simp only [CollatzResearch.WordTrace]
  refine ⟨54798780460891231112169271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73065040614521641482892361 54798780460891231112169271)
  ·
    refine ⟨82198170691336846668253907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54798780460891231112169271 82198170691336846668253907)
    ·
      refine ⟨123297256037005270002380861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82198170691336846668253907 123297256037005270002380861)
      ·
        refine ⟨46236471013876976250892823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123297256037005270002380861 46236471013876976250892823)
        ·
          refine ⟨69354706520815464376339235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46236471013876976250892823 69354706520815464376339235)
          ·
            refine ⟨104032059781223196564508853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69354706520815464376339235 104032059781223196564508853)
            ·
              refine ⟨9753005604489674677922705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104032059781223196564508853 9753005604489674677922705)
              ·
                refine ⟨7314754203367256008442029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9753005604489674677922705 7314754203367256008442029)
                ·
                  refine ⟨2743032826262721003165761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7314754203367256008442029 2743032826262721003165761)
                  ·
                    refine ⟨2057274619697040752374321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2743032826262721003165761 2057274619697040752374321)
                    ·
                      refine ⟨1542955964772780564280741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2057274619697040752374321 1542955964772780564280741)
                      ·
                        rfl

theorem cell23_3004896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 3, 2, 2].length) (baseStart_3004896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004896 prefixEnd_3004896 := by exact prefixLift 3004896
  have htrace : WordTrace (prefixWord ++ tailWord_3004896) baseStart_3004896 baseEnd_3004896 := by
    simpa [prefixWord, tailWord_3004896, baseEnd_3004896] using wordTrace_append hprefix tailTrace_3004896
  have hstable : (prefixWord ++ tailWord_3004896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004896).length < 2 ^ (prefixWord ++ tailWord_3004896).sum := by decide
  have hdescent : baseEnd_3004896 < baseStart_3004896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004964 : List Nat := [2, 3, 1, 5, 1, 2, 1, 3, 1, 2, 2]
def baseStart_3004964 : Nat := 118140960795 + 3004964 * 2 ^ 59
def prefixEnd_3004964 : Nat := 4983230072969 + 3 ^ 40 * 3004964 * 2
def baseEnd_3004964 : Nat := 1542990881457286298230429

theorem tailTrace_3004964 : CollatzResearch.WordTrace tailWord_3004964 prefixEnd_3004964 1542990881457286298230429 := by
  unfold tailWord_3004964
  simp only [CollatzResearch.WordTrace]
  refine ⟨54800020542768054918906973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73066694057024073225209297 54800020542768054918906973)
  ·
    refine ⟨20550007703538020594590115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54800020542768054918906973 20550007703538020594590115)
    ·
      refine ⟨30825011555307030891885173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20550007703538020594590115 30825011555307030891885173)
      ·
        refine ⟨2889844833310034146114235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30825011555307030891885173 2889844833310034146114235)
        ·
          refine ⟨4334767249965051219171353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2889844833310034146114235 4334767249965051219171353)
          ·
            refine ⟨3251075437473788414378515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4334767249965051219171353 3251075437473788414378515)
            ·
              refine ⟨4876613156210682621567773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3251075437473788414378515 4876613156210682621567773)
              ·
                refine ⟨1828729933579005983087915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4876613156210682621567773 1828729933579005983087915)
                ·
                  refine ⟨2743094900368508974631873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1828729933579005983087915 2743094900368508974631873)
                  ·
                    refine ⟨2057321175276381730973905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2743094900368508974631873 2057321175276381730973905)
                    ·
                      refine ⟨1542990881457286298230429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2057321175276381730973905 1542990881457286298230429)
                      ·
                        rfl

theorem cell23_3004964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_3004964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004964 prefixEnd_3004964 := by exact prefixLift 3004964
  have htrace : WordTrace (prefixWord ++ tailWord_3004964) baseStart_3004964 baseEnd_3004964 := by
    simpa [prefixWord, tailWord_3004964, baseEnd_3004964] using wordTrace_append hprefix tailTrace_3004964
  have hstable : (prefixWord ++ tailWord_3004964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004964).length < 2 ^ (prefixWord ++ tailWord_3004964).sum := by decide
  have hdescent : baseEnd_3004964 < baseStart_3004964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005039 : List Nat := [1, 1, 2, 1, 3, 2, 4, 2, 2, 5]
def baseStart_3005039 : Nat := 118140960795 + 3005039 * 2 ^ 59
def prefixEnd_3005039 : Nat := 4983230072969 + 3 ^ 40 * 3005039 * 2
def baseEnd_3005039 : Nat := 514343130835457834930861

theorem tailTrace_3005039 : CollatzResearch.WordTrace tailWord_3005039 prefixEnd_3005039 514343130835457834930861 := by
  unfold tailWord_3005039
  simp only [CollatzResearch.WordTrace]
  refine ⟨109602776560264397646794171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73068517706842931764529447 109602776560264397646794171)
  ·
    refine ⟨164404164840396596470191257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109602776560264397646794171 164404164840396596470191257)
    ·
      refine ⟨123303123630297447352643443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164404164840396596470191257 123303123630297447352643443)
      ·
        refine ⟨184954685445446171028965165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123303123630297447352643443 184954685445446171028965165)
        ·
          refine ⟨69358007042042314135861937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184954685445446171028965165 69358007042042314135861937)
          ·
            refine ⟨52018505281531735601896453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69358007042042314135861937 52018505281531735601896453)
            ·
              refine ⟨9753469740287200425355585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52018505281531735601896453 9753469740287200425355585)
              ·
                refine ⟨7315102305215400319016689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9753469740287200425355585 7315102305215400319016689)
                ·
                  refine ⟨5486326728911550239262517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7315102305215400319016689 5486326728911550239262517)
                  ·
                    refine ⟨514343130835457834930861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5486326728911550239262517 514343130835457834930861)
                    ·
                      rfl

theorem cell23_3005039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 5].length) (baseStart_3005039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005039 prefixEnd_3005039 := by exact prefixLift 3005039
  have htrace : WordTrace (prefixWord ++ tailWord_3005039) baseStart_3005039 baseEnd_3005039 := by
    simpa [prefixWord, tailWord_3005039, baseEnd_3005039] using wordTrace_append hprefix tailTrace_3005039
  have hstable : (prefixWord ++ tailWord_3005039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005039).length < 2 ^ (prefixWord ++ tailWord_3005039).sum := by decide
  have hdescent : baseEnd_3005039 < baseStart_3005039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005049 : List Nat := [1, 2, 1, 3, 3, 2, 2, 1, 1, 2, 5]
def baseStart_3005049 : Nat := 118140960795 + 3005049 * 2 ^ 59
def prefixEnd_3005049 : Nat := 4983230072969 + 3 ^ 40 * 3005049 * 2
def baseEnd_3005049 : Nat := 1543034527312918465667537

theorem tailTrace_3005049 : CollatzResearch.WordTrace tailWord_3005049 prefixEnd_3005049 1543034527312918465667537 := by
  unfold tailWord_3005049
  simp only [CollatzResearch.WordTrace]
  refine ⟨109603141290228169354658201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73068760860152112903105467 109603141290228169354658201)
  ·
    refine ⟨82202355967671127015993651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109603141290228169354658201 82202355967671127015993651)
    ·
      refine ⟨123303533951506690523990477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82202355967671127015993651 123303533951506690523990477)
      ·
        refine ⟨46238825231815008946496429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123303533951506690523990477 46238825231815008946496429)
        ·
          refine ⟨17339559461930628354936161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46238825231815008946496429 17339559461930628354936161)
          ·
            refine ⟨13004669596447971266202121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17339559461930628354936161 13004669596447971266202121)
            ·
              refine ⟨9753502197335978449651591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13004669596447971266202121 9753502197335978449651591)
              ·
                refine ⟨14630253296003967674477387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9753502197335978449651591 14630253296003967674477387)
                ·
                  refine ⟨21945379944005951511716081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14630253296003967674477387 21945379944005951511716081)
                  ·
                    refine ⟨16459034958004463633787061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21945379944005951511716081 16459034958004463633787061)
                    ·
                      refine ⟨1543034527312918465667537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16459034958004463633787061 1543034527312918465667537)
                      ·
                        rfl

theorem cell23_3005049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_3005049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005049 prefixEnd_3005049 := by exact prefixLift 3005049
  have htrace : WordTrace (prefixWord ++ tailWord_3005049) baseStart_3005049 baseEnd_3005049 := by
    simpa [prefixWord, tailWord_3005049, baseEnd_3005049] using wordTrace_append hprefix tailTrace_3005049
  have hstable : (prefixWord ++ tailWord_3005049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005049).length < 2 ^ (prefixWord ++ tailWord_3005049).sum := by decide
  have hdescent : baseEnd_3005049 < baseStart_3005049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005059 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 4]
def baseStart_3005059 : Nat := 118140960795 + 3005059 * 2 ^ 59
def prefixEnd_3005059 : Nat := 4983230072969 + 3 ^ 40 * 3005059 * 2
def baseEnd_3005059 : Nat := 1543039662119463426542491

theorem tailTrace_3005059 : CollatzResearch.WordTrace tailWord_3005059 prefixEnd_3005059 1543039662119463426542491 := by
  unfold tailWord_3005059
  simp only [CollatzResearch.WordTrace]
  refine ⟨109603506020191941062522231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73069004013461294041681487 109603506020191941062522231)
  ·
    refine ⟨164405259030287911593783347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109603506020191941062522231 164405259030287911593783347)
    ·
      refine ⟨246607888545431867390675021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164405259030287911593783347 246607888545431867390675021)
      ·
        refine ⟨92477958204536950271503133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246607888545431867390675021 92477958204536950271503133)
        ·
          refine ⟨34679234326701356351813675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92477958204536950271503133 34679234326701356351813675)
          ·
            refine ⟨52018851490052034527720513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34679234326701356351813675 52018851490052034527720513)
            ·
              refine ⟨39014138617539025895790385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52018851490052034527720513 39014138617539025895790385)
              ·
                refine ⟨29260603963154269421842789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39014138617539025895790385 29260603963154269421842789)
                ·
                  refine ⟨5486363243091425516595523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29260603963154269421842789 5486363243091425516595523)
                  ·
                    refine ⟨8229544864637138274893285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5486363243091425516595523 8229544864637138274893285)
                    ·
                      refine ⟨1543039662119463426542491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8229544864637138274893285 1543039662119463426542491)
                      ·
                        rfl

theorem cell23_3005059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_3005059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005059 prefixEnd_3005059 := by exact prefixLift 3005059
  have htrace : WordTrace (prefixWord ++ tailWord_3005059) baseStart_3005059 baseEnd_3005059 := by
    simpa [prefixWord, tailWord_3005059, baseEnd_3005059] using wordTrace_append hprefix tailTrace_3005059
  have hstable : (prefixWord ++ tailWord_3005059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005059).length < 2 ^ (prefixWord ++ tailWord_3005059).sum := by decide
  have hdescent : baseEnd_3005059 < baseStart_3005059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005103 : List Nat := [1, 1, 2, 1, 2, 5, 2, 4, 1, 4]
def baseStart_3005103 : Nat := 118140960795 + 3005103 * 2 ^ 59
def prefixEnd_3005103 : Nat := 4983230072969 + 3 ^ 40 * 3005103 * 2
def baseEnd_3005103 : Nat := 514354085089420418130763

theorem tailTrace_3005103 : CollatzResearch.WordTrace tailWord_3005103 prefixEnd_3005103 514354085089420418130763 := by
  unfold tailWord_3005103
  simp only [CollatzResearch.WordTrace]
  refine ⟨109605110832032536577123963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73070073888021691051415975 109605110832032536577123963)
  ·
    refine ⟨164407666248048804865685945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109605110832032536577123963 164407666248048804865685945)
    ·
      refine ⟨123305749686036603649264459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164407666248048804865685945 123305749686036603649264459)
      ·
        refine ⟨184958624529054905473896689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123305749686036603649264459 184958624529054905473896689)
        ·
          refine ⟨138718968396791179105422517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184958624529054905473896689 138718968396791179105422517)
          ·
            refine ⟨13004903287199173041133361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138718968396791179105422517 13004903287199173041133361)
            ·
              refine ⟨9753677465399379780850021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13004903287199173041133361 9753677465399379780850021)
              ·
                refine ⟨1828814524762383708909379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9753677465399379780850021 1828814524762383708909379)
                ·
                  refine ⟨2743221787143575563364069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1828814524762383708909379 2743221787143575563364069)
                  ·
                    refine ⟨514354085089420418130763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2743221787143575563364069 514354085089420418130763)
                    ·
                      rfl

theorem cell23_3005103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4, 1, 4].length) (baseStart_3005103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005103 prefixEnd_3005103 := by exact prefixLift 3005103
  have htrace : WordTrace (prefixWord ++ tailWord_3005103) baseStart_3005103 baseEnd_3005103 := by
    simpa [prefixWord, tailWord_3005103, baseEnd_3005103] using wordTrace_append hprefix tailTrace_3005103
  have hstable : (prefixWord ++ tailWord_3005103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005103).length < 2 ^ (prefixWord ++ tailWord_3005103).sum := by decide
  have hdescent : baseEnd_3005103 < baseStart_3005103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005146 : List Nat := [3, 1, 1, 2, 2, 2, 1, 5, 1, 5]
def baseStart_3005146 : Nat := 118140960795 + 3005146 * 2 ^ 59
def prefixEnd_3005146 : Nat := 4983230072969 + 3 ^ 40 * 3005146 * 2
def baseEnd_3005146 : Nat := 514361444978801528718197

theorem tailTrace_3005146 : CollatzResearch.WordTrace tailWord_3005146 prefixEnd_3005146 514361444978801528718197 := by
  unfold tailWord_3005146
  simp only [CollatzResearch.WordTrace]
  refine ⟨27401669792719188730234823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73071119447251169947292861 27401669792719188730234823)
  ·
    refine ⟨41102504689078783095352235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27401669792719188730234823 41102504689078783095352235)
    ·
      refine ⟨61653757033618174643028353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41102504689078783095352235 61653757033618174643028353)
      ·
        refine ⟨46240317775213630982271265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61653757033618174643028353 46240317775213630982271265)
        ·
          refine ⟨34680238331410223236703449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46240317775213630982271265 34680238331410223236703449)
          ·
            refine ⟨26010178748557667427527587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34680238331410223236703449 26010178748557667427527587)
            ·
              refine ⟨39015268122836501141291381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26010178748557667427527587 39015268122836501141291381)
              ·
                refine ⟨3657681386515921981996067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39015268122836501141291381 3657681386515921981996067)
                ·
                  refine ⟨5486522079773882972994101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3657681386515921981996067 5486522079773882972994101)
                  ·
                    refine ⟨514361444978801528718197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5486522079773882972994101 514361444978801528718197)
                    ·
                      rfl

theorem cell23_3005146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 1, 5].length) (baseStart_3005146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005146 prefixEnd_3005146 := by exact prefixLift 3005146
  have htrace : WordTrace (prefixWord ++ tailWord_3005146) baseStart_3005146 baseEnd_3005146 := by
    simpa [prefixWord, tailWord_3005146, baseEnd_3005146] using wordTrace_append hprefix tailTrace_3005146
  have hstable : (prefixWord ++ tailWord_3005146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005146).length < 2 ^ (prefixWord ++ tailWord_3005146).sum := by decide
  have hdescent : baseEnd_3005146 < baseStart_3005146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005153 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 4, 3, 2]
def baseStart_3005153 : Nat := 118140960795 + 3005153 * 2 ^ 59
def prefixEnd_3005153 : Nat := 4983230072969 + 3 ^ 40 * 3005153 * 2
def baseEnd_3005153 : Nat := 1543087929300986058767059

theorem tailTrace_3005153 : CollatzResearch.WordTrace tailWord_3005153 prefixEnd_3005153 1543087929300986058767059 := by
  unfold tailWord_3005153
  simp only [CollatzResearch.WordTrace]
  refine ⟨109606934481851395116444113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73071289654567596744296075 109606934481851395116444113)
  ·
    refine ⟨82205200861388546337333085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109606934481851395116444113 82205200861388546337333085)
    ·
      refine ⟨30826950323020704876499907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82205200861388546337333085 30826950323020704876499907)
      ·
        refine ⟨46240425484531057314749861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30826950323020704876499907 46240425484531057314749861)
        ·
          refine ⟨8670079778349573246515599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46240425484531057314749861 8670079778349573246515599)
          ·
            refine ⟨13005119667524359869773399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8670079778349573246515599 13005119667524359869773399)
            ·
              refine ⟨19507679501286539804660099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13005119667524359869773399 19507679501286539804660099)
              ·
                refine ⟨29261519251929809706990149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19507679501286539804660099 29261519251929809706990149)
                ·
                  refine ⟨5486534859736839320060653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29261519251929809706990149 5486534859736839320060653)
                  ·
                    refine ⟨2057450572401314745022745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5486534859736839320060653 2057450572401314745022745)
                    ·
                      refine ⟨1543087929300986058767059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2057450572401314745022745 1543087929300986058767059)
                      ·
                        rfl

theorem cell23_3005153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 3, 2].length) (baseStart_3005153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005153 prefixEnd_3005153 := by exact prefixLift 3005153
  have htrace : WordTrace (prefixWord ++ tailWord_3005153) baseStart_3005153 baseEnd_3005153 := by
    simpa [prefixWord, tailWord_3005153, baseEnd_3005153] using wordTrace_append hprefix tailTrace_3005153
  have hstable : (prefixWord ++ tailWord_3005153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005153).length < 2 ^ (prefixWord ++ tailWord_3005153).sum := by decide
  have hdescent : baseEnd_3005153 < baseStart_3005153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005183 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 5, 2, 2]
def baseStart_3005183 : Nat := 118140960795 + 3005183 * 2 ^ 59
def prefixEnd_3005183 : Nat := 4983230072969 + 3 ^ 40 * 3005183 * 2
def baseEnd_3005183 : Nat := 1543103333720620941391921

theorem tailTrace_3005183 : CollatzResearch.WordTrace tailWord_3005183 prefixEnd_3005183 1543103333720620941391921 := by
  unfold tailWord_3005183
  simp only [CollatzResearch.WordTrace]
  refine ⟨109608028671742710240036203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73072019114495140160024135 109608028671742710240036203)
  ·
    refine ⟨164412043007614065360054305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109608028671742710240036203 164412043007614065360054305)
    ·
      refine ⟨123309032255710549020040729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164412043007614065360054305 123309032255710549020040729)
      ·
        refine ⟨92481774191782911765030547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123309032255710549020040729 92481774191782911765030547)
        ·
          refine ⟨138722661287674367647545821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92481774191782911765030547 138722661287674367647545821)
          ·
            refine ⟨52020997982877887867829683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138722661287674367647545821 52020997982877887867829683)
            ·
              refine ⟨78031496974316831801744525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52020997982877887867829683 78031496974316831801744525)
              ·
                refine ⟨29261811365368811925654197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78031496974316831801744525 29261811365368811925654197)
                ·
                  refine ⟨2743294815503326118030081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29261811365368811925654197 2743294815503326118030081)
                  ·
                    refine ⟨2057471111627494588522561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2743294815503326118030081 2057471111627494588522561)
                    ·
                      refine ⟨1543103333720620941391921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2057471111627494588522561 1543103333720620941391921)
                      ·
                        rfl

theorem cell23_3005183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5, 2, 2].length) (baseStart_3005183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005183 prefixEnd_3005183 := by exact prefixLift 3005183
  have htrace : WordTrace (prefixWord ++ tailWord_3005183) baseStart_3005183 baseEnd_3005183 := by
    simpa [prefixWord, tailWord_3005183, baseEnd_3005183] using wordTrace_append hprefix tailTrace_3005183
  have hstable : (prefixWord ++ tailWord_3005183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005183).length < 2 ^ (prefixWord ++ tailWord_3005183).sum := by decide
  have hdescent : baseEnd_3005183 < baseStart_3005183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005209 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 2, 2, 6]
def baseStart_3005209 : Nat := 118140960795 + 3005209 * 2 ^ 59
def prefixEnd_3005209 : Nat := 4983230072969 + 3 ^ 40 * 3005209 * 2
def baseEnd_3005209 : Nat := 1543116684217637839666801

theorem tailTrace_3005209 : CollatzResearch.WordTrace tailWord_3005209 prefixEnd_3005209 1543116684217637839666801 := by
  unfold tailWord_3005209
  simp only [CollatzResearch.WordTrace]
  refine ⟨109608976969648516680482681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73072651313099011120321787 109608976969648516680482681)
  ·
    refine ⟨82206732727236387510362011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109608976969648516680482681 82206732727236387510362011)
    ·
      refine ⟨123310099090854581265543017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82206732727236387510362011 123310099090854581265543017)
      ·
        refine ⟨92482574318140935949157263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123310099090854581265543017 92482574318140935949157263)
        ·
          refine ⟨138723861477211403923735895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92482574318140935949157263 138723861477211403923735895)
          ·
            refine ⟨208085792215817105885603843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138723861477211403923735895 208085792215817105885603843)
            ·
              refine ⟨312128688323725658828405765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208085792215817105885603843 312128688323725658828405765)
              ·
                refine ⟨58524129060698561030326081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 312128688323725658828405765 58524129060698561030326081)
                ·
                  refine ⟨43893096795523920772744561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58524129060698561030326081 43893096795523920772744561)
                  ·
                    refine ⟨32919822596642940579558421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43893096795523920772744561 32919822596642940579558421)
                    ·
                      refine ⟨1543116684217637839666801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32919822596642940579558421 1543116684217637839666801)
                      ·
                        rfl

theorem cell23_3005209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_3005209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005209 prefixEnd_3005209 := by exact prefixLift 3005209
  have htrace : WordTrace (prefixWord ++ tailWord_3005209) baseStart_3005209 baseEnd_3005209 := by
    simpa [prefixWord, tailWord_3005209, baseEnd_3005209] using wordTrace_append hprefix tailTrace_3005209
  have hstable : (prefixWord ++ tailWord_3005209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005209).length < 2 ^ (prefixWord ++ tailWord_3005209).sum := by decide
  have hdescent : baseEnd_3005209 < baseStart_3005209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005217 : List Nat := [1, 2, 3, 2, 1, 2, 3, 4, 1, 2, 2]
def baseStart_3005217 : Nat := 118140960795 + 3005217 * 2 ^ 59
def prefixEnd_3005217 : Nat := 4983230072969 + 3 ^ 40 * 3005217 * 2
def baseEnd_3005217 : Nat := 1543120792062873808366765

theorem tailTrace_3005217 : CollatzResearch.WordTrace tailWord_3005217 prefixEnd_3005217 1543120792062873808366765 := by
  unfold tailWord_3005217
  simp only [CollatzResearch.WordTrace]
  refine ⟨109609268753619534046773905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73072845835746356031182603 109609268753619534046773905)
  ·
    refine ⟨82206951565214650535080429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109609268753619534046773905 82206951565214650535080429)
    ·
      refine ⟨30827606836955493950655161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82206951565214650535080429 30827606836955493950655161)
      ·
        refine ⟨23120705127716620462991371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30827606836955493950655161 23120705127716620462991371)
        ·
          refine ⟨34681057691574930694487057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23120705127716620462991371 34681057691574930694487057)
          ·
            refine ⟨26010793268681198020865293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34681057691574930694487057 26010793268681198020865293)
            ·
              refine ⟨9754047475755449257824485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26010793268681198020865293 9754047475755449257824485)
              ·
                refine ⟨1828883901704146735842091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9754047475755449257824485 1828883901704146735842091)
                ·
                  refine ⟨2743325852556220103763137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1828883901704146735842091 2743325852556220103763137)
                  ·
                    refine ⟨2057494389417165077822353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2743325852556220103763137 2057494389417165077822353)
                    ·
                      refine ⟨1543120792062873808366765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2057494389417165077822353 1543120792062873808366765)
                      ·
                        rfl

theorem cell23_3005217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_3005217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005217 prefixEnd_3005217 := by exact prefixLift 3005217
  have htrace : WordTrace (prefixWord ++ tailWord_3005217) baseStart_3005217 baseEnd_3005217 := by
    simpa [prefixWord, tailWord_3005217, baseEnd_3005217] using wordTrace_append hprefix tailTrace_3005217
  have hstable : (prefixWord ++ tailWord_3005217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005217).length < 2 ^ (prefixWord ++ tailWord_3005217).sum := by decide
  have hdescent : baseEnd_3005217 < baseStart_3005217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005230 : List Nat := [4, 1, 3, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_3005230 : Nat := 118140960795 + 3005230 * 2 ^ 59
def prefixEnd_3005230 : Nat := 4983230072969 + 3 ^ 40 * 3005230 * 2
def baseEnd_3005230 : Nat := 1543127467311382257504205

theorem tailTrace_3005230 : CollatzResearch.WordTrace tailWord_3005230 prefixEnd_3005230 1543127467311382257504205 := by
  unfold tailWord_3005230
  simp only [CollatzResearch.WordTrace]
  refine ⟨13701217862821554658374643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73073161935048291511331429 13701217862821554658374643)
  ·
    refine ⟨20551826794232331987561965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13701217862821554658374643 20551826794232331987561965)
    ·
      refine ⟨7706935047837124495335737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20551826794232331987561965 7706935047837124495335737)
      ·
        refine ⟨5780201285877843371501803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7706935047837124495335737 5780201285877843371501803)
        ·
          refine ⟨8670301928816765057252705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5780201285877843371501803 8670301928816765057252705)
          ·
            refine ⟨6502726446612573792939529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8670301928816765057252705 6502726446612573792939529)
            ·
              refine ⟨4877044834959430344704647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6502726446612573792939529 4877044834959430344704647)
              ·
                refine ⟨7315567252439145517056971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4877044834959430344704647 7315567252439145517056971)
                ·
                  refine ⟨10973350878658718275585457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7315567252439145517056971 10973350878658718275585457)
                  ·
                    refine ⟨8230013158994038706689093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10973350878658718275585457 8230013158994038706689093)
                    ·
                      refine ⟨1543127467311382257504205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8230013158994038706689093 1543127467311382257504205)
                      ·
                        rfl

theorem cell23_3005230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_3005230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005230 prefixEnd_3005230 := by exact prefixLift 3005230
  have htrace : WordTrace (prefixWord ++ tailWord_3005230) baseStart_3005230 baseEnd_3005230 := by
    simpa [prefixWord, tailWord_3005230, baseEnd_3005230] using wordTrace_append hprefix tailTrace_3005230
  have hstable : (prefixWord ++ tailWord_3005230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005230).length < 2 ^ (prefixWord ++ tailWord_3005230).sum := by decide
  have hdescent : baseEnd_3005230 < baseStart_3005230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005233 : List Nat := [1, 2, 2, 3, 2, 1, 4, 1, 1, 3, 3]
def baseStart_3005233 : Nat := 118140960795 + 3005233 * 2 ^ 59
def prefixEnd_3005233 : Nat := 4983230072969 + 3 ^ 40 * 3005233 * 2
def baseEnd_3005233 : Nat := 1543129007753345745766691

theorem tailTrace_3005233 : CollatzResearch.WordTrace tailWord_3005233 prefixEnd_3005233 1543129007753345745766691 := by
  unfold tailWord_3005233
  simp only [CollatzResearch.WordTrace]
  refine ⟨109609852321561568779356353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73073234881041045852904235 109609852321561568779356353)
  ·
    refine ⟨82207389241171176584517265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109609852321561568779356353 82207389241171176584517265)
    ·
      refine ⟨61655541930878382438387949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82207389241171176584517265 61655541930878382438387949)
      ·
        refine ⟨23120828224079393414395481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61655541930878382438387949 23120828224079393414395481)
        ·
          refine ⟨17340621168059545060796611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23120828224079393414395481 17340621168059545060796611)
          ·
            refine ⟨26010931752089317591194917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17340621168059545060796611 26010931752089317591194917)
            ·
              refine ⟨4877049703516747048349047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26010931752089317591194917 4877049703516747048349047)
              ·
                refine ⟨7315574555275120572523571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4877049703516747048349047 7315574555275120572523571)
                ·
                  refine ⟨10973361832912680858785357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7315574555275120572523571 10973361832912680858785357)
                  ·
                    refine ⟨4115010687342255322044509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10973361832912680858785357 4115010687342255322044509)
                    ·
                      refine ⟨1543129007753345745766691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4115010687342255322044509 1543129007753345745766691)
                      ·
                        rfl

theorem cell23_3005233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_3005233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005233 prefixEnd_3005233 := by exact prefixLift 3005233
  have htrace : WordTrace (prefixWord ++ tailWord_3005233) baseStart_3005233 baseEnd_3005233 := by
    simpa [prefixWord, tailWord_3005233, baseEnd_3005233] using wordTrace_append hprefix tailTrace_3005233
  have hstable : (prefixWord ++ tailWord_3005233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005233).length < 2 ^ (prefixWord ++ tailWord_3005233).sum := by decide
  have hdescent : baseEnd_3005233 < baseStart_3005233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005254 : List Nat := [6, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3]
def baseStart_3005254 : Nat := 118140960795 + 3005254 * 2 ^ 59
def prefixEnd_3005254 : Nat := 4983230072969 + 3 ^ 40 * 3005254 * 2
def baseEnd_3005254 : Nat := 1543139790847090163604095

theorem tailTrace_3005254 : CollatzResearch.WordTrace tailWord_3005254 prefixEnd_3005254 1543139790847090163604095 := by
  unfold tailWord_3005254
  simp only [CollatzResearch.WordTrace]
  refine ⟨3425331820452671542683463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 73073745502990326243913877 3425331820452671542683463)
  ·
    refine ⟨5137997730679007314025195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3425331820452671542683463 5137997730679007314025195)
    ·
      refine ⟨7706996596018510971037793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5137997730679007314025195 7706996596018510971037793)
      ·
        refine ⟨5780247447013883228278345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7706996596018510971037793 5780247447013883228278345)
        ·
          refine ⟨4335185585260412421208759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5780247447013883228278345 4335185585260412421208759)
          ·
            refine ⟨6502778377890618631813139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4335185585260412421208759 6502778377890618631813139)
            ·
              refine ⟨9754167566835927947719709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6502778377890618631813139 9754167566835927947719709)
              ·
                refine ⟨3657812837563472980394891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9754167566835927947719709 3657812837563472980394891)
                ·
                  refine ⟨5486719256345209470592337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3657812837563472980394891 5486719256345209470592337)
                  ·
                    refine ⟨4115039442258907102944253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5486719256345209470592337 4115039442258907102944253)
                    ·
                      refine ⟨1543139790847090163604095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4115039442258907102944253 1543139790847090163604095)
                      ·
                        rfl

theorem cell23_3005254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_3005254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005254 prefixEnd_3005254 := by exact prefixLift 3005254
  have htrace : WordTrace (prefixWord ++ tailWord_3005254) baseStart_3005254 baseEnd_3005254 := by
    simpa [prefixWord, tailWord_3005254, baseEnd_3005254] using wordTrace_append hprefix tailTrace_3005254
  have hstable : (prefixWord ++ tailWord_3005254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005254).length < 2 ^ (prefixWord ++ tailWord_3005254).sum := by decide
  have hdescent : baseEnd_3005254 < baseStart_3005254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005266 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 4, 6]
def baseStart_3005266 : Nat := 118140960795 + 3005266 * 2 ^ 59
def prefixEnd_3005266 : Nat := 4983230072969 + 3 ^ 40 * 3005266 * 2
def baseEnd_3005266 : Nat := 514381984204981372218013

theorem tailTrace_3005266 : CollatzResearch.WordTrace tailWord_3005266 prefixEnd_3005266 514381984204981372218013 := by
  unfold tailWord_3005266
  simp only [CollatzResearch.WordTrace]
  refine ⟨27402763982610503853826913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73074037286961343610205101 27402763982610503853826913)
  ·
    refine ⟨20552072986957877890370185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27402763982610503853826913 20552072986957877890370185)
    ·
      refine ⟨15414054740218408417777639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20552072986957877890370185 15414054740218408417777639)
      ·
        refine ⟨23121082110327612626666459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15414054740218408417777639 23121082110327612626666459)
        ·
          refine ⟨34681623165491418939999689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23121082110327612626666459 34681623165491418939999689)
          ·
            refine ⟨26011217374118564204999767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34681623165491418939999689 26011217374118564204999767)
            ·
              refine ⟨39016826061177846307499651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26011217374118564204999767 39016826061177846307499651)
              ·
                refine ⟨58525239091766769461249477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39016826061177846307499651 58525239091766769461249477)
                ·
                  refine ⟨10973482329706269273984277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58525239091766769461249477 10973482329706269273984277)
                  ·
                    refine ⟨514381984204981372218013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10973482329706269273984277 514381984204981372218013)
                    ·
                      rfl

theorem cell23_3005266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_3005266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005266 prefixEnd_3005266 := by exact prefixLift 3005266
  have htrace : WordTrace (prefixWord ++ tailWord_3005266) baseStart_3005266 baseEnd_3005266 := by
    simpa [prefixWord, tailWord_3005266, baseEnd_3005266] using wordTrace_append hprefix tailTrace_3005266
  have hstable : (prefixWord ++ tailWord_3005266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005266).length < 2 ^ (prefixWord ++ tailWord_3005266).sum := by decide
  have hdescent : baseEnd_3005266 < baseStart_3005266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005294 : List Nat := [4, 1, 2, 3, 2, 1, 2, 2, 1, 3, 2]
def baseStart_3005294 : Nat := 118140960795 + 3005294 * 2 ^ 59
def prefixEnd_3005294 : Nat := 4983230072969 + 3 ^ 40 * 3005294 * 2
def baseEnd_3005294 : Nat := 1543160330073270007103911

theorem tailTrace_3005294 : CollatzResearch.WordTrace tailWord_3005294 prefixEnd_3005294 1543160330073270007103911 := by
  unfold tailWord_3005294
  simp only [CollatzResearch.WordTrace]
  refine ⟨13701509646792572024665867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73074718116227050798217957 13701509646792572024665867)
  ·
    refine ⟨20552264470188858036998801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13701509646792572024665867 20552264470188858036998801)
    ·
      refine ⟨15414198352641643527749101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20552264470188858036998801 15414198352641643527749101)
      ·
        refine ⟨5780324382240616322905913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15414198352641643527749101 5780324382240616322905913)
        ·
          refine ⟨4335243286680462242179435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5780324382240616322905913 4335243286680462242179435)
          ·
            refine ⟨6502864930020693363269153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4335243286680462242179435 6502864930020693363269153)
            ·
              refine ⟨4877148697515520022451865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6502864930020693363269153 4877148697515520022451865)
              ·
                refine ⟨3657861523136640016838899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4877148697515520022451865 3657861523136640016838899)
                ·
                  refine ⟨5486792284704960025258349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3657861523136640016838899 5486792284704960025258349)
                  ·
                    refine ⟨2057547106764360009471881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5486792284704960025258349 2057547106764360009471881)
                    ·
                      refine ⟨1543160330073270007103911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2057547106764360009471881 1543160330073270007103911)
                      ·
                        rfl

theorem cell23_3005294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_3005294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005294 prefixEnd_3005294 := by exact prefixLift 3005294
  have htrace : WordTrace (prefixWord ++ tailWord_3005294) baseStart_3005294 baseEnd_3005294 := by
    simpa [prefixWord, tailWord_3005294, baseEnd_3005294] using wordTrace_append hprefix tailTrace_3005294
  have hstable : (prefixWord ++ tailWord_3005294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005294).length < 2 ^ (prefixWord ++ tailWord_3005294).sum := by decide
  have hdescent : baseEnd_3005294 < baseStart_3005294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005296 : List Nat := [2, 1, 1, 1, 4, 1, 4, 2, 7]
def baseStart_3005296 : Nat := 118140960795 + 3005296 * 2 ^ 59
def prefixEnd_3005296 : Nat := 4983230072969 + 3 ^ 40 * 3005296 * 2
def baseEnd_3005296 : Nat := 171462373003842111030989

theorem tailTrace_3005296 : CollatzResearch.WordTrace tailWord_3005296 prefixEnd_3005296 171462373003842111030989 := by
  unfold tailWord_3005296
  simp only [CollatzResearch.WordTrace]
  refine ⟨54806075060166665269449871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73074766746888887025933161 54806075060166665269449871)
  ·
    refine ⟨82209112590249997904174807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54806075060166665269449871 82209112590249997904174807)
    ·
      refine ⟨123313668885374996856262211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82209112590249997904174807 123313668885374996856262211)
      ·
        refine ⟨184970503328062495284393317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123313668885374996856262211 184970503328062495284393317)
        ·
          refine ⟨34681969374011717865823747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184970503328062495284393317 34681969374011717865823747)
          ·
            refine ⟨52022954061017576798735621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34681969374011717865823747 52022954061017576798735621)
            ·
              refine ⟨9754303886440795649762929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52022954061017576798735621 9754303886440795649762929)
              ·
                refine ⟨7315727914830596737322197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9754303886440795649762929 7315727914830596737322197)
                ·
                  refine ⟨171462373003842111030989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7315727914830596737322197 171462373003842111030989)
                  ·
                    rfl

theorem cell23_3005296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 7].length) (baseStart_3005296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005296 prefixEnd_3005296 := by exact prefixLift 3005296
  have htrace : WordTrace (prefixWord ++ tailWord_3005296) baseStart_3005296 baseEnd_3005296 := by
    simpa [prefixWord, tailWord_3005296, baseEnd_3005296] using wordTrace_append hprefix tailTrace_3005296
  have hstable : (prefixWord ++ tailWord_3005296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005296).length < 2 ^ (prefixWord ++ tailWord_3005296).sum := by decide
  have hdescent : baseEnd_3005296 < baseStart_3005296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005363 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 3, 6, 2]
def baseStart_3005363 : Nat := 118140960795 + 3005363 * 2 ^ 59
def prefixEnd_3005363 : Nat := 4983230072969 + 3 ^ 40 * 3005363 * 2
def baseEnd_3005363 : Nat := 1543195760238430237141093

theorem tailTrace_3005363 : CollatzResearch.WordTrace tailWord_3005363 prefixEnd_3005363 1543195760238430237141093 := by
  unfold tailWord_3005363
  simp only [CollatzResearch.WordTrace]
  refine ⟨109614593811090600981588743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73076395874060400654392495 109614593811090600981588743)
  ·
    refine ⟨164421890716635901472383115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109614593811090600981588743 164421890716635901472383115)
    ·
      refine ⟨246632836074953852208574673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164421890716635901472383115 246632836074953852208574673)
      ·
        refine ⟨184974627056215389156431005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246632836074953852208574673 184974627056215389156431005)
        ·
          refine ⟨69365485146080770933661627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184974627056215389156431005 69365485146080770933661627)
          ·
            refine ⟨104048227719121156400492441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69365485146080770933661627 104048227719121156400492441)
            ·
              refine ⟨78036170789340867300369331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104048227719121156400492441 78036170789340867300369331)
              ·
                refine ⟨117054256184011300950553997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78036170789340867300369331 117054256184011300950553997)
                ·
                  refine ⟨43895346069004237856457749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117054256184011300950553997 43895346069004237856457749)
                  ·
                    refine ⟨2057594346984573649521457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 43895346069004237856457749 2057594346984573649521457)
                    ·
                      refine ⟨1543195760238430237141093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2057594346984573649521457 1543195760238430237141093)
                      ·
                        rfl

theorem cell23_3005363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 6, 2].length) (baseStart_3005363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005363 prefixEnd_3005363 := by exact prefixLift 3005363
  have htrace : WordTrace (prefixWord ++ tailWord_3005363) baseStart_3005363 baseEnd_3005363 := by
    simpa [prefixWord, tailWord_3005363, baseEnd_3005363] using wordTrace_append hprefix tailTrace_3005363
  have hstable : (prefixWord ++ tailWord_3005363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005363).length < 2 ^ (prefixWord ++ tailWord_3005363).sum := by decide
  have hdescent : baseEnd_3005363 < baseStart_3005363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005397 : List Nat := [1, 3, 2, 3, 3, 1, 1, 1, 2, 4, 2]
def baseStart_3005397 : Nat := 118140960795 + 3005397 * 2 ^ 59
def prefixEnd_3005397 : Nat := 4983230072969 + 3 ^ 40 * 3005397 * 2
def baseEnd_3005397 : Nat := 1543213218580683104115937

theorem tailTrace_3005397 : CollatzResearch.WordTrace tailWord_3005397 prefixEnd_3005397 1543213218580683104115937 := by
  unfold tailWord_3005397
  simp only [CollatzResearch.WordTrace]
  refine ⟨109615833892967424788326445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73077222595311616525550963 109615833892967424788326445)
  ·
    refine ⟨41105937709862784295622417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109615833892967424788326445 41105937709862784295622417)
    ·
      refine ⟨30829453282397088221716813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41105937709862784295622417 30829453282397088221716813)
      ·
        refine ⟨11561044980898908083143805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30829453282397088221716813 11561044980898908083143805)
        ·
          refine ⟨4335391867837090531178927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11561044980898908083143805 4335391867837090531178927)
          ·
            refine ⟨6503087801755635796768391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4335391867837090531178927 6503087801755635796768391)
            ·
              refine ⟨9754631702633453695152587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6503087801755635796768391 9754631702633453695152587)
              ·
                refine ⟨14631947553950180542728881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9754631702633453695152587 14631947553950180542728881)
                ·
                  refine ⟨10973960665462635407046661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14631947553950180542728881 10973960665462635407046661)
                  ·
                    refine ⟨2057617624774244138821249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10973960665462635407046661 2057617624774244138821249)
                    ·
                      refine ⟨1543213218580683104115937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2057617624774244138821249 1543213218580683104115937)
                      ·
                        rfl

theorem cell23_3005397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_3005397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005397 prefixEnd_3005397 := by exact prefixLift 3005397
  have htrace : WordTrace (prefixWord ++ tailWord_3005397) baseStart_3005397 baseEnd_3005397 := by
    simpa [prefixWord, tailWord_3005397, baseEnd_3005397] using wordTrace_append hprefix tailTrace_3005397
  have hstable : (prefixWord ++ tailWord_3005397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005397).length < 2 ^ (prefixWord ++ tailWord_3005397).sum := by decide
  have hdescent : baseEnd_3005397 < baseStart_3005397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005447 : List Nat := [1, 1, 4, 3, 1, 1, 4, 1, 3, 1, 3]
def baseStart_3005447 : Nat := 118140960795 + 3005447 * 2 ^ 59
def prefixEnd_3005447 : Nat := 4983230072969 + 3 ^ 40 * 3005447 * 2
def baseEnd_3005447 : Nat := 1543238892613407908490707

theorem tailTrace_3005447 : CollatzResearch.WordTrace tailWord_3005447 prefixEnd_3005447 1543238892613407908490707 := by
  unfold tailWord_3005447
  simp only [CollatzResearch.WordTrace]
  refine ⟨109617657542786283327646595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73078438361857522218431063 109617657542786283327646595)
  ·
    refine ⟨164426486314179424991469893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109617657542786283327646595 164426486314179424991469893)
    ·
      refine ⟨30829966183908642185900605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164426486314179424991469893 30829966183908642185900605)
      ·
        refine ⟨11561237318965740819712727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30829966183908642185900605 11561237318965740819712727)
        ·
          refine ⟨17341855978448611229569091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11561237318965740819712727 17341855978448611229569091)
          ·
            refine ⟨26012783967672916844353637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17341855978448611229569091 26012783967672916844353637)
            ·
              refine ⟨4877396993938671908316307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26012783967672916844353637 4877396993938671908316307)
              ·
                refine ⟨7316095490908007862474461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4877396993938671908316307 7316095490908007862474461)
                ·
                  refine ⟨2743535809090502948427923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7316095490908007862474461 2743535809090502948427923)
                  ·
                    refine ⟨4115303713635754422641885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2743535809090502948427923 4115303713635754422641885)
                    ·
                      refine ⟨1543238892613407908490707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4115303713635754422641885 1543238892613407908490707)
                      ·
                        rfl

theorem cell23_3005447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_3005447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005447 prefixEnd_3005447 := by exact prefixLift 3005447
  have htrace : WordTrace (prefixWord ++ tailWord_3005447) baseStart_3005447 baseEnd_3005447 := by
    simpa [prefixWord, tailWord_3005447, baseEnd_3005447] using wordTrace_append hprefix tailTrace_3005447
  have hstable : (prefixWord ++ tailWord_3005447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005447).length < 2 ^ (prefixWord ++ tailWord_3005447).sum := by decide
  have hdescent : baseEnd_3005447 < baseStart_3005447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005483 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 4]
def baseStart_3005483 : Nat := 118140960795 + 3005483 * 2 ^ 59
def prefixEnd_3005483 : Nat := 4983230072969 + 3 ^ 40 * 3005483 * 2
def baseEnd_3005483 : Nat := 1543257377916969767640541

theorem tailTrace_3005483 : CollatzResearch.WordTrace tailWord_3005483 prefixEnd_3005483 1543257377916969767640541 := by
  unfold tailWord_3005483
  simp only [CollatzResearch.WordTrace]
  refine ⟨109618970570655861475957103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73079313713770574317304735 109618970570655861475957103)
  ·
    refine ⟨164428455855983792213935655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109618970570655861475957103 164428455855983792213935655)
    ·
      refine ⟨246642683783975688320903483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164428455855983792213935655 246642683783975688320903483)
      ·
        refine ⟨369964025675963532481355225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246642683783975688320903483 369964025675963532481355225)
        ·
          refine ⟨277473019256972649361016419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369964025675963532481355225 277473019256972649361016419)
          ·
            refine ⟨416209528885458974041524629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277473019256972649361016419 416209528885458974041524629)
            ·
              refine ⟨19509821666505889408196467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 416209528885458974041524629 19509821666505889408196467)
              ·
                refine ⟨29264732499758834112294701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19509821666505889408196467 29264732499758834112294701)
                ·
                  refine ⟨10974274687409562792110513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29264732499758834112294701 10974274687409562792110513)
                  ·
                    refine ⟨8230706015557172094082885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10974274687409562792110513 8230706015557172094082885)
                    ·
                      refine ⟨1543257377916969767640541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8230706015557172094082885 1543257377916969767640541)
                      ·
                        rfl

theorem cell23_3005483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 4].length) (baseStart_3005483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005483 prefixEnd_3005483 := by exact prefixLift 3005483
  have htrace : WordTrace (prefixWord ++ tailWord_3005483) baseStart_3005483 baseEnd_3005483 := by
    simpa [prefixWord, tailWord_3005483, baseEnd_3005483] using wordTrace_append hprefix tailTrace_3005483
  have hstable : (prefixWord ++ tailWord_3005483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005483).length < 2 ^ (prefixWord ++ tailWord_3005483).sum := by decide
  have hdescent : baseEnd_3005483 < baseStart_3005483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005490 : List Nat := [3, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5]
def baseStart_3005490 : Nat := 118140960795 + 3005490 * 2 ^ 59
def prefixEnd_3005490 : Nat := 4983230072969 + 3 ^ 40 * 3005490 * 2
def baseEnd_3005490 : Nat := 1543260972281551240253009

theorem tailTrace_3005490 : CollatzResearch.WordTrace tailWord_3005490 prefixEnd_3005490 1543260972281551240253009 := by
  unfold tailWord_3005490
  simp only [CollatzResearch.WordTrace]
  refine ⟨27404806470407625417865481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73079483921087001114307949 27404806470407625417865481)
  ·
    refine ⟨20553604852805719063399111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27404806470407625417865481 20553604852805719063399111)
    ·
      refine ⟨30830407279208578595098667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20553604852805719063399111 30830407279208578595098667)
      ·
        refine ⟨46245610918812867892648001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30830407279208578595098667 46245610918812867892648001)
        ·
          refine ⟨34684208189109650919486001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46245610918812867892648001 34684208189109650919486001)
          ·
            refine ⟨26013156141832238189614501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34684208189109650919486001 26013156141832238189614501)
            ·
              refine ⟨4877466776593544660552719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26013156141832238189614501 4877466776593544660552719)
              ·
                refine ⟨7316200164890316990829079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4877466776593544660552719 7316200164890316990829079)
                ·
                  refine ⟨10974300247335475486243619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7316200164890316990829079 10974300247335475486243619)
                  ·
                    refine ⟨16461450371003213229365429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10974300247335475486243619 16461450371003213229365429)
                    ·
                      refine ⟨1543260972281551240253009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16461450371003213229365429 1543260972281551240253009)
                      ·
                        rfl

theorem cell23_3005490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_3005490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005490 prefixEnd_3005490 := by exact prefixLift 3005490
  have htrace : WordTrace (prefixWord ++ tailWord_3005490) baseStart_3005490 baseEnd_3005490 := by
    simpa [prefixWord, tailWord_3005490, baseEnd_3005490] using wordTrace_append hprefix tailTrace_3005490
  have hstable : (prefixWord ++ tailWord_3005490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005490).length < 2 ^ (prefixWord ++ tailWord_3005490).sum := by decide
  have hdescent : baseEnd_3005490 < baseStart_3005490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005534 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_3005534 : Nat := 118140960795 + 3005534 * 2 ^ 59
def prefixEnd_3005534 : Nat := 4983230072969 + 3 ^ 40 * 3005534 * 2
def baseEnd_3005534 : Nat := 1543283565430349068102807

theorem tailTrace_3005534 : CollatzResearch.WordTrace tailWord_3005534 prefixEnd_3005534 1543283565430349068102807 := by
  unfold tailWord_3005534
  simp only [CollatzResearch.WordTrace]
  refine ⟨13702603836683887148257957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73080553795647398124042437 13702603836683887148257957)
  ·
    refine ⟨2569238219378228840298367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13702603836683887148257957 2569238219378228840298367)
    ·
      refine ⟨3853857329067343260447551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2569238219378228840298367 3853857329067343260447551)
      ·
        refine ⟨5780785993601014890671327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3853857329067343260447551 5780785993601014890671327)
        ·
          refine ⟨8671178990401522336006991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5780785993601014890671327 8671178990401522336006991)
          ·
            refine ⟨13006768485602283504010487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8671178990401522336006991 13006768485602283504010487)
            ·
              refine ⟨19510152728403425256015731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13006768485602283504010487 19510152728403425256015731)
              ·
                refine ⟨29265229092605137884023597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19510152728403425256015731 29265229092605137884023597)
                ·
                  refine ⟨10974460909726926706508849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29265229092605137884023597 10974460909726926706508849)
                  ·
                    refine ⟨8230845682295195029881637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10974460909726926706508849 8230845682295195029881637)
                    ·
                      refine ⟨1543283565430349068102807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8230845682295195029881637 1543283565430349068102807)
                      ·
                        rfl

theorem cell23_3005534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_3005534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005534 prefixEnd_3005534 := by exact prefixLift 3005534
  have htrace : WordTrace (prefixWord ++ tailWord_3005534) baseStart_3005534 baseEnd_3005534 := by
    simpa [prefixWord, tailWord_3005534, baseEnd_3005534] using wordTrace_append hprefix tailTrace_3005534
  have hstable : (prefixWord ++ tailWord_3005534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005534).length < 2 ^ (prefixWord ++ tailWord_3005534).sum := by decide
  have hdescent : baseEnd_3005534 < baseStart_3005534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005554 : List Nat := [3, 2, 1, 2, 2, 1, 4, 2, 2, 1, 3]
def baseStart_3005554 : Nat := 118140960795 + 3005554 * 2 ^ 59
def prefixEnd_3005554 : Nat := 4983230072969 + 3 ^ 40 * 3005554 * 2
def baseEnd_3005554 : Nat := 1543293835043438989852715

theorem tailTrace_3005554 : CollatzResearch.WordTrace tailWord_3005554 prefixEnd_3005554 1543293835043438989852715 := by
  unfold tailWord_3005554
  simp only [CollatzResearch.WordTrace]
  refine ⟨27405390038349660150447929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73081040102265760401194477 27405390038349660150447929)
  ·
    refine ⟨20554042528762245112835947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27405390038349660150447929 20554042528762245112835947)
    ·
      refine ⟨30831063793143367669253921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20554042528762245112835947 30831063793143367669253921)
      ·
        refine ⟨23123297844857525751940441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30831063793143367669253921 23123297844857525751940441)
        ·
          refine ⟨17342473383643144313955331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23123297844857525751940441 17342473383643144313955331)
          ·
            refine ⟨26013710075464716470932997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17342473383643144313955331 26013710075464716470932997)
            ·
              refine ⟨4877570639149634338299937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26013710075464716470932997 4877570639149634338299937)
              ·
                refine ⟨3658177979362225753724953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4877570639149634338299937 3658177979362225753724953)
                ·
                  refine ⟨2743633484521669315293715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3658177979362225753724953 2743633484521669315293715)
                  ·
                    refine ⟨4115450226782503972940573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2743633484521669315293715 4115450226782503972940573)
                    ·
                      refine ⟨1543293835043438989852715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4115450226782503972940573 1543293835043438989852715)
                      ·
                        rfl

theorem cell23_3005554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_3005554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005554 prefixEnd_3005554 := by exact prefixLift 3005554
  have htrace : WordTrace (prefixWord ++ tailWord_3005554) baseStart_3005554 baseEnd_3005554 := by
    simpa [prefixWord, tailWord_3005554, baseEnd_3005554] using wordTrace_append hprefix tailTrace_3005554
  have hstable : (prefixWord ++ tailWord_3005554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005554).length < 2 ^ (prefixWord ++ tailWord_3005554).sum := by decide
  have hdescent : baseEnd_3005554 < baseStart_3005554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005563 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 5]
def baseStart_3005563 : Nat := 118140960795 + 3005563 * 2 ^ 59
def prefixEnd_3005563 : Nat := 4983230072969 + 3 ^ 40 * 3005563 * 2
def baseEnd_3005563 : Nat := 1543298456369329454640173

theorem tailTrace_3005563 : CollatzResearch.WordTrace tailWord_3005563 prefixEnd_3005563 1543298456369329454640173 := by
  unfold tailWord_3005563
  simp only [CollatzResearch.WordTrace]
  refine ⟨109621888410366035138869343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73081258940244023425912895 109621888410366035138869343)
  ·
    refine ⟨164432832615549052708304015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109621888410366035138869343 164432832615549052708304015)
    ·
      refine ⟨246649248923323579062456023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164432832615549052708304015 246649248923323579062456023)
      ·
        refine ⟨369973873384985368593684035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246649248923323579062456023 369973873384985368593684035)
        ·
          refine ⟨554960810077478052890526053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369973873384985368593684035 554960810077478052890526053)
          ·
            refine ⟨104055151889527134916973635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 554960810077478052890526053 104055151889527134916973635)
            ·
              refine ⟨156082727834290702375460453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104055151889527134916973635 156082727834290702375460453)
              ·
                refine ⟨29265511468929506695398835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 156082727834290702375460453 29265511468929506695398835)
                ·
                  refine ⟨43898267203394260043098253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29265511468929506695398835 43898267203394260043098253)
                  ·
                    refine ⟨16461850201272847516161845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43898267203394260043098253 16461850201272847516161845)
                    ·
                      refine ⟨1543298456369329454640173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16461850201272847516161845 1543298456369329454640173)
                      ·
                        rfl

theorem cell23_3005563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 5].length) (baseStart_3005563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005563 prefixEnd_3005563 := by exact prefixLift 3005563
  have htrace : WordTrace (prefixWord ++ tailWord_3005563) baseStart_3005563 baseEnd_3005563 := by
    simpa [prefixWord, tailWord_3005563, baseEnd_3005563] using wordTrace_append hprefix tailTrace_3005563
  have hstable : (prefixWord ++ tailWord_3005563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005563).length < 2 ^ (prefixWord ++ tailWord_3005563).sum := by decide
  have hdescent : baseEnd_3005563 < baseStart_3005563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005577 : List Nat := [1, 2, 1, 1, 4, 3, 1, 3, 1, 4, 2]
def baseStart_3005577 : Nat := 118140960795 + 3005577 * 2 ^ 59
def prefixEnd_3005577 : Nat := 4983230072969 + 3 ^ 40 * 3005577 * 2
def baseEnd_3005577 : Nat := 1543305645098492399865109

theorem tailTrace_3005577 : CollatzResearch.WordTrace tailWord_3005577 prefixEnd_3005577 1543305645098492399865109 := by
  unfold tailWord_3005577
  simp only [CollatzResearch.WordTrace]
  refine ⟨109622399032315315529878985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73081599354876877019919323 109622399032315315529878985)
  ·
    refine ⟨82216799274236486647409239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109622399032315315529878985 82216799274236486647409239)
    ·
      refine ⟨123325198911354729971113859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82216799274236486647409239 123325198911354729971113859)
      ·
        refine ⟨184987798367032094956670789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123325198911354729971113859 184987798367032094956670789)
        ·
          refine ⟨34685212193818517804375773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184987798367032094956670789 34685212193818517804375773)
          ·
            refine ⟨13006954572681944176640915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34685212193818517804375773 13006954572681944176640915)
            ·
              refine ⟨19510431859022916264961373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13006954572681944176640915 19510431859022916264961373)
              ·
                refine ⟨7316411947133593599360515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19510431859022916264961373 7316411947133593599360515)
                ·
                  refine ⟨10974617920700390399040773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7316411947133593599360515 10974617920700390399040773)
                  ·
                    refine ⟨2057740860131323199820145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10974617920700390399040773 2057740860131323199820145)
                    ·
                      refine ⟨1543305645098492399865109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2057740860131323199820145 1543305645098492399865109)
                      ·
                        rfl

theorem cell23_3005577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 4, 2].length) (baseStart_3005577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005577 prefixEnd_3005577 := by exact prefixLift 3005577
  have htrace : WordTrace (prefixWord ++ tailWord_3005577) baseStart_3005577 baseEnd_3005577 := by
    simpa [prefixWord, tailWord_3005577, baseEnd_3005577] using wordTrace_append hprefix tailTrace_3005577
  have hstable : (prefixWord ++ tailWord_3005577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005577).length < 2 ^ (prefixWord ++ tailWord_3005577).sum := by decide
  have hdescent : baseEnd_3005577 < baseStart_3005577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005593 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 7]
def baseStart_3005593 : Nat := 118140960795 + 3005593 * 2 ^ 59
def prefixEnd_3005593 : Nat := 4983230072969 + 3 ^ 40 * 3005593 * 2
def baseEnd_3005593 : Nat := 1543313860788964337265035

theorem tailTrace_3005593 : CollatzResearch.WordTrace tailWord_3005593 prefixEnd_3005593 1543313860788964337265035 := by
  unfold tailWord_3005593
  simp only [CollatzResearch.WordTrace]
  refine ⟨109622982600257350262461433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73081988400171566841640955 109622982600257350262461433)
  ·
    refine ⟨82217236950193012696846075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109622982600257350262461433 82217236950193012696846075)
    ·
      refine ⟨123325855425289519045269113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82217236950193012696846075 123325855425289519045269113)
      ·
        refine ⟨92494391568967139283951835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123325855425289519045269113 92494391568967139283951835)
        ·
          refine ⟨138741587353450708925927753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92494391568967139283951835 138741587353450708925927753)
          ·
            refine ⟨104056190515088031694445815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138741587353450708925927753 104056190515088031694445815)
            ·
              refine ⟨156084285772632047541668723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104056190515088031694445815 156084285772632047541668723)
              ·
                refine ⟨234126428658948071312503085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156084285772632047541668723 234126428658948071312503085)
                ·
                  refine ⟨87797410747105526742188657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234126428658948071312503085 87797410747105526742188657)
                  ·
                    refine ⟨65848058060329145056641493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87797410747105526742188657 65848058060329145056641493)
                    ·
                      refine ⟨1543313860788964337265035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 65848058060329145056641493 1543313860788964337265035)
                      ·
                        rfl

theorem cell23_3005593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_3005593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005593 prefixEnd_3005593 := by exact prefixLift 3005593
  have htrace : WordTrace (prefixWord ++ tailWord_3005593) baseStart_3005593 baseEnd_3005593 := by
    simpa [prefixWord, tailWord_3005593, baseEnd_3005593] using wordTrace_append hprefix tailTrace_3005593
  have hstable : (prefixWord ++ tailWord_3005593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005593).length < 2 ^ (prefixWord ++ tailWord_3005593).sum := by decide
  have hdescent : baseEnd_3005593 < baseStart_3005593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005594 : List Nat := [3, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2]
def baseStart_3005594 : Nat := 118140960795 + 3005594 * 2 ^ 59
def prefixEnd_3005594 : Nat := 4983230072969 + 3 ^ 40 * 3005594 * 2
def baseEnd_3005594 : Nat := 1543314374269618833352531

theorem tailTrace_3005594 : CollatzResearch.WordTrace tailWord_3005594 prefixEnd_3005594 1543314374269618833352531 := by
  unfold tailWord_3005594
  simp only [CollatzResearch.WordTrace]
  refine ⟨27405754768313431858311959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73082012715502484955498557 27405754768313431858311959)
  ·
    refine ⟨41108632152470147787467939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27405754768313431858311959 41108632152470147787467939)
    ·
      refine ⟨61662948228705221681201909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41108632152470147787467939 61662948228705221681201909)
      ·
        refine ⟨5780901396441114532612679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61662948228705221681201909 5780901396441114532612679)
        ·
          refine ⟨8671352094661671798919019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5780901396441114532612679 8671352094661671798919019)
          ·
            refine ⟨13007028141992507698378529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8671352094661671798919019 13007028141992507698378529)
            ·
              refine ⟨9755271106494380773783897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13007028141992507698378529 9755271106494380773783897)
              ·
                refine ⟨7316453329870785580337923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9755271106494380773783897 7316453329870785580337923)
                ·
                  refine ⟨10974679994806178370506885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7316453329870785580337923 10974679994806178370506885)
                  ·
                    refine ⟨2057752499026158444470041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10974679994806178370506885 2057752499026158444470041)
                    ·
                      refine ⟨1543314374269618833352531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2057752499026158444470041 1543314374269618833352531)
                      ·
                        rfl

theorem cell23_3005594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_3005594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005594 prefixEnd_3005594 := by exact prefixLift 3005594
  have htrace : WordTrace (prefixWord ++ tailWord_3005594) baseStart_3005594 baseEnd_3005594 := by
    simpa [prefixWord, tailWord_3005594, baseEnd_3005594] using wordTrace_append hprefix tailTrace_3005594
  have hstable : (prefixWord ++ tailWord_3005594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005594).length < 2 ^ (prefixWord ++ tailWord_3005594).sum := by decide
  have hdescent : baseEnd_3005594 < baseStart_3005594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005598 : List Nat := [4, 3, 1, 1, 2, 1, 4, 1, 1, 3, 2]
def baseStart_3005598 : Nat := 118140960795 + 3005598 * 2 ^ 59
def prefixEnd_3005598 : Nat := 4983230072969 + 3 ^ 40 * 3005598 * 2
def baseEnd_3005598 : Nat := 1543316428192236817702513

theorem tailTrace_3005598 : CollatzResearch.WordTrace tailWord_3005598 prefixEnd_3005598 1543316428192236817702513 := by
  unfold tailWord_3005598
  simp only [CollatzResearch.WordTrace]
  refine ⟨13702895620654904514549181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73082109976826157410928965 13702895620654904514549181)
  ·
    refine ⟨5138585857745589192955943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13702895620654904514549181 5138585857745589192955943)
    ·
      refine ⟨7707878786618383789433915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5138585857745589192955943 7707878786618383789433915)
      ·
        refine ⟨11561818179927575684150873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7707878786618383789433915 11561818179927575684150873)
        ·
          refine ⟨8671363634945681763113155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11561818179927575684150873 8671363634945681763113155)
          ·
            refine ⟨13007045452418522644669733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8671363634945681763113155 13007045452418522644669733)
            ·
              refine ⟨2438821022328472995875575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13007045452418522644669733 2438821022328472995875575)
              ·
                refine ⟨3658231533492709493813363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2438821022328472995875575 3658231533492709493813363)
                ·
                  refine ⟨5487347300239064240720045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3658231533492709493813363 5487347300239064240720045)
                  ·
                    refine ⟨2057755237589649090270017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5487347300239064240720045 2057755237589649090270017)
                    ·
                      refine ⟨1543316428192236817702513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2057755237589649090270017 1543316428192236817702513)
                      ·
                        rfl

theorem cell23_3005598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_3005598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005598 prefixEnd_3005598 := by exact prefixLift 3005598
  have htrace : WordTrace (prefixWord ++ tailWord_3005598) baseStart_3005598 baseEnd_3005598 := by
    simpa [prefixWord, tailWord_3005598, baseEnd_3005598] using wordTrace_append hprefix tailTrace_3005598
  have hstable : (prefixWord ++ tailWord_3005598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005598).length < 2 ^ (prefixWord ++ tailWord_3005598).sum := by decide
  have hdescent : baseEnd_3005598 < baseStart_3005598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005607 : List Nat := [1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_3005607 : Nat := 118140960795 + 3005607 * 2 ^ 59
def prefixEnd_3005607 : Nat := 4983230072969 + 3 ^ 40 * 3005607 * 2
def baseEnd_3005607 : Nat := 1543321049518127282489971

theorem tailTrace_3005607 : CollatzResearch.WordTrace tailWord_3005607 prefixEnd_3005607 1543321049518127282489971 := by
  unfold tailWord_3005607
  simp only [CollatzResearch.WordTrace]
  refine ⟨109623493222206630653471075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73082328814804420435647383 109623493222206630653471075)
  ·
    refine ⟨164435239833309945980206613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109623493222206630653471075 164435239833309945980206613)
    ·
      refine ⟨7707901867186403717822185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 164435239833309945980206613 7707901867186403717822185)
      ·
        refine ⟨5780926400389802788366639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7707901867186403717822185 5780926400389802788366639)
        ·
          refine ⟨8671389600584704182549959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5780926400389802788366639 8671389600584704182549959)
          ·
            refine ⟨13007084400877056273824939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8671389600584704182549959 13007084400877056273824939)
            ·
              refine ⟨19510626601315584410737409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13007084400877056273824939 19510626601315584410737409)
              ·
                refine ⟨14632969950986688308053057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19510626601315584410737409 14632969950986688308053057)
                ·
                  refine ⟨10974727463240016231039793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14632969950986688308053057 10974727463240016231039793)
                  ·
                    refine ⟨8231045597430012173279845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10974727463240016231039793 8231045597430012173279845)
                    ·
                      refine ⟨1543321049518127282489971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8231045597430012173279845 1543321049518127282489971)
                      ·
                        rfl

theorem cell23_3005607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_3005607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005607 prefixEnd_3005607 := by exact prefixLift 3005607
  have htrace : WordTrace (prefixWord ++ tailWord_3005607) baseStart_3005607 baseEnd_3005607 := by
    simpa [prefixWord, tailWord_3005607, baseEnd_3005607] using wordTrace_append hprefix tailTrace_3005607
  have hstable : (prefixWord ++ tailWord_3005607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005607).length < 2 ^ (prefixWord ++ tailWord_3005607).sum := by decide
  have hdescent : baseEnd_3005607 < baseStart_3005607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005617 : List Nat := [1, 2, 2, 5, 1, 2, 2, 1, 7]
def baseStart_3005617 : Nat := 118140960795 + 3005617 * 2 ^ 59
def prefixEnd_3005617 : Nat := 4983230072969 + 3 ^ 40 * 3005617 * 2
def baseEnd_3005617 : Nat := 171480687147185804818325

theorem tailTrace_3005617 : CollatzResearch.WordTrace tailWord_3005617 prefixEnd_3005617 171480687147185804818325 := by
  unfold tailWord_3005617
  simp only [CollatzResearch.WordTrace]
  refine ⟨109623857952170402361335105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73082571968113601574223403 109623857952170402361335105)
  ·
    refine ⟨82217893464127801771001329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109623857952170402361335105 82217893464127801771001329)
    ·
      refine ⟨61663420098095851328250997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82217893464127801771001329 61663420098095851328250997)
      ·
        refine ⟨5780945634196486062023531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61663420098095851328250997 5780945634196486062023531)
        ·
          refine ⟨8671418451294729093035297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5780945634196486062023531 8671418451294729093035297)
          ·
            refine ⟨6503563838471046819776473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8671418451294729093035297 6503563838471046819776473)
            ·
              refine ⟨4877672878853285114832355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6503563838471046819776473 4877672878853285114832355)
              ·
                refine ⟨7316509318279927672248533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4877672878853285114832355 7316509318279927672248533)
                ·
                  refine ⟨171480687147185804818325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7316509318279927672248533 171480687147185804818325)
                  ·
                    rfl

theorem cell23_3005617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 7].length) (baseStart_3005617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005617 prefixEnd_3005617 := by exact prefixLift 3005617
  have htrace : WordTrace (prefixWord ++ tailWord_3005617) baseStart_3005617 baseEnd_3005617 := by
    simpa [prefixWord, tailWord_3005617, baseEnd_3005617] using wordTrace_append hprefix tailTrace_3005617
  have hstable : (prefixWord ++ tailWord_3005617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005617).length < 2 ^ (prefixWord ++ tailWord_3005617).sum := by decide
  have hdescent : baseEnd_3005617 < baseStart_3005617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005628 : List Nat := [2, 2, 2, 3, 2, 2, 3, 1, 2, 2, 2]
def baseStart_3005628 : Nat := 118140960795 + 3005628 * 2 ^ 59
def prefixEnd_3005628 : Nat := 4983230072969 + 3 ^ 40 * 3005628 * 2
def baseEnd_3005628 : Nat := 1543331832611871700327375

theorem tailTrace_3005628 : CollatzResearch.WordTrace tailWord_3005628 prefixEnd_3005628 1543331832611871700327375 := by
  unfold tailWord_3005628
  simp only [CollatzResearch.WordTrace]
  refine ⟨54812129577565275619992769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73082839436753700826657025 54812129577565275619992769)
  ·
    refine ⟨41109097183173956714994577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54812129577565275619992769 41109097183173956714994577)
    ·
      refine ⟨30831822887380467536245933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41109097183173956714994577 30831822887380467536245933)
      ·
        refine ⟨11561933582767675326092225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30831822887380467536245933 11561933582767675326092225)
        ·
          refine ⟨8671450187075756494569169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11561933582767675326092225 8671450187075756494569169)
          ·
            refine ⟨6503587640306817370926877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8671450187075756494569169 6503587640306817370926877)
            ·
              refine ⟨2438845365115056514097579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6503587640306817370926877 2438845365115056514097579)
              ·
                refine ⟨3658268047672584771146369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2438845365115056514097579 3658268047672584771146369)
                ·
                  refine ⟨2743701035754438578359777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3658268047672584771146369 2743701035754438578359777)
                  ·
                    refine ⟨2057775776815828933769833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2743701035754438578359777 2057775776815828933769833)
                    ·
                      refine ⟨1543331832611871700327375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2057775776815828933769833 1543331832611871700327375)
                      ·
                        rfl

theorem cell23_3005628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_3005628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005628 prefixEnd_3005628 := by exact prefixLift 3005628
  have htrace : WordTrace (prefixWord ++ tailWord_3005628) baseStart_3005628 baseEnd_3005628 := by
    simpa [prefixWord, tailWord_3005628, baseEnd_3005628] using wordTrace_append hprefix tailTrace_3005628
  have hstable : (prefixWord ++ tailWord_3005628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005628).length < 2 ^ (prefixWord ++ tailWord_3005628).sum := by decide
  have hdescent : baseEnd_3005628 < baseStart_3005628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005761 : List Nat := [1, 2, 5, 2, 1, 2, 1, 1, 1, 5, 2]
def baseStart_3005761 : Nat := 118140960795 + 3005761 * 2 ^ 59
def prefixEnd_3005761 : Nat := 4983230072969 + 3 ^ 40 * 3005761 * 2
def baseEnd_3005761 : Nat := 1543400125538919679964263

theorem tailTrace_3005761 : CollatzResearch.WordTrace tailWord_3005761 prefixEnd_3005761 1543400125538919679964263 := by
  unfold tailWord_3005761
  simp only [CollatzResearch.WordTrace]
  refine ⟨109629110063648714954577137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73086073375765809969718091 109629110063648714954577137)
  ·
    refine ⟨82221832547736536215932853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109629110063648714954577137 82221832547736536215932853)
    ·
      refine ⟨7708296801350300270243705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82221832547736536215932853 7708296801350300270243705)
      ·
        refine ⟨5781222601012725202682779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7708296801350300270243705 5781222601012725202682779)
        ·
          refine ⟨8671833901519087804024169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5781222601012725202682779 8671833901519087804024169)
          ·
            refine ⟨6503875426139315853018127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8671833901519087804024169 6503875426139315853018127)
            ·
              refine ⟨9755813139208973779527191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6503875426139315853018127 9755813139208973779527191)
              ·
                refine ⟨14633719708813460669290787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9755813139208973779527191 14633719708813460669290787)
                ·
                  refine ⟨21950579563220191003936181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14633719708813460669290787 21950579563220191003936181)
                  ·
                    refine ⟨2057866834051892906619017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21950579563220191003936181 2057866834051892906619017)
                    ·
                      refine ⟨1543400125538919679964263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2057866834051892906619017 1543400125538919679964263)
                      ·
                        rfl

theorem cell23_3005761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_3005761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005761 prefixEnd_3005761 := by exact prefixLift 3005761
  have htrace : WordTrace (prefixWord ++ tailWord_3005761) baseStart_3005761 baseEnd_3005761 := by
    simpa [prefixWord, tailWord_3005761, baseEnd_3005761] using wordTrace_append hprefix tailTrace_3005761
  have hstable : (prefixWord ++ tailWord_3005761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005761).length < 2 ^ (prefixWord ++ tailWord_3005761).sum := by decide
  have hdescent : baseEnd_3005761 < baseStart_3005761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005767 : List Nat := [1, 1, 4, 1, 2, 3, 2, 2, 1, 6]
def baseStart_3005767 : Nat := 118140960795 + 3005767 * 2 ^ 59
def prefixEnd_3005767 : Nat := 4983230072969 + 3 ^ 40 * 3005767 * 2
def baseEnd_3005767 : Nat := 514467735474282218829745

theorem tailTrace_3005767 : CollatzResearch.WordTrace tailWord_3005767 prefixEnd_3005767 514467735474282218829745 := by
  unfold tailWord_3005767
  simp only [CollatzResearch.WordTrace]
  refine ⟨109629328901626977979295555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73086219267751318652863703 109629328901626977979295555)
  ·
    refine ⟨164443993352440466968943333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109629328901626977979295555 164443993352440466968943333)
    ·
      refine ⟨30833248753582587556676875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164443993352440466968943333 30833248753582587556676875)
      ·
        refine ⟨46249873130373881335015313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30833248753582587556676875 46249873130373881335015313)
        ·
          refine ⟨34687404847780411001261485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46249873130373881335015313 34687404847780411001261485)
          ·
            refine ⟨13007776817917654125473057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34687404847780411001261485 13007776817917654125473057)
            ·
              refine ⟨9755832613438240594104793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13007776817917654125473057 9755832613438240594104793)
              ·
                refine ⟨7316874460078680445578595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9755832613438240594104793 7316874460078680445578595)
                ·
                  refine ⟨10975311690118020668367893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7316874460078680445578595 10975311690118020668367893)
                  ·
                    refine ⟨514467735474282218829745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10975311690118020668367893 514467735474282218829745)
                    ·
                      rfl

theorem cell23_3005767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_3005767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005767 prefixEnd_3005767 := by exact prefixLift 3005767
  have htrace : WordTrace (prefixWord ++ tailWord_3005767) baseStart_3005767 baseEnd_3005767 := by
    simpa [prefixWord, tailWord_3005767, baseEnd_3005767] using wordTrace_append hprefix tailTrace_3005767
  have hstable : (prefixWord ++ tailWord_3005767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005767).length < 2 ^ (prefixWord ++ tailWord_3005767).sum := by decide
  have hdescent : baseEnd_3005767 < baseStart_3005767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005774 : List Nat := [4, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4]
def baseStart_3005774 : Nat := 118140960795 + 3005774 * 2 ^ 59
def prefixEnd_3005774 : Nat := 4983230072969 + 3 ^ 40 * 3005774 * 2
def baseEnd_3005774 : Nat := 1543406800787428129101703

theorem tailTrace_3005774 : CollatzResearch.WordTrace tailWord_3005774 prefixEnd_3005774 1543406800787428129101703 := by
  unfold tailWord_3005774
  simp only [CollatzResearch.WordTrace]
  refine ⟨13703698026575202271850047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73086389475067745449866917 13703698026575202271850047)
  ·
    refine ⟨20555547039862803407775071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13703698026575202271850047 20555547039862803407775071)
    ·
      refine ⟨30833320559794205111662607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20555547039862803407775071 30833320559794205111662607)
      ·
        refine ⟨46249980839691307667493911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30833320559794205111662607 46249980839691307667493911)
        ·
          refine ⟨69374971259536961501240867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46249980839691307667493911 69374971259536961501240867)
          ·
            refine ⟨104062456889305442251861301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69374971259536961501240867 104062456889305442251861301)
            ·
              refine ⟨9755855333372385211111997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104062456889305442251861301 9755855333372385211111997)
              ·
                refine ⟨3658445750014644454166999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9755855333372385211111997 3658445750014644454166999)
                ·
                  refine ⟨5487668625021966681250499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3658445750014644454166999 5487668625021966681250499)
                  ·
                    refine ⟨8231502937532950021875749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5487668625021966681250499 8231502937532950021875749)
                    ·
                      refine ⟨1543406800787428129101703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8231502937532950021875749 1543406800787428129101703)
                      ·
                        rfl

theorem cell23_3005774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_3005774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005774 prefixEnd_3005774 := by exact prefixLift 3005774
  have htrace : WordTrace (prefixWord ++ tailWord_3005774) baseStart_3005774 baseEnd_3005774 := by
    simpa [prefixWord, tailWord_3005774, baseEnd_3005774] using wordTrace_append hprefix tailTrace_3005774
  have hstable : (prefixWord ++ tailWord_3005774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005774).length < 2 ^ (prefixWord ++ tailWord_3005774).sum := by decide
  have hdescent : baseEnd_3005774 < baseStart_3005774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005777 : List Nat := [1, 2, 2, 1, 4, 1, 2, 3, 1, 1, 5]
def baseStart_3005777 : Nat := 118140960795 + 3005777 * 2 ^ 59
def prefixEnd_3005777 : Nat := 4983230072969 + 3 ^ 40 * 3005777 * 2
def baseEnd_3005777 : Nat := 1543408341229391617364189

theorem tailTrace_3005777 : CollatzResearch.WordTrace tailWord_3005777 prefixEnd_3005777 1543408341229391617364189 := by
  unfold tailWord_3005777
  simp only [CollatzResearch.WordTrace]
  refine ⟨109629693631590749687159585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73086462421060499791439723 109629693631590749687159585)
  ·
    refine ⟨82222270223693062265369689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109629693631590749687159585 82222270223693062265369689)
    ·
      refine ⟨61666702667769796699027267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82222270223693062265369689 61666702667769796699027267)
      ·
        refine ⟨92500054001654695048540901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61666702667769796699027267 92500054001654695048540901)
        ·
          refine ⟨17343760125310255321601419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92500054001654695048540901 17343760125310255321601419)
          ·
            refine ⟨26015640187965382982402129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17343760125310255321601419 26015640187965382982402129)
            ·
              refine ⟨19511730140974037236801597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26015640187965382982402129 19511730140974037236801597)
              ·
                refine ⟨7316898802865263963800599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19511730140974037236801597 7316898802865263963800599)
                ·
                  refine ⟨10975348204297895945700899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7316898802865263963800599 10975348204297895945700899)
                  ·
                    refine ⟨16463022306446843918551349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10975348204297895945700899 16463022306446843918551349)
                    ·
                      refine ⟨1543408341229391617364189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16463022306446843918551349 1543408341229391617364189)
                      ·
                        rfl

theorem cell23_3005777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_3005777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005777 prefixEnd_3005777 := by exact prefixLift 3005777
  have htrace : WordTrace (prefixWord ++ tailWord_3005777) baseStart_3005777 baseEnd_3005777 := by
    simpa [prefixWord, tailWord_3005777, baseEnd_3005777] using wordTrace_append hprefix tailTrace_3005777
  have hstable : (prefixWord ++ tailWord_3005777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005777).length < 2 ^ (prefixWord ++ tailWord_3005777).sum := by decide
  have hdescent : baseEnd_3005777 < baseStart_3005777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005794 : List Nat := [3, 3, 2, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_3005794 : Nat := 118140960795 + 3005794 * 2 ^ 59
def prefixEnd_3005794 : Nat := 4983230072969 + 3 ^ 40 * 3005794 * 2
def baseEnd_3005794 : Nat := 1543417070400518050851611

theorem tailTrace_3005794 : CollatzResearch.WordTrace tailWord_3005794 prefixEnd_3005794 1543417070400518050851611 := by
  unfold tailWord_3005794
  simp only [CollatzResearch.WordTrace]
  refine ⟨27407578418132290397632109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73086875781686107727018957 27407578418132290397632109)
  ·
    refine ⟨10277841906799608899112041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27407578418132290397632109 10277841906799608899112041)
    ·
      refine ⟨7708381430099706674334031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10277841906799608899112041 7708381430099706674334031)
      ·
        refine ⟨11562572145149560011501047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7708381430099706674334031 11562572145149560011501047)
        ·
          refine ⟨17343858217724340017251571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11562572145149560011501047 17343858217724340017251571)
          ·
            refine ⟨26015787326586510025877357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17343858217724340017251571 26015787326586510025877357)
            ·
              refine ⟨9755920247469941259704009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26015787326586510025877357 9755920247469941259704009)
              ·
                refine ⟨7316940185602455944778007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9755920247469941259704009 7316940185602455944778007)
                ·
                  refine ⟨10975410278403683917167011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7316940185602455944778007 10975410278403683917167011)
                  ·
                    refine ⟨16463115417605525875750517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10975410278403683917167011 16463115417605525875750517)
                    ·
                      refine ⟨1543417070400518050851611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16463115417605525875750517 1543417070400518050851611)
                      ·
                        rfl

theorem cell23_3005794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_3005794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005794 prefixEnd_3005794 := by exact prefixLift 3005794
  have htrace : WordTrace (prefixWord ++ tailWord_3005794) baseStart_3005794 baseEnd_3005794 := by
    simpa [prefixWord, tailWord_3005794, baseEnd_3005794] using wordTrace_append hprefix tailTrace_3005794
  have hstable : (prefixWord ++ tailWord_3005794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005794).length < 2 ^ (prefixWord ++ tailWord_3005794).sum := by decide
  have hdescent : baseEnd_3005794 < baseStart_3005794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005804 : List Nat := [2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 4]
def baseStart_3005804 : Nat := 118140960795 + 3005804 * 2 ^ 59
def prefixEnd_3005804 : Nat := 4983230072969 + 3 ^ 40 * 3005804 * 2
def baseEnd_3005804 : Nat := 1543422205207063011726565

theorem tailTrace_3005804 : CollatzResearch.WordTrace tailWord_3005804 prefixEnd_3005804 1543422205207063011726565 := by
  unfold tailWord_3005804
  simp only [CollatzResearch.WordTrace]
  refine ⟨54815339201246466649196233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73087118934995288865594977 54815339201246466649196233)
  ·
    refine ⟨41111504400934849986897175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54815339201246466649196233 41111504400934849986897175)
    ·
      refine ⟨61667256601402274980345763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41111504400934849986897175 61667256601402274980345763)
      ·
        refine ⟨92500884902103412470518645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61667256601402274980345763 92500884902103412470518645)
        ·
          refine ⟨8671957959572194919111123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92500884902103412470518645 8671957959572194919111123)
          ·
            refine ⟨13007936939358292378666685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8671957959572194919111123 13007936939358292378666685)
            ·
              refine ⟨4877976352259359642000007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13007936939358292378666685 4877976352259359642000007)
              ·
                refine ⟨7316964528389039463000011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4877976352259359642000007 7316964528389039463000011)
                ·
                  refine ⟨10975446792583559194500017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7316964528389039463000011 10975446792583559194500017)
                  ·
                    refine ⟨8231585094437669395875013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10975446792583559194500017 8231585094437669395875013)
                    ·
                      refine ⟨1543422205207063011726565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8231585094437669395875013 1543422205207063011726565)
                      ·
                        rfl

theorem cell23_3005804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 4].length) (baseStart_3005804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005804 prefixEnd_3005804 := by exact prefixLift 3005804
  have htrace : WordTrace (prefixWord ++ tailWord_3005804) baseStart_3005804 baseEnd_3005804 := by
    simpa [prefixWord, tailWord_3005804, baseEnd_3005804] using wordTrace_append hprefix tailTrace_3005804
  have hstable : (prefixWord ++ tailWord_3005804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005804).length < 2 ^ (prefixWord ++ tailWord_3005804).sum := by decide
  have hdescent : baseEnd_3005804 < baseStart_3005804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005842 : List Nat := [3, 2, 3, 3, 1, 2, 1, 1, 3, 2, 2]
def baseStart_3005842 : Nat := 118140960795 + 3005842 * 2 ^ 59
def prefixEnd_3005842 : Nat := 4983230072969 + 3 ^ 40 * 3005842 * 2
def baseEnd_3005842 : Nat := 1543441717471933863051391

theorem tailTrace_3005842 : CollatzResearch.WordTrace tailWord_3005842 prefixEnd_3005842 1543441717471933863051391 := by
  unfold tailWord_3005842
  simp only [CollatzResearch.WordTrace]
  refine ⟨27408016094088816447068945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73088042917570177192183853 27408016094088816447068945)
  ·
    refine ⟨20556012070566612335301709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27408016094088816447068945 20556012070566612335301709)
    ·
      refine ⟨7708504526462479625738141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20556012070566612335301709 7708504526462479625738141)
      ·
        refine ⟨2890689197423429859651803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7708504526462479625738141 2890689197423429859651803)
        ·
          refine ⟨4336033796135144789477705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2890689197423429859651803 4336033796135144789477705)
          ·
            refine ⟨3252025347101358592108279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4336033796135144789477705 3252025347101358592108279)
            ·
              refine ⟨4878038020652037888162419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3252025347101358592108279 4878038020652037888162419)
              ·
                refine ⟨7317057030978056832243629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4878038020652037888162419 7317057030978056832243629)
                ·
                  refine ⟨2743896386616771312091361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7317057030978056832243629 2743896386616771312091361)
                  ·
                    refine ⟨2057922289962578484068521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2743896386616771312091361 2057922289962578484068521)
                    ·
                      refine ⟨1543441717471933863051391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2057922289962578484068521 1543441717471933863051391)
                      ·
                        rfl

theorem cell23_3005842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_3005842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005842 prefixEnd_3005842 := by exact prefixLift 3005842
  have htrace : WordTrace (prefixWord ++ tailWord_3005842) baseStart_3005842 baseEnd_3005842 := by
    simpa [prefixWord, tailWord_3005842, baseEnd_3005842] using wordTrace_append hprefix tailTrace_3005842
  have hstable : (prefixWord ++ tailWord_3005842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005842).length < 2 ^ (prefixWord ++ tailWord_3005842).sum := by decide
  have hdescent : baseEnd_3005842 < baseStart_3005842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005847 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 4]
def baseStart_3005847 : Nat := 118140960795 + 3005847 * 2 ^ 59
def prefixEnd_3005847 : Nat := 4983230072969 + 3 ^ 40 * 3005847 * 2
def baseEnd_3005847 : Nat := 1543444284875206343488867

theorem tailTrace_3005847 : CollatzResearch.WordTrace tailWord_3005847 prefixEnd_3005847 1543444284875206343488867 := by
  unfold tailWord_3005847
  simp only [CollatzResearch.WordTrace]
  refine ⟨109632246741337151642207795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73088164494224767761471863 109632246741337151642207795)
  ·
    refine ⟨164448370112005727463311693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109632246741337151642207795 164448370112005727463311693)
    ·
      refine ⟨61668138792002147798741885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164448370112005727463311693 61668138792002147798741885)
      ·
        refine ⟨23125552047000805424528207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61668138792002147798741885 23125552047000805424528207)
        ·
          refine ⟨34688328070501208136792311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23125552047000805424528207 34688328070501208136792311)
          ·
            refine ⟨52032492105751812205188467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34688328070501208136792311 52032492105751812205188467)
            ·
              refine ⟨78048738158627718307782701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52032492105751812205188467 78048738158627718307782701)
              ·
                refine ⟨29268276809485394365418513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78048738158627718307782701 29268276809485394365418513)
                ·
                  refine ⟨21951207607114045774063885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29268276809485394365418513 21951207607114045774063885)
                  ·
                    refine ⟨8231702852667767165273957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21951207607114045774063885 8231702852667767165273957)
                    ·
                      refine ⟨1543444284875206343488867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8231702852667767165273957 1543444284875206343488867)
                      ·
                        rfl

theorem cell23_3005847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_3005847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005847 prefixEnd_3005847 := by exact prefixLift 3005847
  have htrace : WordTrace (prefixWord ++ tailWord_3005847) baseStart_3005847 baseEnd_3005847 := by
    simpa [prefixWord, tailWord_3005847, baseEnd_3005847] using wordTrace_append hprefix tailTrace_3005847
  have hstable : (prefixWord ++ tailWord_3005847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005847).length < 2 ^ (prefixWord ++ tailWord_3005847).sum := by decide
  have hdescent : baseEnd_3005847 < baseStart_3005847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005852 : List Nat := [2, 2, 3, 4, 2, 1, 2, 1, 2, 4]
def baseStart_3005852 : Nat := 118140960795 + 3005852 * 2 ^ 59
def prefixEnd_3005852 : Nat := 4983230072969 + 3 ^ 40 * 3005852 * 2
def baseEnd_3005852 : Nat := 514482284092826274642115

theorem tailTrace_3005852 : CollatzResearch.WordTrace tailWord_3005852 prefixEnd_3005852 514482284092826274642115 := by
  unfold tailWord_3005852
  simp only [CollatzResearch.WordTrace]
  refine ⟨54816214553159518748069905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73088286070879358330759873 54816214553159518748069905)
  ·
    refine ⟨41112160914869639061052429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54816214553159518748069905 41112160914869639061052429)
    ·
      refine ⟨15417060343076114647894661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41112160914869639061052429 15417060343076114647894661)
      ·
        refine ⟨2890698814326771496480249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15417060343076114647894661 2890698814326771496480249)
        ·
          refine ⟨2168024110745078622360187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2890698814326771496480249 2168024110745078622360187)
          ·
            refine ⟨3252036166117617933540281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2168024110745078622360187 3252036166117617933540281)
            ·
              refine ⟨2439027124588213450155211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3252036166117617933540281 2439027124588213450155211)
              ·
                refine ⟨3658540686882320175232817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2439027124588213450155211 3658540686882320175232817)
                ·
                  refine ⟨2743905515161740131424613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3658540686882320175232817 2743905515161740131424613)
                  ·
                    refine ⟨514482284092826274642115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2743905515161740131424613 514482284092826274642115)
                    ·
                      rfl

theorem cell23_3005852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_3005852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005852 prefixEnd_3005852 := by exact prefixLift 3005852
  have htrace : WordTrace (prefixWord ++ tailWord_3005852) baseStart_3005852 baseEnd_3005852 := by
    simpa [prefixWord, tailWord_3005852, baseEnd_3005852] using wordTrace_append hprefix tailTrace_3005852
  have hstable : (prefixWord ++ tailWord_3005852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005852).length < 2 ^ (prefixWord ++ tailWord_3005852).sum := by decide
  have hdescent : baseEnd_3005852 < baseStart_3005852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005858 : List Nat := [3, 3, 1, 2, 1, 3, 1, 3, 2, 1, 3]
def baseStart_3005858 : Nat := 118140960795 + 3005858 * 2 ^ 59
def prefixEnd_3005858 : Nat := 4983230072969 + 3 ^ 40 * 3005858 * 2
def baseEnd_3005858 : Nat := 1543449933162405800451317

theorem tailTrace_3005858 : CollatzResearch.WordTrace tailWord_3005858 prefixEnd_3005858 1543449933162405800451317 := by
  unfold tailWord_3005858
  simp only [CollatzResearch.WordTrace]
  refine ⟨27408161986074325130214557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73088431962864867013905485 27408161986074325130214557)
  ·
    refine ⟨10278060744777871923830459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27408161986074325130214557 10278060744777871923830459)
    ·
      refine ⟨15417091117166807885745689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10278060744777871923830459 15417091117166807885745689)
      ·
        refine ⟨11562818337875105914309267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15417091117166807885745689 11562818337875105914309267)
        ·
          refine ⟨17344227506812658871463901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11562818337875105914309267 17344227506812658871463901)
          ·
            refine ⟨6504085315054747076798963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17344227506812658871463901 6504085315054747076798963)
            ·
              refine ⟨9756127972582120615198445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6504085315054747076798963 9756127972582120615198445)
              ·
                refine ⟨3658547989718295230699417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9756127972582120615198445 3658547989718295230699417)
                ·
                  refine ⟨2743910992288721423024563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3658547989718295230699417 2743910992288721423024563)
                  ·
                    refine ⟨4115866488433082134536845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2743910992288721423024563 4115866488433082134536845)
                    ·
                      refine ⟨1543449933162405800451317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4115866488433082134536845 1543449933162405800451317)
                      ·
                        rfl

theorem cell23_3005858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_3005858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005858 prefixEnd_3005858 := by exact prefixLift 3005858
  have htrace : WordTrace (prefixWord ++ tailWord_3005858) baseStart_3005858 baseEnd_3005858 := by
    simpa [prefixWord, tailWord_3005858, baseEnd_3005858] using wordTrace_append hprefix tailTrace_3005858
  have hstable : (prefixWord ++ tailWord_3005858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005858).length < 2 ^ (prefixWord ++ tailWord_3005858).sum := by decide
  have hdescent : baseEnd_3005858 < baseStart_3005858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005898 : List Nat := [3, 1, 2, 1, 2, 3, 1, 4, 2, 2, 2]
def baseStart_3005898 : Nat := 118140960795 + 3005898 * 2 ^ 59
def prefixEnd_3005898 : Nat := 4983230072969 + 3 ^ 40 * 3005898 * 2
def baseEnd_3005898 : Nat := 1543470472388585643951133

theorem tailTrace_3005898 : CollatzResearch.WordTrace tailWord_3005898 prefixEnd_3005898 1543470472388585643951133 := by
  unfold tailWord_3005898
  simp only [CollatzResearch.WordTrace]
  refine ⟨27408526716038096838078587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73089404576101591568209565 27408526716038096838078587)
  ·
    refine ⟨41112790074057145257117881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27408526716038096838078587 41112790074057145257117881)
    ·
      refine ⟨30834592555542858942838411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41112790074057145257117881 30834592555542858942838411)
      ·
        refine ⟨46251888833314288414257617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30834592555542858942838411 46251888833314288414257617)
        ·
          refine ⟨34688916624985716310693213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46251888833314288414257617 34688916624985716310693213)
          ·
            refine ⟨13008343734369643616509955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34688916624985716310693213 13008343734369643616509955)
            ·
              refine ⟨19512515601554465424764933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13008343734369643616509955 19512515601554465424764933)
              ·
                refine ⟨3658596675291462267143425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19512515601554465424764933 3658596675291462267143425)
                ·
                  refine ⟨2743947506468596700357569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3658596675291462267143425 2743947506468596700357569)
                  ·
                    refine ⟨2057960629851447525268177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2743947506468596700357569 2057960629851447525268177)
                    ·
                      refine ⟨1543470472388585643951133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2057960629851447525268177 1543470472388585643951133)
                      ·
                        rfl

theorem cell23_3005898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 2, 2, 2].length) (baseStart_3005898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005898 prefixEnd_3005898 := by exact prefixLift 3005898
  have htrace : WordTrace (prefixWord ++ tailWord_3005898) baseStart_3005898 baseEnd_3005898 := by
    simpa [prefixWord, tailWord_3005898, baseEnd_3005898] using wordTrace_append hprefix tailTrace_3005898
  have hstable : (prefixWord ++ tailWord_3005898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005898).length < 2 ^ (prefixWord ++ tailWord_3005898).sum := by decide
  have hdescent : baseEnd_3005898 < baseStart_3005898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005904 : List Nat := [2, 1, 1, 1, 1, 2, 2, 8, 5]
def baseStart_3005904 : Nat := 118140960795 + 3005904 * 2 ^ 59
def prefixEnd_3005904 : Nat := 4983230072969 + 3 ^ 40 * 3005904 * 2
def baseEnd_3005904 : Nat := 171497061474723624497345

theorem tailTrace_3005904 : CollatzResearch.WordTrace tailWord_3005904 prefixEnd_3005904 171497061474723624497345 := by
  unfold tailWord_3005904
  simp only [CollatzResearch.WordTrace]
  refine ⟨54817162851065325188516383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73089550468087100251355177 54817162851065325188516383)
  ·
    refine ⟨82225744276597987782774575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54817162851065325188516383 82225744276597987782774575)
    ·
      refine ⟨123338616414896981674161863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82225744276597987782774575 123338616414896981674161863)
      ·
        refine ⟨185007924622345472511242795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123338616414896981674161863 185007924622345472511242795)
        ·
          refine ⟨277511886933518208766864193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185007924622345472511242795 277511886933518208766864193)
          ·
            refine ⟨208133915200138656575148145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277511886933518208766864193 208133915200138656575148145)
            ·
              refine ⟨156100436400103992431361109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208133915200138656575148145 156100436400103992431361109)
              ·
                refine ⟨1829301989063718661305013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 156100436400103992431361109 1829301989063718661305013)
                ·
                  refine ⟨171497061474723624497345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1829301989063718661305013 171497061474723624497345)
                  ·
                    rfl

theorem cell23_3005904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8, 5].length) (baseStart_3005904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005904 prefixEnd_3005904 := by exact prefixLift 3005904
  have htrace : WordTrace (prefixWord ++ tailWord_3005904) baseStart_3005904 baseEnd_3005904 := by
    simpa [prefixWord, tailWord_3005904, baseEnd_3005904] using wordTrace_append hprefix tailTrace_3005904
  have hstable : (prefixWord ++ tailWord_3005904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005904).length < 2 ^ (prefixWord ++ tailWord_3005904).sum := by decide
  have hdescent : baseEnd_3005904 < baseStart_3005904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005914 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3]
def baseStart_3005914 : Nat := 118140960795 + 3005914 * 2 ^ 59
def prefixEnd_3005914 : Nat := 4983230072969 + 3 ^ 40 * 3005914 * 2
def baseEnd_3005914 : Nat := 1543478688079057581351059

theorem tailTrace_3005914 : CollatzResearch.WordTrace tailWord_3005914 prefixEnd_3005914 1543478688079057581351059 := by
  unfold tailWord_3005914
  simp only [CollatzResearch.WordTrace]
  refine ⟨27408672608023605521224199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73089793621396281389931197 27408672608023605521224199)
  ·
    refine ⟨41113008912035408281836299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27408672608023605521224199 41113008912035408281836299)
    ·
      refine ⟨61669513368053112422754449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41113008912035408281836299 61669513368053112422754449)
      ·
        refine ⟨46252135026039834317065837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61669513368053112422754449 46252135026039834317065837)
        ·
          refine ⟨17344550634764937868899689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46252135026039834317065837 17344550634764937868899689)
          ·
            refine ⟨13008412976073703401674767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17344550634764937868899689 13008412976073703401674767)
            ·
              refine ⟨19512619464110555102512151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13008412976073703401674767 19512619464110555102512151)
              ·
                refine ⟨29268929196165832653768227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19512619464110555102512151 29268929196165832653768227)
                ·
                  refine ⟨43903393794248748980652341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29268929196165832653768227 43903393794248748980652341)
                  ·
                    refine ⟨4115943168210820216936157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43903393794248748980652341 4115943168210820216936157)
                    ·
                      refine ⟨1543478688079057581351059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4115943168210820216936157 1543478688079057581351059)
                      ·
                        rfl

theorem cell23_3005914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_3005914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005914 prefixEnd_3005914 := by exact prefixLift 3005914
  have htrace : WordTrace (prefixWord ++ tailWord_3005914) baseStart_3005914 baseEnd_3005914 := by
    simpa [prefixWord, tailWord_3005914, baseEnd_3005914] using wordTrace_append hprefix tailTrace_3005914
  have hstable : (prefixWord ++ tailWord_3005914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005914).length < 2 ^ (prefixWord ++ tailWord_3005914).sum := by decide
  have hdescent : baseEnd_3005914 < baseStart_3005914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005934 : List Nat := [4, 1, 2, 1, 2, 1, 3, 1, 1, 7]
def baseStart_3005934 : Nat := 118140960795 + 3005934 * 2 ^ 59
def prefixEnd_3005934 : Nat := 4983230072969 + 3 ^ 40 * 3005934 * 2
def baseEnd_3005934 : Nat := 514496319230715834366989

theorem tailTrace_3005934 : CollatzResearch.WordTrace tailWord_3005934 prefixEnd_3005934 514496319230715834366989 := by
  unfold tailWord_3005934
  simp only [CollatzResearch.WordTrace]
  refine ⟨13704427486502745687578107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73090279928014643667083237 13704427486502745687578107)
  ·
    refine ⟨20556641229754118531367161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13704427486502745687578107 20556641229754118531367161)
    ·
      refine ⟨15417480922315588898525371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20556641229754118531367161 15417480922315588898525371)
      ·
        refine ⟨23126221383473383347788057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15417480922315588898525371 23126221383473383347788057)
        ·
          refine ⟨17344666037605037510841043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23126221383473383347788057 17344666037605037510841043)
          ·
            refine ⟨26016999056407556266261565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17344666037605037510841043 26016999056407556266261565)
            ·
              refine ⟨9756374646152833599848087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26016999056407556266261565 9756374646152833599848087)
              ·
                refine ⟨14634561969229250399772131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9756374646152833599848087 14634561969229250399772131)
                ·
                  refine ⟨21951842953843875599658197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14634561969229250399772131 21951842953843875599658197)
                  ·
                    refine ⟨514496319230715834366989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21951842953843875599658197 514496319230715834366989)
                    ·
                      rfl

theorem cell23_3005934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_3005934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005934 prefixEnd_3005934 := by exact prefixLift 3005934
  have htrace : WordTrace (prefixWord ++ tailWord_3005934) baseStart_3005934 baseEnd_3005934 := by
    simpa [prefixWord, tailWord_3005934, baseEnd_3005934] using wordTrace_append hprefix tailTrace_3005934
  have hstable : (prefixWord ++ tailWord_3005934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005934).length < 2 ^ (prefixWord ++ tailWord_3005934).sum := by decide
  have hdescent : baseEnd_3005934 < baseStart_3005934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005938 : List Nat := [3, 2, 1, 4, 1, 2, 2, 3, 5]
def baseStart_3005938 : Nat := 118140960795 + 3005938 * 2 ^ 59
def prefixEnd_3005938 : Nat := 4983230072969 + 3 ^ 40 * 3005938 * 2
def baseEnd_3005938 : Nat := 171499001290529498605661

theorem tailTrace_3005938 : CollatzResearch.WordTrace tailWord_3005938 prefixEnd_3005938 171499001290529498605661 := by
  unfold tailWord_3005938
  simp only [CollatzResearch.WordTrace]
  refine ⟨27408891446001868545942617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73090377189338316122513645 27408891446001868545942617)
  ·
    refine ⟨20556668584501401409456963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27408891446001868545942617 20556668584501401409456963)
    ·
      refine ⟨30835002876752102114185445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20556668584501401409456963 30835002876752102114185445)
      ·
        refine ⟨5781563039391019146409771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30835002876752102114185445 5781563039391019146409771)
        ·
          refine ⟨8672344559086528719614657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5781563039391019146409771 8672344559086528719614657)
          ·
            refine ⟨6504258419314896539710993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8672344559086528719614657 6504258419314896539710993)
            ·
              refine ⟨4878193814486172404783245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6504258419314896539710993 4878193814486172404783245)
              ·
                refine ⟨1829322680432314651793717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4878193814486172404783245 1829322680432314651793717)
                ·
                  refine ⟨171499001290529498605661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1829322680432314651793717 171499001290529498605661)
                  ·
                    rfl

theorem cell23_3005938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3, 5].length) (baseStart_3005938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005938 prefixEnd_3005938 := by exact prefixLift 3005938
  have htrace : WordTrace (prefixWord ++ tailWord_3005938) baseStart_3005938 baseEnd_3005938 := by
    simpa [prefixWord, tailWord_3005938, baseEnd_3005938] using wordTrace_append hprefix tailTrace_3005938
  have hstable : (prefixWord ++ tailWord_3005938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005938).length < 2 ^ (prefixWord ++ tailWord_3005938).sum := by decide
  have hdescent : baseEnd_3005938 < baseStart_3005938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005967 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 6]
def baseStart_3005967 : Nat := 118140960795 + 3005967 * 2 ^ 59
def prefixEnd_3005967 : Nat := 4983230072969 + 3 ^ 40 * 3005967 * 2
def baseEnd_3005967 : Nat := 1543505902553745873988315

theorem tailTrace_3005967 : CollatzResearch.WordTrace tailWord_3005967 prefixEnd_3005967 1543505902553745873988315 := by
  unfold tailWord_3005967
  simp only [CollatzResearch.WordTrace]
  refine ⟨109636623500902412136576155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73091082333934941424384103 109636623500902412136576155)
  ·
    refine ⟨164454935251353618204864233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109636623500902412136576155 164454935251353618204864233)
    ·
      refine ⟨123341201438515213653648175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164454935251353618204864233 123341201438515213653648175)
      ·
        refine ⟨185011802157772820480472263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123341201438515213653648175 185011802157772820480472263)
        ·
          refine ⟨277517703236659230720708395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185011802157772820480472263 277517703236659230720708395)
          ·
            refine ⟨416276554854988846081062593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277517703236659230720708395 416276554854988846081062593)
            ·
              refine ⟨312207416141241634560796945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416276554854988846081062593 312207416141241634560796945)
              ·
                refine ⟨234155562105931225920597709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 312207416141241634560796945 234155562105931225920597709)
                ·
                  refine ⟨87808335789724209720224141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234155562105931225920597709 87808335789724209720224141)
                  ·
                    refine ⟨32928125921146578645084053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87808335789724209720224141 32928125921146578645084053)
                    ·
                      refine ⟨1543505902553745873988315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32928125921146578645084053 1543505902553745873988315)
                      ·
                        rfl

theorem cell23_3005967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 6].length) (baseStart_3005967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005967 prefixEnd_3005967 := by exact prefixLift 3005967
  have htrace : WordTrace (prefixWord ++ tailWord_3005967) baseStart_3005967 baseEnd_3005967 := by
    simpa [prefixWord, tailWord_3005967, baseEnd_3005967] using wordTrace_append hprefix tailTrace_3005967
  have hstable : (prefixWord ++ tailWord_3005967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005967).length < 2 ^ (prefixWord ++ tailWord_3005967).sum := by decide
  have hdescent : baseEnd_3005967 < baseStart_3005967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005971 : List Nat := [1, 1, 1, 2, 1, 6, 2, 1, 2, 4, 2]
def baseStart_3005971 : Nat := 118140960795 + 3005971 * 2 ^ 59
def prefixEnd_3005971 : Nat := 4983230072969 + 3 ^ 40 * 3005971 * 2
def baseEnd_3005971 : Nat := 1543507956476363858338297

theorem tailTrace_3005971 : CollatzResearch.WordTrace tailWord_3005971 prefixEnd_3005971 1543507956476363858338297 := by
  unfold tailWord_3005971
  simp only [CollatzResearch.WordTrace]
  refine ⟨109636769392887920819721767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73091179595258613879814511 109636769392887920819721767)
  ·
    refine ⟨164455154089331881229582651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109636769392887920819721767 164455154089331881229582651)
    ·
      refine ⟨246682731133997821844373977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164455154089331881229582651 246682731133997821844373977)
      ·
        refine ⟨185012048350498366383280483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246682731133997821844373977 185012048350498366383280483)
        ·
          refine ⟨277518072525747549574920725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185012048350498366383280483 277518072525747549574920725)
          ·
            refine ⟨13008659649644416386324409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 277518072525747549574920725 13008659649644416386324409)
            ·
              refine ⟨9756494737233312289743307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13008659649644416386324409 9756494737233312289743307)
              ·
                refine ⟨14634742105849968434614961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9756494737233312289743307 14634742105849968434614961)
                ·
                  refine ⟨10976056579387476325961221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14634742105849968434614961 10976056579387476325961221)
                  ·
                    refine ⟨2058010608635151811117729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10976056579387476325961221 2058010608635151811117729)
                    ·
                      refine ⟨1543507956476363858338297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2058010608635151811117729 1543507956476363858338297)
                      ·
                        rfl

theorem cell23_3005971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 4, 2].length) (baseStart_3005971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005971 prefixEnd_3005971 := by exact prefixLift 3005971
  have htrace : WordTrace (prefixWord ++ tailWord_3005971) baseStart_3005971 baseEnd_3005971 := by
    simpa [prefixWord, tailWord_3005971, baseEnd_3005971] using wordTrace_append hprefix tailTrace_3005971
  have hstable : (prefixWord ++ tailWord_3005971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005971).length < 2 ^ (prefixWord ++ tailWord_3005971).sum := by decide
  have hdescent : baseEnd_3005971 < baseStart_3005971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005977 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 12]
def baseStart_3005977 : Nat := 118140960795 + 3005977 * 2 ^ 59
def prefixEnd_3005977 : Nat := 4983230072969 + 3 ^ 40 * 3005977 * 2
def baseEnd_3005977 : Nat := 171501226373365648318141

theorem tailTrace_3005977 : CollatzResearch.WordTrace tailWord_3005977 prefixEnd_3005977 171501226373365648318141 := by
  unfold tailWord_3005977
  simp only [CollatzResearch.WordTrace]
  refine ⟨109636988230866183844440185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73091325487244122562960123 109636988230866183844440185)
  ·
    refine ⟨82227741173149637883330139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109636988230866183844440185 82227741173149637883330139)
    ·
      refine ⟨123341611759724456824995209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82227741173149637883330139 123341611759724456824995209)
      ·
        refine ⟨92506208819793342618746407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123341611759724456824995209 92506208819793342618746407)
        ·
          refine ⟨138759313229690013928119611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92506208819793342618746407 138759313229690013928119611)
          ·
            refine ⟨208138969844535020892179417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138759313229690013928119611 208138969844535020892179417)
            ·
              refine ⟨156104227383401265669134563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208138969844535020892179417 156104227383401265669134563)
              ·
                refine ⟨234156341075101898503701845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156104227383401265669134563 234156341075101898503701845)
                ·
                  refine ⟨171501226373365648318141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 234156341075101898503701845 171501226373365648318141)
                  ·
                    rfl

theorem cell23_3005977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 12].length) (baseStart_3005977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005977 prefixEnd_3005977 := by exact prefixLift 3005977
  have htrace : WordTrace (prefixWord ++ tailWord_3005977) baseStart_3005977 baseEnd_3005977 := by
    simpa [prefixWord, tailWord_3005977, baseEnd_3005977] using wordTrace_append hprefix tailTrace_3005977
  have hstable : (prefixWord ++ tailWord_3005977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005977).length < 2 ^ (prefixWord ++ tailWord_3005977).sum := by decide
  have hdescent : baseEnd_3005977 < baseStart_3005977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005981 : List Nat := [1, 4, 2, 2, 1, 1, 1, 4, 3, 4]
def baseStart_3005981 : Nat := 118140960795 + 3005981 * 2 ^ 59
def prefixEnd_3005981 : Nat := 4983230072969 + 3 ^ 40 * 3005981 * 2
def baseEnd_3005981 : Nat := 514504363760969606404417

theorem tailTrace_3005981 : CollatzResearch.WordTrace tailWord_3005981 prefixEnd_3005981 514504363760969606404417 := by
  unfold tailWord_3005981
  simp only [CollatzResearch.WordTrace]
  refine ⟨109637134122851692527585797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73091422748567795018390531 109637134122851692527585797)
  ·
    refine ⟨20556962648034692348922337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109637134122851692527585797 20556962648034692348922337)
    ·
      refine ⟨15417721986026019261691753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20556962648034692348922337 15417721986026019261691753)
      ·
        refine ⟨11563291489519514446268815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15417721986026019261691753 11563291489519514446268815)
        ·
          refine ⟨17344937234279271669403223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11563291489519514446268815 17344937234279271669403223)
          ·
            refine ⟨26017405851418907504104835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17344937234279271669403223 26017405851418907504104835)
            ·
              refine ⟨39026108777128361256157253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26017405851418907504104835 39026108777128361256157253)
              ·
                refine ⟨7317395395711567735529485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39026108777128361256157253 7317395395711567735529485)
                ·
                  refine ⟨2744023273391837900823557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7317395395711567735529485 2744023273391837900823557)
                  ·
                    refine ⟨514504363760969606404417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2744023273391837900823557 514504363760969606404417)
                    ·
                      rfl

theorem cell23_3005981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_3005981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005981 prefixEnd_3005981 := by exact prefixLift 3005981
  have htrace : WordTrace (prefixWord ++ tailWord_3005981) baseStart_3005981 baseEnd_3005981 := by
    simpa [prefixWord, tailWord_3005981, baseEnd_3005981] using wordTrace_append hprefix tailTrace_3005981
  have hstable : (prefixWord ++ tailWord_3005981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005981).length < 2 ^ (prefixWord ++ tailWord_3005981).sum := by decide
  have hdescent : baseEnd_3005981 < baseStart_3005981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005994 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 10]
def baseStart_3005994 : Nat := 118140960795 + 3005994 * 2 ^ 59
def prefixEnd_3005994 : Nat := 4983230072969 + 3 ^ 40 * 3005994 * 2
def baseEnd_3005994 : Nat := 171502196281268585372299

theorem tailTrace_3005994 : CollatzResearch.WordTrace tailWord_3005994 prefixEnd_3005994 171502196281268585372299 := by
  unfold tailWord_3005994
  simp only [CollatzResearch.WordTrace]
  refine ⟨27409402067951148936952259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73091738847869730498539357 27409402067951148936952259)
  ·
    refine ⟨41114103101926723405428389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27409402067951148936952259 41114103101926723405428389)
    ·
      refine ⟨7708894331611260638517823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41114103101926723405428389 7708894331611260638517823)
      ·
        refine ⟨11563341497416890957776735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7708894331611260638517823 11563341497416890957776735)
        ·
          refine ⟨17345012246125336436665103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11563341497416890957776735 17345012246125336436665103)
          ·
            refine ⟨26017518369188004654997655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17345012246125336436665103 26017518369188004654997655)
            ·
              refine ⟨39026277553782006982496483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26017518369188004654997655 39026277553782006982496483)
              ·
                refine ⟨58539416330673010473744725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39026277553782006982496483 58539416330673010473744725)
                ·
                  refine ⟨171502196281268585372299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 58539416330673010473744725 171502196281268585372299)
                  ·
                    rfl

theorem cell23_3005994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 10].length) (baseStart_3005994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3005994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3005994 prefixEnd_3005994 := by exact prefixLift 3005994
  have htrace : WordTrace (prefixWord ++ tailWord_3005994) baseStart_3005994 baseEnd_3005994 := by
    simpa [prefixWord, tailWord_3005994, baseEnd_3005994] using wordTrace_append hprefix tailTrace_3005994
  have hstable : (prefixWord ++ tailWord_3005994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005994).length < 2 ^ (prefixWord ++ tailWord_3005994).sum := by decide
  have hdescent : baseEnd_3005994 < baseStart_3005994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006015 : List Nat := [1, 1, 2, 2, 3, 4, 3, 2, 1, 4]
def baseStart_3006015 : Nat := 118140960795 + 3006015 * 2 ^ 59
def prefixEnd_3006015 : Nat := 4983230072969 + 3 ^ 40 * 3006015 * 2
def baseEnd_3006015 : Nat := 514510183208387228729365

theorem tailTrace_3006015 : CollatzResearch.WordTrace tailWord_3006015 prefixEnd_3006015 514510183208387228729365 := by
  unfold tailWord_3006015
  simp only [CollatzResearch.WordTrace]
  refine ⟨109638374204728516334323499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73092249469819010889548999 109638374204728516334323499)
  ·
    refine ⟨164457561307092774501485249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109638374204728516334323499 164457561307092774501485249)
    ·
      refine ⟨123343170980319580876113937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164457561307092774501485249 123343170980319580876113937)
      ·
        refine ⟨92507378235239685657085453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123343170980319580876113937 92507378235239685657085453)
        ·
          refine ⟨34690266838214882121407045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92507378235239685657085453 34690266838214882121407045)
          ·
            refine ⟨6504425032165290397763821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34690266838214882121407045 6504425032165290397763821)
            ·
              refine ⟨2439159387061983899161433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6504425032165290397763821 2439159387061983899161433)
              ·
                refine ⟨1829369540296487924371075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2439159387061983899161433 1829369540296487924371075)
                ·
                  refine ⟨2744054310444731886556613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1829369540296487924371075 2744054310444731886556613)
                  ·
                    refine ⟨514510183208387228729365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2744054310444731886556613 514510183208387228729365)
                    ·
                      rfl

theorem cell23_3006015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2, 1, 4].length) (baseStart_3006015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006015 prefixEnd_3006015 := by exact prefixLift 3006015
  have htrace : WordTrace (prefixWord ++ tailWord_3006015) baseStart_3006015 baseEnd_3006015 := by
    simpa [prefixWord, tailWord_3006015, baseEnd_3006015] using wordTrace_append hprefix tailTrace_3006015
  have hstable : (prefixWord ++ tailWord_3006015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006015).length < 2 ^ (prefixWord ++ tailWord_3006015).sum := by decide
  have hdescent : baseEnd_3006015 < baseStart_3006015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006028 : List Nat := [2, 2, 1, 3, 1, 5, 2, 1, 6]
def baseStart_3006028 : Nat := 118140960795 + 3006028 * 2 ^ 59
def prefixEnd_3006028 : Nat := 4983230072969 + 3 ^ 40 * 3006028 * 2
def baseEnd_3006028 : Nat := 171504136097074459480615

theorem tailTrace_3006028 : CollatzResearch.WordTrace tailWord_3006028 prefixEnd_3006028 171504136097074459480615 := by
  unfold tailWord_3006028
  simp only [CollatzResearch.WordTrace]
  refine ⟨54819424176840709777273369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73092565569120946369697825 54819424176840709777273369)
  ·
    refine ⟨41114568132630532332955027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54819424176840709777273369 41114568132630532332955027)
    ·
      refine ⟨61671852198945798499432541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41114568132630532332955027 61671852198945798499432541)
      ·
        refine ⟨23126944574604674437287203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61671852198945798499432541 23126944574604674437287203)
        ·
          refine ⟨34690416861907011655930805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23126944574604674437287203 34690416861907011655930805)
          ·
            refine ⟨3252226580803782342743513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34690416861907011655930805 3252226580803782342743513)
            ·
              refine ⟨2439169935602836757057635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3252226580803782342743513 2439169935602836757057635)
              ·
                refine ⟨3658754903404255135586453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2439169935602836757057635 3658754903404255135586453)
                ·
                  refine ⟨171504136097074459480615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3658754903404255135586453 171504136097074459480615)
                  ·
                    rfl

theorem cell23_3006028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 6].length) (baseStart_3006028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006028 prefixEnd_3006028 := by exact prefixLift 3006028
  have htrace : WordTrace (prefixWord ++ tailWord_3006028) baseStart_3006028 baseEnd_3006028 := by
    simpa [prefixWord, tailWord_3006028, baseEnd_3006028] using wordTrace_append hprefix tailTrace_3006028
  have hstable : (prefixWord ++ tailWord_3006028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006028).length < 2 ^ (prefixWord ++ tailWord_3006028).sum := by decide
  have hdescent : baseEnd_3006028 < baseStart_3006028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006031 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 6, 3, 2]
def baseStart_3006031 : Nat := 118140960795 + 3006031 * 2 ^ 59
def prefixEnd_3006031 : Nat := 4983230072969 + 3 ^ 40 * 3006031 * 2
def baseEnd_3006031 : Nat := 1543538765315633623588021

theorem tailTrace_3006031 : CollatzResearch.WordTrace tailWord_3006031 prefixEnd_3006031 1543538765315633623588021 := by
  unfold tailWord_3006031
  simp only [CollatzResearch.WordTrace]
  refine ⟨109638957772670551066905947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73092638515113700711270631 109638957772670551066905947)
  ·
    refine ⟨164458436659005826600358921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109638957772670551066905947 164458436659005826600358921)
    ·
      refine ⟨123343827494254369950269191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164458436659005826600358921 123343827494254369950269191)
      ·
        refine ⟨185015741241381554925403787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123343827494254369950269191 185015741241381554925403787)
        ·
          refine ⟨277523611862072332388105681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185015741241381554925403787 277523611862072332388105681)
          ·
            refine ⟨208142708896554249291079261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277523611862072332388105681 208142708896554249291079261)
            ·
              refine ⟨78053515836207843484154723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208142708896554249291079261 78053515836207843484154723)
              ·
                refine ⟨117080273754311765226232085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78053515836207843484154723 117080273754311765226232085)
                ·
                  refine ⟨5488137832233363994979629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 117080273754311765226232085 5488137832233363994979629)
                  ·
                    refine ⟨2058051687087511498117361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5488137832233363994979629 2058051687087511498117361)
                    ·
                      refine ⟨1543538765315633623588021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2058051687087511498117361 1543538765315633623588021)
                      ·
                        rfl

theorem cell23_3006031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 3, 2].length) (baseStart_3006031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006031 prefixEnd_3006031 := by exact prefixLift 3006031
  have htrace : WordTrace (prefixWord ++ tailWord_3006031) baseStart_3006031 baseEnd_3006031 := by
    simpa [prefixWord, tailWord_3006031, baseEnd_3006031] using wordTrace_append hprefix tailTrace_3006031
  have hstable : (prefixWord ++ tailWord_3006031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006031).length < 2 ^ (prefixWord ++ tailWord_3006031).sum := by decide
  have hdescent : baseEnd_3006031 < baseStart_3006031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006074 : List Nat := [3, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6]
def baseStart_3006074 : Nat := 118140960795 + 3006074 * 2 ^ 59
def prefixEnd_3006074 : Nat := 4983230072969 + 3 ^ 40 * 3006074 * 2
def baseEnd_3006074 : Nat := 1543560844983776955350323

theorem tailTrace_3006074 : CollatzResearch.WordTrace tailWord_3006074 prefixEnd_3006074 1543560844983776955350323 := by
  unfold tailWord_3006074
  simp only [CollatzResearch.WordTrace]
  refine ⟨27410131527878692352680319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73093684074343179607147517 27410131527878692352680319)
  ·
    refine ⟨41115197291818038529020479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27410131527878692352680319 41115197291818038529020479)
    ·
      refine ⟨61672795937727057793530719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41115197291818038529020479 61672795937727057793530719)
      ·
        refine ⟨92509193906590586690296079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61672795937727057793530719 92509193906590586690296079)
        ·
          refine ⟨138763790859885880035444119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92509193906590586690296079 138763790859885880035444119)
          ·
            refine ⟨208145686289828820053166179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138763790859885880035444119 208145686289828820053166179)
            ·
              refine ⟨312218529434743230079749269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208145686289828820053166179 312218529434743230079749269)
              ·
                refine ⟨14635243567253588909988247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 312218529434743230079749269 14635243567253588909988247)
                ·
                  refine ⟨21952865350880383364982371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14635243567253588909988247 21952865350880383364982371)
                  ·
                    refine ⟨32929298026320575047473557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21952865350880383364982371 32929298026320575047473557)
                    ·
                      refine ⟨1543560844983776955350323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32929298026320575047473557 1543560844983776955350323)
                      ·
                        rfl

theorem cell23_3006074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_3006074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006074 prefixEnd_3006074 := by exact prefixLift 3006074
  have htrace : WordTrace (prefixWord ++ tailWord_3006074) baseStart_3006074 baseEnd_3006074 := by
    simpa [prefixWord, tailWord_3006074, baseEnd_3006074] using wordTrace_append hprefix tailTrace_3006074
  have hstable : (prefixWord ++ tailWord_3006074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006074).length < 2 ^ (prefixWord ++ tailWord_3006074).sum := by decide
  have hdescent : baseEnd_3006074 < baseStart_3006074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006091 : List Nat := [1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 4]
def baseStart_3006091 : Nat := 118140960795 + 3006091 * 2 ^ 59
def prefixEnd_3006091 : Nat := 4983230072969 + 3 ^ 40 * 3006091 * 2
def baseEnd_3006091 : Nat := 1543569574154903388837745

theorem tailTrace_3006091 : CollatzResearch.WordTrace tailWord_3006091 prefixEnd_3006091 1543569574154903388837745 := by
  unfold tailWord_3006091
  simp only [CollatzResearch.WordTrace]
  refine ⟨109641146152453181314090127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73094097434968787542726751 109641146152453181314090127)
  ·
    refine ⟨164461719228679771971135191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109641146152453181314090127 164461719228679771971135191)
    ·
      refine ⟨246692578843019657956702787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164461719228679771971135191 246692578843019657956702787)
      ·
        refine ⟨370038868264529486935054181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246692578843019657956702787 370038868264529486935054181)
        ·
          refine ⟨69382287799599278800322659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 370038868264529486935054181 69382287799599278800322659)
          ·
            refine ⟨104073431699398918200483989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69382287799599278800322659 104073431699398918200483989)
            ·
              refine ⟨4878442110909324290647687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 104073431699398918200483989 4878442110909324290647687)
              ·
                refine ⟨7317663166363986435971531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4878442110909324290647687 7317663166363986435971531)
                ·
                  refine ⟨10976494749545979653957297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7317663166363986435971531 10976494749545979653957297)
                  ·
                    refine ⟨8232371062159484740467973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10976494749545979653957297 8232371062159484740467973)
                    ·
                      refine ⟨1543569574154903388837745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8232371062159484740467973 1543569574154903388837745)
                      ·
                        rfl

theorem cell23_3006091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 4].length) (baseStart_3006091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006091 prefixEnd_3006091 := by exact prefixLift 3006091
  have htrace : WordTrace (prefixWord ++ tailWord_3006091) baseStart_3006091 baseEnd_3006091 := by
    simpa [prefixWord, tailWord_3006091, baseEnd_3006091] using wordTrace_append hprefix tailTrace_3006091
  have hstable : (prefixWord ++ tailWord_3006091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006091).length < 2 ^ (prefixWord ++ tailWord_3006091).sum := by decide
  have hdescent : baseEnd_3006091 < baseStart_3006091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006112 : List Nat := [2, 1, 1, 4, 3, 1, 1, 5, 1, 2, 2]
def baseStart_3006112 : Nat := 118140960795 + 3006112 * 2 ^ 59
def prefixEnd_3006112 : Nat := 4983230072969 + 3 ^ 40 * 3006112 * 2
def baseEnd_3006112 : Nat := 1543580357248647806675149

theorem tailTrace_3006112 : CollatzResearch.WordTrace tailWord_3006112 prefixEnd_3006112 1543580357248647806675149 := by
  unfold tailWord_3006112
  simp only [CollatzResearch.WordTrace]
  refine ⟨54820956042688550950302295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73094608056918067933736393 54820956042688550950302295)
  ·
    refine ⟨82231434064032826425453443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54820956042688550950302295 82231434064032826425453443)
    ·
      refine ⟨123347151096049239638180165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82231434064032826425453443 123347151096049239638180165)
      ·
        refine ⟨23127590830509232432158781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123347151096049239638180165 23127590830509232432158781)
        ·
          refine ⟨8672846561440962162059543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23127590830509232432158781 8672846561440962162059543)
          ·
            refine ⟨13009269842161443243089315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8672846561440962162059543 13009269842161443243089315)
            ·
              refine ⟨19513904763242164864633973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13009269842161443243089315 19513904763242164864633973)
              ·
                refine ⟨1829428571553952956059435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19513904763242164864633973 1829428571553952956059435)
                ·
                  refine ⟨2744142857330929434089153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1829428571553952956059435 2744142857330929434089153)
                  ·
                    refine ⟨2058107142998197075566865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2744142857330929434089153 2058107142998197075566865)
                    ·
                      refine ⟨1543580357248647806675149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2058107142998197075566865 1543580357248647806675149)
                      ·
                        rfl

theorem cell23_3006112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_3006112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006112 prefixEnd_3006112 := by exact prefixLift 3006112
  have htrace : WordTrace (prefixWord ++ tailWord_3006112) baseStart_3006112 baseEnd_3006112 := by
    simpa [prefixWord, tailWord_3006112, baseEnd_3006112] using wordTrace_append hprefix tailTrace_3006112
  have hstable : (prefixWord ++ tailWord_3006112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006112).length < 2 ^ (prefixWord ++ tailWord_3006112).sum := by decide
  have hdescent : baseEnd_3006112 < baseStart_3006112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006121 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 1, 9, 2]
def baseStart_3006121 : Nat := 118140960795 + 3006121 * 2 ^ 59
def prefixEnd_3006121 : Nat := 4983230072969 + 3 ^ 40 * 3006121 * 2
def baseEnd_3006121 : Nat := 1543584978574538271462607

theorem tailTrace_3006121 : CollatzResearch.WordTrace tailWord_3006121 prefixEnd_3006121 1543584978574538271462607 := by
  unfold tailWord_3006121
  simp only [CollatzResearch.WordTrace]
  refine ⟨109642240342344496437682217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73094826894896330958454811 109642240342344496437682217)
  ·
    refine ⟨82231680256758372328261663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109642240342344496437682217 82231680256758372328261663)
    ·
      refine ⟨123347520385137558492392495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82231680256758372328261663 123347520385137558492392495)
      ·
        refine ⟨185021280577706337738588743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123347520385137558492392495 185021280577706337738588743)
        ·
          refine ⟨277531920866559506607883115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185021280577706337738588743 277531920866559506607883115)
          ·
            refine ⟨416297881299839259911824673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277531920866559506607883115 416297881299839259911824673)
            ·
              refine ⟨312223410974879444933868505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416297881299839259911824673 312223410974879444933868505)
              ·
                refine ⟨234167558231159583700401379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 312223410974879444933868505 234167558231159583700401379)
                ·
                  refine ⟨351251337346739375550602069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 234167558231159583700401379 351251337346739375550602069)
                  ·
                    refine ⟨2058113304766051028616809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 351251337346739375550602069 2058113304766051028616809)
                    ·
                      refine ⟨1543584978574538271462607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2058113304766051028616809 1543584978574538271462607)
                      ·
                        rfl

theorem cell23_3006121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 9, 2].length) (baseStart_3006121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006121 prefixEnd_3006121 := by exact prefixLift 3006121
  have htrace : WordTrace (prefixWord ++ tailWord_3006121) baseStart_3006121 baseEnd_3006121 := by
    simpa [prefixWord, tailWord_3006121, baseEnd_3006121] using wordTrace_append hprefix tailTrace_3006121
  have hstable : (prefixWord ++ tailWord_3006121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006121).length < 2 ^ (prefixWord ++ tailWord_3006121).sum := by decide
  have hdescent : baseEnd_3006121 < baseStart_3006121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006168 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 3, 4, 2]
def baseStart_3006168 : Nat := 118140960795 + 3006168 * 2 ^ 59
def prefixEnd_3006168 : Nat := 4983230072969 + 3 ^ 40 * 3006168 * 2
def baseEnd_3006168 : Nat := 1543609112165299587574891

theorem tailTrace_3006168 : CollatzResearch.WordTrace tailWord_3006168 prefixEnd_3006168 1543609112165299587574891 := by
  unfold tailWord_3006168
  simp only [CollatzResearch.WordTrace]
  refine ⟨54821977286587111732321579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73095969715449482309762105 54821977286587111732321579)
  ·
    refine ⟨82232965929880667598482369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54821977286587111732321579 82232965929880667598482369)
    ·
      refine ⟨61674724447410500698861777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82232965929880667598482369 61674724447410500698861777)
      ·
        refine ⟨46256043335557875524146333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61674724447410500698861777 46256043335557875524146333)
        ·
          refine ⟨17346016250834203321554875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46256043335557875524146333 17346016250834203321554875)
          ·
            refine ⟨26019024376251304982332313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17346016250834203321554875 26019024376251304982332313)
            ·
              refine ⟨19514268282188478736749235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26019024376251304982332313 19514268282188478736749235)
              ·
                refine ⟨29271402423282718105123853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19514268282188478736749235 29271402423282718105123853)
                ·
                  refine ⟨10976775908731019289421445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29271402423282718105123853 10976775908731019289421445)
                  ·
                    refine ⟨2058145482887066116766521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10976775908731019289421445 2058145482887066116766521)
                    ·
                      refine ⟨1543609112165299587574891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2058145482887066116766521 1543609112165299587574891)
                      ·
                        rfl

theorem cell23_3006168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 3, 4, 2].length) (baseStart_3006168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006168 prefixEnd_3006168 := by exact prefixLift 3006168
  have htrace : WordTrace (prefixWord ++ tailWord_3006168) baseStart_3006168 baseEnd_3006168 := by
    simpa [prefixWord, tailWord_3006168, baseEnd_3006168] using wordTrace_append hprefix tailTrace_3006168
  have hstable : (prefixWord ++ tailWord_3006168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006168).length < 2 ^ (prefixWord ++ tailWord_3006168).sum := by decide
  have hdescent : baseEnd_3006168 < baseStart_3006168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006185 : List Nat := [1, 2, 1, 1, 1, 2, 3, 6, 2, 2, 2]
def baseStart_3006185 : Nat := 118140960795 + 3006185 * 2 ^ 59
def prefixEnd_3006185 : Nat := 4983230072969 + 3 ^ 40 * 3006185 * 2
def baseEnd_3006185 : Nat := 1543617841336426021062313

theorem tailTrace_3006185 : CollatzResearch.WordTrace tailWord_3006185 prefixEnd_3006185 1543617841336426021062313 := by
  unfold tailWord_3006185
  simp only [CollatzResearch.WordTrace]
  refine ⟨109644574614112635368012009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73096383076075090245341339 109644574614112635368012009)
  ·
    refine ⟨82233430960584476526009007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109644574614112635368012009 82233430960584476526009007)
    ·
      refine ⟨123350146440876714789013511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82233430960584476526009007 123350146440876714789013511)
      ·
        refine ⟨185025219661315072183520267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123350146440876714789013511 185025219661315072183520267)
        ·
          refine ⟨277537829491972608275280401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185025219661315072183520267 277537829491972608275280401)
          ·
            refine ⟨208153372118979456206460301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277537829491972608275280401 208153372118979456206460301)
            ·
              refine ⟨78057514544617296077422613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208153372118979456206460301 78057514544617296077422613)
              ·
                refine ⟨3658945994278935753629185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78057514544617296077422613 3658945994278935753629185)
                ·
                  refine ⟨2744209495709201815221889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3658945994278935753629185 2744209495709201815221889)
                  ·
                    refine ⟨2058157121781901361416417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2744209495709201815221889 2058157121781901361416417)
                    ·
                      refine ⟨1543617841336426021062313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2058157121781901361416417 1543617841336426021062313)
                      ·
                        rfl

theorem cell23_3006185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2, 2, 2].length) (baseStart_3006185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006185 prefixEnd_3006185 := by exact prefixLift 3006185
  have htrace : WordTrace (prefixWord ++ tailWord_3006185) baseStart_3006185 baseEnd_3006185 := by
    simpa [prefixWord, tailWord_3006185, baseEnd_3006185] using wordTrace_append hprefix tailTrace_3006185
  have hstable : (prefixWord ++ tailWord_3006185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006185).length < 2 ^ (prefixWord ++ tailWord_3006185).sum := by decide
  have hdescent : baseEnd_3006185 < baseStart_3006185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006196 : List Nat := [2, 6, 1, 1, 1, 1, 4, 1, 2, 1, 3]
def baseStart_3006196 : Nat := 118140960795 + 3006196 * 2 ^ 59
def prefixEnd_3006196 : Nat := 4983230072969 + 3 ^ 40 * 3006196 * 2
def baseEnd_3006196 : Nat := 1543623489623625478024763

theorem tailTrace_3006196 : CollatzResearch.WordTrace tailWord_3006196 prefixEnd_3006196 1543623489623625478024763 := by
  unfold tailWord_3006196
  simp only [CollatzResearch.WordTrace]
  refine ⟨54822487908536392123331221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73096650544715189497774961 54822487908536392123331221)
  ·
    refine ⟨2569804120712643380781151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54822487908536392123331221 2569804120712643380781151)
    ·
      refine ⟨3854706181068965071171727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2569804120712643380781151 3854706181068965071171727)
      ·
        refine ⟨5782059271603447606757591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3854706181068965071171727 5782059271603447606757591)
        ·
          refine ⟨8673088907405171410136387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5782059271603447606757591 8673088907405171410136387)
          ·
            refine ⟨13009633361107757115204581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8673088907405171410136387 13009633361107757115204581)
            ·
              refine ⟨2439306255207704459100859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13009633361107757115204581 2439306255207704459100859)
              ·
                refine ⟨3658959382811556688651289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2439306255207704459100859 3658959382811556688651289)
                ·
                  refine ⟨2744219537108667516488467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3658959382811556688651289 2744219537108667516488467)
                  ·
                    refine ⟨4116329305663001274732701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2744219537108667516488467 4116329305663001274732701)
                    ·
                      refine ⟨1543623489623625478024763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4116329305663001274732701 1543623489623625478024763)
                      ·
                        rfl

theorem cell23_3006196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_3006196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006196 prefixEnd_3006196 := by exact prefixLift 3006196
  have htrace : WordTrace (prefixWord ++ tailWord_3006196) baseStart_3006196 baseEnd_3006196 := by
    simpa [prefixWord, tailWord_3006196, baseEnd_3006196] using wordTrace_append hprefix tailTrace_3006196
  have hstable : (prefixWord ++ tailWord_3006196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006196).length < 2 ^ (prefixWord ++ tailWord_3006196).sum := by decide
  have hdescent : baseEnd_3006196 < baseStart_3006196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006206 : List Nat := [4, 2, 2, 1, 4, 1, 1, 2, 1, 3, 2]
def baseStart_3006206 : Nat := 118140960795 + 3006206 * 2 ^ 59
def prefixEnd_3006206 : Nat := 4983230072969 + 3 ^ 40 * 3006206 * 2
def baseEnd_3006206 : Nat := 1543628624430170438899717

theorem tailTrace_3006206 : CollatzResearch.WordTrace tailWord_3006206 prefixEnd_3006206 1543628624430170438899717 := by
  unfold tailWord_3006206
  simp only [CollatzResearch.WordTrace]
  refine ⟨13705667568379569494315809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73096893698024370636350981 13705667568379569494315809)
  ·
    refine ⟨10279250676284677120736857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13705667568379569494315809 10279250676284677120736857)
    ·
      refine ⟨7709438007213507840552643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10279250676284677120736857 7709438007213507840552643)
      ·
        refine ⟨11564157010820261760828965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7709438007213507840552643 11564157010820261760828965)
        ·
          refine ⟨2168279439528799080155431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11564157010820261760828965 2168279439528799080155431)
          ·
            refine ⟨3252419159293198620233147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2168279439528799080155431 3252419159293198620233147)
            ·
              refine ⟨4878628738939797930349721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3252419159293198620233147 4878628738939797930349721)
              ·
                refine ⟨3658971554204848447762291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4878628738939797930349721 3658971554204848447762291)
                ·
                  refine ⟨5488457331307272671643437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3658971554204848447762291 5488457331307272671643437)
                  ·
                    refine ⟨2058171499240227251866289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5488457331307272671643437 2058171499240227251866289)
                    ·
                      refine ⟨1543628624430170438899717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2058171499240227251866289 1543628624430170438899717)
                      ·
                        rfl

theorem cell23_3006206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_3006206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006206 prefixEnd_3006206 := by exact prefixLift 3006206
  have htrace : WordTrace (prefixWord ++ tailWord_3006206) baseStart_3006206 baseEnd_3006206 := by
    simpa [prefixWord, tailWord_3006206, baseEnd_3006206] using wordTrace_append hprefix tailTrace_3006206
  have hstable : (prefixWord ++ tailWord_3006206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006206).length < 2 ^ (prefixWord ++ tailWord_3006206).sum := by decide
  have hdescent : baseEnd_3006206 < baseStart_3006206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006248 : List Nat := [2, 1, 5, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_3006248 : Nat := 118140960795 + 3006248 * 2 ^ 59
def prefixEnd_3006248 : Nat := 4983230072969 + 3 ^ 40 * 3006248 * 2
def baseEnd_3006248 : Nat := 1543650190617659274574523

theorem tailTrace_3006248 : CollatzResearch.WordTrace tailWord_3006248 prefixEnd_3006248 1543650190617659274574523 := by
  unfold tailWord_3006248
  simp only [CollatzResearch.WordTrace]
  refine ⟨54823436206442198563777699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73097914941922931418370265 54823436206442198563777699)
  ·
    refine ⟨82235154309663297845666549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54823436206442198563777699 82235154309663297845666549)
    ·
      refine ⟨7709545716530934173031239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82235154309663297845666549 7709545716530934173031239)
      ·
        refine ⟨11564318574796401259546859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7709545716530934173031239 11564318574796401259546859)
        ·
          refine ⟨17346477862194601889320289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11564318574796401259546859 17346477862194601889320289)
          ·
            refine ⟨13009858396645951416990217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17346477862194601889320289 13009858396645951416990217)
            ·
              refine ⟨9757393797484463562742663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13009858396645951416990217 9757393797484463562742663)
              ·
                refine ⟨14636090696226695344113995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9757393797484463562742663 14636090696226695344113995)
                ·
                  refine ⟨21954136044340043016170993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14636090696226695344113995 21954136044340043016170993)
                  ·
                    refine ⟨16465602033255032262128245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21954136044340043016170993 16465602033255032262128245)
                    ·
                      refine ⟨1543650190617659274574523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16465602033255032262128245 1543650190617659274574523)
                      ·
                        rfl

theorem cell23_3006248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_3006248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006248 prefixEnd_3006248 := by exact prefixLift 3006248
  have htrace : WordTrace (prefixWord ++ tailWord_3006248) baseStart_3006248 baseEnd_3006248 := by
    simpa [prefixWord, tailWord_3006248, baseEnd_3006248] using wordTrace_append hprefix tailTrace_3006248
  have hstable : (prefixWord ++ tailWord_3006248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006248).length < 2 ^ (prefixWord ++ tailWord_3006248).sum := by decide
  have hdescent : baseEnd_3006248 < baseStart_3006248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006268 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 5, 4]
def baseStart_3006268 : Nat := 118140960795 + 3006268 * 2 ^ 59
def prefixEnd_3006268 : Nat := 4983230072969 + 3 ^ 40 * 3006268 * 2
def baseEnd_3006268 : Nat := 514553486743583065441477

theorem tailTrace_3006268 : CollatzResearch.WordTrace tailWord_3006268 prefixEnd_3006268 514553486743583065441477 := by
  unfold tailWord_3006268
  simp only [CollatzResearch.WordTrace]
  refine ⟨54823800936405970271641729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73098401248541293695522305 54823800936405970271641729)
  ·
    refine ⟨41117850702304477703731297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54823800936405970271641729 41117850702304477703731297)
    ·
      refine ⟨30838388026728358277798473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41117850702304477703731297 30838388026728358277798473)
      ·
        refine ⟨23128791020046268708348855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30838388026728358277798473 23128791020046268708348855)
        ·
          refine ⟨34693186530069403062523283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23128791020046268708348855 34693186530069403062523283)
          ·
            refine ⟨52039779795104104593784925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34693186530069403062523283 52039779795104104593784925)
            ·
              refine ⟨19514917423164039222669347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52039779795104104593784925 19514917423164039222669347)
              ·
                refine ⟨29272376134746058834004021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19514917423164039222669347 29272376134746058834004021)
                ·
                  refine ⟨2744285262632443015687877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29272376134746058834004021 2744285262632443015687877)
                  ·
                    refine ⟨514553486743583065441477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2744285262632443015687877 514553486743583065441477)
                    ·
                      rfl

theorem cell23_3006268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_3006268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006268 prefixEnd_3006268 := by exact prefixLift 3006268
  have htrace : WordTrace (prefixWord ++ tailWord_3006268) baseStart_3006268 baseEnd_3006268 := by
    simpa [prefixWord, tailWord_3006268, baseEnd_3006268] using wordTrace_append hprefix tailTrace_3006268
  have hstable : (prefixWord ++ tailWord_3006268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006268).length < 2 ^ (prefixWord ++ tailWord_3006268).sum := by decide
  have hdescent : baseEnd_3006268 < baseStart_3006268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006275 : List Nat := [1, 1, 1, 3, 1, 7, 1, 1, 2, 1, 4]
def baseStart_3006275 : Nat := 118140960795 + 3006275 * 2 ^ 59
def prefixEnd_3006275 : Nat := 4983230072969 + 3 ^ 40 * 3006275 * 2
def baseEnd_3006275 : Nat := 1543664054595330668936899

theorem tailTrace_3006275 : CollatzResearch.WordTrace tailWord_3006275 prefixEnd_3006275 1543664054595330668936899 := by
  unfold tailWord_3006275
  simp only [CollatzResearch.WordTrace]
  refine ⟨109647857183786580738788279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73098571455857720492525519 109647857183786580738788279)
  ·
    refine ⟨164471785775679871108182419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109647857183786580738788279 164471785775679871108182419)
    ·
      refine ⟨246707678663519806662273629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164471785775679871108182419 246707678663519806662273629)
      ·
        refine ⟨92515379498819927498352611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246707678663519806662273629 92515379498819927498352611)
        ·
          refine ⟨138773069248229891247528917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92515379498819927498352611 138773069248229891247528917)
          ·
            refine ⟨3252493810505388076113959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 138773069248229891247528917 3252493810505388076113959)
            ·
              refine ⟨4878740715758082114170939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3252493810505388076113959 4878740715758082114170939)
              ·
                refine ⟨7318111073637123171256409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4878740715758082114170939 7318111073637123171256409)
                ·
                  refine ⟨5488583305227842378442307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7318111073637123171256409 5488583305227842378442307)
                  ·
                    refine ⟨8232874957841763567663461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5488583305227842378442307 8232874957841763567663461)
                    ·
                      refine ⟨1543664054595330668936899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8232874957841763567663461 1543664054595330668936899)
                      ·
                        rfl

theorem cell23_3006275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 1, 4].length) (baseStart_3006275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006275 prefixEnd_3006275 := by exact prefixLift 3006275
  have htrace : WordTrace (prefixWord ++ tailWord_3006275) baseStart_3006275 baseEnd_3006275 := by
    simpa [prefixWord, tailWord_3006275, baseEnd_3006275] using wordTrace_append hprefix tailTrace_3006275
  have hstable : (prefixWord ++ tailWord_3006275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006275).length < 2 ^ (prefixWord ++ tailWord_3006275).sum := by decide
  have hdescent : baseEnd_3006275 < baseStart_3006275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006281 : List Nat := [1, 2, 1, 1, 2, 4, 2, 2, 8]
def baseStart_3006281 : Nat := 118140960795 + 3006281 * 2 ^ 59
def prefixEnd_3006281 : Nat := 4983230072969 + 3 ^ 40 * 3006281 * 2
def baseEnd_3006281 : Nat := 171518570608806405051319

theorem tailTrace_3006281 : CollatzResearch.WordTrace tailWord_3006281 prefixEnd_3006281 171518570608806405051319 := by
  unfold tailWord_3006281
  simp only [CollatzResearch.WordTrace]
  refine ⟨109648076021764843763506697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73098717347843229175671131 109648076021764843763506697)
  ·
    refine ⟨82236057016323632822630023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109648076021764843763506697 82236057016323632822630023)
    ·
      refine ⟨123354085524485449233945035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82236057016323632822630023 123354085524485449233945035)
      ·
        refine ⟨185031128286728173850917553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123354085524485449233945035 185031128286728173850917553)
        ·
          refine ⟨138773346215046130388188165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185031128286728173850917553 138773346215046130388188165)
          ·
            refine ⟨26020002415321149447785281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138773346215046130388188165 26020002415321149447785281)
            ·
              refine ⟨19515001811490862085838961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26020002415321149447785281 19515001811490862085838961)
              ·
                refine ⟨14636251358618146564379221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19515001811490862085838961 14636251358618146564379221)
                ·
                  refine ⟨171518570608806405051319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14636251358618146564379221 171518570608806405051319)
                  ·
                    rfl

theorem cell23_3006281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 8].length) (baseStart_3006281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006281 prefixEnd_3006281 := by exact prefixLift 3006281
  have htrace : WordTrace (prefixWord ++ tailWord_3006281) baseStart_3006281 baseEnd_3006281 := by
    simpa [prefixWord, tailWord_3006281, baseEnd_3006281] using wordTrace_append hprefix tailTrace_3006281
  have hstable : (prefixWord ++ tailWord_3006281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006281).length < 2 ^ (prefixWord ++ tailWord_3006281).sum := by decide
  have hdescent : baseEnd_3006281 < baseStart_3006281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006335 : List Nat := [1, 1, 2, 2, 1, 1, 3, 5, 2, 3, 2]
def baseStart_3006335 : Nat := 118140960795 + 3006335 * 2 ^ 59
def prefixEnd_3006335 : Nat := 4983230072969 + 3 ^ 40 * 3006335 * 2
def baseEnd_3006335 : Nat := 1543694863434600434186623

theorem tailTrace_3006335 : CollatzResearch.WordTrace tailWord_3006335 prefixEnd_3006335 1543694863434600434186623 := by
  unfold tailWord_3006335
  simp only [CollatzResearch.WordTrace]
  refine ⟨109650045563569210985972459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73100030375712807323981639 109650045563569210985972459)
  ·
    refine ⟨164475068345353816478958689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109650045563569210985972459 164475068345353816478958689)
    ·
      refine ⟨123356301259015362359219017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164475068345353816478958689 123356301259015362359219017)
      ·
        refine ⟨92517225944261521769414263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123356301259015362359219017 92517225944261521769414263)
        ·
          refine ⟨138775838916392282654121395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92517225944261521769414263 138775838916392282654121395)
          ·
            refine ⟨208163758374588423981182093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138775838916392282654121395 208163758374588423981182093)
            ·
              refine ⟨78061409390470658992943285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208163758374588423981182093 78061409390470658992943285)
              ·
                refine ⟨7318257130356624280588433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78061409390470658992943285 7318257130356624280588433)
                ·
                  refine ⟨5488692847767468210441325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7318257130356624280588433 5488692847767468210441325)
                  ·
                    refine ⟨2058259817912800578915497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5488692847767468210441325 2058259817912800578915497)
                    ·
                      refine ⟨1543694863434600434186623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2058259817912800578915497 1543694863434600434186623)
                      ·
                        rfl

theorem cell23_3006335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 3, 2].length) (baseStart_3006335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006335 prefixEnd_3006335 := by exact prefixLift 3006335
  have htrace : WordTrace (prefixWord ++ tailWord_3006335) baseStart_3006335 baseEnd_3006335 := by
    simpa [prefixWord, tailWord_3006335, baseEnd_3006335] using wordTrace_append hprefix tailTrace_3006335
  have hstable : (prefixWord ++ tailWord_3006335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006335).length < 2 ^ (prefixWord ++ tailWord_3006335).sum := by decide
  have hdescent : baseEnd_3006335 < baseStart_3006335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006348 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 5, 1, 4]
def baseStart_3006348 : Nat := 118140960795 + 3006348 * 2 ^ 59
def prefixEnd_3006348 : Nat := 4983230072969 + 3 ^ 40 * 3006348 * 2
def baseEnd_3006348 : Nat := 1543701538683108883324063

theorem tailTrace_3006348 : CollatzResearch.WordTrace tailWord_3006348 prefixEnd_3006348 1543701538683108883324063 := by
  unfold tailWord_3006348
  simp only [CollatzResearch.WordTrace]
  refine ⟨54825259856261057103097849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73100346475014742804130465 54825259856261057103097849)
  ·
    refine ⟨41118944892195792827323387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54825259856261057103097849 41118944892195792827323387)
    ·
      refine ⟨61678417338293689240985081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41118944892195792827323387 61678417338293689240985081)
      ·
        refine ⟨46258813003720266930738811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61678417338293689240985081 46258813003720266930738811)
        ·
          refine ⟨69388219505580400396108217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46258813003720266930738811 69388219505580400396108217)
          ·
            refine ⟨52041164629185300297081163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69388219505580400396108217 52041164629185300297081163)
            ·
              refine ⟨78061746943777950445621745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52041164629185300297081163 78061746943777950445621745)
              ·
                refine ⟨58546310207833462834216309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78061746943777950445621745 58546310207833462834216309)
                ·
                  refine ⟨5488716581984387140707779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58546310207833462834216309 5488716581984387140707779)
                  ·
                    refine ⟨8233074872976580711061669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5488716581984387140707779 8233074872976580711061669)
                    ·
                      refine ⟨1543701538683108883324063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8233074872976580711061669 1543701538683108883324063)
                      ·
                        rfl

theorem cell23_3006348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_3006348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006348 prefixEnd_3006348 := by exact prefixLift 3006348
  have htrace : WordTrace (prefixWord ++ tailWord_3006348) baseStart_3006348 baseEnd_3006348 := by
    simpa [prefixWord, tailWord_3006348, baseEnd_3006348] using wordTrace_append hprefix tailTrace_3006348
  have hstable : (prefixWord ++ tailWord_3006348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006348).length < 2 ^ (prefixWord ++ tailWord_3006348).sum := by decide
  have hdescent : baseEnd_3006348 < baseStart_3006348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006366 : List Nat := [4, 3, 1, 3, 1, 2, 2, 1, 6]
def baseStart_3006366 : Nat := 118140960795 + 3006366 * 2 ^ 59
def prefixEnd_3006366 : Nat := 4983230072969 + 3 ^ 40 * 3006366 * 2
def baseEnd_3006366 : Nat := 171523420148321090322109

theorem tailTrace_3006366 : CollatzResearch.WordTrace tailWord_3006366 prefixEnd_3006366 171523420148321090322109 := by
  unfold tailWord_3006366
  simp only [CollatzResearch.WordTrace]
  refine ⟨13706397028307112910043869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73100784150971268853567301 13706397028307112910043869)
  ·
    refine ⟨5139898885615167341266451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13706397028307112910043869 5139898885615167341266451)
    ·
      refine ⟨7709848328422751011899677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5139898885615167341266451 7709848328422751011899677)
      ·
        refine ⟨2891193123158531629462379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7709848328422751011899677 2891193123158531629462379)
        ·
          refine ⟨4336789684737797444193569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2891193123158531629462379 4336789684737797444193569)
          ·
            refine ⟨3252592263553348083145177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4336789684737797444193569 3252592263553348083145177)
            ·
              refine ⟨2439444197665011062358883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3252592263553348083145177 2439444197665011062358883)
              ·
                refine ⟨3659166296497516593538325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2439444197665011062358883 3659166296497516593538325)
                ·
                  refine ⟨171523420148321090322109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3659166296497516593538325 171523420148321090322109)
                  ·
                    rfl

theorem cell23_3006366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_3006366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006366 prefixEnd_3006366 := by exact prefixLift 3006366
  have htrace : WordTrace (prefixWord ++ tailWord_3006366) baseStart_3006366 baseEnd_3006366 := by
    simpa [prefixWord, tailWord_3006366, baseEnd_3006366] using wordTrace_append hprefix tailTrace_3006366
  have hstable : (prefixWord ++ tailWord_3006366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006366).length < 2 ^ (prefixWord ++ tailWord_3006366).sum := by decide
  have hdescent : baseEnd_3006366 < baseStart_3006366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006368 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 3]
def baseStart_3006368 : Nat := 118140960795 + 3006368 * 2 ^ 59
def prefixEnd_3006368 : Nat := 4983230072969 + 3 ^ 40 * 3006368 * 2
def baseEnd_3006368 : Nat := 1543711808296198805073971

theorem tailTrace_3006368 : CollatzResearch.WordTrace tailWord_3006368 prefixEnd_3006368 1543711808296198805073971 := by
  unfold tailWord_3006368
  simp only [CollatzResearch.WordTrace]
  refine ⟨54825624586224828810961879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73100832781633105081282505 54825624586224828810961879)
  ·
    refine ⟨82238436879337243216442819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54825624586224828810961879 82238436879337243216442819)
    ·
      refine ⟨123357655319005864824664229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82238436879337243216442819 123357655319005864824664229)
      ·
        refine ⟨23129560372313599654624543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123357655319005864824664229 23129560372313599654624543)
        ·
          refine ⟨34694340558470399481936815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23129560372313599654624543 34694340558470399481936815)
          ·
            refine ⟨52041510837705599222905223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34694340558470399481936815 52041510837705599222905223)
            ·
              refine ⟨78062266256558398834357835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52041510837705599222905223 78062266256558398834357835)
              ·
                refine ⟨117093399384837598251536753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78062266256558398834357835 117093399384837598251536753)
                ·
                  refine ⟨87820049538628198688652565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117093399384837598251536753 87820049538628198688652565)
                  ·
                    refine ⟨4116564822123196813530589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87820049538628198688652565 4116564822123196813530589)
                    ·
                      refine ⟨1543711808296198805073971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4116564822123196813530589 1543711808296198805073971)
                      ·
                        rfl

theorem cell23_3006368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_3006368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006368 prefixEnd_3006368 := by exact prefixLift 3006368
  have htrace : WordTrace (prefixWord ++ tailWord_3006368) baseStart_3006368 baseEnd_3006368 := by
    simpa [prefixWord, tailWord_3006368, baseEnd_3006368] using wordTrace_append hprefix tailTrace_3006368
  have hstable : (prefixWord ++ tailWord_3006368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006368).length < 2 ^ (prefixWord ++ tailWord_3006368).sum := by decide
  have hdescent : baseEnd_3006368 < baseStart_3006368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006399 : List Nat := [1, 1, 2, 2, 2, 1, 4, 5, 1, 2, 2]
def baseStart_3006399 : Nat := 118140960795 + 3006399 * 2 ^ 59
def prefixEnd_3006399 : Nat := 4983230072969 + 3 ^ 40 * 3006399 * 2
def baseEnd_3006399 : Nat := 1543727726196488183786329

theorem tailTrace_3006399 : CollatzResearch.WordTrace tailWord_3006399 prefixEnd_3006399 1543727726196488183786329 := by
  unfold tailWord_3006399
  simp only [CollatzResearch.WordTrace]
  refine ⟨109652379835337349916302251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73101586556891566610868167 109652379835337349916302251)
  ·
    refine ⟨164478569753006024874453377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109652379835337349916302251 164478569753006024874453377)
    ·
      refine ⟨123358927314754518655840033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164478569753006024874453377 123358927314754518655840033)
      ·
        refine ⟨92519195486065888991880025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123358927314754518655840033 92519195486065888991880025)
        ·
          refine ⟨69389396614549416743910019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92519195486065888991880025 69389396614549416743910019)
          ·
            refine ⟨104084094921824125115865029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69389396614549416743910019 104084094921824125115865029)
            ·
              refine ⟨19515767797842023459224693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104084094921824125115865029 19515767797842023459224693)
              ·
                refine ⟨1829603231047689699302315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19515767797842023459224693 1829603231047689699302315)
                ·
                  refine ⟨2744404846571534548953473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1829603231047689699302315 2744404846571534548953473)
                  ·
                    refine ⟨2058303634928650911715105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2744404846571534548953473 2058303634928650911715105)
                    ·
                      refine ⟨1543727726196488183786329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2058303634928650911715105 1543727726196488183786329)
                      ·
                        rfl

theorem cell23_3006399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5, 1, 2, 2].length) (baseStart_3006399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006399 prefixEnd_3006399 := by exact prefixLift 3006399
  have htrace : WordTrace (prefixWord ++ tailWord_3006399) baseStart_3006399 baseEnd_3006399 := by
    simpa [prefixWord, tailWord_3006399, baseEnd_3006399] using wordTrace_append hprefix tailTrace_3006399
  have hstable : (prefixWord ++ tailWord_3006399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006399).length < 2 ^ (prefixWord ++ tailWord_3006399).sum := by decide
  have hdescent : baseEnd_3006399 < baseStart_3006399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006416 : List Nat := [2, 1, 1, 1, 1, 2, 8, 2, 1, 2, 2]
def baseStart_3006416 : Nat := 118140960795 + 3006416 * 2 ^ 59
def prefixEnd_3006416 : Nat := 4983230072969 + 3 ^ 40 * 3006416 * 2
def baseEnd_3006416 : Nat := 1543736455367614617273751

theorem tailTrace_3006416 : CollatzResearch.WordTrace tailWord_3006416 prefixEnd_3006416 1543736455367614617273751 := by
  unfold tailWord_3006416
  simp only [CollatzResearch.WordTrace]
  refine ⟨54826499938137880909835551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73101999917517174546447401 54826499938137880909835551)
  ·
    refine ⟨82239749907206821364753327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54826499938137880909835551 82239749907206821364753327)
    ·
      refine ⟨123359624860810232047129991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82239749907206821364753327 123359624860810232047129991)
      ·
        refine ⟨185039437291215348070694987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123359624860810232047129991 185039437291215348070694987)
        ·
          refine ⟨277559155936823022106042481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185039437291215348070694987 277559155936823022106042481)
          ·
            refine ⟨208169366952617266579531861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277559155936823022106042481 208169366952617266579531861)
            ·
              refine ⟨2439484768975983592728889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 208169366952617266579531861 2439484768975983592728889)
              ·
                refine ⟨1829613576731987694546667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2439484768975983592728889 1829613576731987694546667)
                ·
                  refine ⟨2744420365097981541820001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1829613576731987694546667 2744420365097981541820001)
                  ·
                    refine ⟨2058315273823486156365001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2744420365097981541820001 2058315273823486156365001)
                    ·
                      refine ⟨1543736455367614617273751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2058315273823486156365001 1543736455367614617273751)
                      ·
                        rfl

theorem cell23_3006416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2, 1, 2, 2].length) (baseStart_3006416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006416 prefixEnd_3006416 := by exact prefixLift 3006416
  have htrace : WordTrace (prefixWord ++ tailWord_3006416) baseStart_3006416 baseEnd_3006416 := by
    simpa [prefixWord, tailWord_3006416, baseEnd_3006416] using wordTrace_append hprefix tailTrace_3006416
  have hstable : (prefixWord ++ tailWord_3006416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006416).length < 2 ^ (prefixWord ++ tailWord_3006416).sum := by decide
  have hdescent : baseEnd_3006416 < baseStart_3006416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006442 : List Nat := [3, 1, 3, 1, 2, 1, 1, 3, 3, 3, 2]
def baseStart_3006442 : Nat := 118140960795 + 3006442 * 2 ^ 59
def prefixEnd_3006442 : Nat := 4983230072969 + 3 ^ 40 * 3006442 * 2
def baseEnd_3006442 : Nat := 1543749805864631515548631

theorem tailTrace_3006442 : CollatzResearch.WordTrace tailWord_3006442 prefixEnd_3006442 1543749805864631515548631 := by
  unfold tailWord_3006442
  simp only [CollatzResearch.WordTrace]
  refine ⟨27413487043545392065029395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73102632116121045506745053 27413487043545392065029395)
  ·
    refine ⟨41120230565318088097544093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27413487043545392065029395 41120230565318088097544093)
    ·
      refine ⟨15420086461994283036579035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41120230565318088097544093 15420086461994283036579035)
      ·
        refine ⟨23130129692991424554868553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15420086461994283036579035 23130129692991424554868553)
        ·
          refine ⟨17347597269743568416151415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23130129692991424554868553 17347597269743568416151415)
          ·
            refine ⟨26021395904615352624227123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17347597269743568416151415 26021395904615352624227123)
            ·
              refine ⟨39032093856923028936340685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26021395904615352624227123 39032093856923028936340685)
              ·
                refine ⟨14637035196346135851127757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39032093856923028936340685 14637035196346135851127757)
                ·
                  refine ⟨5488888198629800944172909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14637035196346135851127757 5488888198629800944172909)
                  ·
                    refine ⟨2058333074486175354064841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5488888198629800944172909 2058333074486175354064841)
                    ·
                      refine ⟨1543749805864631515548631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2058333074486175354064841 1543749805864631515548631)
                      ·
                        rfl

theorem cell23_3006442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_3006442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006442 prefixEnd_3006442 := by exact prefixLift 3006442
  have htrace : WordTrace (prefixWord ++ tailWord_3006442) baseStart_3006442 baseEnd_3006442 := by
    simpa [prefixWord, tailWord_3006442, baseEnd_3006442] using wordTrace_append hprefix tailTrace_3006442
  have hstable : (prefixWord ++ tailWord_3006442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006442).length < 2 ^ (prefixWord ++ tailWord_3006442).sum := by decide
  have hdescent : baseEnd_3006442 < baseStart_3006442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006459 : List Nat := [1, 1, 1, 1, 1, 3, 8, 1, 1, 3, 2]
def baseStart_3006459 : Nat := 118140960795 + 3006459 * 2 ^ 59
def prefixEnd_3006459 : Nat := 4983230072969 + 3 ^ 40 * 3006459 * 2
def baseEnd_3006459 : Nat := 1543758535035757949036053

theorem tailTrace_3006459 : CollatzResearch.WordTrace tailWord_3006459 prefixEnd_3006459 1543758535035757949036053 := by
  unfold tailWord_3006459
  simp only [CollatzResearch.WordTrace]
  refine ⟨109654568215119980163486431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73103045476746653442324287 109654568215119980163486431)
  ·
    refine ⟨164481852322679970245229647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109654568215119980163486431 164481852322679970245229647)
    ·
      refine ⟨246722778484019955367844471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164481852322679970245229647 246722778484019955367844471)
      ·
        refine ⟨370084167726029933051766707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246722778484019955367844471 370084167726029933051766707)
        ·
          refine ⟨555126251589044899577650061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370084167726029933051766707 555126251589044899577650061)
          ·
            refine ⟨208172344345891837341618773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 555126251589044899577650061 208172344345891837341618773)
            ·
              refine ⟨2439519660303419968847095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 208172344345891837341618773 2439519660303419968847095)
              ·
                refine ⟨3659279490455129953270643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2439519660303419968847095 3659279490455129953270643)
                ·
                  refine ⟨5488919235682694929905965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3659279490455129953270643 5488919235682694929905965)
                  ·
                    refine ⟨2058344713381010598714737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5488919235682694929905965 2058344713381010598714737)
                    ·
                      refine ⟨1543758535035757949036053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2058344713381010598714737 1543758535035757949036053)
                      ·
                        rfl

theorem cell23_3006459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 1, 3, 2].length) (baseStart_3006459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006459 prefixEnd_3006459 := by exact prefixLift 3006459
  have htrace : WordTrace (prefixWord ++ tailWord_3006459) baseStart_3006459 baseEnd_3006459 := by
    simpa [prefixWord, tailWord_3006459, baseEnd_3006459] using wordTrace_append hprefix tailTrace_3006459
  have hstable : (prefixWord ++ tailWord_3006459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006459).length < 2 ^ (prefixWord ++ tailWord_3006459).sum := by decide
  have hdescent : baseEnd_3006459 < baseStart_3006459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006512 : List Nat := [2, 1, 1, 1, 2, 5, 3, 3, 5]
def baseStart_3006512 : Nat := 118140960795 + 3006512 * 2 ^ 59
def prefixEnd_3006512 : Nat := 4983230072969 + 3 ^ 40 * 3006512 * 2
def baseEnd_3006512 : Nat := 171531749945605137963701

theorem tailTrace_3006512 : CollatzResearch.WordTrace tailWord_3006512 prefixEnd_3006512 171531749945605137963701 := by
  unfold tailWord_3006512
  simp only [CollatzResearch.WordTrace]
  refine ⟨54828250641963985107582895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73104334189285313476777193 54828250641963985107582895)
  ·
    refine ⟨82242375962945977661374343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54828250641963985107582895 82242375962945977661374343)
    ·
      refine ⟨123363563944418966492061515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82242375962945977661374343 123363563944418966492061515)
      ·
        refine ⟨185045345916628449738092273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123363563944418966492061515 185045345916628449738092273)
        ·
          refine ⟨138784009437471337303569205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185045345916628449738092273 138784009437471337303569205)
          ·
            refine ⟨13011000884762937872209613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138784009437471337303569205 13011000884762937872209613)
            ·
              refine ⟨4879125331786101702078605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13011000884762937872209613 4879125331786101702078605)
              ·
                refine ⟨1829671999419788138279477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4879125331786101702078605 1829671999419788138279477)
                ·
                  refine ⟨171531749945605137963701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1829671999419788138279477 171531749945605137963701)
                  ·
                    rfl

theorem cell23_3006512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3, 5].length) (baseStart_3006512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006512 prefixEnd_3006512 := by exact prefixLift 3006512
  have htrace : WordTrace (prefixWord ++ tailWord_3006512) baseStart_3006512 baseEnd_3006512 := by
    simpa [prefixWord, tailWord_3006512, baseEnd_3006512] using wordTrace_append hprefix tailTrace_3006512
  have hstable : (prefixWord ++ tailWord_3006512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006512).length < 2 ^ (prefixWord ++ tailWord_3006512).sum := by decide
  have hdescent : baseEnd_3006512 < baseStart_3006512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006535 : List Nat := [1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 5]
def baseStart_3006535 : Nat := 118140960795 + 3006535 * 2 ^ 59
def prefixEnd_3006535 : Nat := 4983230072969 + 3 ^ 40 * 3006535 * 2
def baseEnd_3006535 : Nat := 1543797559565499651685703

theorem tailTrace_3006535 : CollatzResearch.WordTrace tailWord_3006535 prefixEnd_3006535 1543797559565499651685703 := by
  unfold tailWord_3006535
  simp only [CollatzResearch.WordTrace]
  refine ⟨109657340162844645143253059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73104893441896430095502039 109657340162844645143253059)
  ·
    refine ⟨164486010244266967714879589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109657340162844645143253059 164486010244266967714879589)
    ·
      refine ⟨30841126920800056446539923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164486010244266967714879589 30841126920800056446539923)
      ·
        refine ⟨46261690381200084669809885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30841126920800056446539923 46261690381200084669809885)
        ·
          refine ⟨17348133892950031751178707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46261690381200084669809885 17348133892950031751178707)
          ·
            refine ⟨26022200839425047626768061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17348133892950031751178707 26022200839425047626768061)
            ·
              refine ⟨9758325314784392860038023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26022200839425047626768061 9758325314784392860038023)
              ·
                refine ⟨14637487972176589290057035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9758325314784392860038023 14637487972176589290057035)
                ·
                  refine ⟨21956231958264883935085553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14637487972176589290057035 21956231958264883935085553)
                  ·
                    refine ⟨16467173968698662951314165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21956231958264883935085553 16467173968698662951314165)
                    ·
                      refine ⟨1543797559565499651685703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16467173968698662951314165 1543797559565499651685703)
                      ·
                        rfl

theorem cell23_3006535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_3006535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006535 prefixEnd_3006535 := by exact prefixLift 3006535
  have htrace : WordTrace (prefixWord ++ tailWord_3006535) baseStart_3006535 baseEnd_3006535 := by
    simpa [prefixWord, tailWord_3006535, baseEnd_3006535] using wordTrace_append hprefix tailTrace_3006535
  have hstable : (prefixWord ++ tailWord_3006535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006535).length < 2 ^ (prefixWord ++ tailWord_3006535).sum := by decide
  have hdescent : baseEnd_3006535 < baseStart_3006535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006545 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 6, 1, 4]
def baseStart_3006545 : Nat := 118140960795 + 3006545 * 2 ^ 59
def prefixEnd_3006545 : Nat := 4983230072969 + 3 ^ 40 * 3006545 * 2
def baseEnd_3006545 : Nat := 1543802694372044612560657

theorem tailTrace_3006545 : CollatzResearch.WordTrace tailWord_3006545 prefixEnd_3006545 1543802694372044612560657 := by
  unfold tailWord_3006545
  simp only [CollatzResearch.WordTrace]
  refine ⟨109657704892808416851117089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73105136595205611234078059 109657704892808416851117089)
  ·
    refine ⟨82243278669606312638337817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109657704892808416851117089 82243278669606312638337817)
    ·
      refine ⟨61682459002204734478753363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82243278669606312638337817 61682459002204734478753363)
      ·
        refine ⟨92523688503307101718130045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61682459002204734478753363 92523688503307101718130045)
        ·
          refine ⟨34696383188740163144298767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92523688503307101718130045 34696383188740163144298767)
          ·
            refine ⟨52044574783110244716448151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34696383188740163144298767 52044574783110244716448151)
            ·
              refine ⟨78066862174665367074672227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52044574783110244716448151 78066862174665367074672227)
              ·
                refine ⟨117100293261998050612008341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78066862174665367074672227 117100293261998050612008341)
                ·
                  refine ⟨5489076246656158622437891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 117100293261998050612008341 5489076246656158622437891)
                  ·
                    refine ⟨8233614369984237933656837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5489076246656158622437891 8233614369984237933656837)
                    ·
                      refine ⟨1543802694372044612560657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8233614369984237933656837 1543802694372044612560657)
                      ·
                        rfl

theorem cell23_3006545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_3006545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006545 prefixEnd_3006545 := by exact prefixLift 3006545
  have htrace : WordTrace (prefixWord ++ tailWord_3006545) baseStart_3006545 baseEnd_3006545 := by
    simpa [prefixWord, tailWord_3006545, baseEnd_3006545] using wordTrace_append hprefix tailTrace_3006545
  have hstable : (prefixWord ++ tailWord_3006545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006545).length < 2 ^ (prefixWord ++ tailWord_3006545).sum := by decide
  have hdescent : baseEnd_3006545 < baseStart_3006545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006602 : List Nat := [3, 1, 2, 3, 1, 2, 2, 3, 6]
def baseStart_3006602 : Nat := 118140960795 + 3006602 * 2 ^ 59
def prefixEnd_3006602 : Nat := 4983230072969 + 3 ^ 40 * 3006602 * 2
def baseEnd_3006602 : Nat := 171536884752150098838655

theorem tailTrace_3006602 : CollatzResearch.WordTrace tailWord_3006602 prefixEnd_3006602 171536884752150098838655 := by
  unfold tailWord_3006602
  simp only [CollatzResearch.WordTrace]
  refine ⟨27414945963400478896485515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73106522569067943723961373 27414945963400478896485515)
  ·
    refine ⟨41122418945100718344728273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27414945963400478896485515 41122418945100718344728273)
    ·
      refine ⟨30841814208825538758546205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41122418945100718344728273 30841814208825538758546205)
      ·
        refine ⟨11565680328309577034454827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30841814208825538758546205 11565680328309577034454827)
        ·
          refine ⟨17348520492464365551682241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11565680328309577034454827 17348520492464365551682241)
          ·
            refine ⟨13011390369348274163761681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17348520492464365551682241 13011390369348274163761681)
            ·
              refine ⟨9758542777011205622821261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13011390369348274163761681 9758542777011205622821261)
              ·
                refine ⟨3659453541379202108557973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9758542777011205622821261 3659453541379202108557973)
                ·
                  refine ⟨171536884752150098838655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3659453541379202108557973 171536884752150098838655)
                  ·
                    rfl

theorem cell23_3006602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 6].length) (baseStart_3006602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006602 prefixEnd_3006602 := by exact prefixLift 3006602
  have htrace : WordTrace (prefixWord ++ tailWord_3006602) baseStart_3006602 baseEnd_3006602 := by
    simpa [prefixWord, tailWord_3006602, baseEnd_3006602] using wordTrace_append hprefix tailTrace_3006602
  have hstable : (prefixWord ++ tailWord_3006602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006602).length < 2 ^ (prefixWord ++ tailWord_3006602).sum := by decide
  have hdescent : baseEnd_3006602 < baseStart_3006602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006616 : List Nat := [2, 1, 2, 4, 3, 2, 1, 1, 2, 2, 3]
def baseStart_3006616 : Nat := 118140960795 + 3006616 * 2 ^ 59
def prefixEnd_3006616 : Nat := 4983230072969 + 3 ^ 40 * 3006616 * 2
def baseEnd_3006616 : Nat := 1543839151498513834772831

theorem tailTrace_3006616 : CollatzResearch.WordTrace tailWord_3006616 prefixEnd_3006616 1543839151498513834772831 := by
  unfold tailWord_3006616
  simp only [CollatzResearch.WordTrace]
  refine ⟨54830147237775597988475851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73106862983700797317967801 54830147237775597988475851)
  ·
    refine ⟨82245220856663396982713777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54830147237775597988475851 82245220856663396982713777)
    ·
      refine ⟨61683915642497547737035333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82245220856663396982713777 61683915642497547737035333)
      ·
        refine ⟨11565734182968290200694125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61683915642497547737035333 11565734182968290200694125)
        ·
          refine ⟨4337150318613108825260297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11565734182968290200694125 4337150318613108825260297)
          ·
            refine ⟨3252862738959831618945223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4337150318613108825260297 3252862738959831618945223)
            ·
              refine ⟨4879294108439747428417835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3252862738959831618945223 4879294108439747428417835)
              ·
                refine ⟨7318941162659621142626753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4879294108439747428417835 7318941162659621142626753)
                ·
                  refine ⟨5489205871994715856970065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7318941162659621142626753 5489205871994715856970065)
                  ·
                    refine ⟨4116904403996036892727549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5489205871994715856970065 4116904403996036892727549)
                    ·
                      refine ⟨1543839151498513834772831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4116904403996036892727549 1543839151498513834772831)
                      ·
                        rfl

theorem cell23_3006616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_3006616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006616 prefixEnd_3006616 := by exact prefixLift 3006616
  have htrace : WordTrace (prefixWord ++ tailWord_3006616) baseStart_3006616 baseEnd_3006616 := by
    simpa [prefixWord, tailWord_3006616, baseEnd_3006616] using wordTrace_append hprefix tailTrace_3006616
  have hstable : (prefixWord ++ tailWord_3006616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006616).length < 2 ^ (prefixWord ++ tailWord_3006616).sum := by decide
  have hdescent : baseEnd_3006616 < baseStart_3006616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006682 : List Nat := [3, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4]
def baseStart_3006682 : Nat := 118140960795 + 3006682 * 2 ^ 59
def prefixEnd_3006682 : Nat := 4983230072969 + 3 ^ 40 * 3006682 * 2
def baseEnd_3006682 : Nat := 1543873041221710576547527

theorem tailTrace_3006682 : CollatzResearch.WordTrace tailWord_3006682 prefixEnd_3006682 1543873041221710576547527 := by
  unfold tailWord_3006682
  simp only [CollatzResearch.WordTrace]
  refine ⟨27415675423328022312213575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73108467795541392832569533 27415675423328022312213575)
  ·
    refine ⟨41123513134992033468320363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27415675423328022312213575 41123513134992033468320363)
    ·
      refine ⟨61685269702488050202480545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41123513134992033468320363 61685269702488050202480545)
      ·
        refine ⟨46263952276866037651860409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61685269702488050202480545 46263952276866037651860409)
        ·
          refine ⟨34697964207649528238895307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46263952276866037651860409 34697964207649528238895307)
          ·
            refine ⟨52046946311474292358342961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34697964207649528238895307 52046946311474292358342961)
            ·
              refine ⟨39035209733605719268757221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52046946311474292358342961 39035209733605719268757221)
              ·
                refine ⟨7319101825051072362891979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39035209733605719268757221 7319101825051072362891979)
                ·
                  refine ⟨10978652737576608544337969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7319101825051072362891979 10978652737576608544337969)
                  ·
                    refine ⟨8233989553182456408253477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10978652737576608544337969 8233989553182456408253477)
                    ·
                      refine ⟨1543873041221710576547527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8233989553182456408253477 1543873041221710576547527)
                      ·
                        rfl

theorem cell23_3006682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_3006682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006682 prefixEnd_3006682 := by exact prefixLift 3006682
  have htrace : WordTrace (prefixWord ++ tailWord_3006682) baseStart_3006682 baseEnd_3006682 := by
    simpa [prefixWord, tailWord_3006682, baseEnd_3006682] using wordTrace_append hprefix tailTrace_3006682
  have hstable : (prefixWord ++ tailWord_3006682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006682).length < 2 ^ (prefixWord ++ tailWord_3006682).sum := by decide
  have hdescent : baseEnd_3006682 < baseStart_3006682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006689 : List Nat := [1, 2, 3, 1, 3, 1, 1, 5, 1, 2, 3]
def baseStart_3006689 : Nat := 118140960795 + 3006689 * 2 ^ 59
def prefixEnd_3006689 : Nat := 4983230072969 + 3 ^ 40 * 3006689 * 2
def baseEnd_3006689 : Nat := 1543876635586292049159995

theorem tailTrace_3006689 : CollatzResearch.WordTrace tailWord_3006689 prefixEnd_3006689 1543876635586292049159995 := by
  unfold tailWord_3006689
  simp only [CollatzResearch.WordTrace]
  refine ⟨109662957004286729444359121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73108638002857819629572747 109662957004286729444359121)
  ·
    refine ⟨82247217753215047083269341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109662957004286729444359121 82247217753215047083269341)
    ·
      refine ⟨30842706657455642656226003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82247217753215047083269341 30842706657455642656226003)
      ·
        refine ⟨46264059986183463984339005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30842706657455642656226003 46264059986183463984339005)
        ·
          refine ⟨17349022494818798994127127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46264059986183463984339005 17349022494818798994127127)
          ·
            refine ⟨26023533742228198491190691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17349022494818798994127127 26023533742228198491190691)
            ·
              refine ⟨39035300613342297736786037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26023533742228198491190691 39035300613342297736786037)
              ·
                refine ⟨3659559432500840412823691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39035300613342297736786037 3659559432500840412823691)
                ·
                  refine ⟨5489339148751260619235537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3659559432500840412823691 5489339148751260619235537)
                  ·
                    refine ⟨4117004361563445464426653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5489339148751260619235537 4117004361563445464426653)
                    ·
                      refine ⟨1543876635586292049159995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4117004361563445464426653 1543876635586292049159995)
                      ·
                        rfl

theorem cell23_3006689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_3006689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006689 prefixEnd_3006689 := by exact prefixLift 3006689
  have htrace : WordTrace (prefixWord ++ tailWord_3006689) baseStart_3006689 baseEnd_3006689 := by
    simpa [prefixWord, tailWord_3006689, baseEnd_3006689] using wordTrace_append hprefix tailTrace_3006689
  have hstable : (prefixWord ++ tailWord_3006689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006689).length < 2 ^ (prefixWord ++ tailWord_3006689).sum := by decide
  have hdescent : baseEnd_3006689 < baseStart_3006689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006703 : List Nat := [1, 1, 2, 1, 6, 3, 1, 1, 3, 2, 2]
def baseStart_3006703 : Nat := 118140960795 + 3006703 * 2 ^ 59
def prefixEnd_3006703 : Nat := 4983230072969 + 3 ^ 40 * 3006703 * 2
def baseEnd_3006703 : Nat := 1543883824315454994384931

theorem tailTrace_3006703 : CollatzResearch.WordTrace tailWord_3006703 prefixEnd_3006703 1543883824315454994384931 := by
  unfold tailWord_3006703
  simp only [CollatzResearch.WordTrace]
  refine ⟨109663467626236009835368763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73108978417490673223579175 109663467626236009835368763)
  ·
    refine ⟨164495201439354014753053145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109663467626236009835368763 164495201439354014753053145)
    ·
      refine ⟨123371401079515511064789859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164495201439354014753053145 123371401079515511064789859)
      ·
        refine ⟨185057101619273266597184789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123371401079515511064789859 185057101619273266597184789)
        ·
          refine ⟨8674551638403434371743037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 185057101619273266597184789 8674551638403434371743037)
          ·
            refine ⟨3252956864401287889403639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8674551638403434371743037 3252956864401287889403639)
            ·
              refine ⟨4879435296601931834105459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3252956864401287889403639 4879435296601931834105459)
              ·
                refine ⟨7319152944902897751158189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4879435296601931834105459 7319152944902897751158189)
                ·
                  refine ⟨2744682354338586656684321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7319152944902897751158189 2744682354338586656684321)
                  ·
                    refine ⟨2058511765753939992513241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2744682354338586656684321 2058511765753939992513241)
                    ·
                      refine ⟨1543883824315454994384931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2058511765753939992513241 1543883824315454994384931)
                      ·
                        rfl

theorem cell23_3006703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3, 2, 2].length) (baseStart_3006703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006703 prefixEnd_3006703 := by exact prefixLift 3006703
  have htrace : WordTrace (prefixWord ++ tailWord_3006703) baseStart_3006703 baseEnd_3006703 := by
    simpa [prefixWord, tailWord_3006703, baseEnd_3006703] using wordTrace_append hprefix tailTrace_3006703
  have hstable : (prefixWord ++ tailWord_3006703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006703).length < 2 ^ (prefixWord ++ tailWord_3006703).sum := by decide
  have hdescent : baseEnd_3006703 < baseStart_3006703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006769 : List Nat := [1, 2, 2, 3, 4, 1, 1, 1, 2, 6]
def baseStart_3006769 : Nat := 118140960795 + 3006769 * 2 ^ 59
def prefixEnd_3006769 : Nat := 4983230072969 + 3 ^ 40 * 3006769 * 2
def baseEnd_3006769 : Nat := 514639238012883912053209

theorem tailTrace_3006769 : CollatzResearch.WordTrace tailWord_3006769 prefixEnd_3006769 514639238012883912053209 := by
  unfold tailWord_3006769
  simp only [CollatzResearch.WordTrace]
  refine ⟨109665874843996903107271361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73110583229331268738180907 109665874843996903107271361)
  ·
    refine ⟨82249406132997677330453521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109665874843996903107271361 82249406132997677330453521)
    ·
      refine ⟨61687054599748257997840141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82249406132997677330453521 61687054599748257997840141)
      ·
        refine ⟨23132645474905596749190053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61687054599748257997840141 23132645474905596749190053)
        ·
          refine ⟨4337371026544799390473135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23132645474905596749190053 4337371026544799390473135)
          ·
            refine ⟨6506056539817199085709703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4337371026544799390473135 6506056539817199085709703)
            ·
              refine ⟨9759084809725798628564555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6506056539817199085709703 9759084809725798628564555)
              ·
                refine ⟨14638627214588697942846833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9759084809725798628564555 14638627214588697942846833)
                ·
                  refine ⟨10978970410941523457135125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14638627214588697942846833 10978970410941523457135125)
                  ·
                    refine ⟨514639238012883912053209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10978970410941523457135125 514639238012883912053209)
                    ·
                      rfl

theorem cell23_3006769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 6].length) (baseStart_3006769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006769 prefixEnd_3006769 := by exact prefixLift 3006769
  have htrace : WordTrace (prefixWord ++ tailWord_3006769) baseStart_3006769 baseEnd_3006769 := by
    simpa [prefixWord, tailWord_3006769, baseEnd_3006769] using wordTrace_append hprefix tailTrace_3006769
  have hstable : (prefixWord ++ tailWord_3006769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006769).length < 2 ^ (prefixWord ++ tailWord_3006769).sum := by decide
  have hdescent : baseEnd_3006769 < baseStart_3006769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006826 : List Nat := [3, 1, 3, 3, 1, 1, 2, 1, 2, 3, 3]
def baseStart_3006826 : Nat := 118140960795 + 3006826 * 2 ^ 59
def prefixEnd_3006826 : Nat := 4983230072969 + 3 ^ 40 * 3006826 * 2
def baseEnd_3006826 : Nat := 1543946982435958013146865

theorem tailTrace_3006826 : CollatzResearch.WordTrace tailWord_3006826 prefixEnd_3006826 1543946982435958013146865 := by
  unfold tailWord_3006826
  simp only [CollatzResearch.WordTrace]
  refine ⟨27416988451197600460524083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73111969203193601228064221 27416988451197600460524083)
  ·
    refine ⟨41125482676796400690786125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27416988451197600460524083 41125482676796400690786125)
    ·
      refine ⟨15422056003798650259044797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41125482676796400690786125 15422056003798650259044797)
      ·
        refine ⟨5783271001424493847141799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15422056003798650259044797 5783271001424493847141799)
        ·
          refine ⟨8674906502136740770712699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5783271001424493847141799 8674906502136740770712699)
          ·
            refine ⟨13012359753205111156069049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8674906502136740770712699 13012359753205111156069049)
            ·
              refine ⟨9759269814903833367051787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13012359753205111156069049 9759269814903833367051787)
              ·
                refine ⟨14638904722355750050577681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9759269814903833367051787 14638904722355750050577681)
                ·
                  refine ⟨10979178541766812537933261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14638904722355750050577681 10979178541766812537933261)
                  ·
                    refine ⟨4117191953162554701724973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10979178541766812537933261 4117191953162554701724973)
                    ·
                      refine ⟨1543946982435958013146865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4117191953162554701724973 1543946982435958013146865)
                      ·
                        rfl

theorem cell23_3006826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_3006826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006826 prefixEnd_3006826 := by exact prefixLift 3006826
  have htrace : WordTrace (prefixWord ++ tailWord_3006826) baseStart_3006826 baseEnd_3006826 := by
    simpa [prefixWord, tailWord_3006826, baseEnd_3006826] using wordTrace_append hprefix tailTrace_3006826
  have hstable : (prefixWord ++ tailWord_3006826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006826).length < 2 ^ (prefixWord ++ tailWord_3006826).sum := by decide
  have hdescent : baseEnd_3006826 < baseStart_3006826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006926 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2]
def baseStart_3006926 : Nat := 118140960795 + 3006926 * 2 ^ 59
def prefixEnd_3006926 : Nat := 4983230072969 + 3 ^ 40 * 3006926 * 2
def baseEnd_3006926 : Nat := 1543998330501407621896405

theorem tailTrace_3006926 : CollatzResearch.WordTrace tailWord_3006926 prefixEnd_3006926 1543998330501407621896405 := by
  unfold tailWord_3006926
  simp only [CollatzResearch.WordTrace]
  refine ⟨13708950138053514865092079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73114400736285412613824421 13708950138053514865092079)
  ·
    refine ⟨20563425207080272297638119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13708950138053514865092079 20563425207080272297638119)
    ·
      refine ⟨30845137810620408446457179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20563425207080272297638119 30845137810620408446457179)
      ·
        refine ⟨46267706715930612669685769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30845137810620408446457179 46267706715930612669685769)
        ·
          refine ⟨34700780036947959502264327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46267706715930612669685769 34700780036947959502264327)
          ·
            refine ⟨52051170055421939253396491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34700780036947959502264327 52051170055421939253396491)
            ·
              refine ⟨78076755083132908880094737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52051170055421939253396491 78076755083132908880094737)
              ·
                refine ⟨58557566312349681660071053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78076755083132908880094737 58557566312349681660071053)
                ·
                  refine ⟨21959087367131130622526645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58557566312349681660071053 21959087367131130622526645)
                  ·
                    refine ⟨2058664440668543495861873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21959087367131130622526645 2058664440668543495861873)
                    ·
                      refine ⟨1543998330501407621896405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2058664440668543495861873 1543998330501407621896405)
                      ·
                        rfl

theorem cell23_3006926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2].length) (baseStart_3006926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006926 prefixEnd_3006926 := by exact prefixLift 3006926
  have htrace : WordTrace (prefixWord ++ tailWord_3006926) baseStart_3006926 baseEnd_3006926 := by
    simpa [prefixWord, tailWord_3006926, baseEnd_3006926] using wordTrace_append hprefix tailTrace_3006926
  have hstable : (prefixWord ++ tailWord_3006926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006926).length < 2 ^ (prefixWord ++ tailWord_3006926).sum := by decide
  have hdescent : baseEnd_3006926 < baseStart_3006926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006956 : List Nat := [2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 4]
def baseStart_3006956 : Nat := 118140960795 + 3006956 * 2 ^ 59
def prefixEnd_3006956 : Nat := 4983230072969 + 3 ^ 40 * 3006956 * 2
def baseEnd_3006956 : Nat := 1544013734921042504521267

theorem tailTrace_3006956 : CollatzResearch.WordTrace tailWord_3006956 prefixEnd_3006956 1544013734921042504521267 := by
  unfold tailWord_3006956
  simp only [CollatzResearch.WordTrace]
  refine ⟨54836347647159717022164361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73115130196212956029552481 54836347647159717022164361)
  ·
    refine ⟨41127260735369787766623271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54836347647159717022164361 41127260735369787766623271)
    ·
      refine ⟨61690891103054681649934907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41127260735369787766623271 61690891103054681649934907)
      ·
        refine ⟨92536336654582022474902361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61690891103054681649934907 92536336654582022474902361)
        ·
          refine ⟨69402252490936516856176771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92536336654582022474902361 69402252490936516856176771)
          ·
            refine ⟨104103378736404775284265157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69402252490936516856176771 104103378736404775284265157)
            ·
              refine ⟨19519383513075895365799717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104103378736404775284265157 19519383513075895365799717)
              ·
                refine ⟨3659884408701730381087447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19519383513075895365799717 3659884408701730381087447)
                ·
                  refine ⟨5489826613052595571631171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3659884408701730381087447 5489826613052595571631171)
                  ·
                    refine ⟨8234739919578893357446757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5489826613052595571631171 8234739919578893357446757)
                    ·
                      refine ⟨1544013734921042504521267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8234739919578893357446757 1544013734921042504521267)
                      ·
                        rfl

theorem cell23_3006956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 4].length) (baseStart_3006956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006956 prefixEnd_3006956 := by exact prefixLift 3006956
  have htrace : WordTrace (prefixWord ++ tailWord_3006956) baseStart_3006956 baseEnd_3006956 := by
    simpa [prefixWord, tailWord_3006956, baseEnd_3006956] using wordTrace_append hprefix tailTrace_3006956
  have hstable : (prefixWord ++ tailWord_3006956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006956).length < 2 ^ (prefixWord ++ tailWord_3006956).sum := by decide
  have hdescent : baseEnd_3006956 < baseStart_3006956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006966 : List Nat := [5, 1, 1, 1, 2, 1, 1, 4, 1, 6]
def baseStart_3006966 : Nat := 118140960795 + 3006966 * 2 ^ 59
def prefixEnd_3006966 : Nat := 4983230072969 + 3 ^ 40 * 3006966 * 2
def baseEnd_3006966 : Nat := 514672956575862488465407

theorem tailTrace_3006966 : CollatzResearch.WordTrace tailWord_3006966 prefixEnd_3006966 514672956575862488465407 := by
  unfold tailWord_3006966
  simp only [CollatzResearch.WordTrace]
  refine ⟨6854566251517700359512047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73115373349522137168128501 6854566251517700359512047)
  ·
    refine ⟨10281849377276550539268071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6854566251517700359512047 10281849377276550539268071)
    ·
      refine ⟨15422774065914825808902107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10281849377276550539268071 15422774065914825808902107)
      ·
        refine ⟨23134161098872238713353161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15422774065914825808902107 23134161098872238713353161)
        ·
          refine ⟨17350620824154179035014871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23134161098872238713353161 17350620824154179035014871)
          ·
            refine ⟨26025931236231268552522307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17350620824154179035014871 26025931236231268552522307)
            ·
              refine ⟨39038896854346902828783461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26025931236231268552522307 39038896854346902828783461)
              ·
                refine ⟨7319793160190044280396899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39038896854346902828783461 7319793160190044280396899)
                ·
                  refine ⟨10979689740285066420595349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7319793160190044280396899 10979689740285066420595349)
                  ·
                    refine ⟨514672956575862488465407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10979689740285066420595349 514672956575862488465407)
                    ·
                      rfl

theorem cell23_3006966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_3006966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006966 prefixEnd_3006966 := by exact prefixLift 3006966
  have htrace : WordTrace (prefixWord ++ tailWord_3006966) baseStart_3006966 baseEnd_3006966 := by
    simpa [prefixWord, tailWord_3006966, baseEnd_3006966] using wordTrace_append hprefix tailTrace_3006966
  have hstable : (prefixWord ++ tailWord_3006966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006966).length < 2 ^ (prefixWord ++ tailWord_3006966).sum := by decide
  have hdescent : baseEnd_3006966 < baseStart_3006966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006973 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 5, 2, 2]
def baseStart_3006973 : Nat := 118140960795 + 3006973 * 2 ^ 59
def prefixEnd_3006973 : Nat := 4983230072969 + 3 ^ 40 * 3006973 * 2
def baseEnd_3006973 : Nat := 1544022464092168938008689

theorem tailTrace_3006973 : CollatzResearch.WordTrace tailWord_3006973 prefixEnd_3006973 1544022464092168938008689 := by
  unfold tailWord_3006973
  simp only [CollatzResearch.WordTrace]
  refine ⟨109673315335257845947697573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73115543556838563965131715 109673315335257845947697573)
  ·
    refine ⟨20563746625360846115193295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109673315335257845947697573 20563746625360846115193295)
    ·
      refine ⟨30845619938041269172789943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20563746625360846115193295 30845619938041269172789943)
      ·
        refine ⟨46268429907061903759184915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30845619938041269172789943 46268429907061903759184915)
        ·
          refine ⟨69402644860592855638777373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46268429907061903759184915 69402644860592855638777373)
          ·
            refine ⟨26025991822722320864541515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69402644860592855638777373 26025991822722320864541515)
            ·
              refine ⟨39038987734083481296812273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26025991822722320864541515 39038987734083481296812273)
              ·
                refine ⟨29279240800562610972609205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39038987734083481296812273 29279240800562610972609205)
                ·
                  refine ⟨2744928825052744778682113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29279240800562610972609205 2744928825052744778682113)
                  ·
                    refine ⟨2058696618789558584011585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2744928825052744778682113 2058696618789558584011585)
                    ·
                      refine ⟨1544022464092168938008689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2058696618789558584011585 1544022464092168938008689)
                      ·
                        rfl

theorem cell23_3006973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5, 2, 2].length) (baseStart_3006973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006973 prefixEnd_3006973 := by exact prefixLift 3006973
  have htrace : WordTrace (prefixWord ++ tailWord_3006973) baseStart_3006973 baseEnd_3006973 := by
    simpa [prefixWord, tailWord_3006973, baseEnd_3006973] using wordTrace_append hprefix tailTrace_3006973
  have hstable : (prefixWord ++ tailWord_3006973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006973).length < 2 ^ (prefixWord ++ tailWord_3006973).sum := by decide
  have hdescent : baseEnd_3006973 < baseStart_3006973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006983 : List Nat := [1, 1, 4, 3, 3, 1, 1, 1, 4, 4]
def baseStart_3006983 : Nat := 118140960795 + 3006983 * 2 ^ 59
def prefixEnd_3006983 : Nat := 4983230072969 + 3 ^ 40 * 3006983 * 2
def baseEnd_3006983 : Nat := 514675866299571299627881

theorem tailTrace_3006983 : CollatzResearch.WordTrace tailWord_3006983 prefixEnd_3006983 514675866299571299627881 := by
  unfold tailWord_3006983
  simp only [CollatzResearch.WordTrace]
  refine ⟨109673680065221617655561603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73115786710147745103707735 109673680065221617655561603)
  ·
    refine ⟨164510520097832426483342405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109673680065221617655561603 164510520097832426483342405)
    ·
      refine ⟨30845722518343579965626701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164510520097832426483342405 30845722518343579965626701)
      ·
        refine ⟨11567145944378842487110013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30845722518343579965626701 11567145944378842487110013)
        ·
          refine ⟨4337679729142065932666255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11567145944378842487110013 4337679729142065932666255)
          ·
            refine ⟨6506519593713098898999383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4337679729142065932666255 6506519593713098898999383)
            ·
              refine ⟨9759779390569648348499075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6506519593713098898999383 9759779390569648348499075)
              ·
                refine ⟨14639669085854472522748613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9759779390569648348499075 14639669085854472522748613)
                ·
                  refine ⟨2744937953597713598015365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14639669085854472522748613 2744937953597713598015365)
                  ·
                    refine ⟨514675866299571299627881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2744937953597713598015365 514675866299571299627881)
                    ·
                      rfl

theorem cell23_3006983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_3006983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006983 prefixEnd_3006983 := by exact prefixLift 3006983
  have htrace : WordTrace (prefixWord ++ tailWord_3006983) baseStart_3006983 baseEnd_3006983 := by
    simpa [prefixWord, tailWord_3006983, baseEnd_3006983] using wordTrace_append hprefix tailTrace_3006983
  have hstable : (prefixWord ++ tailWord_3006983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006983).length < 2 ^ (prefixWord ++ tailWord_3006983).sum := by decide
  have hdescent : baseEnd_3006983 < baseStart_3006983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006990 : List Nat := [4, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2]
def baseStart_3006990 : Nat := 118140960795 + 3006990 * 2 ^ 59
def prefixEnd_3006990 : Nat := 4983230072969 + 3 ^ 40 * 3006990 * 2
def baseEnd_3006990 : Nat := 1544031193263295371496111

theorem tailTrace_3006990 : CollatzResearch.WordTrace tailWord_3006990 prefixEnd_3006990 1544031193263295371496111 := by
  unfold tailWord_3006990
  simp only [CollatzResearch.WordTrace]
  refine ⟨13709241922024532231383303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73115956917464171900710949 13709241922024532231383303)
  ·
    refine ⟨20563862883036798347074955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13709241922024532231383303 20563862883036798347074955)
    ·
      refine ⟨30845794324555197520612433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20563862883036798347074955 30845794324555197520612433)
      ·
        refine ⟨23134345743416398140459325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30845794324555197520612433 23134345743416398140459325)
        ·
          refine ⟨8675379653781149302672247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23134345743416398140459325 8675379653781149302672247)
          ·
            refine ⟨13013069480671723954008371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8675379653781149302672247 13013069480671723954008371)
            ·
              refine ⟨19519604221007585931012557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13013069480671723954008371 19519604221007585931012557)
              ·
                refine ⟨7319851582877844724129709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19519604221007585931012557 7319851582877844724129709)
                ·
                  refine ⟨2744944343579191771548641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7319851582877844724129709 2744944343579191771548641)
                  ·
                    refine ⟨2058708257684393828661481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2744944343579191771548641 2058708257684393828661481)
                    ·
                      refine ⟨1544031193263295371496111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2058708257684393828661481 1544031193263295371496111)
                      ·
                        rfl

theorem cell23_3006990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_3006990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3006990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3006990 prefixEnd_3006990 := by exact prefixLift 3006990
  have htrace : WordTrace (prefixWord ++ tailWord_3006990) baseStart_3006990 baseEnd_3006990 := by
    simpa [prefixWord, tailWord_3006990, baseEnd_3006990] using wordTrace_append hprefix tailTrace_3006990
  have hstable : (prefixWord ++ tailWord_3006990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006990).length < 2 ^ (prefixWord ++ tailWord_3006990).sum := by decide
  have hdescent : baseEnd_3006990 < baseStart_3006990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007000 : List Nat := [2, 1, 2, 3, 3, 2, 3, 1, 2, 4]
def baseStart_3007000 : Nat := 118140960795 + 3007000 * 2 ^ 59
def prefixEnd_3007000 : Nat := 4983230072969 + 3 ^ 40 * 3007000 * 2
def baseEnd_3007000 : Nat := 514678776023280110790355

theorem tailTrace_3007000 : CollatzResearch.WordTrace tailWord_3007000 prefixEnd_3007000 514678776023280110790355 := by
  unfold tailWord_3007000
  simp only [CollatzResearch.WordTrace]
  refine ⟨54837150053080014779465227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73116200070773353039286969 54837150053080014779465227)
  ·
    refine ⟨82255725079620022169197841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54837150053080014779465227 82255725079620022169197841)
    ·
      refine ⟨61691793809715016626898381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82255725079620022169197841 61691793809715016626898381)
      ·
        refine ⟨23134422678643131235086893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61691793809715016626898381 23134422678643131235086893)
        ·
          refine ⟨8675408504491174213157585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23134422678643131235086893 8675408504491174213157585)
          ·
            refine ⟨6506556378368380659868189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8675408504491174213157585 6506556378368380659868189)
            ·
              refine ⟨2439958641888142747450571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6506556378368380659868189 2439958641888142747450571)
              ·
                refine ⟨3659937962832214121175857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2439958641888142747450571 3659937962832214121175857)
                ·
                  refine ⟨2744953472124160590881893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3659937962832214121175857 2744953472124160590881893)
                  ·
                    refine ⟨514678776023280110790355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2744953472124160590881893 514678776023280110790355)
                    ·
                      rfl

theorem cell23_3007000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 2, 4].length) (baseStart_3007000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007000 prefixEnd_3007000 := by exact prefixLift 3007000
  have htrace : WordTrace (prefixWord ++ tailWord_3007000) baseStart_3007000 baseEnd_3007000 := by
    simpa [prefixWord, tailWord_3007000, baseEnd_3007000] using wordTrace_append hprefix tailTrace_3007000
  have hstable : (prefixWord ++ tailWord_3007000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007000).length < 2 ^ (prefixWord ++ tailWord_3007000).sum := by decide
  have hdescent : baseEnd_3007000 < baseStart_3007000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007057 : List Nat := [1, 2, 2, 1, 3, 5, 2, 1, 2, 1, 3]
def baseStart_3007057 : Nat := 118140960795 + 3007057 * 2 ^ 59
def prefixEnd_3007057 : Nat := 4983230072969 + 3 ^ 40 * 3007057 * 2
def baseEnd_3007057 : Nat := 1544065596467146609358303

theorem tailTrace_3007057 : CollatzResearch.WordTrace tailWord_3007057 prefixEnd_3007057 1544065596467146609358303 := by
  unfold tailWord_3007057
  simp only [CollatzResearch.WordTrace]
  refine ⟨109676379066953528293755425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73117586044635685529170283 109676379066953528293755425)
  ·
    refine ⟨82257284300215146220316569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109676379066953528293755425 82257284300215146220316569)
    ·
      refine ⟨61692963225161359665237427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82257284300215146220316569 61692963225161359665237427)
      ·
        refine ⟨92539444837742039497856141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61692963225161359665237427 92539444837742039497856141)
        ·
          refine ⟨34702291814153264811696053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92539444837742039497856141 34702291814153264811696053)
          ·
            refine ⟨3253339857576868576096505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34702291814153264811696053 3253339857576868576096505)
            ·
              refine ⟨2440004893182651432072379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3253339857576868576096505 2440004893182651432072379)
              ·
                refine ⟨3660007339773977148108569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2440004893182651432072379 3660007339773977148108569)
                ·
                  refine ⟨2745005504830482861081427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3660007339773977148108569 2745005504830482861081427)
                  ·
                    refine ⟨4117508257245724291622141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2745005504830482861081427 4117508257245724291622141)
                    ·
                      refine ⟨1544065596467146609358303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4117508257245724291622141 1544065596467146609358303)
                      ·
                        rfl

theorem cell23_3007057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 2, 1, 3].length) (baseStart_3007057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007057 prefixEnd_3007057 := by exact prefixLift 3007057
  have htrace : WordTrace (prefixWord ++ tailWord_3007057) baseStart_3007057 baseEnd_3007057 := by
    simpa [prefixWord, tailWord_3007057, baseEnd_3007057] using wordTrace_append hprefix tailTrace_3007057
  have hstable : (prefixWord ++ tailWord_3007057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007057).length < 2 ^ (prefixWord ++ tailWord_3007057).sum := by decide
  have hdescent : baseEnd_3007057 < baseStart_3007057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007063 : List Nat := [1, 1, 3, 2, 2, 2, 2, 3, 1, 4, 2]
def baseStart_3007063 : Nat := 118140960795 + 3007063 * 2 ^ 59
def prefixEnd_3007063 : Nat := 4983230072969 + 3 ^ 40 * 3007063 * 2
def baseEnd_3007063 : Nat := 1544068677351073585883275

theorem tailTrace_3007063 : CollatzResearch.WordTrace tailWord_3007063 prefixEnd_3007063 1544068677351073585883275 := by
  unfold tailWord_3007063
  simp only [CollatzResearch.WordTrace]
  refine ⟨109676597904931791318473843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73117731936621194212315895 109676597904931791318473843)
  ·
    refine ⟨164514896857397686977710765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109676597904931791318473843 164514896857397686977710765)
    ·
      refine ⟨61693086321524132616641537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164514896857397686977710765 61693086321524132616641537)
      ·
        refine ⟨46269814741143099462481153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61693086321524132616641537 46269814741143099462481153)
        ·
          refine ⟨34702361055857324596860865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46269814741143099462481153 34702361055857324596860865)
          ·
            refine ⟨26026770791892993447645649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34702361055857324596860865 26026770791892993447645649)
            ·
              refine ⟨19520078093919745085734237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26026770791892993447645649 19520078093919745085734237)
              ·
                refine ⟨7320029285219904407150339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19520078093919745085734237 7320029285219904407150339)
                ·
                  refine ⟨10980043927829856610725509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7320029285219904407150339 10980043927829856610725509)
                  ·
                    refine ⟨2058758236468098114511033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10980043927829856610725509 2058758236468098114511033)
                    ·
                      refine ⟨1544068677351073585883275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2058758236468098114511033 1544068677351073585883275)
                      ·
                        rfl

theorem cell23_3007063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 4, 2].length) (baseStart_3007063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007063 prefixEnd_3007063 := by exact prefixLift 3007063
  have htrace : WordTrace (prefixWord ++ tailWord_3007063) baseStart_3007063 baseEnd_3007063 := by
    simpa [prefixWord, tailWord_3007063, baseEnd_3007063] using wordTrace_append hprefix tailTrace_3007063
  have hstable : (prefixWord ++ tailWord_3007063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007063).length < 2 ^ (prefixWord ++ tailWord_3007063).sum := by decide
  have hdescent : baseEnd_3007063 < baseStart_3007063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007096 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 4, 3, 3]
def baseStart_3007096 : Nat := 118140960795 + 3007096 * 2 ^ 59
def prefixEnd_3007096 : Nat := 4983230072969 + 3 ^ 40 * 3007096 * 2
def baseEnd_3007096 : Nat := 1544085622212671956770623

theorem tailTrace_3007096 : CollatzResearch.WordTrace tailWord_3007096 prefixEnd_3007096 1544085622212671956770623 := by
  unfold tailWord_3007096
  simp only [CollatzResearch.WordTrace]
  refine ⟨54838900756906118977212571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73118534342541491969616761 54838900756906118977212571)
  ·
    refine ⟨82258351135359178465818857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54838900756906118977212571 82258351135359178465818857)
    ·
      refine ⟨61693763351519383849364143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82258351135359178465818857 61693763351519383849364143)
      ·
        refine ⟨92540645027279075774046215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61693763351519383849364143 92540645027279075774046215)
        ·
          refine ⟨138810967540918613661069323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92540645027279075774046215 138810967540918613661069323)
          ·
            refine ⟨208216451311377920491603985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138810967540918613661069323 208216451311377920491603985)
            ·
              refine ⟨156162338483533440368702989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208216451311377920491603985 156162338483533440368702989)
              ·
                refine ⟨58560876931325040138263621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156162338483533440368702989 58560876931325040138263621)
                ·
                  refine ⟨10980164424623445025924429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58560876931325040138263621 10980164424623445025924429)
                  ·
                    refine ⟨4117561659233791884721661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10980164424623445025924429 4117561659233791884721661)
                    ·
                      refine ⟨1544085622212671956770623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4117561659233791884721661 1544085622212671956770623)
                      ·
                        rfl

theorem cell23_3007096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 4, 3, 3].length) (baseStart_3007096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007096 prefixEnd_3007096 := by exact prefixLift 3007096
  have htrace : WordTrace (prefixWord ++ tailWord_3007096) baseStart_3007096 baseEnd_3007096 := by
    simpa [prefixWord, tailWord_3007096, baseEnd_3007096] using wordTrace_append hprefix tailTrace_3007096
  have hstable : (prefixWord ++ tailWord_3007096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007096).length < 2 ^ (prefixWord ++ tailWord_3007096).sum := by decide
  have hdescent : baseEnd_3007096 < baseStart_3007096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007097 : List Nat := [1, 2, 1, 3, 3, 3, 2, 2, 2, 2, 2]
def baseStart_3007097 : Nat := 118140960795 + 3007097 * 2 ^ 59
def prefixEnd_3007097 : Nat := 4983230072969 + 3 ^ 40 * 3007097 * 2
def baseEnd_3007097 : Nat := 1544086135693326452858119

theorem tailTrace_3007097 : CollatzResearch.WordTrace tailWord_3007097 prefixEnd_3007097 1544086135693326452858119 := by
  unfold tailWord_3007097
  simp only [CollatzResearch.WordTrace]
  refine ⟨109677837986808615125211545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73118558657872410083474363 109677837986808615125211545)
  ·
    refine ⟨82258378490106461343908659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109677837986808615125211545 82258378490106461343908659)
    ·
      refine ⟨123387567735159692015862989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82258378490106461343908659 123387567735159692015862989)
      ·
        refine ⟨46270337900684884505948621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123387567735159692015862989 46270337900684884505948621)
        ·
          refine ⟨17351376712756831689730733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46270337900684884505948621 17351376712756831689730733)
          ·
            refine ⟨6506766267283811883649025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17351376712756831689730733 6506766267283811883649025)
            ·
              refine ⟨4880074700462858912736769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6506766267283811883649025 4880074700462858912736769)
              ·
                refine ⟨3660056025347144184552577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4880074700462858912736769 3660056025347144184552577)
                ·
                  refine ⟨2745042019010358138414433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3660056025347144184552577 2745042019010358138414433)
                  ·
                    refine ⟨2058781514257768603810825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2745042019010358138414433 2058781514257768603810825)
                    ·
                      refine ⟨1544086135693326452858119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2058781514257768603810825 1544086135693326452858119)
                      ·
                        rfl

theorem cell23_3007097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2, 2, 2].length) (baseStart_3007097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007097 prefixEnd_3007097 := by exact prefixLift 3007097
  have htrace : WordTrace (prefixWord ++ tailWord_3007097) baseStart_3007097 baseEnd_3007097 := by
    simpa [prefixWord, tailWord_3007097, baseEnd_3007097] using wordTrace_append hprefix tailTrace_3007097
  have hstable : (prefixWord ++ tailWord_3007097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007097).length < 2 ^ (prefixWord ++ tailWord_3007097).sum := by decide
  have hdescent : baseEnd_3007097 < baseStart_3007097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007133 : List Nat := [1, 4, 2, 1, 1, 1, 5, 1, 2, 5]
def baseStart_3007133 : Nat := 118140960795 + 3007133 * 2 ^ 59
def prefixEnd_3007133 : Nat := 4983230072969 + 3 ^ 40 * 3007133 * 2
def baseEnd_3007133 : Nat := 514701540332296104002651

theorem tailTrace_3007133 : CollatzResearch.WordTrace tailWord_3007133 prefixEnd_3007133 514701540332296104002651 := by
  unfold tailWord_3007133
  simp only [CollatzResearch.WordTrace]
  refine ⟨109679151014678193273522053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73119434009785462182348035 109679151014678193273522053)
  ·
    refine ⟨20564840815252161238785385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109679151014678193273522053 20564840815252161238785385)
    ·
      refine ⟨15423630611439120929089039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20564840815252161238785385 15423630611439120929089039)
      ·
        refine ⟨23135445917158681393633559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15423630611439120929089039 23135445917158681393633559)
        ·
          refine ⟨34703168875738022090450339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23135445917158681393633559 34703168875738022090450339)
          ·
            refine ⟨52054753313607033135675509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34703168875738022090450339 52054753313607033135675509)
            ·
              refine ⟨4880133123150659356469579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52054753313607033135675509 4880133123150659356469579)
              ·
                refine ⟨7320199684725989034704369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4880133123150659356469579 7320199684725989034704369)
                ·
                  refine ⟨5490149763544491776028277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7320199684725989034704369 5490149763544491776028277)
                  ·
                    refine ⟨514701540332296104002651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5490149763544491776028277 514701540332296104002651)
                    ·
                      rfl

theorem cell23_3007133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_3007133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007133 prefixEnd_3007133 := by exact prefixLift 3007133
  have htrace : WordTrace (prefixWord ++ tailWord_3007133) baseStart_3007133 baseEnd_3007133 := by
    simpa [prefixWord, tailWord_3007133, baseEnd_3007133] using wordTrace_append hprefix tailTrace_3007133
  have hstable : (prefixWord ++ tailWord_3007133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007133).length < 2 ^ (prefixWord ++ tailWord_3007133).sum := by decide
  have hdescent : baseEnd_3007133 < baseStart_3007133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007180 : List Nat := [2, 2, 1, 5, 1, 1, 2, 2, 3, 4]
def baseStart_3007180 : Nat := 118140960795 + 3007180 * 2 ^ 59
def prefixEnd_3007180 : Nat := 4983230072969 + 3 ^ 40 * 3007180 * 2
def baseEnd_3007180 : Nat := 514709584862549876040079

theorem tailTrace_3007180 : CollatzResearch.WordTrace tailWord_3007180 prefixEnd_3007180 514709584862549876040079 := by
  unfold tailWord_3007180
  simp only [CollatzResearch.WordTrace]
  refine ⟨54840432622753960150241497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73120576830338613533655329 54840432622753960150241497)
  ·
    refine ⟨41130324467065470112681123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54840432622753960150241497 41130324467065470112681123)
    ·
      refine ⟨61695486700598205169021685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41130324467065470112681123 61695486700598205169021685)
      ·
        refine ⟨5783951878181081734595783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61695486700598205169021685 5783951878181081734595783)
        ·
          refine ⟨8675927817271622601893675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5783951878181081734595783 8675927817271622601893675)
          ·
            refine ⟨13013891725907433902840513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8675927817271622601893675 13013891725907433902840513)
            ·
              refine ⟨9760418794430575427130385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13013891725907433902840513 9760418794430575427130385)
              ·
                refine ⟨7320314095822931570347789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9760418794430575427130385 7320314095822931570347789)
                ·
                  refine ⟨2745117785933599338880421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7320314095822931570347789 2745117785933599338880421)
                  ·
                    refine ⟨514709584862549876040079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2745117785933599338880421 514709584862549876040079)
                    ·
                      rfl

theorem cell23_3007180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 3, 4].length) (baseStart_3007180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007180 prefixEnd_3007180 := by exact prefixLift 3007180
  have htrace : WordTrace (prefixWord ++ tailWord_3007180) baseStart_3007180 baseEnd_3007180 := by
    simpa [prefixWord, tailWord_3007180, baseEnd_3007180] using wordTrace_append hprefix tailTrace_3007180
  have hstable : (prefixWord ++ tailWord_3007180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007180).length < 2 ^ (prefixWord ++ tailWord_3007180).sum := by decide
  have hdescent : baseEnd_3007180 < baseStart_3007180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007214 : List Nat := [4, 1, 2, 1, 1, 4, 3, 2, 1, 4]
def baseStart_3007214 : Nat := 118140960795 + 3007214 * 2 ^ 59
def prefixEnd_3007214 : Nat := 4983230072969 + 3 ^ 40 * 3007214 * 2
def baseEnd_3007214 : Nat := 514715404309967498365027

theorem tailTrace_3007214 : CollatzResearch.WordTrace tailWord_3007214 prefixEnd_3007214 514715404309967498365027 := by
  unfold tailWord_3007214
  simp only [CollatzResearch.WordTrace]
  refine ⟨13710263165923093013402587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73121403551589829404813797 13710263165923093013402587)
  ·
    refine ⟨20565394748884639520103881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13710263165923093013402587 20565394748884639520103881)
    ·
      refine ⟨15424046061663479640077911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20565394748884639520103881 15424046061663479640077911)
      ·
        refine ⟨23136069092495219460116867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15424046061663479640077911 23136069092495219460116867)
        ·
          refine ⟨34704103638742829190175301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23136069092495219460116867 34704103638742829190175301)
          ·
            refine ⟨6507019432264280473157869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34704103638742829190175301 6507019432264280473157869)
            ·
              refine ⟨2440132287099105177434201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6507019432264280473157869 2440132287099105177434201)
              ·
                refine ⟨1830099215324328883075651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2440132287099105177434201 1830099215324328883075651)
                ·
                  refine ⟨2745148822986493324613477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1830099215324328883075651 2745148822986493324613477)
                  ·
                    refine ⟨514715404309967498365027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2745148822986493324613477 514715404309967498365027)
                    ·
                      rfl

theorem cell23_3007214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_3007214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007214 prefixEnd_3007214 := by exact prefixLift 3007214
  have htrace : WordTrace (prefixWord ++ tailWord_3007214) baseStart_3007214 baseEnd_3007214 := by
    simpa [prefixWord, tailWord_3007214, baseEnd_3007214] using wordTrace_append hprefix tailTrace_3007214
  have hstable : (prefixWord ++ tailWord_3007214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007214).length < 2 ^ (prefixWord ++ tailWord_3007214).sum := by decide
  have hdescent : baseEnd_3007214 < baseStart_3007214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007240 : List Nat := [2, 1, 3, 2, 2, 2, 3, 2, 1, 5]
def baseStart_3007240 : Nat := 118140960795 + 3007240 * 2 ^ 59
def prefixEnd_3007240 : Nat := 4983230072969 + 3 ^ 40 * 3007240 * 2
def baseEnd_3007240 : Nat := 514719854475639797789987

theorem tailTrace_3007240 : CollatzResearch.WordTrace tailWord_3007240 prefixEnd_3007240 514719854475639797789987 := by
  unfold tailWord_3007240
  simp only [CollatzResearch.WordTrace]
  refine ⟨54841526812645275273833587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73122035750193700365111449 54841526812645275273833587)
  ·
    refine ⟨82262290218967912910750381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54841526812645275273833587 82262290218967912910750381)
    ·
      refine ⟨30848358832112967341531393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82262290218967912910750381 30848358832112967341531393)
      ·
        refine ⟨23136269124084725506148545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30848358832112967341531393 23136269124084725506148545)
        ·
          refine ⟨17352201843063544129611409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23136269124084725506148545 17352201843063544129611409)
          ·
            refine ⟨13014151382297658097208557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17352201843063544129611409 13014151382297658097208557)
            ·
              refine ⟨4880306768361621786453209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13014151382297658097208557 4880306768361621786453209)
              ·
                refine ⟨3660230076271216339839907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4880306768361621786453209 3660230076271216339839907)
                ·
                  refine ⟨5490345114406824509759861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3660230076271216339839907 5490345114406824509759861)
                  ·
                    refine ⟨514719854475639797789987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5490345114406824509759861 514719854475639797789987)
                    ·
                      rfl

theorem cell23_3007240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_3007240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007240 prefixEnd_3007240 := by exact prefixLift 3007240
  have htrace : WordTrace (prefixWord ++ tailWord_3007240) baseStart_3007240 baseEnd_3007240 := by
    simpa [prefixWord, tailWord_3007240, baseEnd_3007240] using wordTrace_append hprefix tailTrace_3007240
  have hstable : (prefixWord ++ tailWord_3007240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007240).length < 2 ^ (prefixWord ++ tailWord_3007240).sum := by decide
  have hdescent : baseEnd_3007240 < baseStart_3007240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007253 : List Nat := [1, 3, 2, 1, 2, 2, 3, 2, 1, 6]
def baseStart_3007253 : Nat := 118140960795 + 3007253 * 2 ^ 59
def prefixEnd_3007253 : Nat := 4983230072969 + 3 ^ 40 * 3007253 * 2
def baseEnd_3007253 : Nat := 514722079558475947502467

theorem tailTrace_3007253 : CollatzResearch.WordTrace tailWord_3007253 prefixEnd_3007253 514722079558475947502467 := by
  unfold tailWord_3007253
  simp only [CollatzResearch.WordTrace]
  refine ⟨109683527774243453767890413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73122351849495635845260275 109683527774243453767890413)
  ·
    refine ⟨41131322915341295162958905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109683527774243453767890413 41131322915341295162958905)
    ·
      refine ⟨30848492186505971372219179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41131322915341295162958905 30848492186505971372219179)
      ·
        refine ⟨46272738279758957058328769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30848492186505971372219179 46272738279758957058328769)
        ·
          refine ⟨34704553709819217793746577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46272738279758957058328769 34704553709819217793746577)
          ·
            refine ⟨26028415282364413345309933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34704553709819217793746577 26028415282364413345309933)
            ·
              refine ⟨9760655730886655004491225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26028415282364413345309933 9760655730886655004491225)
              ·
                refine ⟨7320491798164991253368419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9760655730886655004491225 7320491798164991253368419)
                ·
                  refine ⟨10980737697247486880052629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7320491798164991253368419 10980737697247486880052629)
                  ·
                    refine ⟨514722079558475947502467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10980737697247486880052629 514722079558475947502467)
                    ·
                      rfl

theorem cell23_3007253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_3007253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007253 prefixEnd_3007253 := by exact prefixLift 3007253
  have htrace : WordTrace (prefixWord ++ tailWord_3007253) baseStart_3007253 baseEnd_3007253 := by
    simpa [prefixWord, tailWord_3007253, baseEnd_3007253] using wordTrace_append hprefix tailTrace_3007253
  have hstable : (prefixWord ++ tailWord_3007253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007253).length < 2 ^ (prefixWord ++ tailWord_3007253).sum := by decide
  have hdescent : baseEnd_3007253 < baseStart_3007253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007283 : List Nat := [1, 1, 1, 2, 6, 1, 3, 8]
def baseStart_3007283 : Nat := 118140960795 + 3007283 * 2 ^ 59
def prefixEnd_3007283 : Nat := 4983230072969 + 3 ^ 40 * 3007283 * 2
def baseEnd_3007283 : Nat := 57191912707224545375269

theorem tailTrace_3007283 : CollatzResearch.WordTrace tailWord_3007283 prefixEnd_3007283 57191912707224545375269 := by
  unfold tailWord_3007283
  simp only [CollatzResearch.WordTrace]
  refine ⟨109684621964134768891482503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73123081309423179260988335 109684621964134768891482503)
  ·
    refine ⟨164526932946202153337223755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109684621964134768891482503 164526932946202153337223755)
    ·
      refine ⟨246790399419303230005835633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164526932946202153337223755 246790399419303230005835633)
      ·
        refine ⟨185092799564477422504376725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246790399419303230005835633 185092799564477422504376725)
        ·
          refine ⟨8676224979584879179892659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 185092799564477422504376725 8676224979584879179892659)
          ·
            refine ⟨13014337469377318769838989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8676224979584879179892659 13014337469377318769838989)
            ·
              refine ⟨4880376551016494538689621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13014337469377318769838989 4880376551016494538689621)
              ·
                refine ⟨57191912707224545375269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4880376551016494538689621 57191912707224545375269)
                ·
                  rfl

theorem cell23_3007283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 8].length) (baseStart_3007283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007283 prefixEnd_3007283 := by exact prefixLift 3007283
  have htrace : WordTrace (prefixWord ++ tailWord_3007283) baseStart_3007283 baseEnd_3007283 := by
    simpa [prefixWord, tailWord_3007283, baseEnd_3007283] using wordTrace_append hprefix tailTrace_3007283
  have hstable : (prefixWord ++ tailWord_3007283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007283).length < 2 ^ (prefixWord ++ tailWord_3007283).sum := by decide
  have hdescent : baseEnd_3007283 < baseStart_3007283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007333 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 1, 5, 4]
def baseStart_3007333 : Nat := 118140960795 + 3007333 * 2 ^ 59
def prefixEnd_3007333 : Nat := 4983230072969 + 3 ^ 40 * 3007333 * 2
def baseEnd_3007333 : Nat := 1544207317127787529507033

theorem tailTrace_3007333 : CollatzResearch.WordTrace tailWord_3007333 prefixEnd_3007333 1544207317127787529507033 := by
  unfold tailWord_3007333
  simp only [CollatzResearch.WordTrace]
  refine ⟨109686445613953627430802653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73124297075969084953868435 109686445613953627430802653)
  ·
    refine ⟨41132417105232610286550995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109686445613953627430802653 41132417105232610286550995)
    ·
      refine ⟨61698625657848915429826493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41132417105232610286550995 61698625657848915429826493)
      ·
        refine ⟨23136984621693343286184935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61698625657848915429826493 23136984621693343286184935)
        ·
          refine ⟨34705476932540014929277403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23136984621693343286184935 34705476932540014929277403)
          ·
            refine ⟨52058215398810022393916105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34705476932540014929277403 52058215398810022393916105)
            ·
              refine ⟨39043661549107516795437079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52058215398810022393916105 39043661549107516795437079)
              ·
                refine ⟨58565492323661275193155619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39043661549107516795437079 58565492323661275193155619)
                ·
                  refine ⟨87848238485491912789733429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58565492323661275193155619 87848238485491912789733429)
                  ·
                    refine ⟨8235772358014866824037509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87848238485491912789733429 8235772358014866824037509)
                    ·
                      refine ⟨1544207317127787529507033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8235772358014866824037509 1544207317127787529507033)
                      ·
                        rfl

theorem cell23_3007333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_3007333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007333 prefixEnd_3007333 := by exact prefixLift 3007333
  have htrace : WordTrace (prefixWord ++ tailWord_3007333) baseStart_3007333 baseEnd_3007333 := by
    simpa [prefixWord, tailWord_3007333, baseEnd_3007333] using wordTrace_append hprefix tailTrace_3007333
  have hstable : (prefixWord ++ tailWord_3007333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007333).length < 2 ^ (prefixWord ++ tailWord_3007333).sum := by decide
  have hdescent : baseEnd_3007333 < baseStart_3007333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007362 : List Nat := [3, 4, 2, 2, 1, 2, 1, 3, 1, 2, 2]
def baseStart_3007362 : Nat := 118140960795 + 3007362 * 2 ^ 59
def prefixEnd_3007362 : Nat := 4983230072969 + 3 ^ 40 * 3007362 * 2
def baseEnd_3007362 : Nat := 1544222208066767916044401

theorem tailTrace_3007362 : CollatzResearch.WordTrace tailWord_3007362 prefixEnd_3007362 1544222208066767916044401 := by
  unfold tailWord_3007362
  simp only [CollatzResearch.WordTrace]
  refine ⟨27421875832712141345902085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73125002220565710255738893 27421875832712141345902085)
  ·
    refine ⟨5141601718633526502356641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27421875832712141345902085 5141601718633526502356641)
    ·
      refine ⟨3856201288975144876767481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5141601718633526502356641 3856201288975144876767481)
      ·
        refine ⟨2892150966731358657575611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3856201288975144876767481 2892150966731358657575611)
        ·
          refine ⟨4338226450097037986363417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2892150966731358657575611 4338226450097037986363417)
          ·
            refine ⟨3253669837572778489772563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4338226450097037986363417 3253669837572778489772563)
            ·
              refine ⟨4880504756359167734658845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3253669837572778489772563 4880504756359167734658845)
              ·
                refine ⟨1830189283634687900497067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4880504756359167734658845 1830189283634687900497067)
                ·
                  refine ⟨2745283925452031850745601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1830189283634687900497067 2745283925452031850745601)
                  ·
                    refine ⟨2058962944089023888059201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2745283925452031850745601 2058962944089023888059201)
                    ·
                      refine ⟨1544222208066767916044401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2058962944089023888059201 1544222208066767916044401)
                      ·
                        rfl

theorem cell23_3007362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_3007362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007362 prefixEnd_3007362 := by exact prefixLift 3007362
  have htrace : WordTrace (prefixWord ++ tailWord_3007362) baseStart_3007362 baseEnd_3007362 := by
    simpa [prefixWord, tailWord_3007362, baseEnd_3007362] using wordTrace_append hprefix tailTrace_3007362
  have hstable : (prefixWord ++ tailWord_3007362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007362).length < 2 ^ (prefixWord ++ tailWord_3007362).sum := by decide
  have hdescent : baseEnd_3007362 < baseStart_3007362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007370 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 1, 3, 5]
def baseStart_3007370 : Nat := 118140960795 + 3007370 * 2 ^ 59
def prefixEnd_3007370 : Nat := 4983230072969 + 3 ^ 40 * 3007370 * 2
def baseEnd_3007370 : Nat := 1544226315912003884744363

theorem tailTrace_3007370 : CollatzResearch.WordTrace tailWord_3007370 prefixEnd_3007370 1544226315912003884744363 := by
  unfold tailWord_3007370
  simp only [CollatzResearch.WordTrace]
  refine ⟨27421948778704895687474891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73125196743213055166599709 27421948778704895687474891)
  ·
    refine ⟨41132923168057343531212337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27421948778704895687474891 41132923168057343531212337)
    ·
      refine ⟨30849692376043007648409253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41132923168057343531212337 30849692376043007648409253)
      ·
        refine ⟨5784317320508063934076735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30849692376043007648409253 5784317320508063934076735)
        ·
          refine ⟨8676475980762095901115103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5784317320508063934076735 8676475980762095901115103)
          ·
            refine ⟨13014713971143143851672655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8676475980762095901115103 13014713971143143851672655)
            ·
              refine ⟨19522070956714715777508983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13014713971143143851672655 19522070956714715777508983)
              ·
                refine ⟨29283106435072073666263475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19522070956714715777508983 29283106435072073666263475)
                ·
                  refine ⟨43924659652608110499395213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29283106435072073666263475 43924659652608110499395213)
                  ·
                    refine ⟨16471747369728041437273205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43924659652608110499395213 16471747369728041437273205)
                    ·
                      refine ⟨1544226315912003884744363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16471747369728041437273205 1544226315912003884744363)
                      ·
                        rfl

theorem cell23_3007370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_3007370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007370 prefixEnd_3007370 := by exact prefixLift 3007370
  have htrace : WordTrace (prefixWord ++ tailWord_3007370) baseStart_3007370 baseEnd_3007370 := by
    simpa [prefixWord, tailWord_3007370, baseEnd_3007370] using wordTrace_append hprefix tailTrace_3007370
  have hstable : (prefixWord ++ tailWord_3007370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007370).length < 2 ^ (prefixWord ++ tailWord_3007370).sum := by decide
  have hdescent : baseEnd_3007370 < baseStart_3007370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007383 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 7]
def baseStart_3007383 : Nat := 118140960795 + 3007383 * 2 ^ 59
def prefixEnd_3007383 : Nat := 4983230072969 + 3 ^ 40 * 3007383 * 2
def baseEnd_3007383 : Nat := 1544232991160512333881803

theorem tailTrace_3007383 : CollatzResearch.WordTrace tailWord_3007383 prefixEnd_3007383 1544232991160512333881803 := by
  unfold tailWord_3007383
  simp only [CollatzResearch.WordTrace]
  refine ⟨109688269263772485970122803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73125512842514990646748535 109688269263772485970122803)
  ·
    refine ⟨164532403895658728955184205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109688269263772485970122803 164532403895658728955184205)
    ·
      refine ⟨61699651460872023358194077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164532403895658728955184205 61699651460872023358194077)
      ·
        refine ⟨23137369297827008759322779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61699651460872023358194077 23137369297827008759322779)
        ·
          refine ⟨34706053946740513138984169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23137369297827008759322779 34706053946740513138984169)
          ·
            refine ⟨26029540460055384854238127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34706053946740513138984169 26029540460055384854238127)
            ·
              refine ⟨39044310690083077281357191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26029540460055384854238127 39044310690083077281357191)
              ·
                refine ⟨58566466035124615922035787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39044310690083077281357191 58566466035124615922035787)
                ·
                  refine ⟨87849699052686923883053681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58566466035124615922035787 87849699052686923883053681)
                  ·
                    refine ⟨65887274289515192912290261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87849699052686923883053681 65887274289515192912290261)
                    ·
                      refine ⟨1544232991160512333881803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 65887274289515192912290261 1544232991160512333881803)
                      ·
                        rfl

theorem cell23_3007383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_3007383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007383 prefixEnd_3007383 := by exact prefixLift 3007383
  have htrace : WordTrace (prefixWord ++ tailWord_3007383) baseStart_3007383 baseEnd_3007383 := by
    simpa [prefixWord, tailWord_3007383, baseEnd_3007383] using wordTrace_append hprefix tailTrace_3007383
  have hstable : (prefixWord ++ tailWord_3007383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007383).length < 2 ^ (prefixWord ++ tailWord_3007383).sum := by decide
  have hdescent : baseEnd_3007383 < baseStart_3007383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007405 : List Nat := [1, 5, 2, 3, 2, 1, 1, 2, 1, 3, 2]
def baseStart_3007405 : Nat := 118140960795 + 3007405 * 2 ^ 59
def prefixEnd_3007405 : Nat := 4983230072969 + 3 ^ 40 * 3007405 * 2
def baseEnd_3007405 : Nat := 1544244287734911247806703

theorem tailTrace_3007405 : CollatzResearch.WordTrace tailWord_3007405 prefixEnd_3007405 1544244287734911247806703 := by
  unfold tailWord_3007405
  simp only [CollatzResearch.WordTrace]
  refine ⟨109689071669692783727423669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73126047779795189151615779 109689071669692783727423669)
  ·
    refine ⟨10283350469033698474445969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109689071669692783727423669 10283350469033698474445969)
    ·
      refine ⟨7712512851775273855834477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10283350469033698474445969 7712512851775273855834477)
      ·
        refine ⟨2892192319415727695937929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7712512851775273855834477 2892192319415727695937929)
        ·
          refine ⟨2169144239561795771953447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2892192319415727695937929 2169144239561795771953447)
          ·
            refine ⟨3253716359342693657930171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2169144239561795771953447 3253716359342693657930171)
            ·
              refine ⟨4880574539014040486895257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3253716359342693657930171 4880574539014040486895257)
              ·
                refine ⟨3660430904260530365171443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4880574539014040486895257 3660430904260530365171443)
                ·
                  refine ⟨5490646356390795547757165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3660430904260530365171443 5490646356390795547757165)
                  ·
                    refine ⟨2058992383646548330408937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5490646356390795547757165 2058992383646548330408937)
                    ·
                      refine ⟨1544244287734911247806703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2058992383646548330408937 1544244287734911247806703)
                      ·
                        rfl

theorem cell23_3007405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_3007405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007405 prefixEnd_3007405 := by exact prefixLift 3007405
  have htrace : WordTrace (prefixWord ++ tailWord_3007405) baseStart_3007405 baseEnd_3007405 := by
    simpa [prefixWord, tailWord_3007405, baseEnd_3007405] using wordTrace_append hprefix tailTrace_3007405
  have hstable : (prefixWord ++ tailWord_3007405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007405).length < 2 ^ (prefixWord ++ tailWord_3007405).sum := by decide
  have hdescent : baseEnd_3007405 < baseStart_3007405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007474 : List Nat := [3, 2, 1, 5, 1, 1, 1, 1, 1, 3, 4]
def baseStart_3007474 : Nat := 118140960795 + 3007474 * 2 ^ 59
def prefixEnd_3007474 : Nat := 4983230072969 + 3 ^ 40 * 3007474 * 2
def baseEnd_3007474 : Nat := 1544279717900071477843885

theorem tailTrace_3007474 : CollatzResearch.WordTrace tailWord_3007474 prefixEnd_3007474 1544279717900071477843885 := by
  unfold tailWord_3007474
  simp only [CollatzResearch.WordTrace]
  refine ⟨27422897076610702127921369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73127725537628539007790317 27422897076610702127921369)
  ·
    refine ⟨20567172807458026595941027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27422897076610702127921369 20567172807458026595941027)
    ·
      refine ⟨30850759211187039893911541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20567172807458026595941027 30850759211187039893911541)
      ·
        refine ⟨2892258676048784990054207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30850759211187039893911541 2892258676048784990054207)
        ·
          refine ⟨4338388014073177485081311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2892258676048784990054207 4338388014073177485081311)
          ·
            refine ⟨6507582021109766227621967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4338388014073177485081311 6507582021109766227621967)
            ·
              refine ⟨9761373031664649341432951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6507582021109766227621967 9761373031664649341432951)
              ·
                refine ⟨14642059547496974012149427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9761373031664649341432951 14642059547496974012149427)
                ·
                  refine ⟨21963089321245461018224141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14642059547496974012149427 21963089321245461018224141)
                  ·
                    refine ⟨8236158495467047881834053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21963089321245461018224141 8236158495467047881834053)
                    ·
                      refine ⟨1544279717900071477843885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8236158495467047881834053 1544279717900071477843885)
                      ·
                        rfl

theorem cell23_3007474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_3007474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007474 prefixEnd_3007474 := by exact prefixLift 3007474
  have htrace : WordTrace (prefixWord ++ tailWord_3007474) baseStart_3007474 baseEnd_3007474 := by
    simpa [prefixWord, tailWord_3007474, baseEnd_3007474] using wordTrace_append hprefix tailTrace_3007474
  have hstable : (prefixWord ++ tailWord_3007474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007474).length < 2 ^ (prefixWord ++ tailWord_3007474).sum := by decide
  have hdescent : baseEnd_3007474 < baseStart_3007474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007484 : List Nat := [2, 2, 2, 1, 2, 3, 1, 5, 1, 4]
def baseStart_3007484 : Nat := 118140960795 + 3007484 * 2 ^ 59
def prefixEnd_3007484 : Nat := 4983230072969 + 3 ^ 40 * 3007484 * 2
def baseEnd_3007484 : Nat := 514761617568872146239613

theorem tailTrace_3007484 : CollatzResearch.WordTrace tailWord_3007484 prefixEnd_3007484 514761617568872146239613 := by
  unfold tailWord_3007484
  simp only [CollatzResearch.WordTrace]
  refine ⟨54845976518203290109774753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73127968690937720146366337 54845976518203290109774753)
  ·
    refine ⟨41134482388652467582331065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54845976518203290109774753 41134482388652467582331065)
    ·
      refine ⟨30850861791489350686748299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41134482388652467582331065 30850861791489350686748299)
      ·
        refine ⟨46276292687234026030122449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30850861791489350686748299 46276292687234026030122449)
        ·
          refine ⟨34707219515425519522591837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46276292687234026030122449 34707219515425519522591837)
          ·
            refine ⟨13015207318284569820971939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34707219515425519522591837 13015207318284569820971939)
            ·
              refine ⟨19522810977426854731457909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13015207318284569820971939 19522810977426854731457909)
              ·
                refine ⟨1830263529133767631074179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19522810977426854731457909 1830263529133767631074179)
                ·
                  refine ⟨2745395293700651446611269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1830263529133767631074179 2745395293700651446611269)
                  ·
                    refine ⟨514761617568872146239613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2745395293700651446611269 514761617568872146239613)
                    ·
                      rfl

theorem cell23_3007484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_3007484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007484 prefixEnd_3007484 := by exact prefixLift 3007484
  have htrace : WordTrace (prefixWord ++ tailWord_3007484) baseStart_3007484 baseEnd_3007484 := by
    simpa [prefixWord, tailWord_3007484, baseEnd_3007484] using wordTrace_append hprefix tailTrace_3007484
  have hstable : (prefixWord ++ tailWord_3007484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007484).length < 2 ^ (prefixWord ++ tailWord_3007484).sum := by decide
  have hdescent : baseEnd_3007484 < baseStart_3007484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007500 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 1, 2, 6]
def baseStart_3007500 : Nat := 118140960795 + 3007500 * 2 ^ 59
def prefixEnd_3007500 : Nat := 4983230072969 + 3 ^ 40 * 3007500 * 2
def baseEnd_3007500 : Nat := 1544293068397088376118765

theorem tailTrace_3007500 : CollatzResearch.WordTrace tailWord_3007500 prefixEnd_3007500 1544293068397088376118765 := by
  unfold tailWord_3007500
  simp only [CollatzResearch.WordTrace]
  refine ⟨54846268302174307476065977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73128357736232409968087969 54846268302174307476065977)
  ·
    refine ⟨41134701226630730607049483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54846268302174307476065977 41134701226630730607049483)
    ·
      refine ⟨61702051839946095910574225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41134701226630730607049483 61702051839946095910574225)
      ·
        refine ⟨46276538879959571932930669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61702051839946095910574225 46276538879959571932930669)
        ·
          refine ⟨17353702079984839474849001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46276538879959571932930669 17353702079984839474849001)
          ·
            refine ⟨13015276559988629606136751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17353702079984839474849001 13015276559988629606136751)
            ·
              refine ⟨19522914839982944409205127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13015276559988629606136751 19522914839982944409205127)
              ·
                refine ⟨29284372259974416613807691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19522914839982944409205127 29284372259974416613807691)
                ·
                  refine ⟨43926558389961624920711537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29284372259974416613807691 43926558389961624920711537)
                  ·
                    refine ⟨32944918792471218690533653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43926558389961624920711537 32944918792471218690533653)
                    ·
                      refine ⟨1544293068397088376118765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32944918792471218690533653 1544293068397088376118765)
                      ·
                        rfl

theorem cell23_3007500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_3007500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007500 prefixEnd_3007500 := by exact prefixLift 3007500
  have htrace : WordTrace (prefixWord ++ tailWord_3007500) baseStart_3007500 baseEnd_3007500 := by
    simpa [prefixWord, tailWord_3007500, baseEnd_3007500] using wordTrace_append hprefix tailTrace_3007500
  have hstable : (prefixWord ++ tailWord_3007500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007500).length < 2 ^ (prefixWord ++ tailWord_3007500).sum := by decide
  have hdescent : baseEnd_3007500 < baseStart_3007500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007534 : List Nat := [4, 1, 3, 1, 1, 1, 1, 3, 1, 5, 2]
def baseStart_3007534 : Nat := 118140960795 + 3007534 * 2 ^ 59
def prefixEnd_3007534 : Nat := 4983230072969 + 3 ^ 40 * 3007534 * 2
def baseEnd_3007534 : Nat := 1544310526739341243093609

theorem tailTrace_3007534 : CollatzResearch.WordTrace tailWord_3007534 prefixEnd_3007534 1544310526739341243093609 := by
  unfold tailWord_3007534
  simp only [CollatzResearch.WordTrace]
  refine ⟨13711722085778179844858707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73129184457483625839246437 13711722085778179844858707)
  ·
    refine ⟨20567583128667269767288061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13711722085778179844858707 20567583128667269767288061)
    ·
      refine ⟨7712843673250226162733023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20567583128667269767288061 7712843673250226162733023)
      ·
        refine ⟨11569265509875339244099535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7712843673250226162733023 11569265509875339244099535)
        ·
          refine ⟨17353898264813008866149303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11569265509875339244099535 17353898264813008866149303)
          ·
            refine ⟨26030847397219513299223955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17353898264813008866149303 26030847397219513299223955)
            ·
              refine ⟨39046271095829269948835933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26030847397219513299223955 39046271095829269948835933)
              ·
                refine ⟨14642351660935976230813475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39046271095829269948835933 14642351660935976230813475)
                ·
                  refine ⟨21963527491403964346220213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14642351660935976230813475 21963527491403964346220213)
                  ·
                    refine ⟨2059080702319121657458145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21963527491403964346220213 2059080702319121657458145)
                    ·
                      refine ⟨1544310526739341243093609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2059080702319121657458145 1544310526739341243093609)
                      ·
                        rfl

theorem cell23_3007534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_3007534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007534 prefixEnd_3007534 := by exact prefixLift 3007534
  have htrace : WordTrace (prefixWord ++ tailWord_3007534) baseStart_3007534 baseEnd_3007534 := by
    simpa [prefixWord, tailWord_3007534, baseEnd_3007534] using wordTrace_append hprefix tailTrace_3007534
  have hstable : (prefixWord ++ tailWord_3007534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007534).length < 2 ^ (prefixWord ++ tailWord_3007534).sum := by decide
  have hdescent : baseEnd_3007534 < baseStart_3007534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007557 : List Nat := [1, 3, 1, 1, 1, 3, 4, 1, 4, 4]
def baseStart_3007557 : Nat := 118140960795 + 3007557 * 2 ^ 59
def prefixEnd_3007557 : Nat := 4983230072969 + 3 ^ 40 * 3007557 * 2
def baseEnd_3007557 : Nat := 514774112264798217702001

theorem tailTrace_3007557 : CollatzResearch.WordTrace tailWord_3007557 prefixEnd_3007557 514774112264798217702001 := by
  unfold tailWord_3007557
  simp only [CollatzResearch.WordTrace]
  refine ⟨109694615565142113686956925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73129743710094742457971283 109694615565142113686956925)
  ·
    refine ⟨41135480836928292632608847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109694615565142113686956925 41135480836928292632608847)
    ·
      refine ⟨61703221255392438948913271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41135480836928292632608847 61703221255392438948913271)
      ·
        refine ⟨92554831883088658423369907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61703221255392438948913271 92554831883088658423369907)
        ·
          refine ⟨138832247824632987635054861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92554831883088658423369907 138832247824632987635054861)
          ·
            refine ⟨52062092934237370363145573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138832247824632987635054861 52062092934237370363145573)
            ·
              refine ⟨9761642425169506943089795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52062092934237370363145573 9761642425169506943089795)
              ·
                refine ⟨14642463637754260414634693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9761642425169506943089795 14642463637754260414634693)
                ·
                  refine ⟨2745461932078923827744005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14642463637754260414634693 2745461932078923827744005)
                  ·
                    refine ⟨514774112264798217702001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2745461932078923827744005 514774112264798217702001)
                    ·
                      rfl

theorem cell23_3007557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4, 4].length) (baseStart_3007557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007557 prefixEnd_3007557 := by exact prefixLift 3007557
  have htrace : WordTrace (prefixWord ++ tailWord_3007557) baseStart_3007557 baseEnd_3007557 := by
    simpa [prefixWord, tailWord_3007557, baseEnd_3007557] using wordTrace_append hprefix tailTrace_3007557
  have hstable : (prefixWord ++ tailWord_3007557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007557).length < 2 ^ (prefixWord ++ tailWord_3007557).sum := by decide
  have hdescent : baseEnd_3007557 < baseStart_3007557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007558 : List Nat := [6, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3]
def baseStart_3007558 : Nat := 118140960795 + 3007558 * 2 ^ 59
def prefixEnd_3007558 : Nat := 4983230072969 + 3 ^ 40 * 3007558 * 2
def baseEnd_3007558 : Nat := 1544322850275049149193499

theorem tailTrace_3007558 : CollatzResearch.WordTrace tailWord_3007558 prefixEnd_3007558 1544322850275049149193499 := by
  unfold tailWord_3007558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3427957876191827839304479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 73129768025425660571828885 3427957876191827839304479)
  ·
    refine ⟨5141936814287741758956719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3427957876191827839304479 5141936814287741758956719)
    ·
      refine ⟨7712905221431612638435079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5141936814287741758956719 7712905221431612638435079)
      ·
        refine ⟨11569357832147418957652619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7712905221431612638435079 11569357832147418957652619)
        ·
          refine ⟨17354036748221128436478929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11569357832147418957652619 17354036748221128436478929)
          ·
            refine ⟨13015527561165846327359197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17354036748221128436478929 13015527561165846327359197)
            ·
              refine ⟨4880822835437192372759699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13015527561165846327359197 4880822835437192372759699)
              ·
                refine ⟨7321234253155788559139549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4880822835437192372759699 7321234253155788559139549)
                ·
                  refine ⟨2745462844933420709677331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7321234253155788559139549 2745462844933420709677331)
                  ·
                    refine ⟨4118194267400131064515997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2745462844933420709677331 4118194267400131064515997)
                    ·
                      refine ⟨1544322850275049149193499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4118194267400131064515997 1544322850275049149193499)
                      ·
                        rfl

theorem cell23_3007558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_3007558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007558 prefixEnd_3007558 := by exact prefixLift 3007558
  have htrace : WordTrace (prefixWord ++ tailWord_3007558) baseStart_3007558 baseEnd_3007558 := by
    simpa [prefixWord, tailWord_3007558, baseEnd_3007558] using wordTrace_append hprefix tailTrace_3007558
  have hstable : (prefixWord ++ tailWord_3007558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007558).length < 2 ^ (prefixWord ++ tailWord_3007558).sum := by decide
  have hdescent : baseEnd_3007558 < baseStart_3007558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007560 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 3, 1, 6]
def baseStart_3007560 : Nat := 118140960795 + 3007560 * 2 ^ 59
def prefixEnd_3007560 : Nat := 4983230072969 + 3 ^ 40 * 3007560 * 2
def baseEnd_3007560 : Nat := 1544323877236358141368489

theorem tailTrace_3007560 : CollatzResearch.WordTrace tailWord_3007560 prefixEnd_3007560 1544323877236358141368489 := by
  unfold tailWord_3007560
  simp only [CollatzResearch.WordTrace]
  refine ⟨54847362492065622599658067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73129816656087496799544089 54847362492065622599658067)
  ·
    refine ⟨82271043738098433899487101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54847362492065622599658067 82271043738098433899487101)
    ·
      refine ⟨30851641401786912712307663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82271043738098433899487101 30851641401786912712307663)
      ·
        refine ⟨46277462102680369068461495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30851641401786912712307663 46277462102680369068461495)
        ·
          refine ⟨69416193154020553602692243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46277462102680369068461495 69416193154020553602692243)
          ·
            refine ⟨104124289731030830404038365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69416193154020553602692243 104124289731030830404038365)
            ·
              refine ⟨39046608649136561401514387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104124289731030830404038365 39046608649136561401514387)
              ·
                refine ⟨58569912973704842102271581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39046608649136561401514387 58569912973704842102271581)
                ·
                  refine ⟨21963717365139315788351843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58569912973704842102271581 21963717365139315788351843)
                  ·
                    refine ⟨32945576047708973682527765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21963717365139315788351843 32945576047708973682527765)
                    ·
                      refine ⟨1544323877236358141368489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32945576047708973682527765 1544323877236358141368489)
                      ·
                        rfl

theorem cell23_3007560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_3007560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007560 prefixEnd_3007560 := by exact prefixLift 3007560
  have htrace : WordTrace (prefixWord ++ tailWord_3007560) baseStart_3007560 baseEnd_3007560 := by
    simpa [prefixWord, tailWord_3007560, baseEnd_3007560] using wordTrace_append hprefix tailTrace_3007560
  have hstable : (prefixWord ++ tailWord_3007560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007560).length < 2 ^ (prefixWord ++ tailWord_3007560).sum := by decide
  have hdescent : baseEnd_3007560 < baseStart_3007560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007581 : List Nat := [1, 4, 4, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_3007581 : Nat := 118140960795 + 3007581 * 2 ^ 59
def prefixEnd_3007581 : Nat := 4983230072969 + 3 ^ 40 * 3007581 * 2
def baseEnd_3007581 : Nat := 1544334660330102559205893

theorem tailTrace_3007581 : CollatzResearch.WordTrace tailWord_3007581 prefixEnd_3007581 1544334660330102559205893 := by
  unfold tailWord_3007581
  simp only [CollatzResearch.WordTrace]
  refine ⟨109695490917055165785830597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73130327278036777190553731 109695490917055165785830597)
  ·
    refine ⟨20567904546947843584843237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109695490917055165785830597 20567904546947843584843237)
    ·
      refine ⟨3856482102552720672158107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20567904546947843584843237 3856482102552720672158107)
      ·
        refine ⟨5784723153829081008237161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3856482102552720672158107 5784723153829081008237161)
        ·
          refine ⟨4338542365371810756177871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5784723153829081008237161 4338542365371810756177871)
          ·
            refine ⟨6507813548057716134266807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4338542365371810756177871 6507813548057716134266807)
            ·
              refine ⟨9761720322086574201400211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6507813548057716134266807 9761720322086574201400211)
              ·
                refine ⟨14642580483129861302100317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9761720322086574201400211 14642580483129861302100317)
                ·
                  refine ⟨5490967681173697988287619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14642580483129861302100317 5490967681173697988287619)
                  ·
                    refine ⟨8236451521760546982431429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5490967681173697988287619 8236451521760546982431429)
                    ·
                      refine ⟨1544334660330102559205893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8236451521760546982431429 1544334660330102559205893)
                      ·
                        rfl

theorem cell23_3007581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_3007581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007581 prefixEnd_3007581 := by exact prefixLift 3007581
  have htrace : WordTrace (prefixWord ++ tailWord_3007581) baseStart_3007581 baseEnd_3007581 := by
    simpa [prefixWord, tailWord_3007581, baseEnd_3007581] using wordTrace_append hprefix tailTrace_3007581
  have hstable : (prefixWord ++ tailWord_3007581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007581).length < 2 ^ (prefixWord ++ tailWord_3007581).sum := by decide
  have hdescent : baseEnd_3007581 < baseStart_3007581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007594 : List Nat := [3, 1, 3, 2, 2, 2, 1, 2, 1, 2, 4]
def baseStart_3007594 : Nat := 118140960795 + 3007594 * 2 ^ 59
def prefixEnd_3007594 : Nat := 4983230072969 + 3 ^ 40 * 3007594 * 2
def baseEnd_3007594 : Nat := 1544341335578611008343333

theorem tailTrace_3007594 : CollatzResearch.WordTrace tailWord_3007594 prefixEnd_3007594 1544341335578611008343333 := by
  unfold tailWord_3007594
  simp only [CollatzResearch.WordTrace]
  refine ⟨27423991266502017251513459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73130643377338712670702557 27423991266502017251513459)
  ·
    refine ⟨41135986899753025877270189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27423991266502017251513459 41135986899753025877270189)
    ·
      refine ⟨15425995087407384703976321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41135986899753025877270189 15425995087407384703976321)
      ·
        refine ⟨11569496315555538527982241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15425995087407384703976321 11569496315555538527982241)
        ·
          refine ⟨8677122236666653895986681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11569496315555538527982241 8677122236666653895986681)
          ·
            refine ⟨6507841677499990421990011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8677122236666653895986681 6507841677499990421990011)
            ·
              refine ⟨9761762516249985632985017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6507841677499990421990011 9761762516249985632985017)
              ·
                refine ⟨7321321887187489224738763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9761762516249985632985017 7321321887187489224738763)
                ·
                  refine ⟨10981982830781233837108145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7321321887187489224738763 10981982830781233837108145)
                  ·
                    refine ⟨8236487123085925377831109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10981982830781233837108145 8236487123085925377831109)
                    ·
                      refine ⟨1544341335578611008343333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8236487123085925377831109 1544341335578611008343333)
                      ·
                        rfl

theorem cell23_3007594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_3007594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007594 prefixEnd_3007594 := by exact prefixLift 3007594
  have htrace : WordTrace (prefixWord ++ tailWord_3007594) baseStart_3007594 baseEnd_3007594 := by
    simpa [prefixWord, tailWord_3007594, baseEnd_3007594] using wordTrace_append hprefix tailTrace_3007594
  have hstable : (prefixWord ++ tailWord_3007594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007594).length < 2 ^ (prefixWord ++ tailWord_3007594).sum := by decide
  have hdescent : baseEnd_3007594 < baseStart_3007594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007610 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7]
def baseStart_3007610 : Nat := 118140960795 + 3007610 * 2 ^ 59
def prefixEnd_3007610 : Nat := 4983230072969 + 3 ^ 40 * 3007610 * 2
def baseEnd_3007610 : Nat := 1544349551269082945743259

theorem tailTrace_3007610 : CollatzResearch.WordTrace tailWord_3007610 prefixEnd_3007610 1544349551269082945743259 := by
  unfold tailWord_3007610
  simp only [CollatzResearch.WordTrace]
  refine ⟨27424137158487525934659071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73131032422633402492424189 27424137158487525934659071)
  ·
    refine ⟨41136205737731288901988607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27424137158487525934659071 41136205737731288901988607)
    ·
      refine ⟨61704308606596933352982911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41136205737731288901988607 61704308606596933352982911)
      ·
        refine ⟨92556462909895400029474367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61704308606596933352982911 92556462909895400029474367)
        ·
          refine ⟨138834694364843100044211551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92556462909895400029474367 138834694364843100044211551)
          ·
            refine ⟨208252041547264650066317327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138834694364843100044211551 208252041547264650066317327)
            ·
              refine ⟨312378062320896975099475991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208252041547264650066317327 312378062320896975099475991)
              ·
                refine ⟨468567093481345462649213987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312378062320896975099475991 468567093481345462649213987)
                ·
                  refine ⟨702850640222018193973820981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 468567093481345462649213987 702850640222018193973820981)
                  ·
                    refine ⟨65892247520814205685045717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 702850640222018193973820981 65892247520814205685045717)
                    ·
                      refine ⟨1544349551269082945743259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 65892247520814205685045717 1544349551269082945743259)
                      ·
                        rfl

theorem cell23_3007610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_3007610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007610 prefixEnd_3007610 := by exact prefixLift 3007610
  have htrace : WordTrace (prefixWord ++ tailWord_3007610) baseStart_3007610 baseEnd_3007610 := by
    simpa [prefixWord, tailWord_3007610, baseEnd_3007610] using wordTrace_append hprefix tailTrace_3007610
  have hstable : (prefixWord ++ tailWord_3007610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007610).length < 2 ^ (prefixWord ++ tailWord_3007610).sum := by decide
  have hdescent : baseEnd_3007610 < baseStart_3007610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007617 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 2, 7]
def baseStart_3007617 : Nat := 118140960795 + 3007617 * 2 ^ 59
def prefixEnd_3007617 : Nat := 4983230072969 + 3 ^ 40 * 3007617 * 2
def baseEnd_3007617 : Nat := 514784381877888139451909

theorem tailTrace_3007617 : CollatzResearch.WordTrace tailWord_3007617 prefixEnd_3007617 514784381877888139451909 := by
  unfold tailWord_3007617
  simp only [CollatzResearch.WordTrace]
  refine ⟨109696803944924743934141105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73131202629949829289427403 109696803944924743934141105)
  ·
    refine ⟨82272602958693557950605829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109696803944924743934141105 82272602958693557950605829)
    ·
      refine ⟨15426113054755042115738593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82272602958693557950605829 15426113054755042115738593)
      ·
        refine ⟨11569584791066281586803945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15426113054755042115738593 11569584791066281586803945)
        ·
          refine ⟨8677188593299711190102959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11569584791066281586803945 8677188593299711190102959)
          ·
            refine ⟨13015782889949566785154439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8677188593299711190102959 13015782889949566785154439)
            ·
              refine ⟨19523674334924350177731659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13015782889949566785154439 19523674334924350177731659)
              ·
                refine ⟨29285511502386525266597489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19523674334924350177731659 29285511502386525266597489)
                ·
                  refine ⟨21964133626789893949948117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29285511502386525266597489 21964133626789893949948117)
                  ·
                    refine ⟨514784381877888139451909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21964133626789893949948117 514784381877888139451909)
                    ·
                      rfl

theorem cell23_3007617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_3007617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007617 prefixEnd_3007617 := by exact prefixLift 3007617
  have htrace : WordTrace (prefixWord ++ tailWord_3007617) baseStart_3007617 baseEnd_3007617 := by
    simpa [prefixWord, tailWord_3007617, baseEnd_3007617] using wordTrace_append hprefix tailTrace_3007617
  have hstable : (prefixWord ++ tailWord_3007617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007617).length < 2 ^ (prefixWord ++ tailWord_3007617).sum := by decide
  have hdescent : baseEnd_3007617 < baseStart_3007617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007667 : List Nat := [1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 4]
def baseStart_3007667 : Nat := 118140960795 + 3007667 * 2 ^ 59
def prefixEnd_3007667 : Nat := 4983230072969 + 3 ^ 40 * 3007667 * 2
def baseEnd_3007667 : Nat := 1544378819666389222730497

theorem tailTrace_3007667 : CollatzResearch.WordTrace tailWord_3007667 prefixEnd_3007667 1544378819666389222730497 := by
  unfold tailWord_3007667
  simp only [CollatzResearch.WordTrace]
  refine ⟨109698627594743602473461255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73132418396495734982307503 109698627594743602473461255)
  ·
    refine ⟨164547941392115403710191883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109698627594743602473461255 164547941392115403710191883)
    ·
      refine ⟨246821912088173105565287825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164547941392115403710191883 246821912088173105565287825)
      ·
        refine ⟨185116434066129829173965869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246821912088173105565287825 185116434066129829173965869)
        ·
          refine ⟨69418662774798685940237201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185116434066129829173965869 69418662774798685940237201)
          ·
            refine ⟨52063997081099014455177901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69418662774798685940237201 52063997081099014455177901)
            ·
              refine ⟨19523998905412130420691713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52063997081099014455177901 19523998905412130420691713)
              ·
                refine ⟨14642999179059097815518785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19523998905412130420691713 14642999179059097815518785)
                ·
                  refine ⟨10982249384294323361639089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14642999179059097815518785 10982249384294323361639089)
                  ·
                    refine ⟨8236687038220742521229317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10982249384294323361639089 8236687038220742521229317)
                    ·
                      refine ⟨1544378819666389222730497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8236687038220742521229317 1544378819666389222730497)
                      ·
                        rfl

theorem cell23_3007667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 4].length) (baseStart_3007667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007667 prefixEnd_3007667 := by exact prefixLift 3007667
  have htrace : WordTrace (prefixWord ++ tailWord_3007667) baseStart_3007667 baseEnd_3007667 := by
    simpa [prefixWord, tailWord_3007667, baseEnd_3007667] using wordTrace_append hprefix tailTrace_3007667
  have hstable : (prefixWord ++ tailWord_3007667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007667).length < 2 ^ (prefixWord ++ tailWord_3007667).sum := by decide
  have hdescent : baseEnd_3007667 < baseStart_3007667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007671 : List Nat := [1, 1, 3, 1, 4, 1, 3, 1, 4, 2, 2]
def baseStart_3007671 : Nat := 118140960795 + 3007671 * 2 ^ 59
def prefixEnd_3007671 : Nat := 4983230072969 + 3 ^ 40 * 3007671 * 2
def baseEnd_3007671 : Nat := 1544380873589007207080479

theorem tailTrace_3007671 : CollatzResearch.WordTrace tailWord_3007671 prefixEnd_3007671 1544380873589007207080479 := by
  unfold tailWord_3007671
  simp only [CollatzResearch.WordTrace]
  refine ⟨109698773486729111156606867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73132515657819407437737911 109698773486729111156606867)
  ·
    refine ⟨164548160230093666734910301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109698773486729111156606867 164548160230093666734910301)
    ·
      refine ⟨61705560086285125025591363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164548160230093666734910301 61705560086285125025591363)
      ·
        refine ⟨92558340129427687538387045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61705560086285125025591363 92558340129427687538387045)
        ·
          refine ⟨17354688774267691413447571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92558340129427687538387045 17354688774267691413447571)
          ·
            refine ⟨26032033161401537120171357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17354688774267691413447571 26032033161401537120171357)
            ·
              refine ⟨9762012435525576420064259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26032033161401537120171357 9762012435525576420064259)
              ·
                refine ⟨14643018653288364630096389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9762012435525576420064259 14643018653288364630096389)
                ·
                  refine ⟨2745565997491568368143073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14643018653288364630096389 2745565997491568368143073)
                  ·
                    refine ⟨2059174498118676276107305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2745565997491568368143073 2059174498118676276107305)
                    ·
                      refine ⟨1544380873589007207080479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2059174498118676276107305 1544380873589007207080479)
                      ·
                        rfl

theorem cell23_3007671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4, 2, 2].length) (baseStart_3007671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007671 prefixEnd_3007671 := by exact prefixLift 3007671
  have htrace : WordTrace (prefixWord ++ tailWord_3007671) baseStart_3007671 baseEnd_3007671 := by
    simpa [prefixWord, tailWord_3007671, baseEnd_3007671] using wordTrace_append hprefix tailTrace_3007671
  have hstable : (prefixWord ++ tailWord_3007671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007671).length < 2 ^ (prefixWord ++ tailWord_3007671).sum := by decide
  have hdescent : baseEnd_3007671 < baseStart_3007671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007677 : List Nat := [1, 4, 1, 2, 1, 1, 3, 3, 7]
def baseStart_3007677 : Nat := 118140960795 + 3007677 * 2 ^ 59
def prefixEnd_3007677 : Nat := 4983230072969 + 3 ^ 40 * 3007677 * 2
def baseEnd_3007677 : Nat := 171598217163659353733939

theorem tailTrace_3007677 : CollatzResearch.WordTrace tailWord_3007677 prefixEnd_3007677 171598217163659353733939 := by
  unfold tailWord_3007677
  simp only [CollatzResearch.WordTrace]
  refine ⟨109698992324707374181325285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73132661549804916120883523 109698992324707374181325285)
  ·
    refine ⟨20568561060882632658998491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109698992324707374181325285 20568561060882632658998491)
    ·
      refine ⟨30852841591323948988497737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20568561060882632658998491 30852841591323948988497737)
      ·
        refine ⟨23139631193492961741373303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30852841591323948988497737 23139631193492961741373303)
        ·
          refine ⟨34709446790239442612059955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23139631193492961741373303 34709446790239442612059955)
          ·
            refine ⟨52064170185359163918089933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34709446790239442612059955 52064170185359163918089933)
            ·
              refine ⟨19524063819509686469283725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52064170185359163918089933 19524063819509686469283725)
              ·
                refine ⟨7321523932316132425981397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19524063819509686469283725 7321523932316132425981397)
                ·
                  refine ⟨171598217163659353733939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7321523932316132425981397 171598217163659353733939)
                  ·
                    rfl

theorem cell23_3007677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 7].length) (baseStart_3007677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007677 prefixEnd_3007677 := by exact prefixLift 3007677
  have htrace : WordTrace (prefixWord ++ tailWord_3007677) baseStart_3007677 baseEnd_3007677 := by
    simpa [prefixWord, tailWord_3007677, baseEnd_3007677] using wordTrace_append hprefix tailTrace_3007677
  have hstable : (prefixWord ++ tailWord_3007677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007677).length < 2 ^ (prefixWord ++ tailWord_3007677).sum := by decide
  have hdescent : baseEnd_3007677 < baseStart_3007677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007682 : List Nat := [3, 5, 1, 1, 3, 1, 1, 1, 1, 3, 3]
def baseStart_3007682 : Nat := 118140960795 + 3007682 * 2 ^ 59
def prefixEnd_3007682 : Nat := 4983230072969 + 3 ^ 40 * 3007682 * 2
def baseEnd_3007682 : Nat := 1544386521876206664042929

theorem tailTrace_3007682 : CollatzResearch.WordTrace tailWord_3007682 prefixEnd_3007682 1544386521876206664042929 := by
  unfold tailWord_3007682
  simp only [CollatzResearch.WordTrace]
  refine ⟨27424793672422315008814325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73132783126459506690171533 27424793672422315008814325)
  ·
    refine ⟨2571074406789592032076343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27424793672422315008814325 2571074406789592032076343)
    ·
      refine ⟨3856611610184388048114515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2571074406789592032076343 3856611610184388048114515)
      ·
        refine ⟨5784917415276582072171773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3856611610184388048114515 5784917415276582072171773)
        ·
          refine ⟨2169344030728718277064415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5784917415276582072171773 2169344030728718277064415)
          ·
            refine ⟨3254016046093077415596623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2169344030728718277064415 3254016046093077415596623)
            ·
              refine ⟨4881024069139616123394935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3254016046093077415596623 4881024069139616123394935)
              ·
                refine ⟨7321536103709424185092403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4881024069139616123394935 7321536103709424185092403)
                ·
                  refine ⟨10982304155564136277638605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7321536103709424185092403 10982304155564136277638605)
                  ·
                    refine ⟨4118364058336551104114477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10982304155564136277638605 4118364058336551104114477)
                    ·
                      refine ⟨1544386521876206664042929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4118364058336551104114477 1544386521876206664042929)
                      ·
                        rfl

theorem cell23_3007682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_3007682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007682 prefixEnd_3007682 := by exact prefixLift 3007682
  have htrace : WordTrace (prefixWord ++ tailWord_3007682) baseStart_3007682 baseEnd_3007682 := by
    simpa [prefixWord, tailWord_3007682, baseEnd_3007682] using wordTrace_append hprefix tailTrace_3007682
  have hstable : (prefixWord ++ tailWord_3007682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007682).length < 2 ^ (prefixWord ++ tailWord_3007682).sum := by decide
  have hdescent : baseEnd_3007682 < baseStart_3007682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007724 : List Nat := [2, 2, 1, 1, 2, 5, 1, 2, 2, 5]
def baseStart_3007724 : Nat := 118140960795 + 3007724 * 2 ^ 59
def prefixEnd_3007724 : Nat := 4983230072969 + 3 ^ 40 * 3007724 * 2
def baseEnd_3007724 : Nat := 514802696021231833239245

theorem tailTrace_3007724 : CollatzResearch.WordTrace tailWord_3007724 prefixEnd_3007724 514802696021231833239245 := by
  unfold tailWord_3007724
  simp only [CollatzResearch.WordTrace]
  refine ⟨54850353277768550604143113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73133804370358067472190817 54850353277768550604143113)
  ·
    refine ⟨41137764958326412953107335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54850353277768550604143113 41137764958326412953107335)
    ·
      refine ⟨61706647437489619429661003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41137764958326412953107335 61706647437489619429661003)
      ·
        refine ⟨92559971156234429144491505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61706647437489619429661003 92559971156234429144491505)
        ·
          refine ⟨69419978367175821858368629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92559971156234429144491505 69419978367175821858368629)
          ·
            refine ⟨6508122971922733299222059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69419978367175821858368629 6508122971922733299222059)
            ·
              refine ⟨9762184457884099948833089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6508122971922733299222059 9762184457884099948833089)
              ·
                refine ⟨7321638343413074961624817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9762184457884099948833089 7321638343413074961624817)
                ·
                  refine ⟨5491228757559806221218613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7321638343413074961624817 5491228757559806221218613)
                  ·
                    refine ⟨514802696021231833239245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5491228757559806221218613 514802696021231833239245)
                    ·
                      rfl

theorem cell23_3007724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 5].length) (baseStart_3007724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007724 prefixEnd_3007724 := by exact prefixLift 3007724
  have htrace : WordTrace (prefixWord ++ tailWord_3007724) baseStart_3007724 baseEnd_3007724 := by
    simpa [prefixWord, tailWord_3007724, baseEnd_3007724] using wordTrace_append hprefix tailTrace_3007724
  have hstable : (prefixWord ++ tailWord_3007724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007724).length < 2 ^ (prefixWord ++ tailWord_3007724).sum := by decide
  have hdescent : baseEnd_3007724 < baseStart_3007724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007744 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 1, 6, 2]
def baseStart_3007744 : Nat := 118140960795 + 3007744 * 2 ^ 59
def prefixEnd_3007744 : Nat := 4983230072969 + 3 ^ 40 * 3007744 * 2
def baseEnd_3007744 : Nat := 1544418357676785421467643

theorem tailTrace_3007744 : CollatzResearch.WordTrace tailWord_3007744 prefixEnd_3007744 1544418357676785421467643 := by
  unfold tailWord_3007744
  simp only [CollatzResearch.WordTrace]
  refine ⟨54850718007732322312007143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73134290676976429749342857 54850718007732322312007143)
  ·
    refine ⟨82276077011598483468010715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54850718007732322312007143 82276077011598483468010715)
    ·
      refine ⟨123414115517397725202016073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82276077011598483468010715 123414115517397725202016073)
      ·
        refine ⟨92560586638048293901512055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123414115517397725202016073 92560586638048293901512055)
        ·
          refine ⟨138840879957072440852268083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92560586638048293901512055 138840879957072440852268083)
          ·
            refine ⟨208261319935608661278402125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138840879957072440852268083 208261319935608661278402125)
            ·
              refine ⟨78097994975853247979400797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208261319935608661278402125 78097994975853247979400797)
              ·
                refine ⟨29286748115944967992275299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78097994975853247979400797 29286748115944967992275299)
                ·
                  refine ⟨43930122173917451988412949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29286748115944967992275299 43930122173917451988412949)
                  ·
                    refine ⟨2059224476902380561956857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 43930122173917451988412949 2059224476902380561956857)
                    ·
                      refine ⟨1544418357676785421467643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2059224476902380561956857 1544418357676785421467643)
                      ·
                        rfl

theorem cell23_3007744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 1, 6, 2].length) (baseStart_3007744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007744 prefixEnd_3007744 := by exact prefixLift 3007744
  have htrace : WordTrace (prefixWord ++ tailWord_3007744) baseStart_3007744 baseEnd_3007744 := by
    simpa [prefixWord, tailWord_3007744, baseEnd_3007744] using wordTrace_append hprefix tailTrace_3007744
  have hstable : (prefixWord ++ tailWord_3007744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007744).length < 2 ^ (prefixWord ++ tailWord_3007744).sum := by decide
  have hdescent : baseEnd_3007744 < baseStart_3007744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007754 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 5, 4]
def baseStart_3007754 : Nat := 118140960795 + 3007754 * 2 ^ 59
def prefixEnd_3007754 : Nat := 4983230072969 + 3 ^ 40 * 3007754 * 2
def baseEnd_3007754 : Nat := 514807830827776794114199

theorem tailTrace_3007754 : CollatzResearch.WordTrace tailWord_3007754 prefixEnd_3007754 514807830827776794114199 := by
  unfold tailWord_3007754
  simp only [CollatzResearch.WordTrace]
  refine ⟨27425450186357104082969579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73134533830285610887918877 27425450186357104082969579)
  ·
    refine ⟨41138175279535656124454369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27425450186357104082969579 41138175279535656124454369)
    ·
      refine ⟨30853631459651742093340777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41138175279535656124454369 30853631459651742093340777)
      ·
        refine ⟨23140223594738806570005583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30853631459651742093340777 23140223594738806570005583)
        ·
          refine ⟨34710335392108209855008375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23140223594738806570005583 34710335392108209855008375)
          ·
            refine ⟨52065503088162314782512563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34710335392108209855008375 52065503088162314782512563)
            ·
              refine ⟨78098254632243472173768845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52065503088162314782512563 78098254632243472173768845)
              ·
                refine ⟨29286845487091302065163317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78098254632243472173768845 29286845487091302065163317)
                ·
                  refine ⟨2745641764414809568609061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29286845487091302065163317 2745641764414809568609061)
                  ·
                    refine ⟨514807830827776794114199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2745641764414809568609061 514807830827776794114199)
                    ·
                      rfl

theorem cell23_3007754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_3007754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007754 prefixEnd_3007754 := by exact prefixLift 3007754
  have htrace : WordTrace (prefixWord ++ tailWord_3007754) baseStart_3007754 baseEnd_3007754 := by
    simpa [prefixWord, tailWord_3007754, baseEnd_3007754] using wordTrace_append hprefix tailTrace_3007754
  have hstable : (prefixWord ++ tailWord_3007754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007754).length < 2 ^ (prefixWord ++ tailWord_3007754).sum := by decide
  have hdescent : baseEnd_3007754 < baseStart_3007754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007771 : List Nat := [1, 1, 1, 1, 1, 1, 5, 7, 1, 4]
def baseStart_3007771 : Nat := 118140960795 + 3007771 * 2 ^ 59
def prefixEnd_3007771 : Nat := 4983230072969 + 3 ^ 40 * 3007771 * 2
def baseEnd_3007771 : Nat := 514810740551485605276673

theorem tailTrace_3007771 : CollatzResearch.WordTrace tailWord_3007771 prefixEnd_3007771 514810740551485605276673 := by
  unfold tailWord_3007771
  simp only [CollatzResearch.WordTrace]
  refine ⟨109702420786366828235247167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73134947190911218823498111 109702420786366828235247167)
  ·
    refine ⟨164553631179550242352870751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109702420786366828235247167 164553631179550242352870751)
    ·
      refine ⟨246830446769325363529306127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164553631179550242352870751 246830446769325363529306127)
      ·
        refine ⟨370245670153988045293959191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246830446769325363529306127 370245670153988045293959191)
        ·
          refine ⟨555368505230982067940938787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370245670153988045293959191 555368505230982067940938787)
          ·
            refine ⟨833052757846473101911408181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555368505230982067940938787 833052757846473101911408181)
            ·
              refine ⟨78098696048106853304194517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 833052757846473101911408181 78098696048106853304194517)
              ·
                refine ⟨1830438188627504374317059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 78098696048106853304194517 1830438188627504374317059)
                ·
                  refine ⟨2745657282941256561475589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1830438188627504374317059 2745657282941256561475589)
                  ·
                    refine ⟨514810740551485605276673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2745657282941256561475589 514810740551485605276673)
                    ·
                      rfl

theorem cell23_3007771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 1, 4].length) (baseStart_3007771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007771 prefixEnd_3007771 := by exact prefixLift 3007771
  have htrace : WordTrace (prefixWord ++ tailWord_3007771) baseStart_3007771 baseEnd_3007771 := by
    simpa [prefixWord, tailWord_3007771, baseEnd_3007771] using wordTrace_append hprefix tailTrace_3007771
  have hstable : (prefixWord ++ tailWord_3007771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007771).length < 2 ^ (prefixWord ++ tailWord_3007771).sum := by decide
  have hdescent : baseEnd_3007771 < baseStart_3007771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007781 : List Nat := [1, 3, 1, 2, 4, 1, 2, 2, 2, 2, 3]
def baseStart_3007781 : Nat := 118140960795 + 3007781 * 2 ^ 59
def prefixEnd_3007781 : Nat := 4983230072969 + 3 ^ 40 * 3007781 * 2
def baseEnd_3007781 : Nat := 1544437356461001776704973

theorem tailTrace_3007781 : CollatzResearch.WordTrace tailWord_3007781 prefixEnd_3007781 1544437356461001776704973 := by
  unfold tailWord_3007781
  simp only [CollatzResearch.WordTrace]
  refine ⟨109702785516330599943111197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73135190344220399962074131 109702785516330599943111197)
  ·
    refine ⟨41138544568623974978666699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109702785516330599943111197 41138544568623974978666699)
    ·
      refine ⟨61707816852935962468000049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41138544568623974978666699 61707816852935962468000049)
      ·
        refine ⟨46280862639701971851000037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61707816852935962468000049 46280862639701971851000037)
        ·
          refine ⟨8677661744944119722062507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46280862639701971851000037 8677661744944119722062507)
          ·
            refine ⟨13016492617416179583093761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8677661744944119722062507 13016492617416179583093761)
            ·
              refine ⟨9762369463062134687320321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13016492617416179583093761 9762369463062134687320321)
              ·
                refine ⟨7321777097296601015490241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9762369463062134687320321 7321777097296601015490241)
                ·
                  refine ⟨5491332822972450761617681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7321777097296601015490241 5491332822972450761617681)
                  ·
                    refine ⟨4118499617229338071213261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5491332822972450761617681 4118499617229338071213261)
                    ·
                      refine ⟨1544437356461001776704973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4118499617229338071213261 1544437356461001776704973)
                      ·
                        rfl

theorem cell23_3007781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_3007781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007781 prefixEnd_3007781 := by exact prefixLift 3007781
  have htrace : WordTrace (prefixWord ++ tailWord_3007781) baseStart_3007781 baseEnd_3007781 := by
    simpa [prefixWord, tailWord_3007781, baseEnd_3007781] using wordTrace_append hprefix tailTrace_3007781
  have hstable : (prefixWord ++ tailWord_3007781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007781).length < 2 ^ (prefixWord ++ tailWord_3007781).sum := by decide
  have hdescent : baseEnd_3007781 < baseStart_3007781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007831 : List Nat := [1, 1, 3, 2, 3, 3, 1, 3, 1, 5]
def baseStart_3007831 : Nat := 118140960795 + 3007831 * 2 ^ 59
def prefixEnd_3007831 : Nat := 4983230072969 + 3 ^ 40 * 3007831 * 2
def baseEnd_3007831 : Nat := 514821010164575527026581

theorem tailTrace_3007831 : CollatzResearch.WordTrace tailWord_3007831 prefixEnd_3007831 514821010164575527026581 := by
  unfold tailWord_3007831
  simp only [CollatzResearch.WordTrace]
  refine ⟨109704609166149458482431347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73136406110766305654954231 109704609166149458482431347)
  ·
    refine ⟨164556913749224187723647021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109704609166149458482431347 164556913749224187723647021)
    ·
      refine ⟨61708842655959070396367633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164556913749224187723647021 61708842655959070396367633)
      ·
        refine ⟨46281631991969302797275725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61708842655959070396367633 46281631991969302797275725)
        ·
          refine ⟨17355611996988488548978397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46281631991969302797275725 17355611996988488548978397)
          ·
            refine ⟨6508354498870683205866899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17355611996988488548978397 6508354498870683205866899)
            ·
              refine ⟨9762531748306024808800349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6508354498870683205866899 9762531748306024808800349)
              ·
                refine ⟨3660949405614759303300131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9762531748306024808800349 3660949405614759303300131)
                ·
                  refine ⟨5491424108422138954950197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3660949405614759303300131 5491424108422138954950197)
                  ·
                    refine ⟨514821010164575527026581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5491424108422138954950197 514821010164575527026581)
                    ·
                      rfl

theorem cell23_3007831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 5].length) (baseStart_3007831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007831 prefixEnd_3007831 := by exact prefixLift 3007831
  have htrace : WordTrace (prefixWord ++ tailWord_3007831) baseStart_3007831 baseEnd_3007831 := by
    simpa [prefixWord, tailWord_3007831, baseEnd_3007831] using wordTrace_append hprefix tailTrace_3007831
  have hstable : (prefixWord ++ tailWord_3007831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007831).length < 2 ^ (prefixWord ++ tailWord_3007831).sum := by decide
  have hdescent : baseEnd_3007831 < baseStart_3007831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007868 : List Nat := [2, 2, 2, 1, 1, 1, 3, 4, 3, 2, 2]
def baseStart_3007868 : Nat := 118140960795 + 3007868 * 2 ^ 59
def prefixEnd_3007868 : Nat := 4983230072969 + 3 ^ 40 * 3007868 * 2
def baseEnd_3007868 : Nat := 1544482029277942936317073

theorem tailTrace_3007868 : CollatzResearch.WordTrace tailWord_3007868 prefixEnd_3007868 1544482029277942936317073 := by
  unfold tailWord_3007868
  simp only [CollatzResearch.WordTrace]
  refine ⟨54852979333507706900764129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73137305778010275867685505 54852979333507706900764129)
  ·
    refine ⟨41139734500130780175573097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54852979333507706900764129 41139734500130780175573097)
    ·
      refine ⟨30854800875098085131679823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41139734500130780175573097 30854800875098085131679823)
      ·
        refine ⟨46282201312647127697519735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30854800875098085131679823 46282201312647127697519735)
        ·
          refine ⟨69423301968970691546279603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46282201312647127697519735 69423301968970691546279603)
          ·
            refine ⟨104134952953456037319419405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69423301968970691546279603 104134952953456037319419405)
            ·
              refine ⟨39050607357546013994782277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104134952953456037319419405 39050607357546013994782277)
              ·
                refine ⟨7321988879539877624021677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39050607357546013994782277 7321988879539877624021677)
                ·
                  refine ⟨2745745829827454109008129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7321988879539877624021677 2745745829827454109008129)
                  ·
                    refine ⟨2059309372370590581756097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2745745829827454109008129 2059309372370590581756097)
                    ·
                      refine ⟨1544482029277942936317073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2059309372370590581756097 1544482029277942936317073)
                      ·
                        rfl

theorem cell23_3007868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 3, 2, 2].length) (baseStart_3007868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007868 prefixEnd_3007868 := by exact prefixLift 3007868
  have htrace : WordTrace (prefixWord ++ tailWord_3007868) baseStart_3007868 baseEnd_3007868 := by
    simpa [prefixWord, tailWord_3007868, baseEnd_3007868] using wordTrace_append hprefix tailTrace_3007868
  have hstable : (prefixWord ++ tailWord_3007868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007868).length < 2 ^ (prefixWord ++ tailWord_3007868).sum := by decide
  have hdescent : baseEnd_3007868 < baseStart_3007868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007904 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 2, 7]
def baseStart_3007904 : Nat := 118140960795 + 3007904 * 2 ^ 59
def prefixEnd_3007904 : Nat := 4983230072969 + 3 ^ 40 * 3007904 * 2
def baseEnd_3007904 : Nat := 514833504860501598488969

theorem tailTrace_3007904 : CollatzResearch.WordTrace tailWord_3007904 prefixEnd_3007904 514833504860501598488969 := by
  unfold tailWord_3007904
  simp only [CollatzResearch.WordTrace]
  refine ⟨54853635847442495974919383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73138181129923327966559177 54853635847442495974919383)
  ·
    refine ⟨82280453771163743962379075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54853635847442495974919383 82280453771163743962379075)
    ·
      refine ⟨123420680656745615943568613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82280453771163743962379075 123420680656745615943568613)
      ·
        refine ⟨23141377623139802989419115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123420680656745615943568613 23141377623139802989419115)
        ·
          refine ⟨34712066434709704484128673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23141377623139802989419115 34712066434709704484128673)
          ·
            refine ⟨26034049826032278363096505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34712066434709704484128673 26034049826032278363096505)
            ·
              refine ⟨19525537369524208772322379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26034049826032278363096505 19525537369524208772322379)
              ·
                refine ⟨29288306054286313158483569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19525537369524208772322379 29288306054286313158483569)
                ·
                  refine ⟨21966229540714734868862677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29288306054286313158483569 21966229540714734868862677)
                  ·
                    refine ⟨514833504860501598488969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21966229540714734868862677 514833504860501598488969)
                    ·
                      rfl

theorem cell23_3007904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 2, 7].length) (baseStart_3007904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007904 prefixEnd_3007904 := by exact prefixLift 3007904
  have htrace : WordTrace (prefixWord ++ tailWord_3007904) baseStart_3007904 baseEnd_3007904 := by
    simpa [prefixWord, tailWord_3007904, baseEnd_3007904] using wordTrace_append hprefix tailTrace_3007904
  have hstable : (prefixWord ++ tailWord_3007904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007904).length < 2 ^ (prefixWord ++ tailWord_3007904).sum := by decide
  have hdescent : baseEnd_3007904 < baseStart_3007904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007958 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_3007958 : Nat := 118140960795 + 3007958 * 2 ^ 59
def prefixEnd_3007958 : Nat := 4983230072969 + 3 ^ 40 * 3007958 * 2
def baseEnd_3007958 : Nat := 1544528242536847584191659

theorem tailTrace_3007958 : CollatzResearch.WordTrace tailWord_3007958 prefixEnd_3007958 1544528242536847584191659 := by
  unfold tailWord_3007958
  simp only [CollatzResearch.WordTrace]
  refine ⟨6856827577293084948269033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73139494157792906114869685 6856827577293084948269033)
  ·
    refine ⟨5142620682969813711201775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6856827577293084948269033 5142620682969813711201775)
    ·
      refine ⟨7713931024454720566802663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5142620682969813711201775 7713931024454720566802663)
      ·
        refine ⟨11570896536682080850203995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7713931024454720566802663 11570896536682080850203995)
        ·
          refine ⟨17356344805023121275305993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11570896536682080850203995 17356344805023121275305993)
          ·
            refine ⟨13017258603767340956479495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17356344805023121275305993 13017258603767340956479495)
            ·
              refine ⟨19525887905651011434719243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13017258603767340956479495 19525887905651011434719243)
              ·
                refine ⟨29288831858476517152078865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19525887905651011434719243 29288831858476517152078865)
                ·
                  refine ⟨21966623893857387864059149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29288831858476517152078865 21966623893857387864059149)
                  ·
                    refine ⟨8237483960196520449022181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21966623893857387864059149 8237483960196520449022181)
                    ·
                      refine ⟨1544528242536847584191659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8237483960196520449022181 1544528242536847584191659)
                      ·
                        rfl

theorem cell23_3007958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_3007958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007958 prefixEnd_3007958 := by exact prefixLift 3007958
  have htrace : WordTrace (prefixWord ++ tailWord_3007958) baseStart_3007958 baseEnd_3007958 := by
    simpa [prefixWord, tailWord_3007958, baseEnd_3007958] using wordTrace_append hprefix tailTrace_3007958
  have hstable : (prefixWord ++ tailWord_3007958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007958).length < 2 ^ (prefixWord ++ tailWord_3007958).sum := by decide
  have hdescent : baseEnd_3007958 < baseStart_3007958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007961 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 2, 4, 3]
def baseStart_3007961 : Nat := 118140960795 + 3007961 * 2 ^ 59
def prefixEnd_3007961 : Nat := 4983230072969 + 3 ^ 40 * 3007961 * 2
def baseEnd_3007961 : Nat := 1544529782978811072454145

theorem tailTrace_3007961 : CollatzResearch.WordTrace tailWord_3007961 prefixEnd_3007961 1544529782978811072454145 := by
  unfold tailWord_3007961
  simp only [CollatzResearch.WordTrace]
  refine ⟨109709350655678490684663737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73139567103785660456442491 109709350655678490684663737)
  ·
    refine ⟨82282012991758868013497803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109709350655678490684663737 82282012991758868013497803)
    ·
      refine ⟨123423019487638302020246705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82282012991758868013497803 123423019487638302020246705)
      ·
        refine ⟨92567264615728726515185029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123423019487638302020246705 92567264615728726515185029)
        ·
          refine ⟨17356362115449136221597193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92567264615728726515185029 17356362115449136221597193)
          ·
            refine ⟨13017271586586852166197895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17356362115449136221597193 13017271586586852166197895)
            ·
              refine ⟨19525907379880278249296843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13017271586586852166197895 19525907379880278249296843)
              ·
                refine ⟨29288861069820417373945265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19525907379880278249296843 29288861069820417373945265)
                ·
                  refine ⟨21966645802365313030458949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29288861069820417373945265 21966645802365313030458949)
                  ·
                    refine ⟨4118746087943496193211053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21966645802365313030458949 4118746087943496193211053)
                    ·
                      refine ⟨1544529782978811072454145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4118746087943496193211053 1544529782978811072454145)
                      ·
                        rfl

theorem cell23_3007961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 4, 3].length) (baseStart_3007961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007961 prefixEnd_3007961 := by exact prefixLift 3007961
  have htrace : WordTrace (prefixWord ++ tailWord_3007961) baseStart_3007961 baseEnd_3007961 := by
    simpa [prefixWord, tailWord_3007961, baseEnd_3007961] using wordTrace_append hprefix tailTrace_3007961
  have hstable : (prefixWord ++ tailWord_3007961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007961).length < 2 ^ (prefixWord ++ tailWord_3007961).sum := by decide
  have hdescent : baseEnd_3007961 < baseStart_3007961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007971 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 4]
def baseStart_3007971 : Nat := 118140960795 + 3007971 * 2 ^ 59
def prefixEnd_3007971 : Nat := 4983230072969 + 3 ^ 40 * 3007971 * 2
def baseEnd_3007971 : Nat := 1544534917785356033329099

theorem tailTrace_3007971 : CollatzResearch.WordTrace tailWord_3007971 prefixEnd_3007971 1544534917785356033329099 := by
  unfold tailWord_3007971
  simp only [CollatzResearch.WordTrace]
  refine ⟨109709715385642262392527767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73139810257094841595018511 109709715385642262392527767)
  ·
    refine ⟨164564573078463393588791651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109709715385642262392527767 164564573078463393588791651)
    ·
      refine ⟨246846859617695090383187477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164564573078463393588791651 246846859617695090383187477)
      ·
        refine ⟨11570946544579457361711913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 246846859617695090383187477 11570946544579457361711913)
        ·
          refine ⟨8678209908434593021283935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11570946544579457361711913 8678209908434593021283935)
          ·
            refine ⟨13017314862651889531925903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8678209908434593021283935 13017314862651889531925903)
            ·
              refine ⟨19525972293977834297888855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13017314862651889531925903 19525972293977834297888855)
              ·
                refine ⟨29288958440966751446833283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19525972293977834297888855 29288958440966751446833283)
                ·
                  refine ⟨43933437661450127170249925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29288958440966751446833283 43933437661450127170249925)
                  ·
                    refine ⟨8237519561521898844421861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43933437661450127170249925 8237519561521898844421861)
                    ·
                      refine ⟨1544534917785356033329099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8237519561521898844421861 1544534917785356033329099)
                      ·
                        rfl

theorem cell23_3007971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_3007971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007971 prefixEnd_3007971 := by exact prefixLift 3007971
  have htrace : WordTrace (prefixWord ++ tailWord_3007971) baseStart_3007971 baseEnd_3007971 := by
    simpa [prefixWord, tailWord_3007971, baseEnd_3007971] using wordTrace_append hprefix tailTrace_3007971
  have hstable : (prefixWord ++ tailWord_3007971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007971).length < 2 ^ (prefixWord ++ tailWord_3007971).sum := by decide
  have hdescent : baseEnd_3007971 < baseStart_3007971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3007975 : List Nat := [1, 1, 5, 2, 1, 3, 2, 1, 1, 4, 2]
def baseStart_3007975 : Nat := 118140960795 + 3007975 * 2 ^ 59
def prefixEnd_3007975 : Nat := 4983230072969 + 3 ^ 40 * 3007975 * 2
def baseEnd_3007975 : Nat := 1544536971707974017679081

theorem tailTrace_3007975 : CollatzResearch.WordTrace tailWord_3007975 prefixEnd_3007975 1544536971707974017679081 := by
  unfold tailWord_3007975
  simp only [CollatzResearch.WordTrace]
  refine ⟨109709861277627771075673379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73139907518418514050448919 109709861277627771075673379)
  ·
    refine ⟨164564791916441656613510069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109709861277627771075673379 164564791916441656613510069)
    ·
      refine ⟨15427949242166405307516569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164564791916441656613510069 15427949242166405307516569)
      ·
        refine ⟨11570961931624803980637427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15427949242166405307516569 11570961931624803980637427)
        ·
          refine ⟨17356442897437205970956141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11570961931624803980637427 17356442897437205970956141)
          ·
            refine ⟨6508666086538952239108553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17356442897437205970956141 6508666086538952239108553)
            ·
              refine ⟨4881499564904214179331415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6508666086538952239108553 4881499564904214179331415)
              ·
                refine ⟨7322249347356321268997123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4881499564904214179331415 7322249347356321268997123)
                ·
                  refine ⟨10983374021034481903495685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7322249347356321268997123 10983374021034481903495685)
                  ·
                    refine ⟨2059382628943965356905441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10983374021034481903495685 2059382628943965356905441)
                    ·
                      refine ⟨1544536971707974017679081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2059382628943965356905441 1544536971707974017679081)
                      ·
                        rfl

theorem cell23_3007975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_3007975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3007975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3007975 prefixEnd_3007975 := by exact prefixLift 3007975
  have htrace : WordTrace (prefixWord ++ tailWord_3007975) baseStart_3007975 baseEnd_3007975 := by
    simpa [prefixWord, tailWord_3007975, baseEnd_3007975] using wordTrace_append hprefix tailTrace_3007975
  have hstable : (prefixWord ++ tailWord_3007975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3007975).length < 2 ^ (prefixWord ++ tailWord_3007975).sum := by decide
  have hdescent : baseEnd_3007975 < baseStart_3007975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3007975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008031 : List Nat := [1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 4]
def baseStart_3008031 : Nat := 118140960795 + 3008031 * 2 ^ 59
def prefixEnd_3008031 : Nat := 4983230072969 + 3 ^ 40 * 3008031 * 2
def baseEnd_3008031 : Nat := 1544565726624625798578823

theorem tailTrace_3008031 : CollatzResearch.WordTrace tailWord_3008031 prefixEnd_3008031 1544565726624625798578823 := by
  unfold tailWord_3008031
  simp only [CollatzResearch.WordTrace]
  refine ⟨109711903765424892639711947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73141269176949928426474631 109711903765424892639711947)
  ·
    refine ⟨164567855648137338959567921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109711903765424892639711947 164567855648137338959567921)
    ·
      refine ⟨123425891736103004219675941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164567855648137338959567921 123425891736103004219675941)
      ·
        refine ⟨23142354700519313291189239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123425891736103004219675941 23142354700519313291189239)
        ·
          refine ⟨34713532050778969936783859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23142354700519313291189239 34713532050778969936783859)
          ·
            refine ⟨52070298076168454905175789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34713532050778969936783859 52070298076168454905175789)
            ·
              refine ⟨19526361778563170589440921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52070298076168454905175789 19526361778563170589440921)
              ·
                refine ⟨14644771333922377942080691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19526361778563170589440921 14644771333922377942080691)
                ·
                  refine ⟨21967157000883566913121037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14644771333922377942080691 21967157000883566913121037)
                  ·
                    refine ⟨8237683875331337592420389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21967157000883566913121037 8237683875331337592420389)
                    ·
                      refine ⟨1544565726624625798578823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8237683875331337592420389 1544565726624625798578823)
                      ·
                        rfl

theorem cell23_3008031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_3008031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008031 prefixEnd_3008031 := by exact prefixLift 3008031
  have htrace : WordTrace (prefixWord ++ tailWord_3008031) baseStart_3008031 baseEnd_3008031 := by
    simpa [prefixWord, tailWord_3008031, baseEnd_3008031] using wordTrace_append hprefix tailTrace_3008031
  have hstable : (prefixWord ++ tailWord_3008031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008031).length < 2 ^ (prefixWord ++ tailWord_3008031).sum := by decide
  have hdescent : baseEnd_3008031 < baseStart_3008031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008131 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 5, 6]
def baseStart_3008131 : Nat := 118140960795 + 3008131 * 2 ^ 59
def prefixEnd_3008131 : Nat := 4983230072969 + 3 ^ 40 * 3008131 * 2
def baseEnd_3008131 : Nat := 514872358230025135776121

theorem tailTrace_3008131 : CollatzResearch.WordTrace tailWord_3008131 prefixEnd_3008131 514872358230025135776121 := by
  unfold tailWord_3008131
  simp only [CollatzResearch.WordTrace]
  refine ⟨109715551065062609718352247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73143700710041739812234831 109715551065062609718352247)
  ·
    refine ⟨164573326597593914577528371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109715551065062609718352247 164573326597593914577528371)
    ·
      refine ⟨246859989896390871866292557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164573326597593914577528371 246859989896390871866292557)
      ·
        refine ⟨92572496211146576949859709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246859989896390871866292557 92572496211146576949859709)
        ·
          refine ⟨34714686079179966356197391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92572496211146576949859709 34714686079179966356197391)
          ·
            refine ⟨52072029118769949534296087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34714686079179966356197391 52072029118769949534296087)
            ·
              refine ⟨78108043678154924301444131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52072029118769949534296087 78108043678154924301444131)
              ·
                refine ⟨117162065517232386452166197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78108043678154924301444131 117162065517232386452166197)
                ·
                  refine ⟨10983943642240536229890581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117162065517232386452166197 10983943642240536229890581)
                  ·
                    refine ⟨514872358230025135776121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10983943642240536229890581 514872358230025135776121)
                    ·
                      rfl

theorem cell23_3008131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 6].length) (baseStart_3008131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008131 prefixEnd_3008131 := by exact prefixLift 3008131
  have htrace : WordTrace (prefixWord ++ tailWord_3008131) baseStart_3008131 baseEnd_3008131 := by
    simpa [prefixWord, tailWord_3008131, baseEnd_3008131] using wordTrace_append hprefix tailTrace_3008131
  have hstable : (prefixWord ++ tailWord_3008131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008131).length < 2 ^ (prefixWord ++ tailWord_3008131).sum := by decide
  have hdescent : baseEnd_3008131 < baseStart_3008131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008175 : List Nat := [1, 1, 2, 1, 2, 4, 3, 3, 1, 2, 3]
def baseStart_3008175 : Nat := 118140960795 + 3008175 * 2 ^ 59
def prefixEnd_3008175 : Nat := 4983230072969 + 3 ^ 40 * 3008175 * 2
def baseEnd_3008175 : Nat := 1544639667838873235178161

theorem tailTrace_3008175 : CollatzResearch.WordTrace tailWord_3008175 prefixEnd_3008175 1544639667838873235178161 := by
  unfold tailWord_3008175
  simp only [CollatzResearch.WordTrace]
  refine ⟨109717155876903205232953979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73144770584602136821969319 109717155876903205232953979)
  ·
    refine ⟨164575733815354807849430969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109717155876903205232953979 164575733815354807849430969)
    ·
      refine ⟨123431800361516105887073227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164575733815354807849430969 123431800361516105887073227)
      ·
        refine ⟨185147700542274158830609841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123431800361516105887073227 185147700542274158830609841)
        ·
          refine ⟨138860775406705619122957381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185147700542274158830609841 138860775406705619122957381)
          ·
            refine ⟨26036395388757303585554509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138860775406705619122957381 26036395388757303585554509)
            ·
              refine ⟨9763648270783988844582941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26036395388757303585554509 9763648270783988844582941)
              ·
                refine ⟨3661368101543995816718603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9763648270783988844582941 3661368101543995816718603)
                ·
                  refine ⟨5492052152315993725077905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3661368101543995816718603 5492052152315993725077905)
                  ·
                    refine ⟨4119039114236995293808429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5492052152315993725077905 4119039114236995293808429)
                    ·
                      refine ⟨1544639667838873235178161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4119039114236995293808429 1544639667838873235178161)
                      ·
                        rfl

theorem cell23_3008175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 2, 3].length) (baseStart_3008175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008175 prefixEnd_3008175 := by exact prefixLift 3008175
  have htrace : WordTrace (prefixWord ++ tailWord_3008175) baseStart_3008175 baseEnd_3008175 := by
    simpa [prefixWord, tailWord_3008175, baseEnd_3008175] using wordTrace_append hprefix tailTrace_3008175
  have hstable : (prefixWord ++ tailWord_3008175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008175).length < 2 ^ (prefixWord ++ tailWord_3008175).sum := by decide
  have hdescent : baseEnd_3008175 < baseStart_3008175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008189 : List Nat := [1, 4, 1, 2, 1, 2, 1, 6, 1, 2, 2]
def baseStart_3008189 : Nat := 118140960795 + 3008189 * 2 ^ 59
def prefixEnd_3008189 : Nat := 4983230072969 + 3 ^ 40 * 3008189 * 2
def baseEnd_3008189 : Nat := 1544646856568036180403097

theorem tailTrace_3008189 : CollatzResearch.WordTrace tailWord_3008189 prefixEnd_3008189 1544646856568036180403097 := by
  unfold tailWord_3008189
  simp only [CollatzResearch.WordTrace]
  refine ⟨109717666498852485623963621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73145110999234990415975747 109717666498852485623963621)
  ·
    refine ⟨20572062468534841054493179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109717666498852485623963621 20572062468534841054493179)
    ·
      refine ⟨30858093702802261581739769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20572062468534841054493179 30858093702802261581739769)
      ·
        refine ⟨23143570277101696186304827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30858093702802261581739769 23143570277101696186304827)
        ·
          refine ⟨34715355415652544279457241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23143570277101696186304827 34715355415652544279457241)
          ·
            refine ⟨26036516561739408209592931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34715355415652544279457241 26036516561739408209592931)
            ·
              refine ⟨39054774842609112314389397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26036516561739408209592931 39054774842609112314389397)
              ·
                refine ⟨1830692570747302139737003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39054774842609112314389397 1830692570747302139737003)
                ·
                  refine ⟨2746038856120953209605505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1830692570747302139737003 2746038856120953209605505)
                  ·
                    refine ⟨2059529142090714907204129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2746038856120953209605505 2059529142090714907204129)
                    ·
                      refine ⟨1544646856568036180403097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2059529142090714907204129 1544646856568036180403097)
                      ·
                        rfl

theorem cell23_3008189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_3008189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008189 prefixEnd_3008189 := by exact prefixLift 3008189
  have htrace : WordTrace (prefixWord ++ tailWord_3008189) baseStart_3008189 baseEnd_3008189 := by
    simpa [prefixWord, tailWord_3008189, baseEnd_3008189] using wordTrace_append hprefix tailTrace_3008189
  have hstable : (prefixWord ++ tailWord_3008189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008189).length < 2 ^ (prefixWord ++ tailWord_3008189).sum := by decide
  have hdescent : baseEnd_3008189 < baseStart_3008189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008202 : List Nat := [3, 1, 2, 1, 5, 2, 1, 1, 1, 2, 4]
def baseStart_3008202 : Nat := 118140960795 + 3008202 * 2 ^ 59
def prefixEnd_3008202 : Nat := 4983230072969 + 3 ^ 40 * 3008202 * 2
def baseEnd_3008202 : Nat := 1544653531816544629540537

theorem tailTrace_3008202 : CollatzResearch.WordTrace tailWord_3008202 prefixEnd_3008202 1544653531816544629540537 := by
  unfold tailWord_3008202
  simp only [CollatzResearch.WordTrace]
  refine ⟨27429535161951347211046715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73145427098536925896124573 27429535161951347211046715)
  ·
    refine ⟨41144302742927020816570073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27429535161951347211046715 41144302742927020816570073)
    ·
      refine ⟨30858227057195265612427555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41144302742927020816570073 30858227057195265612427555)
      ·
        refine ⟨46287340585792898418641333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30858227057195265612427555 46287340585792898418641333)
        ·
          refine ⟨4339438179918084226747625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46287340585792898418641333 4339438179918084226747625)
          ·
            refine ⟨3254578634938563170060719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4339438179918084226747625 3254578634938563170060719)
            ·
              refine ⟨4881867952407844755091079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3254578634938563170060719 4881867952407844755091079)
              ·
                refine ⟨7322801928611767132636619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4881867952407844755091079 7322801928611767132636619)
                ·
                  refine ⟨10984202892917650698954929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7322801928611767132636619 10984202892917650698954929)
                  ·
                    refine ⟨8238152169688238024216197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10984202892917650698954929 8238152169688238024216197)
                    ·
                      refine ⟨1544653531816544629540537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8238152169688238024216197 1544653531816544629540537)
                      ·
                        rfl

theorem cell23_3008202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_3008202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008202 prefixEnd_3008202 := by exact prefixLift 3008202
  have htrace : WordTrace (prefixWord ++ tailWord_3008202) baseStart_3008202 baseEnd_3008202 := by
    simpa [prefixWord, tailWord_3008202, baseEnd_3008202] using wordTrace_append hprefix tailTrace_3008202
  have hstable : (prefixWord ++ tailWord_3008202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008202).length < 2 ^ (prefixWord ++ tailWord_3008202).sum := by decide
  have hdescent : baseEnd_3008202 < baseStart_3008202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008212 : List Nat := [2, 4, 1, 3, 1, 3, 2, 7]
def baseStart_3008212 : Nat := 118140960795 + 3008212 * 2 ^ 59
def prefixEnd_3008212 : Nat := 4983230072969 + 3 ^ 40 * 3008212 * 2
def baseEnd_3008212 : Nat := 57209580245299614459833

theorem tailTrace_3008212 : CollatzResearch.WordTrace tailWord_3008212 prefixEnd_3008212 57209580245299614459833 := by
  unfold tailWord_3008212
  simp only [CollatzResearch.WordTrace]
  refine ⟨54859252688884580276025445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73145670251846107034700593 54859252688884580276025445)
  ·
    refine ⟨10286109879165858801754771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54859252688884580276025445 10286109879165858801754771)
    ·
      refine ⟨15429164818748788202632157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10286109879165858801754771 15429164818748788202632157)
      ·
        refine ⟨5785936807030795575987059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15429164818748788202632157 5785936807030795575987059)
        ·
          refine ⟨8678905210546193363980589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5785936807030795575987059 8678905210546193363980589)
          ·
            refine ⟨3254589453954822511492721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8678905210546193363980589 3254589453954822511492721)
            ·
              refine ⟨2440942090466116883619541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3254589453954822511492721 2440942090466116883619541)
              ·
                refine ⟨57209580245299614459833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2440942090466116883619541 57209580245299614459833)
                ·
                  rfl

theorem cell23_3008212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 7].length) (baseStart_3008212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008212 prefixEnd_3008212 := by exact prefixLift 3008212
  have htrace : WordTrace (prefixWord ++ tailWord_3008212) baseStart_3008212 baseEnd_3008212 := by
    simpa [prefixWord, tailWord_3008212, baseEnd_3008212] using wordTrace_append hprefix tailTrace_3008212
  have hstable : (prefixWord ++ tailWord_3008212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008212).length < 2 ^ (prefixWord ++ tailWord_3008212).sum := by decide
  have hdescent : baseEnd_3008212 < baseStart_3008212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008218 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5]
def baseStart_3008218 : Nat := 118140960795 + 3008218 * 2 ^ 59
def prefixEnd_3008218 : Nat := 4983230072969 + 3 ^ 40 * 3008218 * 2
def baseEnd_3008218 : Nat := 1544661747507016566940463

theorem tailTrace_3008218 : CollatzResearch.WordTrace tailWord_3008218 prefixEnd_3008218 1544661747507016566940463 := by
  unfold tailWord_3008218
  simp only [CollatzResearch.WordTrace]
  refine ⟨27429681053936855894192327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73145816143831615717846205 27429681053936855894192327)
  ·
    refine ⟨41144521580905283841288491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27429681053936855894192327 41144521580905283841288491)
    ·
      refine ⟨61716782371357925761932737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41144521580905283841288491 61716782371357925761932737)
      ·
        refine ⟨46287586778518444321449553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61716782371357925761932737 46287586778518444321449553)
        ·
          refine ⟨34715690083888833241087165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46287586778518444321449553 34715690083888833241087165)
          ·
            refine ⟨13018383781458312465407687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34715690083888833241087165 13018383781458312465407687)
            ·
              refine ⟨19527575672187468698111531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13018383781458312465407687 19527575672187468698111531)
              ·
                refine ⟨29291363508281203047167297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19527575672187468698111531 29291363508281203047167297)
                ·
                  refine ⟨21968522631210902285375473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29291363508281203047167297 21968522631210902285375473)
                  ·
                    refine ⟨16476391973408176714031605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21968522631210902285375473 16476391973408176714031605)
                    ·
                      refine ⟨1544661747507016566940463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16476391973408176714031605 1544661747507016566940463)
                      ·
                        rfl

theorem cell23_3008218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_3008218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008218 prefixEnd_3008218 := by exact prefixLift 3008218
  have htrace : WordTrace (prefixWord ++ tailWord_3008218) baseStart_3008218 baseEnd_3008218 := by
    simpa [prefixWord, tailWord_3008218, baseEnd_3008218] using wordTrace_append hprefix tailTrace_3008218
  have hstable : (prefixWord ++ tailWord_3008218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008218).length < 2 ^ (prefixWord ++ tailWord_3008218).sum := by decide
  have hdescent : baseEnd_3008218 < baseStart_3008218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008268 : List Nat := [2, 2, 1, 2, 2, 1, 2, 4, 7]
def baseStart_3008268 : Nat := 118140960795 + 3008268 * 2 ^ 59
def prefixEnd_3008268 : Nat := 4983230072969 + 3 ^ 40 * 3008268 * 2
def baseEnd_3008268 : Nat := 171631935726637930146137

theorem tailTrace_3008268 : CollatzResearch.WordTrace tailWord_3008268 prefixEnd_3008268 171631935726637930146137 := by
  unfold tailWord_3008268
  simp only [CollatzResearch.WordTrace]
  refine ⟨54860273932783141058044729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73147031910377521410726305 54860273932783141058044729)
  ·
    refine ⟨41145205449587355793533547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54860273932783141058044729 41145205449587355793533547)
    ·
      refine ⟨61717808174381033690300321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41145205449587355793533547 61717808174381033690300321)
      ·
        refine ⟨46288356130785775267725241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61717808174381033690300321 46288356130785775267725241)
        ·
          refine ⟨34716267098089331450793931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46288356130785775267725241 34716267098089331450793931)
          ·
            refine ⟨52074400647133997176190897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34716267098089331450793931 52074400647133997176190897)
            ·
              refine ⟨39055800485350497882143173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52074400647133997176190897 39055800485350497882143173)
              ·
                refine ⟨7322962591003218352901845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39055800485350497882143173 7322962591003218352901845)
                ·
                  refine ⟨171631935726637930146137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7322962591003218352901845 171631935726637930146137)
                  ·
                    rfl

theorem cell23_3008268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 7].length) (baseStart_3008268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008268 prefixEnd_3008268 := by exact prefixLift 3008268
  have htrace : WordTrace (prefixWord ++ tailWord_3008268) baseStart_3008268 baseEnd_3008268 := by
    simpa [prefixWord, tailWord_3008268, baseEnd_3008268] using wordTrace_append hprefix tailTrace_3008268
  have hstable : (prefixWord ++ tailWord_3008268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008268).length < 2 ^ (prefixWord ++ tailWord_3008268).sum := by decide
  have hdescent : baseEnd_3008268 < baseStart_3008268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008296 : List Nat := [2, 1, 5, 1, 1, 3, 2, 2, 2, 2, 2]
def baseStart_3008296 : Nat := 118140960795 + 3008296 * 2 ^ 59
def prefixEnd_3008296 : Nat := 4983230072969 + 3 ^ 40 * 3008296 * 2
def baseEnd_3008296 : Nat := 1544701798998067261765105

theorem tailTrace_3008296 : CollatzResearch.WordTrace tailWord_3008296 prefixEnd_3008296 1544701798998067261765105 := by
  unfold tailWord_3008296
  simp only [CollatzResearch.WordTrace]
  refine ⟨54860784554732421449054371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73147712739643228598739161 54860784554732421449054371)
  ·
    refine ⟨82291176832098632173581557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54860784554732421449054371 82291176832098632173581557)
    ·
      refine ⟨7714797828009246766273271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82291176832098632173581557 7714797828009246766273271)
      ·
        refine ⟨11572196742013870149409907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7714797828009246766273271 11572196742013870149409907)
        ·
          refine ⟨17358295113020805224114861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11572196742013870149409907 17358295113020805224114861)
          ·
            refine ⟨6509360667382801959043073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17358295113020805224114861 6509360667382801959043073)
            ·
              refine ⟨4882020500537101469282305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6509360667382801959043073 4882020500537101469282305)
              ·
                refine ⟨3661515375402826101961729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4882020500537101469282305 3661515375402826101961729)
                ·
                  refine ⟨2746136531552119576471297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3661515375402826101961729 2746136531552119576471297)
                  ·
                    refine ⟨2059602398664089682353473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2746136531552119576471297 2059602398664089682353473)
                    ·
                      refine ⟨1544701798998067261765105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2059602398664089682353473 1544701798998067261765105)
                      ·
                        rfl

theorem cell23_3008296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_3008296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008296 prefixEnd_3008296 := by exact prefixLift 3008296
  have htrace : WordTrace (prefixWord ++ tailWord_3008296) baseStart_3008296 baseEnd_3008296 := by
    simpa [prefixWord, tailWord_3008296, baseEnd_3008296] using wordTrace_append hprefix tailTrace_3008296
  have hstable : (prefixWord ++ tailWord_3008296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008296).length < 2 ^ (prefixWord ++ tailWord_3008296).sum := by decide
  have hdescent : baseEnd_3008296 < baseStart_3008296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008345 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 5, 4]
def baseStart_3008345 : Nat := 118140960795 + 3008345 * 2 ^ 59
def prefixEnd_3008345 : Nat := 4983230072969 + 3 ^ 40 * 3008345 * 2
def baseEnd_3008345 : Nat := 514908986516712523350793

theorem tailTrace_3008345 : CollatzResearch.WordTrace tailWord_3008345 prefixEnd_3008345 514908986516712523350793 := by
  unfold tailWord_3008345
  simp only [CollatzResearch.WordTrace]
  refine ⟨109723356286287324266642489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73148904190858216177761659 109723356286287324266642489)
  ·
    refine ⟨82292517214715493199981867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109723356286287324266642489 82292517214715493199981867)
    ·
      refine ⟨123438775822073239799972801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82292517214715493199981867 123438775822073239799972801)
      ·
        refine ⟨92579081866554929849979601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123438775822073239799972801 92579081866554929849979601)
        ·
          refine ⟨69434311399916197387484701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92579081866554929849979601 69434311399916197387484701)
          ·
            refine ⟨26037866774968574020306763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69434311399916197387484701 26037866774968574020306763)
            ·
              refine ⟨39056800162452861030460145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26037866774968574020306763 39056800162452861030460145)
              ·
                refine ⟨29292600121839645772845109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39056800162452861030460145 29292600121839645772845109)
                ·
                  refine ⟨2746181261422466791204229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29292600121839645772845109 2746181261422466791204229)
                  ·
                    refine ⟨514908986516712523350793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2746181261422466791204229 514908986516712523350793)
                    ·
                      rfl

theorem cell23_3008345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5, 4].length) (baseStart_3008345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008345 prefixEnd_3008345 := by exact prefixLift 3008345
  have htrace : WordTrace (prefixWord ++ tailWord_3008345) baseStart_3008345 baseEnd_3008345 := by
    simpa [prefixWord, tailWord_3008345, baseEnd_3008345] using wordTrace_append hprefix tailTrace_3008345
  have hstable : (prefixWord ++ tailWord_3008345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008345).length < 2 ^ (prefixWord ++ tailWord_3008345).sum := by decide
  have hdescent : baseEnd_3008345 < baseStart_3008345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008352 : List Nat := [2, 1, 1, 3, 3, 2, 1, 2, 2, 4, 2]
def baseStart_3008352 : Nat := 118140960795 + 3008352 * 2 ^ 59
def prefixEnd_3008352 : Nat := 4983230072969 + 3 ^ 40 * 3008352 * 2
def baseEnd_3008352 : Nat := 1544730553914719042664847

theorem tailTrace_3008352 : CollatzResearch.WordTrace tailWord_3008352 prefixEnd_3008352 1544730553914719042664847 := by
  unfold tailWord_3008352
  simp only [CollatzResearch.WordTrace]
  refine ⟨54861805798630982231073655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73149074398174642974764873 54861805798630982231073655)
  ·
    refine ⟨82292708697946473346610483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54861805798630982231073655 82292708697946473346610483)
    ·
      refine ⟨123439063046919710019915725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82292708697946473346610483 123439063046919710019915725)
      ·
        refine ⟨46289648642594891257468397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123439063046919710019915725 46289648642594891257468397)
        ·
          refine ⟨17358618240973084221550649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46289648642594891257468397 17358618240973084221550649)
          ·
            refine ⟨13018963680729813166162987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17358618240973084221550649 13018963680729813166162987)
            ·
              refine ⟨19528445521094719749244481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13018963680729813166162987 19528445521094719749244481)
              ·
                refine ⟨14646334140821039811933361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19528445521094719749244481 14646334140821039811933361)
                ·
                  refine ⟨10984750605615779858950021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14646334140821039811933361 10984750605615779858950021)
                  ·
                    refine ⟨2059640738552958723553129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10984750605615779858950021 2059640738552958723553129)
                    ·
                      refine ⟨1544730553914719042664847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2059640738552958723553129 1544730553914719042664847)
                      ·
                        rfl

theorem cell23_3008352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 2, 4, 2].length) (baseStart_3008352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008352 prefixEnd_3008352 := by exact prefixLift 3008352
  have htrace : WordTrace (prefixWord ++ tailWord_3008352) baseStart_3008352 baseEnd_3008352 := by
    simpa [prefixWord, tailWord_3008352, baseEnd_3008352] using wordTrace_append hprefix tailTrace_3008352
  have hstable : (prefixWord ++ tailWord_3008352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008352).length < 2 ^ (prefixWord ++ tailWord_3008352).sum := by decide
  have hdescent : baseEnd_3008352 < baseStart_3008352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008435 : List Nat := [1, 1, 1, 2, 3, 1, 4, 3, 1, 6]
def baseStart_3008435 : Nat := 118140960795 + 3008435 * 2 ^ 59
def prefixEnd_3008435 : Nat := 4983230072969 + 3 ^ 40 * 3008435 * 2
def baseEnd_3008435 : Nat := 514924390936347405975655

theorem tailTrace_3008435 : CollatzResearch.WordTrace tailWord_3008435 prefixEnd_3008435 514924390936347405975655 := by
  unfold tailWord_3008435
  simp only [CollatzResearch.WordTrace]
  refine ⟨109726638855961269637418759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73151092570640846424945839 109726638855961269637418759)
  ·
    refine ⟨164589958283941904456128139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109726638855961269637418759 164589958283941904456128139)
    ·
      refine ⟨246884937425912856684192209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164589958283941904456128139 246884937425912856684192209)
      ·
        refine ⟨185163703069434642513144157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246884937425912856684192209 185163703069434642513144157)
        ·
          refine ⟨69436388651037990942429059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185163703069434642513144157 69436388651037990942429059)
          ·
            refine ⟨104154582976556986413643589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69436388651037990942429059 104154582976556986413643589)
            ·
              refine ⟨19528984308104434952558173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104154582976556986413643589 19528984308104434952558173)
              ·
                refine ⟨7323369115539163107209315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19528984308104434952558173 7323369115539163107209315)
                ·
                  refine ⟨10985053673308744660813973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7323369115539163107209315 10985053673308744660813973)
                  ·
                    refine ⟨514924390936347405975655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10985053673308744660813973 514924390936347405975655)
                    ·
                      rfl

theorem cell23_3008435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 6].length) (baseStart_3008435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008435 prefixEnd_3008435 := by exact prefixLift 3008435
  have htrace : WordTrace (prefixWord ++ tailWord_3008435) baseStart_3008435 baseEnd_3008435 := by
    simpa [prefixWord, tailWord_3008435, baseEnd_3008435] using wordTrace_append hprefix tailTrace_3008435
  have hstable : (prefixWord ++ tailWord_3008435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008435).length < 2 ^ (prefixWord ++ tailWord_3008435).sum := by decide
  have hdescent : baseEnd_3008435 < baseStart_3008435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008442 : List Nat := [3, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4]
def baseStart_3008442 : Nat := 118140960795 + 3008442 * 2 ^ 59
def prefixEnd_3008442 : Nat := 4983230072969 + 3 ^ 40 * 3008442 * 2
def baseEnd_3008442 : Nat := 1544776767173623690539433

theorem tailTrace_3008442 : CollatzResearch.WordTrace tailWord_3008442 prefixEnd_3008442 1544776767173623690539433 := by
  unfold tailWord_3008442
  simp only [CollatzResearch.WordTrace]
  refine ⟨27431723541733977458230895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73151262777957273221949053 27431723541733977458230895)
  ·
    refine ⟨41147585312600966187346343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27431723541733977458230895 41147585312600966187346343)
    ·
      refine ⟨61721377968901449281019515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41147585312600966187346343 61721377968901449281019515)
      ·
        refine ⟨92582066953352173921529273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61721377968901449281019515 92582066953352173921529273)
        ·
          refine ⟨69436550215014130441146955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92582066953352173921529273 69436550215014130441146955)
          ·
            refine ⟨104154825322521195661720433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69436550215014130441146955 104154825322521195661720433)
            ·
              refine ⟨78116118991890896746290325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104154825322521195661720433 78116118991890896746290325)
              ·
                refine ⟨3661693077744885784982359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78116118991890896746290325 3661693077744885784982359)
                ·
                  refine ⟨5492539616617328677473539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3661693077744885784982359 5492539616617328677473539)
                  ·
                    refine ⟨8238809424925993016210309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5492539616617328677473539 8238809424925993016210309)
                    ·
                      refine ⟨1544776767173623690539433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8238809424925993016210309 1544776767173623690539433)
                      ·
                        rfl

theorem cell23_3008442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4].length) (baseStart_3008442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008442 prefixEnd_3008442 := by exact prefixLift 3008442
  have htrace : WordTrace (prefixWord ++ tailWord_3008442) baseStart_3008442 baseEnd_3008442 := by
    simpa [prefixWord, tailWord_3008442, baseEnd_3008442] using wordTrace_append hprefix tailTrace_3008442
  have hstable : (prefixWord ++ tailWord_3008442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008442).length < 2 ^ (prefixWord ++ tailWord_3008442).sum := by decide
  have hdescent : baseEnd_3008442 < baseStart_3008442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008446 : List Nat := [4, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2]
def baseStart_3008446 : Nat := 118140960795 + 3008446 * 2 ^ 59
def prefixEnd_3008446 : Nat := 4983230072969 + 3 ^ 40 * 3008446 * 2
def baseEnd_3008446 : Nat := 1544778821096241674889415

theorem tailTrace_3008446 : CollatzResearch.WordTrace tailWord_3008446 prefixEnd_3008446 1544778821096241674889415 := by
  unfold tailWord_3008446
  simp only [CollatzResearch.WordTrace]
  refine ⟨13715880007365177314508649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73151360039280945677379461 13715880007365177314508649)
  ·
    refine ⟨10286910005523882985881487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13715880007365177314508649 10286910005523882985881487)
    ·
      refine ⟨15430365008285824478822231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10286910005523882985881487 15430365008285824478822231)
      ·
        refine ⟨23145547512428736718233347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15430365008285824478822231 23145547512428736718233347)
        ·
          refine ⟨34718321268643105077350021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23145547512428736718233347 34718321268643105077350021)
          ·
            refine ⟨6509685237870582202003129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34718321268643105077350021 6509685237870582202003129)
            ·
              refine ⟨4882263928402936651502347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6509685237870582202003129 4882263928402936651502347)
              ·
                refine ⟨7323395892604404977253521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4882263928402936651502347 7323395892604404977253521)
                ·
                  refine ⟨5492546919453303732940141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7323395892604404977253521 5492546919453303732940141)
                  ·
                    refine ⟨2059705094794988899852553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5492546919453303732940141 2059705094794988899852553)
                    ·
                      refine ⟨1544778821096241674889415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2059705094794988899852553 1544778821096241674889415)
                      ·
                        rfl

theorem cell23_3008446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_3008446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008446 prefixEnd_3008446 := by exact prefixLift 3008446
  have htrace : WordTrace (prefixWord ++ tailWord_3008446) baseStart_3008446 baseEnd_3008446 := by
    simpa [prefixWord, tailWord_3008446, baseEnd_3008446] using wordTrace_append hprefix tailTrace_3008446
  have hstable : (prefixWord ++ tailWord_3008446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008446).length < 2 ^ (prefixWord ++ tailWord_3008446).sum := by decide
  have hdescent : baseEnd_3008446 < baseStart_3008446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008459 : List Nat := [1, 1, 1, 1, 3, 4, 5, 1, 1, 1, 4]
def baseStart_3008459 : Nat := 118140960795 + 3008459 * 2 ^ 59
def prefixEnd_3008459 : Nat := 4983230072969 + 3 ^ 40 * 3008459 * 2
def baseEnd_3008459 : Nat := 1544785496344750124026855

theorem tailTrace_3008459 : CollatzResearch.WordTrace tailWord_3008459 prefixEnd_3008459 1544785496344750124026855 := by
  unfold tailWord_3008459
  simp only [CollatzResearch.WordTrace]
  refine ⟨109727514207874321736292431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73151676138582881157528287 109727514207874321736292431)
  ·
    refine ⟨164591271311811482604438647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109727514207874321736292431 164591271311811482604438647)
    ·
      refine ⟨246886906967717223906657971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164591271311811482604438647 246886906967717223906657971)
      ·
        refine ⟨370330360451575835859986957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246886906967717223906657971 370330360451575835859986957)
        ·
          refine ⟨138873885169340938447495109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 370330360451575835859986957 138873885169340938447495109)
          ·
            refine ⟨26038853469251425958905333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138873885169340938447495109 26038853469251425958905333)
            ·
              refine ⟨2441142512742321183647375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26038853469251425958905333 2441142512742321183647375)
              ·
                refine ⟨3661713769113481775471063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2441142512742321183647375 3661713769113481775471063)
                ·
                  refine ⟨5492570653670222663206595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3661713769113481775471063 5492570653670222663206595)
                  ·
                    refine ⟨8238855980505333994809893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5492570653670222663206595 8238855980505333994809893)
                    ·
                      refine ⟨1544785496344750124026855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8238855980505333994809893 1544785496344750124026855)
                      ·
                        rfl

theorem cell23_3008459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 1, 1, 4].length) (baseStart_3008459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008459 prefixEnd_3008459 := by exact prefixLift 3008459
  have htrace : WordTrace (prefixWord ++ tailWord_3008459) baseStart_3008459 baseEnd_3008459 := by
    simpa [prefixWord, tailWord_3008459, baseEnd_3008459] using wordTrace_append hprefix tailTrace_3008459
  have hstable : (prefixWord ++ tailWord_3008459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008459).length < 2 ^ (prefixWord ++ tailWord_3008459).sum := by decide
  have hdescent : baseEnd_3008459 < baseStart_3008459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008469 : List Nat := [1, 3, 2, 3, 2, 1, 1, 4, 2, 4]
def baseStart_3008469 : Nat := 118140960795 + 3008469 * 2 ^ 59
def prefixEnd_3008469 : Nat := 4983230072969 + 3 ^ 40 * 3008469 * 2
def baseEnd_3008469 : Nat := 514930210383765028300603

theorem tailTrace_3008469 : CollatzResearch.WordTrace tailWord_3008469 prefixEnd_3008469 514930210383765028300603 := by
  unfold tailWord_3008469
  simp only [CollatzResearch.WordTrace]
  refine ⟨109727878937838093444156461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73151919291892062296104307 109727878937838093444156461)
  ·
    refine ⟨41147954601689285041558673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109727878937838093444156461 41147954601689285041558673)
    ·
      refine ⟨30860965951266963781169005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41147954601689285041558673 30860965951266963781169005)
      ·
        refine ⟨11572862231725111417938377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30860965951266963781169005 11572862231725111417938377)
        ·
          refine ⟨8679646673793833563453783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11572862231725111417938377 8679646673793833563453783)
          ·
            refine ⟨13019470010690750345180675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8679646673793833563453783 13019470010690750345180675)
            ·
              refine ⟨19529205016036125517771013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13019470010690750345180675 19529205016036125517771013)
              ·
                refine ⟨3661725940506773534582065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19529205016036125517771013 3661725940506773534582065)
                ·
                  refine ⟨2746294455380080150936549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3661725940506773534582065 2746294455380080150936549)
                  ·
                    refine ⟨514930210383765028300603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2746294455380080150936549 514930210383765028300603)
                    ·
                      rfl

theorem cell23_3008469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_3008469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008469 prefixEnd_3008469 := by exact prefixLift 3008469
  have htrace : WordTrace (prefixWord ++ tailWord_3008469) baseStart_3008469 baseEnd_3008469 := by
    simpa [prefixWord, tailWord_3008469, baseEnd_3008469] using wordTrace_append hprefix tailTrace_3008469
  have hstable : (prefixWord ++ tailWord_3008469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008469).length < 2 ^ (prefixWord ++ tailWord_3008469).sum := by decide
  have hdescent : baseEnd_3008469 < baseStart_3008469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008470 : List Nat := [5, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3]
def baseStart_3008470 : Nat := 118140960795 + 3008470 * 2 ^ 59
def prefixEnd_3008470 : Nat := 4983230072969 + 3 ^ 40 * 3008470 * 2
def baseEnd_3008470 : Nat := 1544791144631949580989305

theorem tailTrace_3008470 : CollatzResearch.WordTrace tailWord_3008470 prefixEnd_3008470 1544791144631949580989305 := by
  unfold tailWord_3008470
  simp only [CollatzResearch.WordTrace]
  refine ⟨6857994713177154413433929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73151943607222980409961909 6857994713177154413433929)
  ·
    refine ⟨5143496034882865810075447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6857994713177154413433929 5143496034882865810075447)
    ·
      refine ⟨7715244052324298715113171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5143496034882865810075447 7715244052324298715113171)
      ·
        refine ⟨11572866078486448072669757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7715244052324298715113171 11572866078486448072669757)
        ·
          refine ⟨4339824779432418027251159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11572866078486448072669757 4339824779432418027251159)
          ·
            refine ⟨6509737169148627040876739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4339824779432418027251159 6509737169148627040876739)
            ·
              refine ⟨9764605753722940561315109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6509737169148627040876739 9764605753722940561315109)
              ·
                refine ⟨1830863578823051355246583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9764605753722940561315109 1830863578823051355246583)
                ·
                  refine ⟨2746295368234577032869875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1830863578823051355246583 2746295368234577032869875)
                  ·
                    refine ⟨4119443052351865549304813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2746295368234577032869875 4119443052351865549304813)
                    ·
                      refine ⟨1544791144631949580989305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4119443052351865549304813 1544791144631949580989305)
                      ·
                        rfl

theorem cell23_3008470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_3008470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008470 prefixEnd_3008470 := by exact prefixLift 3008470
  have htrace : WordTrace (prefixWord ++ tailWord_3008470) baseStart_3008470 baseEnd_3008470 := by
    simpa [prefixWord, tailWord_3008470, baseEnd_3008470] using wordTrace_append hprefix tailTrace_3008470
  have hstable : (prefixWord ++ tailWord_3008470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008470).length < 2 ^ (prefixWord ++ tailWord_3008470).sum := by decide
  have hdescent : baseEnd_3008470 < baseStart_3008470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008495 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 2, 7]
def baseStart_3008495 : Nat := 118140960795 + 3008495 * 2 ^ 59
def prefixEnd_3008495 : Nat := 4983230072969 + 3 ^ 40 * 3008495 * 2
def baseEnd_3008495 : Nat := 514934660549437327725563

theorem tailTrace_3008495 : CollatzResearch.WordTrace tailWord_3008495 prefixEnd_3008495 514934660549437327725563 := by
  unfold tailWord_3008495
  simp only [CollatzResearch.WordTrace]
  refine ⟨109728827235743899884602939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73152551490495933256401959 109728827235743899884602939)
  ·
    refine ⟨164593240853615849826904409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109728827235743899884602939 164593240853615849826904409)
    ·
      refine ⟨123444930640211887370178307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164593240853615849826904409 123444930640211887370178307)
      ·
        refine ⟨185167395960317831055267461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123444930640211887370178307 185167395960317831055267461)
        ·
          refine ⟨34718886742559593322862649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185167395960317831055267461 34718886742559593322862649)
          ·
            refine ⟨26039165056919694992146987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34718886742559593322862649 26039165056919694992146987)
            ·
              refine ⟨39058747585379542488220481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26039165056919694992146987 39058747585379542488220481)
              ·
                refine ⟨29294060689034656866165361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39058747585379542488220481 29294060689034656866165361)
                ·
                  refine ⟨21970545516775992649624021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29294060689034656866165361 21970545516775992649624021)
                  ·
                    refine ⟨514934660549437327725563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21970545516775992649624021 514934660549437327725563)
                    ·
                      rfl

theorem cell23_3008495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 7].length) (baseStart_3008495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008495 prefixEnd_3008495 := by exact prefixLift 3008495
  have htrace : WordTrace (prefixWord ++ tailWord_3008495) baseStart_3008495 baseEnd_3008495 := by
    simpa [prefixWord, tailWord_3008495, baseEnd_3008495] using wordTrace_append hprefix tailTrace_3008495
  have hstable : (prefixWord ++ tailWord_3008495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008495).length < 2 ^ (prefixWord ++ tailWord_3008495).sum := by decide
  have hdescent : baseEnd_3008495 < baseStart_3008495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008510 : List Nat := [4, 2, 2, 2, 1, 1, 1, 5, 1, 2, 2]
def baseStart_3008510 : Nat := 118140960795 + 3008510 * 2 ^ 59
def prefixEnd_3008510 : Nat := 4983230072969 + 3 ^ 40 * 3008510 * 2
def baseEnd_3008510 : Nat := 1544811683858129424489121

theorem tailTrace_3008510 : CollatzResearch.WordTrace tailWord_3008510 prefixEnd_3008510 1544811683858129424489121 := by
  unfold tailWord_3008510
  simp only [CollatzResearch.WordTrace]
  refine ⟨13716171791336194680799873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73152916220459704964265989 13716171791336194680799873)
  ·
    refine ⟨10287128843502146010599905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13716171791336194680799873 10287128843502146010599905)
    ·
      refine ⟨7715346632626609507949929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10287128843502146010599905 7715346632626609507949929)
      ·
        refine ⟨5786509974469957130962447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7715346632626609507949929 5786509974469957130962447)
        ·
          refine ⟨8679764961704935696443671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5786509974469957130962447 8679764961704935696443671)
          ·
            refine ⟨13019647442557403544665507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8679764961704935696443671 13019647442557403544665507)
            ·
              refine ⟨19529471163836105316998261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13019647442557403544665507 19529471163836105316998261)
              ·
                refine ⟨1830887921609634873468587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19529471163836105316998261 1830887921609634873468587)
                ·
                  refine ⟨2746331882414452310202881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1830887921609634873468587 2746331882414452310202881)
                  ·
                    refine ⟨2059748911810839232652161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2746331882414452310202881 2059748911810839232652161)
                    ·
                      refine ⟨1544811683858129424489121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2059748911810839232652161 1544811683858129424489121)
                      ·
                        rfl

theorem cell23_3008510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_3008510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008510 prefixEnd_3008510 := by exact prefixLift 3008510
  have htrace : WordTrace (prefixWord ++ tailWord_3008510) baseStart_3008510 baseEnd_3008510 := by
    simpa [prefixWord, tailWord_3008510, baseEnd_3008510] using wordTrace_append hprefix tailTrace_3008510
  have hstable : (prefixWord ++ tailWord_3008510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008510).length < 2 ^ (prefixWord ++ tailWord_3008510).sum := by decide
  have hdescent : baseEnd_3008510 < baseStart_3008510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008555 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 9]
def baseStart_3008555 : Nat := 118140960795 + 3008555 * 2 ^ 59
def prefixEnd_3008555 : Nat := 4983230072969 + 3 ^ 40 * 3008555 * 2
def baseEnd_3008555 : Nat := 171648310054175749825157

theorem tailTrace_3008555 : CollatzResearch.WordTrace tailWord_3008555 prefixEnd_3008555 171648310054175749825157 := by
  unfold tailWord_3008555
  simp only [CollatzResearch.WordTrace]
  refine ⟨109731015615526530131787119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73154010410351020087858079 109731015615526530131787119)
  ·
    refine ⟨164596523423289795197680679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109731015615526530131787119 164596523423289795197680679)
    ·
      refine ⟨246894785134934692796521019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164596523423289795197680679 246894785134934692796521019)
      ·
        refine ⟨370342177702402039194781529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246894785134934692796521019 370342177702402039194781529)
        ·
          refine ⟨277756633276801529396086147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370342177702402039194781529 277756633276801529396086147)
          ·
            refine ⟨416634949915202294094129221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277756633276801529396086147 416634949915202294094129221)
            ·
              refine ⟨78119053109100430142649229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 416634949915202294094129221 78119053109100430142649229)
              ·
                refine ⟨29294644915912661303493461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78119053109100430142649229 29294644915912661303493461)
                ·
                  refine ⟨171648310054175749825157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29294644915912661303493461 171648310054175749825157)
                  ·
                    rfl

theorem cell23_3008555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 9].length) (baseStart_3008555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008555 prefixEnd_3008555 := by exact prefixLift 3008555
  have htrace : WordTrace (prefixWord ++ tailWord_3008555) baseStart_3008555 baseEnd_3008555 := by
    simpa [prefixWord, tailWord_3008555, baseEnd_3008555] using wordTrace_append hprefix tailTrace_3008555
  have hstable : (prefixWord ++ tailWord_3008555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008555).length < 2 ^ (prefixWord ++ tailWord_3008555).sum := by decide
  have hdescent : baseEnd_3008555 < baseStart_3008555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008566 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 3, 4, 2]
def baseStart_3008566 : Nat := 118140960795 + 3008566 * 2 ^ 59
def prefixEnd_3008566 : Nat := 4983230072969 + 3 ^ 40 * 3008566 * 2
def baseEnd_3008566 : Nat := 1544840438774781205388863

theorem tailTrace_3008566 : CollatzResearch.WordTrace tailWord_3008566 prefixEnd_3008566 1544840438774781205388863 := by
  unfold tailWord_3008566
  simp only [CollatzResearch.WordTrace]
  refine ⟨6858213551155417438152347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73154277878991119340291701 6858213551155417438152347)
  ·
    refine ⟨10287320326733126157228521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6858213551155417438152347 10287320326733126157228521)
    ·
      refine ⟨7715490245049844617921391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10287320326733126157228521 7715490245049844617921391)
      ·
        refine ⟨11573235367574766926882087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7715490245049844617921391 11573235367574766926882087)
        ·
          refine ⟨17359853051362150390323131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11573235367574766926882087 17359853051362150390323131)
          ·
            refine ⟨26039779577043225585484697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17359853051362150390323131 26039779577043225585484697)
            ·
              refine ⟨19529834682782419189113523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26039779577043225585484697 19529834682782419189113523)
              ·
                refine ⟨29294752024173628783670285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19529834682782419189113523 29294752024173628783670285)
                ·
                  refine ⟨10985532009065110793876357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29294752024173628783670285 10985532009065110793876357)
                  ·
                    refine ⟨2059787251699708273851817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10985532009065110793876357 2059787251699708273851817)
                    ·
                      refine ⟨1544840438774781205388863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2059787251699708273851817 1544840438774781205388863)
                      ·
                        rfl

theorem cell23_3008566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_3008566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008566 prefixEnd_3008566 := by exact prefixLift 3008566
  have htrace : WordTrace (prefixWord ++ tailWord_3008566) baseStart_3008566 baseEnd_3008566 := by
    simpa [prefixWord, tailWord_3008566, baseEnd_3008566] using wordTrace_append hprefix tailTrace_3008566
  have hstable : (prefixWord ++ tailWord_3008566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008566).length < 2 ^ (prefixWord ++ tailWord_3008566).sum := by decide
  have hdescent : baseEnd_3008566 < baseStart_3008566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008569 : List Nat := [1, 2, 1, 5, 3, 1, 1, 1, 2, 1, 5]
def baseStart_3008569 : Nat := 118140960795 + 3008569 * 2 ^ 59
def prefixEnd_3008569 : Nat := 4983230072969 + 3 ^ 40 * 3008569 * 2
def baseEnd_3008569 : Nat := 1544841979216744693651349

theorem tailTrace_3008569 : CollatzResearch.WordTrace tailWord_3008569 prefixEnd_3008569 1544841979216744693651349 := by
  unfold tailWord_3008569
  simp only [CollatzResearch.WordTrace]
  refine ⟨109731526237475810522796761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73154350824983873681864507 109731526237475810522796761)
  ·
    refine ⟨82298644678106857892097571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109731526237475810522796761 82298644678106857892097571)
    ·
      refine ⟨123447967017160286838146357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82298644678106857892097571 123447967017160286838146357)
      ·
        refine ⟨11573246907858776891076221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123447967017160286838146357 11573246907858776891076221)
        ·
          refine ⟨4339967590447041334153583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11573246907858776891076221 4339967590447041334153583)
          ·
            refine ⟨6509951385670562001230375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4339967590447041334153583 6509951385670562001230375)
            ·
              refine ⟨9764927078505843001845563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6509951385670562001230375 9764927078505843001845563)
              ·
                refine ⟨14647390617758764502768345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9764927078505843001845563 14647390617758764502768345)
                ·
                  refine ⟨10985542963319073377076259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14647390617758764502768345 10985542963319073377076259)
                  ·
                    refine ⟨16478314444978610065614389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10985542963319073377076259 16478314444978610065614389)
                    ·
                      refine ⟨1544841979216744693651349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16478314444978610065614389 1544841979216744693651349)
                      ·
                        rfl

theorem cell23_3008569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_3008569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008569 prefixEnd_3008569 := by exact prefixLift 3008569
  have htrace : WordTrace (prefixWord ++ tailWord_3008569) baseStart_3008569 baseEnd_3008569 := by
    simpa [prefixWord, tailWord_3008569, baseEnd_3008569] using wordTrace_append hprefix tailTrace_3008569
  have hstable : (prefixWord ++ tailWord_3008569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008569).length < 2 ^ (prefixWord ++ tailWord_3008569).sum := by decide
  have hdescent : baseEnd_3008569 < baseStart_3008569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008600 : List Nat := [2, 1, 2, 2, 1, 6, 2, 1, 2, 2, 2]
def baseStart_3008600 : Nat := 118140960795 + 3008600 * 2 ^ 59
def prefixEnd_3008600 : Nat := 4983230072969 + 3 ^ 40 * 3008600 * 2
def baseEnd_3008600 : Nat := 1544857897117034072363707

theorem tailTrace_3008600 : CollatzResearch.WordTrace tailWord_3008600 prefixEnd_3008600 1544857897117034072363707 := by
  unfold tailWord_3008600
  simp only [CollatzResearch.WordTrace]
  refine ⟨54866328450181751408587627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73155104600242335211450169 54866328450181751408587627)
  ·
    refine ⟨82299492675272627112881441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54866328450181751408587627 82299492675272627112881441)
    ·
      refine ⟨61724619506454470334661081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82299492675272627112881441 61724619506454470334661081)
      ·
        refine ⟨46293464629840852750995811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61724619506454470334661081 46293464629840852750995811)
        ·
          refine ⟨69440196944761279126493717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46293464629840852750995811 69440196944761279126493717)
          ·
            refine ⟨3255009231785684959054393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 69440196944761279126493717 3255009231785684959054393)
            ·
              refine ⟨2441256923839263719290795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3255009231785684959054393 2441256923839263719290795)
              ·
                refine ⟨3661885385758895578936193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2441256923839263719290795 3661885385758895578936193)
                ·
                  refine ⟨2746414039319171684202145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3661885385758895578936193 2746414039319171684202145)
                  ·
                    refine ⟨2059810529489378763151609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2746414039319171684202145 2059810529489378763151609)
                    ·
                      refine ⟨1544857897117034072363707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2059810529489378763151609 1544857897117034072363707)
                      ·
                        rfl

theorem cell23_3008600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 2, 2, 2].length) (baseStart_3008600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008600 prefixEnd_3008600 := by exact prefixLift 3008600
  have htrace : WordTrace (prefixWord ++ tailWord_3008600) baseStart_3008600 baseEnd_3008600 := by
    simpa [prefixWord, tailWord_3008600, baseEnd_3008600] using wordTrace_append hprefix tailTrace_3008600
  have hstable : (prefixWord ++ tailWord_3008600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008600).length < 2 ^ (prefixWord ++ tailWord_3008600).sum := by decide
  have hdescent : baseEnd_3008600 < baseStart_3008600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008602 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 4, 5]
def baseStart_3008602 : Nat := 118140960795 + 3008602 * 2 ^ 59
def prefixEnd_3008602 : Nat := 4983230072969 + 3 ^ 40 * 3008602 * 2
def baseEnd_3008602 : Nat := 514952974692781021512899

theorem tailTrace_3008602 : CollatzResearch.WordTrace tailWord_3008602 prefixEnd_3008602 514952974692781021512899 := by
  unfold tailWord_3008602
  simp only [CollatzResearch.WordTrace]
  refine ⟨27433182461589064289687015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73155153230904171439165373 27433182461589064289687015)
  ·
    refine ⟨41149773692383596434530523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27433182461589064289687015 41149773692383596434530523)
    ·
      refine ⟨61724660538575394651795785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41149773692383596434530523 61724660538575394651795785)
      ·
        refine ⟨46293495403931545988846839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61724660538575394651795785 46293495403931545988846839)
        ·
          refine ⟨69440243105897318983270259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46293495403931545988846839 69440243105897318983270259)
          ·
            refine ⟨104160364658845978474905389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69440243105897318983270259 104160364658845978474905389)
            ·
              refine ⟨39060136747067241928089521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104160364658845978474905389 39060136747067241928089521)
              ·
                refine ⟨29295102560300431446067141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39060136747067241928089521 29295102560300431446067141)
                ·
                  refine ⟨5492831730056330896137589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29295102560300431446067141 5492831730056330896137589)
                  ·
                    refine ⟨514952974692781021512899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5492831730056330896137589 514952974692781021512899)
                    ·
                      rfl

theorem cell23_3008602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 4, 5].length) (baseStart_3008602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008602 prefixEnd_3008602 := by exact prefixLift 3008602
  have htrace : WordTrace (prefixWord ++ tailWord_3008602) baseStart_3008602 baseEnd_3008602 := by
    simpa [prefixWord, tailWord_3008602, baseEnd_3008602] using wordTrace_append hprefix tailTrace_3008602
  have hstable : (prefixWord ++ tailWord_3008602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008602).length < 2 ^ (prefixWord ++ tailWord_3008602).sum := by decide
  have hdescent : baseEnd_3008602 < baseStart_3008602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008649 : List Nat := [1, 2, 1, 1, 4, 2, 2, 3, 3, 4]
def baseStart_3008649 : Nat := 118140960795 + 3008649 * 2 ^ 59
def prefixEnd_3008649 : Nat := 4983230072969 + 3 ^ 40 * 3008649 * 2
def baseEnd_3008649 : Nat := 514961019223034793550327

theorem tailTrace_3008649 : CollatzResearch.WordTrace tailWord_3008649 prefixEnd_3008649 514961019223034793550327 := by
  unfold tailWord_3008649
  simp only [CollatzResearch.WordTrace]
  refine ⟨109734444077185984185709001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73156296051457322790472667 109734444077185984185709001)
  ·
    refine ⟨82300833057889488139281751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109734444077185984185709001 82300833057889488139281751)
    ·
      refine ⟨123451249586834232208922627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82300833057889488139281751 123451249586834232208922627)
      ·
        refine ⟨185176874380251348313383941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123451249586834232208922627 185176874380251348313383941)
        ·
          refine ⟨34720663946297127808759489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185176874380251348313383941 34720663946297127808759489)
          ·
            refine ⟨26040497959722845856569617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34720663946297127808759489 26040497959722845856569617)
            ·
              refine ⟨19530373469792134392427213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26040497959722845856569617 19530373469792134392427213)
              ·
                refine ⟨7323890051172050397160205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19530373469792134392427213 7323890051172050397160205)
                ·
                  refine ⟨2746458769189518898935077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7323890051172050397160205 2746458769189518898935077)
                  ·
                    refine ⟨514961019223034793550327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2746458769189518898935077 514961019223034793550327)
                    ·
                      rfl

theorem cell23_3008649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3, 4].length) (baseStart_3008649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008649 prefixEnd_3008649 := by exact prefixLift 3008649
  have htrace : WordTrace (prefixWord ++ tailWord_3008649) baseStart_3008649 baseEnd_3008649 := by
    simpa [prefixWord, tailWord_3008649, baseEnd_3008649] using wordTrace_append hprefix tailTrace_3008649
  have hstable : (prefixWord ++ tailWord_3008649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008649).length < 2 ^ (prefixWord ++ tailWord_3008649).sum := by decide
  have hdescent : baseEnd_3008649 < baseStart_3008649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008652 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 4, 4, 4]
def baseStart_3008652 : Nat := 118140960795 + 3008652 * 2 ^ 59
def prefixEnd_3008652 : Nat := 4983230072969 + 3 ^ 40 * 3008652 * 2
def baseEnd_3008652 : Nat := 1544884598111067868913467

theorem tailTrace_3008652 : CollatzResearch.WordTrace tailWord_3008652 prefixEnd_3008652 1544884598111067868913467 := by
  unfold tailWord_3008652
  simp only [CollatzResearch.WordTrace]
  refine ⟨54867276748087557849034105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73156368997450077132045473 54867276748087557849034105)
  ·
    refine ⟨41150457561065668386775579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54867276748087557849034105 41150457561065668386775579)
    ·
      refine ⟨61725686341598502580163369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41150457561065668386775579 61725686341598502580163369)
      ·
        refine ⟨46294264756198876935122527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61725686341598502580163369 46294264756198876935122527)
        ·
          refine ⟨69441397134298315402683791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46294264756198876935122527 69441397134298315402683791)
          ·
            refine ⟨104162095701447473104025687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69441397134298315402683791 104162095701447473104025687)
            ·
              refine ⟨156243143552171209656038531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104162095701447473104025687 156243143552171209656038531)
              ·
                refine ⟨234364715328256814484057797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156243143552171209656038531 234364715328256814484057797)
                ·
                  refine ⟨43943384124048152715760837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 234364715328256814484057797 43943384124048152715760837)
                  ·
                    refine ⟨8239384523259028634205157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43943384124048152715760837 8239384523259028634205157)
                    ·
                      refine ⟨1544884598111067868913467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8239384523259028634205157 1544884598111067868913467)
                      ·
                        rfl

theorem cell23_3008652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_3008652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008652 prefixEnd_3008652 := by exact prefixLift 3008652
  have htrace : WordTrace (prefixWord ++ tailWord_3008652) baseStart_3008652 baseEnd_3008652 := by
    simpa [prefixWord, tailWord_3008652, baseEnd_3008652] using wordTrace_append hprefix tailTrace_3008652
  have hstable : (prefixWord ++ tailWord_3008652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008652).length < 2 ^ (prefixWord ++ tailWord_3008652).sum := by decide
  have hdescent : baseEnd_3008652 < baseStart_3008652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008670 : List Nat := [4, 3, 1, 1, 4, 1, 1, 1, 2, 5]
def baseStart_3008670 : Nat := 118140960795 + 3008670 * 2 ^ 59
def prefixEnd_3008670 : Nat := 4983230072969 + 3 ^ 40 * 3008670 * 2
def baseEnd_3008670 : Nat := 514964613587616266162795

theorem tailTrace_3008670 : CollatzResearch.WordTrace tailWord_3008670 prefixEnd_3008670 514964613587616266162795 := by
  unfold tailWord_3008670
  simp only [CollatzResearch.WordTrace]
  refine ⟨13716901251263738096527933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73156806673406603181482309 13716901251263738096527933)
  ·
    refine ⟨5143837969223901786197975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13716901251263738096527933 5143837969223901786197975)
    ·
      refine ⟨7715756953835852679296963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5143837969223901786197975 7715756953835852679296963)
      ·
        refine ⟨11573635430753779018945445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7715756953835852679296963 11573635430753779018945445)
        ·
          refine ⟨2170056643266333566052271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11573635430753779018945445 2170056643266333566052271)
          ·
            refine ⟨3255084964899500349078407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2170056643266333566052271 3255084964899500349078407)
            ·
              refine ⟨4882627447349250523617611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3255084964899500349078407 4882627447349250523617611)
              ·
                refine ⟨7323941171023875785426417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4882627447349250523617611 7323941171023875785426417)
                ·
                  refine ⟨5492955878267906839069813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7323941171023875785426417 5492955878267906839069813)
                  ·
                    refine ⟨514964613587616266162795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5492955878267906839069813 514964613587616266162795)
                    ·
                      rfl

theorem cell23_3008670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_3008670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008670 prefixEnd_3008670 := by exact prefixLift 3008670
  have htrace : WordTrace (prefixWord ++ tailWord_3008670) baseStart_3008670 baseEnd_3008670 := by
    simpa [prefixWord, tailWord_3008670, baseEnd_3008670] using wordTrace_append hprefix tailTrace_3008670
  have hstable : (prefixWord ++ tailWord_3008670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008670).length < 2 ^ (prefixWord ++ tailWord_3008670).sum := by decide
  have hdescent : baseEnd_3008670 < baseStart_3008670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008676 : List Nat := [2, 3, 1, 2, 4, 1, 1, 1, 1, 4, 3]
def baseStart_3008676 : Nat := 118140960795 + 3008676 * 2 ^ 59
def prefixEnd_3008676 : Nat := 4983230072969 + 3 ^ 40 * 3008676 * 2
def baseEnd_3008676 : Nat := 1544896921646775775013357

theorem tailTrace_3008676 : CollatzResearch.WordTrace tailWord_3008676 prefixEnd_3008676 1544896921646775775013357 := by
  unfold tailWord_3008676
  simp only [CollatzResearch.WordTrace]
  refine ⟨54867714424044083898470941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73156952565392111864627921 54867714424044083898470941)
  ·
    refine ⟨20575392909016531461926603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54867714424044083898470941 20575392909016531461926603)
    ·
      refine ⟨30863089363524797192889905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20575392909016531461926603 30863089363524797192889905)
      ·
        refine ⟨23147317022643597894667429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30863089363524797192889905 23147317022643597894667429)
        ·
          refine ⟨4340121941745674605250143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23147317022643597894667429 4340121941745674605250143)
          ·
            refine ⟨6510182912618511907875215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4340121941745674605250143 6510182912618511907875215)
            ·
              refine ⟨9765274368927767861812823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6510182912618511907875215 9765274368927767861812823)
              ·
                refine ⟨14647911553391651792719235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9765274368927767861812823 14647911553391651792719235)
                ·
                  refine ⟨21971867330087477689078853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14647911553391651792719235 21971867330087477689078853)
                  ·
                    refine ⟨4119725124391402066702285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21971867330087477689078853 4119725124391402066702285)
                    ·
                      refine ⟨1544896921646775775013357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4119725124391402066702285 1544896921646775775013357)
                      ·
                        rfl

theorem cell23_3008676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_3008676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008676 prefixEnd_3008676 := by exact prefixLift 3008676
  have htrace : WordTrace (prefixWord ++ tailWord_3008676) baseStart_3008676 baseEnd_3008676 := by
    simpa [prefixWord, tailWord_3008676, baseEnd_3008676] using wordTrace_append hprefix tailTrace_3008676
  have hstable : (prefixWord ++ tailWord_3008676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008676).length < 2 ^ (prefixWord ++ tailWord_3008676).sum := by decide
  have hdescent : baseEnd_3008676 < baseStart_3008676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008729 : List Nat := [1, 2, 1, 2, 3, 1, 2, 3, 3, 1, 4]
def baseStart_3008729 : Nat := 118140960795 + 3008729 * 2 ^ 59
def prefixEnd_3008729 : Nat := 4983230072969 + 3 ^ 40 * 3008729 * 2
def baseEnd_3008729 : Nat := 1544924136121464067650613

theorem tailTrace_3008729 : CollatzResearch.WordTrace tailWord_3008729 prefixEnd_3008729 1544924136121464067650613 := by
  unfold tailWord_3008729
  simp only [CollatzResearch.WordTrace]
  refine ⟨109737361916896157848621241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73158241277930771899080827 109737361916896157848621241)
  ·
    refine ⟨82303021437672118386465931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109737361916896157848621241 82303021437672118386465931)
    ·
      refine ⟨123454532156508177579698897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82303021437672118386465931 123454532156508177579698897)
      ·
        refine ⟨92590899117381133184774173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123454532156508177579698897 92590899117381133184774173)
        ·
          refine ⟨34721587169017924944290315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92590899117381133184774173 34721587169017924944290315)
          ·
            refine ⟨52082380753526887416435473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34721587169017924944290315 52082380753526887416435473)
            ·
              refine ⟨39061785565145165562326605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52082380753526887416435473 39061785565145165562326605)
              ·
                refine ⟨14648169586929437085872477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39061785565145165562326605 14648169586929437085872477)
                ·
                  refine ⟨5493063595098538907202179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14648169586929437085872477 5493063595098538907202179)
                  ·
                    refine ⟨8239595392647808360803269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5493063595098538907202179 8239595392647808360803269)
                    ·
                      refine ⟨1544924136121464067650613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8239595392647808360803269 1544924136121464067650613)
                      ·
                        rfl

theorem cell23_3008729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_3008729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008729 prefixEnd_3008729 := by exact prefixLift 3008729
  have htrace : WordTrace (prefixWord ++ tailWord_3008729) baseStart_3008729 baseEnd_3008729 := by
    simpa [prefixWord, tailWord_3008729, baseEnd_3008729] using wordTrace_append hprefix tailTrace_3008729
  have hstable : (prefixWord ++ tailWord_3008729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008729).length < 2 ^ (prefixWord ++ tailWord_3008729).sum := by decide
  have hdescent : baseEnd_3008729 < baseStart_3008729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008733 : List Nat := [1, 4, 3, 2, 1, 1, 2, 1, 1, 5, 2]
def baseStart_3008733 : Nat := 118140960795 + 3008733 * 2 ^ 59
def prefixEnd_3008733 : Nat := 4983230072969 + 3 ^ 40 * 3008733 * 2
def baseEnd_3008733 : Nat := 1544926190044082052000595

theorem tailTrace_3008733 : CollatzResearch.WordTrace tailWord_3008733 prefixEnd_3008733 1544926190044082052000595 := by
  unfold tailWord_3008733
  simp only [CollatzResearch.WordTrace]
  refine ⟨109737507808881666531766853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73158338539254444354511235 109737507808881666531766853)
  ·
    refine ⟨20575782714165312474706285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109737507808881666531766853 20575782714165312474706285)
    ·
      refine ⟨7715918517811992178014857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20575782714165312474706285 7715918517811992178014857)
      ·
        refine ⟨5786938888358994133511143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7715918517811992178014857 5786938888358994133511143)
        ·
          refine ⟨8680408332538491200266715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5786938888358994133511143 8680408332538491200266715)
          ·
            refine ⟨13020612498807736800400073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8680408332538491200266715 13020612498807736800400073)
            ·
              refine ⟨9765459374105802600300055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13020612498807736800400073 9765459374105802600300055)
              ·
                refine ⟨14648189061158703900450083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9765459374105802600300055 14648189061158703900450083)
                ·
                  refine ⟨21972283591738055850675125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14648189061158703900450083 21972283591738055850675125)
                  ·
                    refine ⟨2059901586725442736000793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21972283591738055850675125 2059901586725442736000793)
                    ·
                      refine ⟨1544926190044082052000595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2059901586725442736000793 1544926190044082052000595)
                      ·
                        rfl

theorem cell23_3008733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_3008733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008733 prefixEnd_3008733 := by exact prefixLift 3008733
  have htrace : WordTrace (prefixWord ++ tailWord_3008733) baseStart_3008733 baseEnd_3008733 := by
    simpa [prefixWord, tailWord_3008733, baseEnd_3008733] using wordTrace_append hprefix tailTrace_3008733
  have hstable : (prefixWord ++ tailWord_3008733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008733).length < 2 ^ (prefixWord ++ tailWord_3008733).sum := by decide
  have hdescent : baseEnd_3008733 < baseStart_3008733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008746 : List Nat := [3, 1, 3, 1, 1, 2, 1, 5, 1, 1, 4]
def baseStart_3008746 : Nat := 118140960795 + 3008746 * 2 ^ 59
def prefixEnd_3008746 : Nat := 4983230072969 + 3 ^ 40 * 3008746 * 2
def baseEnd_3008746 : Nat := 1544932865292590501138035

theorem tailTrace_3008746 : CollatzResearch.WordTrace tailWord_3008746 prefixEnd_3008746 1544932865292590501138035 := by
  unfold tailWord_3008746
  simp only [CollatzResearch.WordTrace]
  refine ⟨27434495489458642437997523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73158654638556379834660061 27434495489458642437997523)
  ·
    refine ⟨41151743234187963656996285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27434495489458642437997523 41151743234187963656996285)
    ·
      refine ⟨15431903712820486371373607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41151743234187963656996285 15431903712820486371373607)
      ·
        refine ⟨23147855569230729557060411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15431903712820486371373607 23147855569230729557060411)
        ·
          refine ⟨34721783353846094335590617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23147855569230729557060411 34721783353846094335590617)
          ·
            refine ⟨26041337515384570751692963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34721783353846094335590617 26041337515384570751692963)
            ·
              refine ⟨39062006273076856127539445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26041337515384570751692963 39062006273076856127539445)
              ·
                refine ⟨3662063088100955261956823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39062006273076856127539445 3662063088100955261956823)
                ·
                  refine ⟨5493094632151432892935235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3662063088100955261956823 5493094632151432892935235)
                  ·
                    refine ⟨8239641948227149339402853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5493094632151432892935235 8239641948227149339402853)
                    ·
                      refine ⟨1544932865292590501138035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8239641948227149339402853 1544932865292590501138035)
                      ·
                        rfl

theorem cell23_3008746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_3008746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008746 prefixEnd_3008746 := by exact prefixLift 3008746
  have htrace : WordTrace (prefixWord ++ tailWord_3008746) baseStart_3008746 baseEnd_3008746 := by
    simpa [prefixWord, tailWord_3008746, baseEnd_3008746] using wordTrace_append hprefix tailTrace_3008746
  have hstable : (prefixWord ++ tailWord_3008746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008746).length < 2 ^ (prefixWord ++ tailWord_3008746).sum := by decide
  have hdescent : baseEnd_3008746 < baseStart_3008746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008766 : List Nat := [4, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_3008766 : Nat := 118140960795 + 3008766 * 2 ^ 59
def prefixEnd_3008766 : Nat := 4983230072969 + 3 ^ 40 * 3008766 * 2
def baseEnd_3008766 : Nat := 1544943134905680422887943

theorem tailTrace_3008766 : CollatzResearch.WordTrace tailWord_3008766 prefixEnd_3008766 1544943134905680422887943 := by
  unfold tailWord_3008766
  simp only [CollatzResearch.WordTrace]
  refine ⟨13717338927220264145964769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73159140945174742111812101 13717338927220264145964769)
  ·
    refine ⟨10288004195415198109473577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13717338927220264145964769 10288004195415198109473577)
    ·
      refine ⟨7716003146561398582105183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10288004195415198109473577 7716003146561398582105183)
      ·
        refine ⟨11574004719842097873157775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7716003146561398582105183 11574004719842097873157775)
        ·
          refine ⟨17361007079763146809736663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11574004719842097873157775 17361007079763146809736663)
          ·
            refine ⟨26041510619644720214604995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17361007079763146809736663 26041510619644720214604995)
            ·
              refine ⟨39062265929467080321907493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26041510619644720214604995 39062265929467080321907493)
              ·
                refine ⟨7324174861775077560357655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39062265929467080321907493 7324174861775077560357655)
                ·
                  refine ⟨10986262292662616340536483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7324174861775077560357655 10986262292662616340536483)
                  ·
                    refine ⟨16479393438993924510804725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10986262292662616340536483 16479393438993924510804725)
                    ·
                      refine ⟨1544943134905680422887943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16479393438993924510804725 1544943134905680422887943)
                      ·
                        rfl

theorem cell23_3008766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_3008766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008766 prefixEnd_3008766 := by exact prefixLift 3008766
  have htrace : WordTrace (prefixWord ++ tailWord_3008766) baseStart_3008766 baseEnd_3008766 := by
    simpa [prefixWord, tailWord_3008766, baseEnd_3008766] using wordTrace_append hprefix tailTrace_3008766
  have hstable : (prefixWord ++ tailWord_3008766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008766).length < 2 ^ (prefixWord ++ tailWord_3008766).sum := by decide
  have hdescent : baseEnd_3008766 < baseStart_3008766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008769 : List Nat := [1, 2, 4, 1, 1, 2, 4, 8]
def baseStart_3008769 : Nat := 118140960795 + 3008769 * 2 ^ 59
def prefixEnd_3008769 : Nat := 4983230072969 + 3 ^ 40 * 3008769 * 2
def baseEnd_3008769 : Nat := 57220173161023848561127

theorem tailTrace_3008769 : CollatzResearch.WordTrace tailWord_3008769 prefixEnd_3008769 57220173161023848561127 := by
  unfold tailWord_3008769
  simp only [CollatzResearch.WordTrace]
  refine ⟨109738820836751244680077361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73159213891167496453384907 109738820836751244680077361)
  ·
    refine ⟨82304115627563433510058021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109738820836751244680077361 82304115627563433510058021)
    ·
      refine ⟨15432021680168143783135879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82304115627563433510058021 15432021680168143783135879)
      ·
        refine ⟨23148032520252215674703819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15432021680168143783135879 23148032520252215674703819)
        ·
          refine ⟨34722048780378323512055729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23148032520252215674703819 34722048780378323512055729)
          ·
            refine ⟨26041536585283742634041797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34722048780378323512055729 26041536585283742634041797)
            ·
              refine ⟨4882788109740701743882837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26041536585283742634041797 4882788109740701743882837)
              ·
                refine ⟨57220173161023848561127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4882788109740701743882837 57220173161023848561127)
                ·
                  rfl

theorem cell23_3008769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 8].length) (baseStart_3008769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008769 prefixEnd_3008769 := by exact prefixLift 3008769
  have htrace : WordTrace (prefixWord ++ tailWord_3008769) baseStart_3008769 baseEnd_3008769 := by
    simpa [prefixWord, tailWord_3008769, baseEnd_3008769] using wordTrace_append hprefix tailTrace_3008769
  have hstable : (prefixWord ++ tailWord_3008769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008769).length < 2 ^ (prefixWord ++ tailWord_3008769).sum := by decide
  have hdescent : baseEnd_3008769 < baseStart_3008769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008800 : List Nat := [2, 1, 1, 5, 2, 2, 3, 1, 1, 2, 3]
def baseStart_3008800 : Nat := 118140960795 + 3008800 * 2 ^ 59
def prefixEnd_3008800 : Nat := 4983230072969 + 3 ^ 40 * 3008800 * 2
def baseEnd_3008800 : Nat := 1544960593247933289862787

theorem tailTrace_3008800 : CollatzResearch.WordTrace tailWord_3008800 prefixEnd_3008800 1544960593247933289862787 := by
  unfold tailWord_3008800
  simp only [CollatzResearch.WordTrace]
  refine ⟨54869975749819468487227927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73159967666425957982970569 54869975749819468487227927)
  ·
    refine ⟨82304963624729202730841891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54869975749819468487227927 82304963624729202730841891)
    ·
      refine ⟨123457445437093804096262837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82304963624729202730841891 123457445437093804096262837)
      ·
        refine ⟨11574135509727544134024641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123457445437093804096262837 11574135509727544134024641)
        ·
          refine ⟨8680601632295658100518481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11574135509727544134024641 8680601632295658100518481)
          ·
            refine ⟨6510451224221743575388861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8680601632295658100518481 6510451224221743575388861)
            ·
              refine ⟨2441419209083153840770823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6510451224221743575388861 2441419209083153840770823)
              ·
                refine ⟨3662128813624730761156235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2441419209083153840770823 3662128813624730761156235)
                ·
                  refine ⟨5493193220437096141734353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3662128813624730761156235 5493193220437096141734353)
                  ·
                    refine ⟨4119894915327822106300765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5493193220437096141734353 4119894915327822106300765)
                    ·
                      refine ⟨1544960593247933289862787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4119894915327822106300765 1544960593247933289862787)
                      ·
                        rfl

theorem cell23_3008800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_3008800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008800 prefixEnd_3008800 := by exact prefixLift 3008800
  have htrace : WordTrace (prefixWord ++ tailWord_3008800) baseStart_3008800 baseEnd_3008800 := by
    simpa [prefixWord, tailWord_3008800, baseEnd_3008800] using wordTrace_append hprefix tailTrace_3008800
  have hstable : (prefixWord ++ tailWord_3008800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008800).length < 2 ^ (prefixWord ++ tailWord_3008800).sum := by decide
  have hdescent : baseEnd_3008800 < baseStart_3008800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008819 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 4]
def baseStart_3008819 : Nat := 118140960795 + 3008819 * 2 ^ 59
def prefixEnd_3008819 : Nat := 4983230072969 + 3 ^ 40 * 3008819 * 2
def baseEnd_3008819 : Nat := 1544970349380368715525199

theorem tailTrace_3008819 : CollatzResearch.WordTrace tailWord_3008819 prefixEnd_3008819 1544970349380368715525199 := by
  unfold tailWord_3008819
  simp only [CollatzResearch.WordTrace]
  refine ⟨109740644486570103219397511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73160429657713402146265007 109740644486570103219397511)
  ·
    refine ⟨164610966729855154829096267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109740644486570103219397511 164610966729855154829096267)
    ·
      refine ⟨246916450094782732243644401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164610966729855154829096267 246916450094782732243644401)
      ·
        refine ⟨185187337571087049182733301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246916450094782732243644401 185187337571087049182733301)
        ·
          refine ⟨17361312897289410860881247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 185187337571087049182733301 17361312897289410860881247)
          ·
            refine ⟨26041969345934116291321871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17361312897289410860881247 26041969345934116291321871)
            ·
              refine ⟨39062954018901174436982807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26041969345934116291321871 39062954018901174436982807)
              ·
                refine ⟨58594431028351761655474211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39062954018901174436982807 58594431028351761655474211)
                ·
                  refine ⟨87891646542527642483211317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58594431028351761655474211 87891646542527642483211317)
                  ·
                    refine ⟨8239841863361966482801061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87891646542527642483211317 8239841863361966482801061)
                    ·
                      refine ⟨1544970349380368715525199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8239841863361966482801061 1544970349380368715525199)
                      ·
                        rfl

theorem cell23_3008819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 4].length) (baseStart_3008819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008819 prefixEnd_3008819 := by exact prefixLift 3008819
  have htrace : WordTrace (prefixWord ++ tailWord_3008819) baseStart_3008819 baseEnd_3008819 := by
    simpa [prefixWord, tailWord_3008819, baseEnd_3008819] using wordTrace_append hprefix tailTrace_3008819
  have hstable : (prefixWord ++ tailWord_3008819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008819).length < 2 ^ (prefixWord ++ tailWord_3008819).sum := by decide
  have hdescent : baseEnd_3008819 < baseStart_3008819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008830 : List Nat := [4, 2, 1, 2, 1, 2, 2, 3, 2, 1, 3]
def baseStart_3008830 : Nat := 118140960795 + 3008830 * 2 ^ 59
def prefixEnd_3008830 : Nat := 4983230072969 + 3 ^ 40 * 3008830 * 2
def baseEnd_3008830 : Nat := 1544975997667568172487649

theorem tailTrace_3008830 : CollatzResearch.WordTrace tailWord_3008830 prefixEnd_3008830 1544975997667568172487649 := by
  unfold tailWord_3008830
  simp only [CollatzResearch.WordTrace]
  refine ⟨13717630711191281512255993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73160697126353501398698629 13717630711191281512255993)
  ·
    refine ⟨10288223033393461134191995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13717630711191281512255993 10288223033393461134191995)
    ·
      refine ⟨15432334550090191701287993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10288223033393461134191995 15432334550090191701287993)
      ·
        refine ⟨11574250912567643775965995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15432334550090191701287993 11574250912567643775965995)
        ·
          refine ⟨17361376368851465663948993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11574250912567643775965995 17361376368851465663948993)
          ·
            refine ⟨13021032276638599247961745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17361376368851465663948993 13021032276638599247961745)
            ·
              refine ⟨9765774207478949435971309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13021032276638599247961745 9765774207478949435971309)
              ·
                refine ⟨3662165327804606038489241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9765774207478949435971309 3662165327804606038489241)
                ·
                  refine ⟨2746623995853454528866931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3662165327804606038489241 2746623995853454528866931)
                  ·
                    refine ⟨4119935993780181793300397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2746623995853454528866931 4119935993780181793300397)
                    ·
                      refine ⟨1544975997667568172487649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4119935993780181793300397 1544975997667568172487649)
                      ·
                        rfl

theorem cell23_3008830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_3008830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008830 prefixEnd_3008830 := by exact prefixLift 3008830
  have htrace : WordTrace (prefixWord ++ tailWord_3008830) baseStart_3008830 baseEnd_3008830 := by
    simpa [prefixWord, tailWord_3008830, baseEnd_3008830] using wordTrace_append hprefix tailTrace_3008830
  have hstable : (prefixWord ++ tailWord_3008830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008830).length < 2 ^ (prefixWord ++ tailWord_3008830).sum := by decide
  have hdescent : baseEnd_3008830 < baseStart_3008830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008910 : List Nat := [4, 1, 1, 4, 1, 1, 3, 3, 5]
def baseStart_3008910 : Nat := 118140960795 + 3008910 * 2 ^ 59
def prefixEnd_3008910 : Nat := 4983230072969 + 3 ^ 40 * 3008910 * 2
def baseEnd_3008910 : Nat := 171668564013325317720809

theorem tailTrace_3008910 : CollatzResearch.WordTrace tailWord_3008910 prefixEnd_3008910 171668564013325317720809 := by
  unfold tailWord_3008910
  simp only [CollatzResearch.WordTrace]
  refine ⟨13717995441155053220120023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73162642352826950507306789 13717995441155053220120023)
  ·
    refine ⟨20576993161732579830180035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13717995441155053220120023 20576993161732579830180035)
    ·
      refine ⟨30865489742598869745270053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20576993161732579830180035 30865489742598869745270053)
      ·
        refine ⟨5787279326737288077238135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30865489742598869745270053 5787279326737288077238135)
        ·
          refine ⟨8680918990105932115857203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5787279326737288077238135 8680918990105932115857203)
          ·
            refine ⟨13021378485158898173785805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8680918990105932115857203 13021378485158898173785805)
            ·
              refine ⟨4883016931934586815169677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13021378485158898173785805 4883016931934586815169677)
              ·
                refine ⟨1831131349475470055688629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4883016931934586815169677 1831131349475470055688629)
                ·
                  refine ⟨171668564013325317720809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1831131349475470055688629 171668564013325317720809)
                  ·
                    rfl

theorem cell23_3008910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3, 5].length) (baseStart_3008910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008910 prefixEnd_3008910 := by exact prefixLift 3008910
  have htrace : WordTrace (prefixWord ++ tailWord_3008910) baseStart_3008910 baseEnd_3008910 := by
    simpa [prefixWord, tailWord_3008910, baseEnd_3008910] using wordTrace_append hprefix tailTrace_3008910
  have hstable : (prefixWord ++ tailWord_3008910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008910).length < 2 ^ (prefixWord ++ tailWord_3008910).sum := by decide
  have hdescent : baseEnd_3008910 < baseStart_3008910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008970 : List Nat := [3, 1, 2, 1, 2, 2, 2, 5, 1, 4]
def baseStart_3008970 : Nat := 118140960795 + 3008970 * 2 ^ 59
def prefixEnd_3008970 : Nat := 4983230072969 + 3 ^ 40 * 3008970 * 2
def baseEnd_3008970 : Nat := 515015961653065874912335

theorem tailTrace_3008970 : CollatzResearch.WordTrace tailWord_3008970 prefixEnd_3008970 515015961653065874912335 := by
  unfold tailWord_3008970
  simp only [CollatzResearch.WordTrace]
  refine ⟨27436537977255764002036091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73164101272682037338762909 27436537977255764002036091)
  ·
    refine ⟨41154806965883646003054137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27436537977255764002036091 41154806965883646003054137)
    ·
      refine ⟨30866105224412734502290603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41154806965883646003054137 30866105224412734502290603)
      ·
        refine ⟨46299157836619101753435905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30866105224412734502290603 46299157836619101753435905)
        ·
          refine ⟨34724368377464326315076929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46299157836619101753435905 34724368377464326315076929)
          ·
            refine ⟨26043276283098244736307697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34724368377464326315076929 26043276283098244736307697)
            ·
              refine ⟨19532457212323683552230773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26043276283098244736307697 19532457212323683552230773)
              ·
                refine ⟨1831167863655345333021635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19532457212323683552230773 1831167863655345333021635)
                ·
                  refine ⟨2746751795483017999532453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1831167863655345333021635 2746751795483017999532453)
                  ·
                    refine ⟨515015961653065874912335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2746751795483017999532453 515015961653065874912335)
                    ·
                      rfl

theorem cell23_3008970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_3008970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008970 prefixEnd_3008970 := by exact prefixLift 3008970
  have htrace : WordTrace (prefixWord ++ tailWord_3008970) baseStart_3008970 baseEnd_3008970 := by
    simpa [prefixWord, tailWord_3008970, baseEnd_3008970] using wordTrace_append hprefix tailTrace_3008970
  have hstable : (prefixWord ++ tailWord_3008970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008970).length < 2 ^ (prefixWord ++ tailWord_3008970).sum := by decide
  have hdescent : baseEnd_3008970 < baseStart_3008970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008980 : List Nat := [2, 4, 1, 2, 2, 1, 2, 2, 2, 2, 3]
def baseStart_3008980 : Nat := 118140960795 + 3008980 * 2 ^ 59
def prefixEnd_3008980 : Nat := 4983230072969 + 3 ^ 40 * 3008980 * 2
def baseEnd_3008980 : Nat := 1545053019765742585611959

theorem tailTrace_3008980 : CollatzResearch.WordTrace tailWord_3008980 prefixEnd_3008980 1545053019765742585611959 := by
  unfold tailWord_3008980
  simp only [CollatzResearch.WordTrace]
  refine ⟨54873258319493413858004197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73164344425991218477338929 54873258319493413858004197)
  ·
    refine ⟨10288735934905015098375787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54873258319493413858004197 10288735934905015098375787)
    ·
      refine ⟨15433103902357522647563681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10288735934905015098375787 15433103902357522647563681)
      ·
        refine ⟨11574827926768141985672761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15433103902357522647563681 11574827926768141985672761)
        ·
          refine ⟨8681120945076106489254571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11574827926768141985672761 8681120945076106489254571)
          ·
            refine ⟨13021681417614159733881857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8681120945076106489254571 13021681417614159733881857)
            ·
              refine ⟨9766261063210619800411393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13021681417614159733881857 9766261063210619800411393)
              ·
                refine ⟨7324695797407964850308545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9766261063210619800411393 7324695797407964850308545)
                ·
                  refine ⟨5493521848055973637731409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7324695797407964850308545 5493521848055973637731409)
                  ·
                    refine ⟨4120141386041980228298557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5493521848055973637731409 4120141386041980228298557)
                    ·
                      refine ⟨1545053019765742585611959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4120141386041980228298557 1545053019765742585611959)
                      ·
                        rfl

theorem cell23_3008980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_3008980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008980 prefixEnd_3008980 := by exact prefixLift 3008980
  have htrace : WordTrace (prefixWord ++ tailWord_3008980) baseStart_3008980 baseEnd_3008980 := by
    simpa [prefixWord, tailWord_3008980, baseEnd_3008980] using wordTrace_append hprefix tailTrace_3008980
  have hstable : (prefixWord ++ tailWord_3008980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008980).length < 2 ^ (prefixWord ++ tailWord_3008980).sum := by decide
  have hdescent : baseEnd_3008980 < baseStart_3008980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008986 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6]
def baseStart_3008986 : Nat := 118140960795 + 3008986 * 2 ^ 59
def prefixEnd_3008986 : Nat := 4983230072969 + 3 ^ 40 * 3008986 * 2
def baseEnd_3008986 : Nat := 1545056100649669562136931

theorem tailTrace_3008986 : CollatzResearch.WordTrace tailWord_3008986 prefixEnd_3008986 1545056100649669562136931 := by
  unfold tailWord_3008986
  simp only [CollatzResearch.WordTrace]
  refine ⟨27436683869241272685181703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73164490317976727160484541 27436683869241272685181703)
  ·
    refine ⟨41155025803861909027772555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27436683869241272685181703 41155025803861909027772555)
    ·
      refine ⟨61732538705792863541658833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41155025803861909027772555 61732538705792863541658833)
      ·
        refine ⟨46299404029344647656244125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61732538705792863541658833 46299404029344647656244125)
        ·
          refine ⟨17362276511004242871091547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46299404029344647656244125 17362276511004242871091547)
          ·
            refine ⟨26043414766506364306637321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17362276511004242871091547 26043414766506364306637321)
            ·
              refine ⟨19532561074879773229977991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26043414766506364306637321 19532561074879773229977991)
              ·
                refine ⟨29298841612319659844966987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19532561074879773229977991 29298841612319659844966987)
                ·
                  refine ⟨43948262418479489767450481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29298841612319659844966987 43948262418479489767450481)
                  ·
                    refine ⟨32961196813859617325587861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43948262418479489767450481 32961196813859617325587861)
                    ·
                      refine ⟨1545056100649669562136931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32961196813859617325587861 1545056100649669562136931)
                      ·
                        rfl

theorem cell23_3008986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_3008986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008986 prefixEnd_3008986 := by exact prefixLift 3008986
  have htrace : WordTrace (prefixWord ++ tailWord_3008986) baseStart_3008986 baseEnd_3008986 := by
    simpa [prefixWord, tailWord_3008986, baseEnd_3008986] using wordTrace_append hprefix tailTrace_3008986
  have hstable : (prefixWord ++ tailWord_3008986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008986).length < 2 ^ (prefixWord ++ tailWord_3008986).sum := by decide
  have hdescent : baseEnd_3008986 < baseStart_3008986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3008994 : List Nat := [3, 3, 3, 2, 1, 1, 1, 1, 2, 4, 2]
def baseStart_3008994 : Nat := 118140960795 + 3008994 * 2 ^ 59
def prefixEnd_3008994 : Nat := 4983230072969 + 3 ^ 40 * 3008994 * 2
def baseEnd_3008994 : Nat := 1545060208494905530836895

theorem tailTrace_3008994 : CollatzResearch.WordTrace tailWord_3008994 prefixEnd_3008994 1545060208494905530836895 := by
  unfold tailWord_3008994
  simp only [CollatzResearch.WordTrace]
  refine ⟨27436756815234027026754509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73164684840624072071345357 27436756815234027026754509)
  ·
    refine ⟨10288783805712760135032941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27436756815234027026754509 10288783805712760135032941)
    ·
      refine ⟨3858293927142285050637353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10288783805712760135032941 3858293927142285050637353)
      ·
        refine ⟨2893720445356713787978015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3858293927142285050637353 2893720445356713787978015)
        ·
          refine ⟨4340580668035070681967023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2893720445356713787978015 4340580668035070681967023)
          ·
            refine ⟨6510871002052606022950535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4340580668035070681967023 6510871002052606022950535)
            ·
              refine ⟨9766306503078909034425803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6510871002052606022950535 9766306503078909034425803)
              ·
                refine ⟨14649459754618363551638705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9766306503078909034425803 14649459754618363551638705)
                ·
                  refine ⟨10987094815963772663729029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14649459754618363551638705 10987094815963772663729029)
                  ·
                    refine ⟨2060080277993207374449193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10987094815963772663729029 2060080277993207374449193)
                    ·
                      refine ⟨1545060208494905530836895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2060080277993207374449193 1545060208494905530836895)
                      ·
                        rfl

theorem cell23_3008994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_3008994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3008994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3008994 prefixEnd_3008994 := by exact prefixLift 3008994
  have htrace : WordTrace (prefixWord ++ tailWord_3008994) baseStart_3008994 baseEnd_3008994 := by
    simpa [prefixWord, tailWord_3008994, baseEnd_3008994] using wordTrace_append hprefix tailTrace_3008994
  have hstable : (prefixWord ++ tailWord_3008994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3008994).length < 2 ^ (prefixWord ++ tailWord_3008994).sum := by decide
  have hdescent : baseEnd_3008994 < baseStart_3008994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3008994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009003 : List Nat := [1, 1, 1, 1, 2, 3, 4, 2, 1, 5, 2]
def baseStart_3009003 : Nat := 118140960795 + 3009003 * 2 ^ 59
def prefixEnd_3009003 : Nat := 4983230072969 + 3 ^ 40 * 3009003 * 2
def baseEnd_3009003 : Nat := 1545064829820795995624353

theorem tailTrace_3009003 : CollatzResearch.WordTrace tailWord_3009003 prefixEnd_3009003 1545064829820795995624353 := by
  unfold tailWord_3009003
  simp only [CollatzResearch.WordTrace]
  refine ⟨109747355517903502644095663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73164903678602335096063775 109747355517903502644095663)
  ·
    refine ⟨164621033276855253966143495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109747355517903502644095663 164621033276855253966143495)
    ·
      refine ⟨246931549915282880949215243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164621033276855253966143495 246931549915282880949215243)
      ·
        refine ⟨370397324872924321423822865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246931549915282880949215243 370397324872924321423822865)
        ·
          refine ⟨277797993654693241067867149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370397324872924321423822865 277797993654693241067867149)
          ·
            refine ⟨104174247620509965400450181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 277797993654693241067867149 104174247620509965400450181)
            ·
              refine ⟨19532671428845618512584409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104174247620509965400450181 19532671428845618512584409)
              ·
                refine ⟨14649503571634213884438307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19532671428845618512584409 14649503571634213884438307)
                ·
                  refine ⟨21974255357451320826657461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14649503571634213884438307 21974255357451320826657461)
                  ·
                    refine ⟨2060086439761061327499137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21974255357451320826657461 2060086439761061327499137)
                    ·
                      refine ⟨1545064829820795995624353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2060086439761061327499137 1545064829820795995624353)
                      ·
                        rfl

theorem cell23_3009003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 5, 2].length) (baseStart_3009003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009003 prefixEnd_3009003 := by exact prefixLift 3009003
  have htrace : WordTrace (prefixWord ++ tailWord_3009003) baseStart_3009003 baseEnd_3009003 := by
    simpa [prefixWord, tailWord_3009003, baseEnd_3009003] using wordTrace_append hprefix tailTrace_3009003
  have hstable : (prefixWord ++ tailWord_3009003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009003).length < 2 ^ (prefixWord ++ tailWord_3009003).sum := by decide
  have hdescent : baseEnd_3009003 < baseStart_3009003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009027 : List Nat := [1, 1, 1, 3, 2, 1, 6, 3, 1, 1, 3]
def baseStart_3009027 : Nat := 118140960795 + 3009027 * 2 ^ 59
def prefixEnd_3009027 : Nat := 4983230072969 + 3 ^ 40 * 3009027 * 2
def baseEnd_3009027 : Nat := 1545077153356503901724243

theorem tailTrace_3009027 : CollatzResearch.WordTrace tailWord_3009027 prefixEnd_3009027 1545077153356503901724243 := by
  unfold tailWord_3009027
  simp only [CollatzResearch.WordTrace]
  refine ⟨109748230869816554742969335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73165487246544369828646223 109748230869816554742969335)
  ·
    refine ⟨164622346304724832114454003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109748230869816554742969335 164622346304724832114454003)
    ·
      refine ⟨246933519457087248171681005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164622346304724832114454003 246933519457087248171681005)
      ·
        refine ⟨92600069796407718064380377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246933519457087248171681005 92600069796407718064380377)
        ·
          refine ⟨69450052347305788548285283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92600069796407718064380377 69450052347305788548285283)
          ·
            refine ⟨104175078520958682822427925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69450052347305788548285283 104175078520958682822427925)
            ·
              refine ⟨4883206805669938257301309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 104175078520958682822427925 4883206805669938257301309)
              ·
                refine ⟨1831202552126226846487991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4883206805669938257301309 1831202552126226846487991)
                ·
                  refine ⟨2746803828189340269731987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1831202552126226846487991 2746803828189340269731987)
                  ·
                    refine ⟨4120205742284010404597981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2746803828189340269731987 4120205742284010404597981)
                    ·
                      refine ⟨1545077153356503901724243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4120205742284010404597981 1545077153356503901724243)
                      ·
                        rfl

theorem cell23_3009027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3, 1, 1, 3].length) (baseStart_3009027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009027 prefixEnd_3009027 := by exact prefixLift 3009027
  have htrace : WordTrace (prefixWord ++ tailWord_3009027) baseStart_3009027 baseEnd_3009027 := by
    simpa [prefixWord, tailWord_3009027, baseEnd_3009027] using wordTrace_append hprefix tailTrace_3009027
  have hstable : (prefixWord ++ tailWord_3009027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009027).length < 2 ^ (prefixWord ++ tailWord_3009027).sum := by decide
  have hdescent : baseEnd_3009027 < baseStart_3009027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009043 : List Nat := [1, 1, 1, 2, 1, 5, 3, 1, 4, 4]
def baseStart_3009043 : Nat := 118140960795 + 3009043 * 2 ^ 59
def prefixEnd_3009043 : Nat := 4983230072969 + 3 ^ 40 * 3009043 * 2
def baseEnd_3009043 : Nat := 515028456348991946374723

theorem tailTrace_3009043 : CollatzResearch.WordTrace tailWord_3009043 prefixEnd_3009043 515028456348991946374723 := by
  unfold tailWord_3009043
  simp only [CollatzResearch.WordTrace]
  refine ⟨109748814437758589475551783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73165876291839059650367855 109748814437758589475551783)
  ·
    refine ⟨164623221656637884213327675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109748814437758589475551783 164623221656637884213327675)
    ·
      refine ⟨246934832484956826319991513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164623221656637884213327675 246934832484956826319991513)
      ·
        refine ⟨185201124363717619739993635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246934832484956826319991513 185201124363717619739993635)
        ·
          refine ⟨277801686545576429609990453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185201124363717619739993635 277801686545576429609990453)
          ·
            refine ⟨26043908113647790275936605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 277801686545576429609990453 26043908113647790275936605)
            ·
              refine ⟨9766465542617921353476227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26043908113647790275936605 9766465542617921353476227)
              ·
                refine ⟨14649698313926882030214341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9766465542617921353476227 14649698313926882030214341)
                ·
                  refine ⟨2746818433861290380665189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14649698313926882030214341 2746818433861290380665189)
                  ·
                    refine ⟨515028456348991946374723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2746818433861290380665189 515028456348991946374723)
                    ·
                      rfl

theorem cell23_3009043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4, 4].length) (baseStart_3009043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009043 prefixEnd_3009043 := by exact prefixLift 3009043
  have htrace : WordTrace (prefixWord ++ tailWord_3009043) baseStart_3009043 baseEnd_3009043 := by
    simpa [prefixWord, tailWord_3009043, baseEnd_3009043] using wordTrace_append hprefix tailTrace_3009043
  have hstable : (prefixWord ++ tailWord_3009043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009043).length < 2 ^ (prefixWord ++ tailWord_3009043).sum := by decide
  have hdescent : baseEnd_3009043 < baseStart_3009043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009044 : List Nat := [2, 4, 3, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_3009044 : Nat := 118140960795 + 3009044 * 2 ^ 59
def prefixEnd_3009044 : Nat := 4983230072969 + 3 ^ 40 * 3009044 * 2
def baseEnd_3009044 : Nat := 1545085882527630335211665

theorem tailTrace_3009044 : CollatzResearch.WordTrace tailWord_3009044 prefixEnd_3009044 1545085882527630335211665 := by
  unfold tailWord_3009044
  simp only [CollatzResearch.WordTrace]
  refine ⟨54874425455377483323169093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73165900607169977764225457 54874425455377483323169093)
  ·
    refine ⟨10288954772883278123094205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54874425455377483323169093 10288954772883278123094205)
    ·
      refine ⟨3858358039831229296160327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10288954772883278123094205 3858358039831229296160327)
      ·
        refine ⟨5787537059746843944240491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3858358039831229296160327 5787537059746843944240491)
        ·
          refine ⟨8681305589620265916360737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5787537059746843944240491 8681305589620265916360737)
          ·
            refine ⟨6510979192215199437270553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8681305589620265916360737 6510979192215199437270553)
            ·
              refine ⟨4883234394161399577952915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6510979192215199437270553 4883234394161399577952915)
              ·
                refine ⟨7324851591242099366929373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4883234394161399577952915 7324851591242099366929373)
                ·
                  refine ⟨2746819346715787262598515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7324851591242099366929373 2746819346715787262598515)
                  ·
                    refine ⟨4120229020073680893897773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2746819346715787262598515 4120229020073680893897773)
                    ·
                      refine ⟨1545085882527630335211665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4120229020073680893897773 1545085882527630335211665)
                      ·
                        rfl

theorem cell23_3009044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_3009044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009044 prefixEnd_3009044 := by exact prefixLift 3009044
  have htrace : WordTrace (prefixWord ++ tailWord_3009044) baseStart_3009044 baseEnd_3009044 := by
    simpa [prefixWord, tailWord_3009044, baseEnd_3009044] using wordTrace_append hprefix tailTrace_3009044
  have hstable : (prefixWord ++ tailWord_3009044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009044).length < 2 ^ (prefixWord ++ tailWord_3009044).sum := by decide
  have hdescent : baseEnd_3009044 < baseStart_3009044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009053 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_3009053 : Nat := 118140960795 + 3009053 * 2 ^ 59
def prefixEnd_3009053 : Nat := 4983230072969 + 3 ^ 40 * 3009053 * 2
def baseEnd_3009053 : Nat := 1545090503853520799999123

theorem tailTrace_3009053 : CollatzResearch.WordTrace tailWord_3009053 prefixEnd_3009053 1545090503853520799999123 := by
  unfold tailWord_3009053
  simp only [CollatzResearch.WordTrace]
  refine ⟨109749179167722361183415813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73166119445148240788943875 109749179167722361183415813)
  ·
    refine ⟨20577971093947942721890465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109749179167722361183415813 20577971093947942721890465)
    ·
      refine ⟨15433478320460957041417849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20577971093947942721890465 15433478320460957041417849)
      ·
        refine ⟨11575108740345717781063387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15433478320460957041417849 11575108740345717781063387)
        ·
          refine ⟨17362663110518576671595081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11575108740345717781063387 17362663110518576671595081)
          ·
            refine ⟨13021997332888932503696311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17362663110518576671595081 13021997332888932503696311)
            ·
              refine ⟨19532995999333398755544467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13021997332888932503696311 19532995999333398755544467)
              ·
                refine ⟨29299493999000098133316701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19532995999333398755544467 29299493999000098133316701)
                ·
                  refine ⟨10987310249625036799993763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29299493999000098133316701 10987310249625036799993763)
                  ·
                    refine ⟨16480965374437555199990645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10987310249625036799993763 16480965374437555199990645)
                    ·
                      refine ⟨1545090503853520799999123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16480965374437555199990645 1545090503853520799999123)
                      ·
                        rfl

theorem cell23_3009053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_3009053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009053 prefixEnd_3009053 := by exact prefixLift 3009053
  have htrace : WordTrace (prefixWord ++ tailWord_3009053) baseStart_3009053 baseEnd_3009053 := by
    simpa [prefixWord, tailWord_3009053, baseEnd_3009053] using wordTrace_append hprefix tailTrace_3009053
  have hstable : (prefixWord ++ tailWord_3009053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009053).length < 2 ^ (prefixWord ++ tailWord_3009053).sum := by decide
  have hdescent : baseEnd_3009053 < baseStart_3009053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009073 : List Nat := [1, 2, 2, 3, 1, 1, 6, 7]
def baseStart_3009073 : Nat := 118140960795 + 3009073 * 2 ^ 59
def prefixEnd_3009073 : Nat := 4983230072969 + 3 ^ 40 * 3009073 * 2
def baseEnd_3009073 : Nat := 57225954572837434138853

theorem tailTrace_3009073 : CollatzResearch.WordTrace tailWord_3009073 prefixEnd_3009073 57225954572837434138853 := by
  unfold tailWord_3009073
  simp only [CollatzResearch.WordTrace]
  refine ⟨109749908627649904599143873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73166605751766603066095915 109749908627649904599143873)
  ·
    refine ⟨82312431470737428449357905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109749908627649904599143873 82312431470737428449357905)
    ·
      refine ⟨61734323603053071337018429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82312431470737428449357905 61734323603053071337018429)
      ·
        refine ⟨23150371351144901751381911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61734323603053071337018429 23150371351144901751381911)
        ·
          refine ⟨34725557026717352627072867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23150371351144901751381911 34725557026717352627072867)
          ·
            refine ⟨52088335540076028940609301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34725557026717352627072867 52088335540076028940609301)
            ·
              refine ⟨2441640728441063856591061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52088335540076028940609301 2441640728441063856591061)
              ·
                refine ⟨57225954572837434138853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2441640728441063856591061 57225954572837434138853)
                ·
                  rfl

theorem cell23_3009073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 7].length) (baseStart_3009073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009073 prefixEnd_3009073 := by exact prefixLift 3009073
  have htrace : WordTrace (prefixWord ++ tailWord_3009073) baseStart_3009073 baseEnd_3009073 := by
    simpa [prefixWord, tailWord_3009073, baseEnd_3009073] using wordTrace_append hprefix tailTrace_3009073
  have hstable : (prefixWord ++ tailWord_3009073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009073).length < 2 ^ (prefixWord ++ tailWord_3009073).sum := by decide
  have hdescent : baseEnd_3009073 < baseStart_3009073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009100 : List Nat := [2, 2, 1, 3, 1, 2, 1, 3, 4, 1, 3]
def baseStart_3009100 : Nat := 118140960795 + 3009100 * 2 ^ 59
def prefixEnd_3009100 : Nat := 4983230072969 + 3 ^ 40 * 3009100 * 2
def baseEnd_3009100 : Nat := 1545114637444282116111407

theorem tailTrace_3009100 : CollatzResearch.WordTrace tailWord_3009100 prefixEnd_3009100 1545114637444282116111407 := by
  unfold tailWord_3009100
  simp only [CollatzResearch.WordTrace]
  refine ⟨54875446699276044105188377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73167262265701392140251169 54875446699276044105188377)
  ·
    refine ⟨41156585024457033078891283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54875446699276044105188377 41156585024457033078891283)
    ·
      refine ⟨61734877536685549618336925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41156585024457033078891283 61734877536685549618336925)
      ·
        refine ⟨23150579076257081106876347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61734877536685549618336925 23150579076257081106876347)
        ·
          refine ⟨34725868614385621660314521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23150579076257081106876347 34725868614385621660314521)
          ·
            refine ⟨26044401460789216245235891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34725868614385621660314521 26044401460789216245235891)
            ·
              refine ⟨39066602191183824367853837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26044401460789216245235891 39066602191183824367853837)
              ·
                refine ⟨14649975821693934137945189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39066602191183824367853837 14649975821693934137945189)
                ·
                  refine ⟨2746870466567612650864723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14649975821693934137945189 2746870466567612650864723)
                  ·
                    refine ⟨4120305699851418976297085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2746870466567612650864723 4120305699851418976297085)
                    ·
                      refine ⟨1545114637444282116111407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4120305699851418976297085 1545114637444282116111407)
                      ·
                        rfl

theorem cell23_3009100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_3009100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009100 prefixEnd_3009100 := by exact prefixLift 3009100
  have htrace : WordTrace (prefixWord ++ tailWord_3009100) baseStart_3009100 baseEnd_3009100 := by
    simpa [prefixWord, tailWord_3009100, baseEnd_3009100] using wordTrace_append hprefix tailTrace_3009100
  have hstable : (prefixWord ++ tailWord_3009100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009100).length < 2 ^ (prefixWord ++ tailWord_3009100).sum := by decide
  have hdescent : baseEnd_3009100 < baseStart_3009100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009101 : List Nat := [1, 6, 1, 1, 2, 3, 1, 1, 3, 2, 2]
def baseStart_3009101 : Nat := 118140960795 + 3009101 * 2 ^ 59
def prefixEnd_3009101 : Nat := 4983230072969 + 3 ^ 40 * 3009101 * 2
def baseEnd_3009101 : Nat := 1545115150924936612198903

theorem tailTrace_3009101 : CollatzResearch.WordTrace tailWord_3009101 prefixEnd_3009101 1545115150924936612198903 := by
  unfold tailWord_3009101
  simp only [CollatzResearch.WordTrace]
  refine ⟨109750929871548465381163157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73167286581032310254108771 109750929871548465381163157)
  ·
    refine ⟨5144574837728834314742023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 109750929871548465381163157 5144574837728834314742023)
    ·
      refine ⟨7716862256593251472113035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5144574837728834314742023 7716862256593251472113035)
      ·
        refine ⟨11575293384889877208169553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7716862256593251472113035 11575293384889877208169553)
        ·
          refine ⟨8681470038667407906127165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11575293384889877208169553 8681470038667407906127165)
          ·
            refine ⟨3255551264500277964797687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8681470038667407906127165 3255551264500277964797687)
            ·
              refine ⟨4883326896750416947196531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3255551264500277964797687 4883326896750416947196531)
              ·
                refine ⟨7324990345125625420794797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4883326896750416947196531 7324990345125625420794797)
                ·
                  refine ⟨2746871379422109532798049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7324990345125625420794797 2746871379422109532798049)
                  ·
                    refine ⟨2060153534566582149598537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2746871379422109532798049 2060153534566582149598537)
                    ·
                      refine ⟨1545115150924936612198903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2060153534566582149598537 1545115150924936612198903)
                      ·
                        rfl

theorem cell23_3009101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_3009101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009101 prefixEnd_3009101 := by exact prefixLift 3009101
  have htrace : WordTrace (prefixWord ++ tailWord_3009101) baseStart_3009101 baseEnd_3009101 := by
    simpa [prefixWord, tailWord_3009101, baseEnd_3009101] using wordTrace_append hprefix tailTrace_3009101
  have hstable : (prefixWord ++ tailWord_3009101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009101).length < 2 ^ (prefixWord ++ tailWord_3009101).sum := by decide
  have hdescent : baseEnd_3009101 < baseStart_3009101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009118 : List Nat := [4, 4, 1, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_3009118 : Nat := 118140960795 + 3009118 * 2 ^ 59
def prefixEnd_3009118 : Nat := 4983230072969 + 3 ^ 40 * 3009118 * 2
def baseEnd_3009118 : Nat := 1545123880096063045686325

theorem tailTrace_3009118 : CollatzResearch.WordTrace tailWord_3009118 prefixEnd_3009118 1545123880096063045686325 := by
  unfold tailWord_3009118
  simp only [CollatzResearch.WordTrace]
  refine ⟨13718943739060859660566501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73167699941657918189688005 13718943739060859660566501)
  ·
    refine ⟨2572301951073911186356219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13718943739060859660566501 2572301951073911186356219)
    ·
      refine ⟨3858452926610866779534329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2572301951073911186356219 3858452926610866779534329)
      ·
        refine ⟨2893839694958150084650747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3858452926610866779534329 2893839694958150084650747)
        ·
          refine ⟨4340759542437225126976121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2893839694958150084650747 4340759542437225126976121)
          ·
            refine ⟨3255569656827918845232091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4340759542437225126976121 3255569656827918845232091)
            ·
              refine ⟨4883354485241878267848137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3255569656827918845232091 4883354485241878267848137)
              ·
                refine ⟨3662515863931408700886103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4883354485241878267848137 3662515863931408700886103)
                ·
                  refine ⟨5493773795897113051329155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3662515863931408700886103 5493773795897113051329155)
                  ·
                    refine ⟨8240660693845669576993733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5493773795897113051329155 8240660693845669576993733)
                    ·
                      refine ⟨1545123880096063045686325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8240660693845669576993733 1545123880096063045686325)
                      ·
                        rfl

theorem cell23_3009118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_3009118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009118 prefixEnd_3009118 := by exact prefixLift 3009118
  have htrace : WordTrace (prefixWord ++ tailWord_3009118) baseStart_3009118 baseEnd_3009118 := by
    simpa [prefixWord, tailWord_3009118, baseEnd_3009118] using wordTrace_append hprefix tailTrace_3009118
  have hstable : (prefixWord ++ tailWord_3009118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009118).length < 2 ^ (prefixWord ++ tailWord_3009118).sum := by decide
  have hdescent : baseEnd_3009118 < baseStart_3009118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009143 : List Nat := [1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 5]
def baseStart_3009143 : Nat := 118140960795 + 3009143 * 2 ^ 59
def prefixEnd_3009143 : Nat := 4983230072969 + 3 ^ 40 * 3009143 * 2
def baseEnd_3009143 : Nat := 1545136717112425447873709

theorem tailTrace_3009143 : CollatzResearch.WordTrace tailWord_3009143 prefixEnd_3009143 1545136717112425447873709 := by
  unfold tailWord_3009143
  simp only [CollatzResearch.WordTrace]
  refine ⟨109752461737396306554192083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73168307824930871036128055 109752461737396306554192083)
  ·
    refine ⟨164628692606094459831288125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109752461737396306554192083 164628692606094459831288125)
    ·
      refine ⟨61735759727285422436733047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164628692606094459831288125 61735759727285422436733047)
      ·
        refine ⟨92603639590928133655099571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61735759727285422436733047 92603639590928133655099571)
        ·
          refine ⟨138905459386392200482649357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92603639590928133655099571 138905459386392200482649357)
          ·
            refine ⟨52089547269897075180993509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138905459386392200482649357 52089547269897075180993509)
            ·
              refine ⟨9766790113105701596436283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52089547269897075180993509 9766790113105701596436283)
              ·
                refine ⟨14650185169658552394654425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9766790113105701596436283 14650185169658552394654425)
                ·
                  refine ⟨10987638877243914295990819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14650185169658552394654425 10987638877243914295990819)
                  ·
                    refine ⟨16481458315865871443986229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10987638877243914295990819 16481458315865871443986229)
                    ·
                      refine ⟨1545136717112425447873709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16481458315865871443986229 1545136717112425447873709)
                      ·
                        rfl

theorem cell23_3009143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_3009143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009143 prefixEnd_3009143 := by exact prefixLift 3009143
  have htrace : WordTrace (prefixWord ++ tailWord_3009143) baseStart_3009143 baseEnd_3009143 := by
    simpa [prefixWord, tailWord_3009143, baseEnd_3009143] using wordTrace_append hprefix tailTrace_3009143
  have hstable : (prefixWord ++ tailWord_3009143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009143).length < 2 ^ (prefixWord ++ tailWord_3009143).sum := by decide
  have hdescent : baseEnd_3009143 < baseStart_3009143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009170 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_3009170 : Nat := 118140960795 + 3009170 * 2 ^ 59
def prefixEnd_3009170 : Nat := 4983230072969 + 3 ^ 40 * 3009170 * 2
def baseEnd_3009170 : Nat := 1545150581090096842236085

theorem tailTrace_3009170 : CollatzResearch.WordTrace tailWord_3009170 prefixEnd_3009170 1545150581090096842236085 := by
  unfold tailWord_3009170
  simp only [CollatzResearch.WordTrace]
  refine ⟨27438361627074622541356241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73168964338865660110283309 27438361627074622541356241)
  ·
    refine ⟨20578771220305966906017181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27438361627074622541356241 20578771220305966906017181)
    ·
      refine ⟨7717039207614737589756443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20578771220305966906017181 7717039207614737589756443)
      ·
        refine ⟨11575558811422106384634665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7717039207614737589756443 11575558811422106384634665)
        ·
          refine ⟨8681669108566579788475999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11575558811422106384634665 8681669108566579788475999)
          ·
            refine ⟨13022503662849869682713999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8681669108566579788475999 13022503662849869682713999)
            ·
              refine ⟨19533755494274804524070999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13022503662849869682713999 19533755494274804524070999)
              ·
                refine ⟨29300633241412206786106499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19533755494274804524070999 29300633241412206786106499)
                ·
                  refine ⟨43950949862118310179159749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29300633241412206786106499 43950949862118310179159749)
                  ·
                    refine ⟨8240803099147183158592453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43950949862118310179159749 8240803099147183158592453)
                    ·
                      refine ⟨1545150581090096842236085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8240803099147183158592453 1545150581090096842236085)
                      ·
                        rfl

theorem cell23_3009170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_3009170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009170 prefixEnd_3009170 := by exact prefixLift 3009170
  have htrace : WordTrace (prefixWord ++ tailWord_3009170) baseStart_3009170 baseEnd_3009170 := by
    simpa [prefixWord, tailWord_3009170, baseEnd_3009170] using wordTrace_append hprefix tailTrace_3009170
  have hstable : (prefixWord ++ tailWord_3009170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009170).length < 2 ^ (prefixWord ++ tailWord_3009170).sum := by decide
  have hdescent : baseEnd_3009170 < baseStart_3009170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009180 : List Nat := [2, 2, 3, 2, 2, 2, 1, 2, 7]
def baseStart_3009180 : Nat := 118140960795 + 3009180 * 2 ^ 59
def prefixEnd_3009180 : Nat := 4983230072969 + 3 ^ 40 * 3009180 * 2
def baseEnd_3009180 : Nat := 171683968432960200345671

theorem tailTrace_3009180 : CollatzResearch.WordTrace tailWord_3009180 prefixEnd_3009180 171683968432960200345671 := by
  unfold tailWord_3009180
  simp only [CollatzResearch.WordTrace]
  refine ⟨54876905619131130936644497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73169207492174841248859329 54876905619131130936644497)
  ·
    refine ⟨41157679214348348202483373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54876905619131130936644497 41157679214348348202483373)
    ·
      refine ⟨15434129705380630575931265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41157679214348348202483373 15434129705380630575931265)
      ·
        refine ⟨11575597279035472931948449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15434129705380630575931265 11575597279035472931948449)
        ·
          refine ⟨8681697959276604698961337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11575597279035472931948449 8681697959276604698961337)
          ·
            refine ⟨6511273469457453524221003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8681697959276604698961337 6511273469457453524221003)
            ·
              refine ⟨9766910204186180286331505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6511273469457453524221003 9766910204186180286331505)
              ·
                refine ⟨7325182653139635214748629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9766910204186180286331505 7325182653139635214748629)
                ·
                  refine ⟨171683968432960200345671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7325182653139635214748629 171683968432960200345671)
                  ·
                    rfl

theorem cell23_3009180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 7].length) (baseStart_3009180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009180 prefixEnd_3009180 := by exact prefixLift 3009180
  have htrace : WordTrace (prefixWord ++ tailWord_3009180) baseStart_3009180 baseEnd_3009180 := by
    simpa [prefixWord, tailWord_3009180, baseEnd_3009180] using wordTrace_append hprefix tailTrace_3009180
  have hstable : (prefixWord ++ tailWord_3009180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009180).length < 2 ^ (prefixWord ++ tailWord_3009180).sum := by decide
  have hdescent : baseEnd_3009180 < baseStart_3009180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009197 : List Nat := [1, 5, 2, 1, 1, 2, 1, 5, 5]
def baseStart_3009197 : Nat := 118140960795 + 3009197 * 2 ^ 59
def prefixEnd_3009197 : Nat := 4983230072969 + 3 ^ 40 * 3009197 * 2
def baseEnd_3009197 : Nat := 171684938340863137399829

theorem tailTrace_3009197 : CollatzResearch.WordTrace tailWord_3009197 prefixEnd_3009197 171684938340863137399829 := by
  unfold tailWord_3009197
  simp only [CollatzResearch.WordTrace]
  refine ⟨109754431279200673776657845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73169620852800449184438563 109754431279200673776657845)
  ·
    refine ⟨10289477932425063166561673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109754431279200673776657845 10289477932425063166561673)
    ·
      refine ⟨7717108449318797374921255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10289477932425063166561673 7717108449318797374921255)
      ·
        refine ⟨11575662673978196062381883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7717108449318797374921255 11575662673978196062381883)
        ·
          refine ⟨17363494010967294093572825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11575662673978196062381883 17363494010967294093572825)
          ·
            refine ⟨13022620508225470570179619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17363494010967294093572825 13022620508225470570179619)
            ·
              refine ⟨19533930762338205855269429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13022620508225470570179619 19533930762338205855269429)
              ·
                refine ⟨1831306008969206798931509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19533930762338205855269429 1831306008969206798931509)
                ·
                  refine ⟨171684938340863137399829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1831306008969206798931509 171684938340863137399829)
                  ·
                    rfl

theorem cell23_3009197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_3009197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009197 prefixEnd_3009197 := by exact prefixLift 3009197
  have htrace : WordTrace (prefixWord ++ tailWord_3009197) baseStart_3009197 baseEnd_3009197 := by
    simpa [prefixWord, tailWord_3009197, baseEnd_3009197] using wordTrace_append hprefix tailTrace_3009197
  have hstable : (prefixWord ++ tailWord_3009197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009197).length < 2 ^ (prefixWord ++ tailWord_3009197).sum := by decide
  have hdescent : baseEnd_3009197 < baseStart_3009197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009230 : List Nat := [4, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4]
def baseStart_3009230 : Nat := 118140960795 + 3009230 * 2 ^ 59
def prefixEnd_3009230 : Nat := 4983230072969 + 3 ^ 40 * 3009230 * 2
def baseEnd_3009230 : Nat := 1545181389929366607485809

theorem tailTrace_3009230 : CollatzResearch.WordTrace tailWord_3009230 prefixEnd_3009230 1545181389929366607485809 := by
  unfold tailWord_3009230
  simp only [CollatzResearch.WordTrace]
  refine ⟨13719454361010140051576143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73170423258720746941739429 13719454361010140051576143)
  ·
    refine ⟨20579181541515210077364215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13719454361010140051576143 20579181541515210077364215)
    ·
      refine ⟨30868772312272815116046323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20579181541515210077364215 30868772312272815116046323)
      ·
        refine ⟨46303158468409222674069485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30868772312272815116046323 46303158468409222674069485)
        ·
          refine ⟨17363684425653458502776057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46303158468409222674069485 17363684425653458502776057)
          ·
            refine ⟨13022763319240093877082043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17363684425653458502776057 13022763319240093877082043)
            ·
              refine ⟨19534144978860140815623065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13022763319240093877082043 19534144978860140815623065)
              ·
                refine ⟨14650608734145105611717299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19534144978860140815623065 14650608734145105611717299)
                ·
                  refine ⟨21975913101217658417575949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14650608734145105611717299 21975913101217658417575949)
                  ·
                    refine ⟨8240967412956621906590981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21975913101217658417575949 8240967412956621906590981)
                    ·
                      refine ⟨1545181389929366607485809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8240967412956621906590981 1545181389929366607485809)
                      ·
                        rfl

theorem cell23_3009230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_3009230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009230 prefixEnd_3009230 := by exact prefixLift 3009230
  have htrace : WordTrace (prefixWord ++ tailWord_3009230) baseStart_3009230 baseEnd_3009230 := by
    simpa [prefixWord, tailWord_3009230, baseEnd_3009230] using wordTrace_append hprefix tailTrace_3009230
  have hstable : (prefixWord ++ tailWord_3009230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009230).length < 2 ^ (prefixWord ++ tailWord_3009230).sum := by decide
  have hdescent : baseEnd_3009230 < baseStart_3009230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009270 : List Nat := [5, 1, 1, 1, 1, 2, 1, 3, 8]
def baseStart_3009270 : Nat := 118140960795 + 3009270 * 2 ^ 59
def prefixEnd_3009270 : Nat := 4983230072969 + 3 ^ 40 * 3009270 * 2
def baseEnd_3009270 : Nat := 171689103239505161220625

theorem tailTrace_3009270 : CollatzResearch.WordTrace tailWord_3009270 prefixEnd_3009270 171689103239505161220625 := by
  unfold tailWord_3009270
  simp only [CollatzResearch.WordTrace]
  refine ⟨6859818362996012952754079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73171395871957471496043509 6859818362996012952754079)
  ·
    refine ⟨10289727544494019429131119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6859818362996012952754079 10289727544494019429131119)
    ·
      refine ⟨15434591316741029143696679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10289727544494019429131119 15434591316741029143696679)
      ·
        refine ⟨23151886975111543715545019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15434591316741029143696679 23151886975111543715545019)
        ·
          refine ⟨34727830462667315573317529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23151886975111543715545019 34727830462667315573317529)
          ·
            refine ⟨26045872847000486679988147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34727830462667315573317529 26045872847000486679988147)
            ·
              refine ⟨39068809270500730019982221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26045872847000486679988147 39068809270500730019982221)
              ·
                refine ⟨14650803476437773757493333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39068809270500730019982221 14650803476437773757493333)
                ·
                  refine ⟨171689103239505161220625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14650803476437773757493333 171689103239505161220625)
                  ·
                    rfl

theorem cell23_3009270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_3009270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009270 prefixEnd_3009270 := by exact prefixLift 3009270
  have htrace : WordTrace (prefixWord ++ tailWord_3009270) baseStart_3009270 baseEnd_3009270 := by
    simpa [prefixWord, tailWord_3009270, baseEnd_3009270] using wordTrace_append hprefix tailTrace_3009270
  have hstable : (prefixWord ++ tailWord_3009270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009270).length < 2 ^ (prefixWord ++ tailWord_3009270).sum := by decide
  have hdescent : baseEnd_3009270 < baseStart_3009270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009273 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 1, 1, 8]
def baseStart_3009273 : Nat := 118140960795 + 3009273 * 2 ^ 59
def prefixEnd_3009273 : Nat := 4983230072969 + 3 ^ 40 * 3009273 * 2
def baseEnd_3009273 : Nat := 1545203469597509939248111

theorem tailTrace_3009273 : CollatzResearch.WordTrace tailWord_3009273 prefixEnd_3009273 1545203469597509939248111 := by
  unfold tailWord_3009273
  simp only [CollatzResearch.WordTrace]
  refine ⟨109757203226925338756424473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73171468817950225837616315 109757203226925338756424473)
  ·
    refine ⟨82317902420194004067318355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109757203226925338756424473 82317902420194004067318355)
    ·
      refine ⟨123476853630291006100977533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82317902420194004067318355 123476853630291006100977533)
      ·
        refine ⟨46303820111359127287866575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123476853630291006100977533 46303820111359127287866575)
        ·
          refine ⟨69455730167038690931799863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46303820111359127287866575 69455730167038690931799863)
          ·
            refine ⟨104183595250558036397699795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69455730167038690931799863 104183595250558036397699795)
            ·
              refine ⟨156275392875837054596549693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104183595250558036397699795 156275392875837054596549693)
              ·
                refine ⟨58603272328438895473706135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156275392875837054596549693 58603272328438895473706135)
                ·
                  refine ⟨87904908492658343210559203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58603272328438895473706135 87904908492658343210559203)
                  ·
                    refine ⟨131857362738987514815838805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87904908492658343210559203 131857362738987514815838805)
                    ·
                      refine ⟨1545203469597509939248111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 131857362738987514815838805 1545203469597509939248111)
                      ·
                        rfl

theorem cell23_3009273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_3009273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009273 prefixEnd_3009273 := by exact prefixLift 3009273
  have htrace : WordTrace (prefixWord ++ tailWord_3009273) baseStart_3009273 baseEnd_3009273 := by
    simpa [prefixWord, tailWord_3009273, baseEnd_3009273] using wordTrace_append hprefix tailTrace_3009273
  have hstable : (prefixWord ++ tailWord_3009273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009273).length < 2 ^ (prefixWord ++ tailWord_3009273).sum := by decide
  have hdescent : baseEnd_3009273 < baseStart_3009273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009283 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 2, 9]
def baseStart_3009283 : Nat := 118140960795 + 3009283 * 2 ^ 59
def prefixEnd_3009283 : Nat := 4983230072969 + 3 ^ 40 * 3009283 * 2
def baseEnd_3009283 : Nat := 515069534801351633374355

theorem tailTrace_3009283 : CollatzResearch.WordTrace tailWord_3009283 prefixEnd_3009283 515069534801351633374355 := by
  unfold tailWord_3009283
  simp only [CollatzResearch.WordTrace]
  refine ⟨109757567956889110464288503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73171711971259406976192335 109757567956889110464288503)
  ·
    refine ⟨164636351935333665696432755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109757567956889110464288503 164636351935333665696432755)
    ·
      refine ⟨246954527903000498544649133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164636351935333665696432755 246954527903000498544649133)
      ·
        refine ⟨92607947963625186954243425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246954527903000498544649133 92607947963625186954243425)
        ·
          refine ⟨69455960972718890215682569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92607947963625186954243425 69455960972718890215682569)
          ·
            refine ⟨52091970729539167661761927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69455960972718890215682569 52091970729539167661761927)
            ·
              refine ⟨78137956094308751492642891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52091970729539167661761927 78137956094308751492642891)
              ·
                refine ⟨117206934141463127238964337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78137956094308751492642891 117206934141463127238964337)
                ·
                  refine ⟨87905200606097345429223253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117206934141463127238964337 87905200606097345429223253)
                  ·
                    refine ⟨515069534801351633374355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 87905200606097345429223253 515069534801351633374355)
                    ·
                      rfl

theorem cell23_3009283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 9].length) (baseStart_3009283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009283 prefixEnd_3009283 := by exact prefixLift 3009283
  have htrace : WordTrace (prefixWord ++ tailWord_3009283) baseStart_3009283 baseEnd_3009283 := by
    simpa [prefixWord, tailWord_3009283, baseEnd_3009283] using wordTrace_append hprefix tailTrace_3009283
  have hstable : (prefixWord ++ tailWord_3009283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009283).length < 2 ^ (prefixWord ++ tailWord_3009283).sum := by decide
  have hdescent : baseEnd_3009283 < baseStart_3009283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009287 : List Nat := [1, 1, 4, 4, 1, 2, 1, 3, 6]
def baseStart_3009287 : Nat := 118140960795 + 3009287 * 2 ^ 59
def prefixEnd_3009287 : Nat := 4983230072969 + 3 ^ 40 * 3009287 * 2
def baseEnd_3009287 : Nat := 171690073147408098274783

theorem tailTrace_3009287 : CollatzResearch.WordTrace tailWord_3009287 prefixEnd_3009287 171690073147408098274783 := by
  unfold tailWord_3009287
  simp only [CollatzResearch.WordTrace]
  refine ⟨109757713848874619147434115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73171809232583079431622743 109757713848874619147434115)
  ·
    refine ⟨164636570773311928721151173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109757713848874619147434115 164636570773311928721151173)
    ·
      refine ⟨30869357019995986635215845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164636570773311928721151173 30869357019995986635215845)
      ·
        refine ⟨5788004441249247494102971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30869357019995986635215845 5788004441249247494102971)
        ·
          refine ⟨8682006661873871241154457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5788004441249247494102971 8682006661873871241154457)
          ·
            refine ⟨6511504996405403430865843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8682006661873871241154457 6511504996405403430865843)
            ·
              refine ⟨9767257494608105146298765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6511504996405403430865843 9767257494608105146298765)
              ·
                refine ⟨3662721560478039429862037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9767257494608105146298765 3662721560478039429862037)
                ·
                  refine ⟨171690073147408098274783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3662721560478039429862037 171690073147408098274783)
                  ·
                    rfl

theorem cell23_3009287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 6].length) (baseStart_3009287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009287 prefixEnd_3009287 := by exact prefixLift 3009287
  have htrace : WordTrace (prefixWord ++ tailWord_3009287) baseStart_3009287 baseEnd_3009287 := by
    simpa [prefixWord, tailWord_3009287, baseEnd_3009287] using wordTrace_append hprefix tailTrace_3009287
  have hstable : (prefixWord ++ tailWord_3009287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009287).length < 2 ^ (prefixWord ++ tailWord_3009287).sum := by decide
  have hdescent : baseEnd_3009287 < baseStart_3009287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009297 : List Nat := [1, 2, 2, 1, 1, 3, 2, 4, 3, 1, 3]
def baseStart_3009297 : Nat := 118140960795 + 3009297 * 2 ^ 59
def prefixEnd_3009297 : Nat := 4983230072969 + 3 ^ 40 * 3009297 * 2
def baseEnd_3009297 : Nat := 1545215793133217845348001

theorem tailTrace_3009297 : CollatzResearch.WordTrace tailWord_3009297 prefixEnd_3009297 1545215793133217845348001 := by
  unfold tailWord_3009297
  simp only [CollatzResearch.WordTrace]
  refine ⟨109758078578838390855298145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73172052385892260570198763 109758078578838390855298145)
  ·
    refine ⟨82318558934128793141473609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109758078578838390855298145 82318558934128793141473609)
    ·
      refine ⟨61738919200596594856105207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82318558934128793141473609 61738919200596594856105207)
      ·
        refine ⟨92608378800894892284157811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61738919200596594856105207 92608378800894892284157811)
        ·
          refine ⟨138912568201342338426236717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92608378800894892284157811 138912568201342338426236717)
          ·
            refine ⟨52092213075503376909838769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138912568201342338426236717 52092213075503376909838769)
            ·
              refine ⟨39069159806627532682379077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52092213075503376909838769 39069159806627532682379077)
              ·
                refine ⟨7325467463742662377946077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39069159806627532682379077 7325467463742662377946077)
                ·
                  refine ⟨2747050298903498391729779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7325467463742662377946077 2747050298903498391729779)
                  ·
                    refine ⟨4120575448355247587594669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2747050298903498391729779 4120575448355247587594669)
                    ·
                      refine ⟨1545215793133217845348001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4120575448355247587594669 1545215793133217845348001)
                      ·
                        rfl

theorem cell23_3009297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3, 1, 3].length) (baseStart_3009297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009297 prefixEnd_3009297 := by exact prefixLift 3009297
  have htrace : WordTrace (prefixWord ++ tailWord_3009297) baseStart_3009297 baseEnd_3009297 := by
    simpa [prefixWord, tailWord_3009297, baseEnd_3009297] using wordTrace_append hprefix tailTrace_3009297
  have hstable : (prefixWord ++ tailWord_3009297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009297).length < 2 ^ (prefixWord ++ tailWord_3009297).sum := by decide
  have hdescent : baseEnd_3009297 < baseStart_3009297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009330 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 3, 6]
def baseStart_3009330 : Nat := 118140960795 + 3009330 * 2 ^ 59
def prefixEnd_3009330 : Nat := 4983230072969 + 3 ^ 40 * 3009330 * 2
def baseEnd_3009330 : Nat := 515077579331605405411783

theorem tailTrace_3009330 : CollatzResearch.WordTrace tailWord_3009330 prefixEnd_3009330 515077579331605405411783 := by
  unfold tailWord_3009330
  simp only [CollatzResearch.WordTrace]
  refine ⟨27439820546929709372812361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73172854791812558327499629 27439820546929709372812361)
  ·
    refine ⟨20579865410197282029609271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27439820546929709372812361 20579865410197282029609271)
    ·
      refine ⟨30869798115295923044413907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20579865410197282029609271 30869798115295923044413907)
      ·
        refine ⟨46304697172943884566620861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30869798115295923044413907 46304697172943884566620861)
        ·
          refine ⟨17364261439853956712482823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46304697172943884566620861 17364261439853956712482823)
          ·
            refine ⟨26046392159780935068724235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17364261439853956712482823 26046392159780935068724235)
            ·
              refine ⟨39069588239671402603086353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26046392159780935068724235 39069588239671402603086353)
              ·
                refine ⟨29302191179753551952314765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39069588239671402603086353 29302191179753551952314765)
                ·
                  refine ⟨10988321692407581982118037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29302191179753551952314765 10988321692407581982118037)
                  ·
                    refine ⟨515077579331605405411783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10988321692407581982118037 515077579331605405411783)
                    ·
                      rfl

theorem cell23_3009330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_3009330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009330 prefixEnd_3009330 := by exact prefixLift 3009330
  have htrace : WordTrace (prefixWord ++ tailWord_3009330) baseStart_3009330 baseEnd_3009330 := by
    simpa [prefixWord, tailWord_3009330, baseEnd_3009330] using wordTrace_append hprefix tailTrace_3009330
  have hstable : (prefixWord ++ tailWord_3009330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009330).length < 2 ^ (prefixWord ++ tailWord_3009330).sum := by decide
  have hdescent : baseEnd_3009330 < baseStart_3009330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009331 : List Nat := [1, 1, 1, 2, 6, 2, 1, 4, 1, 1, 3]
def baseStart_3009331 : Nat := 118140960795 + 3009331 * 2 ^ 59
def prefixEnd_3009331 : Nat := 4983230072969 + 3 ^ 40 * 3009331 * 2
def baseEnd_3009331 : Nat := 1545233251475470712322845

theorem tailTrace_3009331 : CollatzResearch.WordTrace tailWord_3009331 prefixEnd_3009331 1545233251475470712322845 := by
  unfold tailWord_3009331
  simp only [CollatzResearch.WordTrace]
  refine ⟨109759318660715214662035847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73172879107143476441357231 109759318660715214662035847)
  ·
    refine ⟨164638977991072821993053771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109759318660715214662035847 164638977991072821993053771)
    ·
      refine ⟨246958466986609232989580657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164638977991072821993053771 246958466986609232989580657)
      ·
        refine ⟨185218850239956924742185493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246958466986609232989580657 185218850239956924742185493)
        ·
          refine ⟨8682133604997980847289945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 185218850239956924742185493 8682133604997980847289945)
          ·
            refine ⟨6511600203748485635467459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8682133604997980847289945 6511600203748485635467459)
            ·
              refine ⟨9767400305622728453201189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6511600203748485635467459 9767400305622728453201189)
              ·
                refine ⟨1831387557304261584975223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9767400305622728453201189 1831387557304261584975223)
                ·
                  refine ⟨2747081335956392377462835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1831387557304261584975223 2747081335956392377462835)
                  ·
                    refine ⟨4120622003934588566194253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2747081335956392377462835 4120622003934588566194253)
                    ·
                      refine ⟨1545233251475470712322845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4120622003934588566194253 1545233251475470712322845)
                      ·
                        rfl

theorem cell23_3009331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4, 1, 1, 3].length) (baseStart_3009331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009331 prefixEnd_3009331 := by exact prefixLift 3009331
  have htrace : WordTrace (prefixWord ++ tailWord_3009331) baseStart_3009331 baseEnd_3009331 := by
    simpa [prefixWord, tailWord_3009331, baseEnd_3009331] using wordTrace_append hprefix tailTrace_3009331
  have hstable : (prefixWord ++ tailWord_3009331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009331).length < 2 ^ (prefixWord ++ tailWord_3009331).sum := by decide
  have hdescent : baseEnd_3009331 < baseStart_3009331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009340 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 3, 1, 5]
def baseStart_3009340 : Nat := 118140960795 + 3009340 * 2 ^ 59
def prefixEnd_3009340 : Nat := 4983230072969 + 3 ^ 40 * 3009340 * 2
def baseEnd_3009340 : Nat := 1545237872801361177110303

theorem tailTrace_3009340 : CollatzResearch.WordTrace tailWord_3009340 prefixEnd_3009340 1545237872801361177110303 := by
  unfold tailWord_3009340
  simp only [CollatzResearch.WordTrace]
  refine ⟨54879823458841304599556737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73173097945121739466075649 54879823458841304599556737)
  ·
    refine ⟨41159867594130978449667553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54879823458841304599556737 41159867594130978449667553)
    ·
      refine ⟨30869900695598233837250665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41159867594130978449667553 30869900695598233837250665)
      ·
        refine ⟨23152425521698675377937999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30869900695598233837250665 23152425521698675377937999)
        ·
          refine ⟨34728638282548013066906999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23152425521698675377937999 34728638282548013066906999)
          ·
            refine ⟨52092957423822019600360499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34728638282548013066906999 52092957423822019600360499)
            ·
              refine ⟨78139436135733029400540749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52092957423822019600360499 78139436135733029400540749)
              ·
                refine ⟨29302288550899886025202781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78139436135733029400540749 29302288550899886025202781)
                ·
                  refine ⟨10988358206587457259451043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29302288550899886025202781 10988358206587457259451043)
                  ·
                    refine ⟨16482537309881185889176565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10988358206587457259451043 16482537309881185889176565)
                    ·
                      refine ⟨1545237872801361177110303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16482537309881185889176565 1545237872801361177110303)
                      ·
                        rfl

theorem cell23_3009340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_3009340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009340 prefixEnd_3009340 := by exact prefixLift 3009340
  have htrace : WordTrace (prefixWord ++ tailWord_3009340) baseStart_3009340 baseEnd_3009340 := by
    simpa [prefixWord, tailWord_3009340, baseEnd_3009340] using wordTrace_append hprefix tailTrace_3009340
  have hstable : (prefixWord ++ tailWord_3009340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009340).length < 2 ^ (prefixWord ++ tailWord_3009340).sum := by decide
  have hdescent : baseEnd_3009340 < baseStart_3009340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009347 : List Nat := [1, 1, 1, 3, 1, 4, 1, 5, 2, 4]
def baseStart_3009347 : Nat := 118140960795 + 3009347 * 2 ^ 59
def prefixEnd_3009347 : Nat := 4983230072969 + 3 ^ 40 * 3009347 * 2
def baseEnd_3009347 : Nat := 515080489055314216574257

theorem tailTrace_3009347 : CollatzResearch.WordTrace tailWord_3009347 prefixEnd_3009347 515080489055314216574257 := by
  unfold tailWord_3009347
  simp only [CollatzResearch.WordTrace]
  refine ⟨109759902228657249394618295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73173268152438166263078863 109759902228657249394618295)
  ·
    refine ⟨164639853342985874091927443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109759902228657249394618295 164639853342985874091927443)
    ·
      refine ⟨246959780014478811137891165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164639853342985874091927443 246959780014478811137891165)
      ·
        refine ⟨92609917505429554176709187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246959780014478811137891165 92609917505429554176709187)
        ·
          refine ⟨138914876258144331265063781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92609917505429554176709187 138914876258144331265063781)
          ·
            refine ⟨26046539298402062112199459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138914876258144331265063781 26046539298402062112199459)
            ·
              refine ⟨39069808947603093168299189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26046539298402062112199459 39069808947603093168299189)
              ·
                refine ⟨3662794588837789984528049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39069808947603093168299189 3662794588837789984528049)
                ·
                  refine ⟨2747095941628342488396037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3662794588837789984528049 2747095941628342488396037)
                  ·
                    refine ⟨515080489055314216574257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2747095941628342488396037 515080489055314216574257)
                    ·
                      rfl

theorem cell23_3009347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2, 4].length) (baseStart_3009347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009347 prefixEnd_3009347 := by exact prefixLift 3009347
  have htrace : WordTrace (prefixWord ++ tailWord_3009347) baseStart_3009347 baseEnd_3009347 := by
    simpa [prefixWord, tailWord_3009347, baseEnd_3009347] using wordTrace_append hprefix tailTrace_3009347
  have hstable : (prefixWord ++ tailWord_3009347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009347).length < 2 ^ (prefixWord ++ tailWord_3009347).sum := by decide
  have hdescent : baseEnd_3009347 < baseStart_3009347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009348 : List Nat := [2, 3, 4, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_3009348 : Nat := 118140960795 + 3009348 * 2 ^ 59
def prefixEnd_3009348 : Nat := 4983230072969 + 3 ^ 40 * 3009348 * 2
def baseEnd_3009348 : Nat := 1545241980646597145810267

theorem tailTrace_3009348 : CollatzResearch.WordTrace tailWord_3009348 prefixEnd_3009348 1545241980646597145810267 := by
  unfold tailWord_3009348
  simp only [CollatzResearch.WordTrace]
  refine ⟨54879969350826813282702349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73173292467769084376936465 54879969350826813282702349)
  ·
    refine ⟨20579988506560054981013381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54879969350826813282702349 20579988506560054981013381)
    ·
      refine ⟨3858747844980010308940009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20579988506560054981013381 3858747844980010308940009)
      ·
        refine ⟨2894060883735007731705007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3858747844980010308940009 2894060883735007731705007)
        ·
          refine ⟨4341091325602511597557511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2894060883735007731705007 4341091325602511597557511)
          ·
            refine ⟨6511636988403767396336267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4341091325602511597557511 6511636988403767396336267)
            ·
              refine ⟨9767455482605651094504401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6511636988403767396336267 9767455482605651094504401)
              ·
                refine ⟨7325591611954238320878301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9767455482605651094504401 7325591611954238320878301)
                ·
                  refine ⟨2747096854482839370329363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7325591611954238320878301 2747096854482839370329363)
                  ·
                    refine ⟨4120645281724259055494045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2747096854482839370329363 4120645281724259055494045)
                    ·
                      refine ⟨1545241980646597145810267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4120645281724259055494045 1545241980646597145810267)
                      ·
                        rfl

theorem cell23_3009348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_3009348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009348 prefixEnd_3009348 := by exact prefixLift 3009348
  have htrace : WordTrace (prefixWord ++ tailWord_3009348) baseStart_3009348 baseEnd_3009348 := by
    simpa [prefixWord, tailWord_3009348, baseEnd_3009348] using wordTrace_append hprefix tailTrace_3009348
  have hstable : (prefixWord ++ tailWord_3009348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009348).length < 2 ^ (prefixWord ++ tailWord_3009348).sum := by decide
  have hdescent : baseEnd_3009348 < baseStart_3009348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009367 : List Nat := [1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 4]
def baseStart_3009367 : Nat := 118140960795 + 3009367 * 2 ^ 59
def prefixEnd_3009367 : Nat := 4983230072969 + 3 ^ 40 * 3009367 * 2
def baseEnd_3009367 : Nat := 1545251736779032571472679

theorem tailTrace_3009367 : CollatzResearch.WordTrace tailWord_3009367 prefixEnd_3009367 1545251736779032571472679 := by
  unfold tailWord_3009367
  simp only [CollatzResearch.WordTrace]
  refine ⟨109760631688584792810346355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73173754459056528540230903 109760631688584792810346355)
  ·
    refine ⟨164640947532877189215519533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109760631688584792810346355 164640947532877189215519533)
    ·
      refine ⟨61740355324828945955819825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164640947532877189215519533 61740355324828945955819825)
      ·
        refine ⟨46305266493621709466864869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61740355324828945955819825 46305266493621709466864869)
        ·
          refine ⟨8682237467554070525037163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46305266493621709466864869 8682237467554070525037163)
          ·
            refine ⟨13023356201331105787555745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8682237467554070525037163 13023356201331105787555745)
            ·
              refine ⟨9767517150998329340666809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13023356201331105787555745 9767517150998329340666809)
              ·
                refine ⟨7325637863248747005500107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9767517150998329340666809 7325637863248747005500107)
                ·
                  refine ⟨10988456794873120508250161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7325637863248747005500107 10988456794873120508250161)
                  ·
                    refine ⟨8241342596154840381187621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10988456794873120508250161 8241342596154840381187621)
                    ·
                      refine ⟨1545251736779032571472679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8241342596154840381187621 1545251736779032571472679)
                      ·
                        rfl

theorem cell23_3009367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_3009367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009367 prefixEnd_3009367 := by exact prefixLift 3009367
  have htrace : WordTrace (prefixWord ++ tailWord_3009367) baseStart_3009367 baseEnd_3009367 := by
    simpa [prefixWord, tailWord_3009367, baseEnd_3009367] using wordTrace_append hprefix tailTrace_3009367
  have hstable : (prefixWord ++ tailWord_3009367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009367).length < 2 ^ (prefixWord ++ tailWord_3009367).sum := by decide
  have hdescent : baseEnd_3009367 < baseStart_3009367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009398 : List Nat := [5, 1, 1, 3, 1, 2, 3, 1, 2, 4]
def baseStart_3009398 : Nat := 118140960795 + 3009398 * 2 ^ 59
def prefixEnd_3009398 : Nat := 4983230072969 + 3 ^ 40 * 3009398 * 2
def baseEnd_3009398 : Nat := 515089218226440650061679

theorem tailTrace_3009398 : CollatzResearch.WordTrace tailWord_3009398 prefixEnd_3009398 515089218226440650061679 := by
  unfold tailWord_3009398
  simp only [CollatzResearch.WordTrace]
  refine ⟨6860110146967030319045303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73174508234314990069816565 6860110146967030319045303)
  ·
    refine ⟨10290165220450545478567955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6860110146967030319045303 10290165220450545478567955)
    ·
      refine ⟨15435247830675818217851933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10290165220450545478567955 15435247830675818217851933)
      ·
        refine ⟨5788217936503431831694475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15435247830675818217851933 5788217936503431831694475)
        ·
          refine ⟨8682326904755147747541713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5788217936503431831694475 8682326904755147747541713)
          ·
            refine ⟨6511745178566360810656285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8682326904755147747541713 6511745178566360810656285)
            ·
              refine ⟨2441904441962385303996107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6511745178566360810656285 2441904441962385303996107)
              ·
                refine ⟨3662856662943577955994161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2441904441962385303996107 3662856662943577955994161)
                ·
                  refine ⟨2747142497207683466995621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3662856662943577955994161 2747142497207683466995621)
                  ·
                    refine ⟨515089218226440650061679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2747142497207683466995621 515089218226440650061679)
                    ·
                      rfl

theorem cell23_3009398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_3009398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009398 prefixEnd_3009398 := by exact prefixLift 3009398
  have htrace : WordTrace (prefixWord ++ tailWord_3009398) baseStart_3009398 baseEnd_3009398 := by
    simpa [prefixWord, tailWord_3009398, baseEnd_3009398] using wordTrace_append hprefix tailTrace_3009398
  have hstable : (prefixWord ++ tailWord_3009398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009398).length < 2 ^ (prefixWord ++ tailWord_3009398).sum := by decide
  have hdescent : baseEnd_3009398 < baseStart_3009398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009404 : List Nat := [2, 2, 2, 1, 1, 1, 1, 7, 2, 1, 3]
def baseStart_3009404 : Nat := 118140960795 + 3009404 * 2 ^ 59
def prefixEnd_3009404 : Nat := 4983230072969 + 3 ^ 40 * 3009404 * 2
def baseEnd_3009404 : Nat := 1545270735563248926710009

theorem tailTrace_3009404 : CollatzResearch.WordTrace tailWord_3009404 prefixEnd_3009404 1545270735563248926710009 := by
  unfold tailWord_3009404
  simp only [CollatzResearch.WordTrace]
  refine ⟨54880990594725374064721633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73174654126300498752962177 54880990594725374064721633)
  ·
    refine ⟨41160742946044030548541225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54880990594725374064721633 41160742946044030548541225)
    ·
      refine ⟨30870557209533022911405919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41160742946044030548541225 30870557209533022911405919)
      ·
        refine ⟨46305835814299534367108879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30870557209533022911405919 46305835814299534367108879)
        ·
          refine ⟨69458753721449301550663319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46305835814299534367108879 69458753721449301550663319)
          ·
            refine ⟨104188130582173952325994979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69458753721449301550663319 104188130582173952325994979)
            ·
              refine ⟨156282195873260928488992469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104188130582173952325994979 156282195873260928488992469)
              ·
                refine ⟨3662863965779553011460761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 156282195873260928488992469 3662863965779553011460761)
                ·
                  refine ⟨2747147974334664758595571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3662863965779553011460761 2747147974334664758595571)
                  ·
                    refine ⟨4120721961501997137893357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2747147974334664758595571 4120721961501997137893357)
                    ·
                      refine ⟨1545270735563248926710009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4120721961501997137893357 1545270735563248926710009)
                      ·
                        rfl

theorem cell23_3009404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_3009404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009404 prefixEnd_3009404 := by exact prefixLift 3009404
  have htrace : WordTrace (prefixWord ++ tailWord_3009404) baseStart_3009404 baseEnd_3009404 := by
    simpa [prefixWord, tailWord_3009404, baseEnd_3009404] using wordTrace_append hprefix tailTrace_3009404
  have hstable : (prefixWord ++ tailWord_3009404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009404).length < 2 ^ (prefixWord ++ tailWord_3009404).sum := by decide
  have hdescent : baseEnd_3009404 < baseStart_3009404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009420 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 1, 8]
def baseStart_3009420 : Nat := 118140960795 + 3009420 * 2 ^ 59
def prefixEnd_3009420 : Nat := 4983230072969 + 3 ^ 40 * 3009420 * 2
def baseEnd_3009420 : Nat := 515092983751240288036645

theorem tailTrace_3009420 : CollatzResearch.WordTrace tailWord_3009420 prefixEnd_3009420 515092983751240288036645 := by
  unfold tailWord_3009420
  simp only [CollatzResearch.WordTrace]
  refine ⟨54881282378696391431012857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73175043171595188574683809 54881282378696391431012857)
  ·
    refine ⟨41160961784022293573259643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54881282378696391431012857 41160961784022293573259643)
    ·
      refine ⟨61741442676033440359889465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41160961784022293573259643 61741442676033440359889465)
      ·
        refine ⟨46306082007025080269917099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61741442676033440359889465 46306082007025080269917099)
        ·
          refine ⟨69459123010537620404875649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46306082007025080269917099 69459123010537620404875649)
          ·
            refine ⟨52094342257903215303656737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69459123010537620404875649 52094342257903215303656737)
            ·
              refine ⟨39070756693427411477742553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52094342257903215303656737 39070756693427411477742553)
              ·
                refine ⟨29303067520070558608306915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39070756693427411477742553 29303067520070558608306915)
                ·
                  refine ⟨43954601280105837912460373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29303067520070558608306915 43954601280105837912460373)
                  ·
                    refine ⟨515092983751240288036645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43954601280105837912460373 515092983751240288036645)
                    ·
                      rfl

theorem cell23_3009420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 8].length) (baseStart_3009420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009420 prefixEnd_3009420 := by exact prefixLift 3009420
  have htrace : WordTrace (prefixWord ++ tailWord_3009420) baseStart_3009420 baseEnd_3009420 := by
    simpa [prefixWord, tailWord_3009420, baseEnd_3009420] using wordTrace_append hprefix tailTrace_3009420
  have hstable : (prefixWord ++ tailWord_3009420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009420).length < 2 ^ (prefixWord ++ tailWord_3009420).sum := by decide
  have hdescent : baseEnd_3009420 < baseStart_3009420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009484 : List Nat := [2, 2, 1, 4, 1, 1, 2, 5, 5]
def baseStart_3009484 : Nat := 118140960795 + 3009484 * 2 ^ 59
def prefixEnd_3009484 : Nat := 4983230072969 + 3 ^ 40 * 3009484 * 2
def baseEnd_3009484 : Nat := 171701312668400957078849

theorem tailTrace_3009484 : CollatzResearch.WordTrace tailWord_3009484 prefixEnd_3009484 171701312668400957078849 := by
  unfold tailWord_3009484
  simp only [CollatzResearch.WordTrace]
  refine ⟨54882449514580460896177753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73176599352773947861570337 54882449514580460896177753)
  ·
    refine ⟨41161837135935345672133315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54882449514580460896177753 41161837135935345672133315)
    ·
      refine ⟨61742755703903018508199973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41161837135935345672133315 61742755703903018508199973)
      ·
        refine ⟨11576766694481815970287495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61742755703903018508199973 11576766694481815970287495)
        ·
          refine ⟨17365150041722723955431243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11576766694481815970287495 17365150041722723955431243)
          ·
            refine ⟨26047725062584085933146865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17365150041722723955431243 26047725062584085933146865)
            ·
              refine ⟨19535793796938064449860149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26047725062584085933146865 19535793796938064449860149)
              ·
                refine ⟨1831480668462943542174389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19535793796938064449860149 1831480668462943542174389)
                ·
                  refine ⟨171701312668400957078849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1831480668462943542174389 171701312668400957078849)
                  ·
                    rfl

theorem cell23_3009484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5, 5].length) (baseStart_3009484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009484 prefixEnd_3009484 := by exact prefixLift 3009484
  have htrace : WordTrace (prefixWord ++ tailWord_3009484) baseStart_3009484 baseEnd_3009484 := by
    simpa [prefixWord, tailWord_3009484, baseEnd_3009484] using wordTrace_append hprefix tailTrace_3009484
  have hstable : (prefixWord ++ tailWord_3009484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009484).length < 2 ^ (prefixWord ++ tailWord_3009484).sum := by decide
  have hdescent : baseEnd_3009484 < baseStart_3009484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009501 : List Nat := [1, 4, 3, 1, 2, 2, 1, 4, 5]
def baseStart_3009501 : Nat := 118140960795 + 3009501 * 2 ^ 59
def prefixEnd_3009501 : Nat := 4983230072969 + 3 ^ 40 * 3009501 * 2
def baseEnd_3009501 : Nat := 171702282576303894133007

theorem tailTrace_3009501 : CollatzResearch.WordTrace tailWord_3009501 prefixEnd_3009501 171702282576303894133007 := by
  unfold tailWord_3009501
  simp only [CollatzResearch.WordTrace]
  refine ⟨109765519070099333695724357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73177012713399555797149571 109765519070099333695724357)
  ·
    refine ⟨20581034825643625067948317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109765519070099333695724357 20581034825643625067948317)
    ·
      refine ⟨7717888059616359400480619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20581034825643625067948317 7717888059616359400480619)
      ·
        refine ⟨11576832089424539100720929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7717888059616359400480619 11576832089424539100720929)
        ·
          refine ⟨8682624067068404325540697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11576832089424539100720929 8682624067068404325540697)
          ·
            refine ⟨6511968050301303244155523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8682624067068404325540697 6511968050301303244155523)
            ·
              refine ⟨9767952075451954866233285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6511968050301303244155523 9767952075451954866233285)
              ·
                refine ⟨1831491014147241537418741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9767952075451954866233285 1831491014147241537418741)
                ·
                  refine ⟨171702282576303894133007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1831491014147241537418741 171702282576303894133007)
                  ·
                    rfl

theorem cell23_3009501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4, 5].length) (baseStart_3009501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009501 prefixEnd_3009501 := by exact prefixLift 3009501
  have htrace : WordTrace (prefixWord ++ tailWord_3009501) baseStart_3009501 baseEnd_3009501 := by
    simpa [prefixWord, tailWord_3009501, baseEnd_3009501] using wordTrace_append hprefix tailTrace_3009501
  have hstable : (prefixWord ++ tailWord_3009501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009501).length < 2 ^ (prefixWord ++ tailWord_3009501).sum := by decide
  have hdescent : baseEnd_3009501 < baseStart_3009501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009507 : List Nat := [1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 5]
def baseStart_3009507 : Nat := 118140960795 + 3009507 * 2 ^ 59
def prefixEnd_3009507 : Nat := 4983230072969 + 3 ^ 40 * 3009507 * 2
def baseEnd_3009507 : Nat := 1545323624070662023722035

theorem tailTrace_3009507 : CollatzResearch.WordTrace tailWord_3009507 prefixEnd_3009507 1545323624070662023722035 := by
  unfold tailWord_3009507
  simp only [CollatzResearch.WordTrace]
  refine ⟨109765737908077596720442775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73177158605385064480295183 109765737908077596720442775)
  ·
    refine ⟨164648606862116395080664163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109765737908077596720442775 164648606862116395080664163)
    ·
      refine ⟨246972910293174592620996245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164648606862116395080664163 246972910293174592620996245)
      ·
        refine ⟨11576855169992559029109199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 246972910293174592620996245 11576855169992559029109199)
        ·
          refine ⟨17365282754988838543663799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11576855169992559029109199 17365282754988838543663799)
          ·
            refine ⟨26047924132483257815495699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17365282754988838543663799 26047924132483257815495699)
            ·
              refine ⟨39071886198724886723243549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26047924132483257815495699 39071886198724886723243549)
              ·
                refine ⟨14651957324521832521216331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39071886198724886723243549 14651957324521832521216331)
                ·
                  refine ⟨21977935986782748781824497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14651957324521832521216331 21977935986782748781824497)
                  ·
                    refine ⟨16483451990087061586368373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21977935986782748781824497 16483451990087061586368373)
                    ·
                      refine ⟨1545323624070662023722035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16483451990087061586368373 1545323624070662023722035)
                      ·
                        rfl

theorem cell23_3009507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_3009507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009507 prefixEnd_3009507 := by exact prefixLift 3009507
  have htrace : WordTrace (prefixWord ++ tailWord_3009507) baseStart_3009507 baseEnd_3009507 := by
    simpa [prefixWord, tailWord_3009507, baseEnd_3009507] using wordTrace_append hprefix tailTrace_3009507
  have hstable : (prefixWord ++ tailWord_3009507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009507).length < 2 ^ (prefixWord ++ tailWord_3009507).sum := by decide
  have hdescent : baseEnd_3009507 < baseStart_3009507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009547 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 6]
def baseStart_3009547 : Nat := 118140960795 + 3009547 * 2 ^ 59
def prefixEnd_3009547 : Nat := 4983230072969 + 3 ^ 40 * 3009547 * 2
def baseEnd_3009547 : Nat := 1545344163296841867221851

theorem tailTrace_3009547 : CollatzResearch.WordTrace tailWord_3009547 prefixEnd_3009547 1545344163296841867221851 := by
  unfold tailWord_3009547
  simp only [CollatzResearch.WordTrace]
  refine ⟨109767196827932683551898895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73178131218621789034599263 109767196827932683551898895)
  ·
    refine ⟨164650795241899025327848343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109767196827932683551898895 164650795241899025327848343)
    ·
      refine ⟨246976192862848537991772515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164650795241899025327848343 246976192862848537991772515)
      ·
        refine ⟨370464289294272806987658773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246976192862848537991772515 370464289294272806987658773)
        ·
          refine ⟨17365513560669037827546505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 370464289294272806987658773 17365513560669037827546505)
          ·
            refine ⟨13024135170501778370659879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17365513560669037827546505 13024135170501778370659879)
            ·
              refine ⟨19536202755752667555989819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13024135170501778370659879 19536202755752667555989819)
              ·
                refine ⟨29304304133629001333984729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19536202755752667555989819 29304304133629001333984729)
                ·
                  refine ⟨21978228100221751000488547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29304304133629001333984729 21978228100221751000488547)
                  ·
                    refine ⟨32967342150332626500732821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21978228100221751000488547 32967342150332626500732821)
                    ·
                      refine ⟨1545344163296841867221851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32967342150332626500732821 1545344163296841867221851)
                      ·
                        rfl

theorem cell23_3009547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 6].length) (baseStart_3009547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009547 prefixEnd_3009547 := by exact prefixLift 3009547
  have htrace : WordTrace (prefixWord ++ tailWord_3009547) baseStart_3009547 baseEnd_3009547 := by
    simpa [prefixWord, tailWord_3009547, baseEnd_3009547] using wordTrace_append hprefix tailTrace_3009547
  have hstable : (prefixWord ++ tailWord_3009547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009547).length < 2 ^ (prefixWord ++ tailWord_3009547).sum := by decide
  have hdescent : baseEnd_3009547 < baseStart_3009547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009561 : List Nat := [1, 2, 1, 2, 1, 1, 6, 4, 1, 4]
def baseStart_3009561 : Nat := 118140960795 + 3009561 * 2 ^ 59
def prefixEnd_3009561 : Nat := 4983230072969 + 3 ^ 40 * 3009561 * 2
def baseEnd_3009561 : Nat := 515117117342001604148929

theorem tailTrace_3009561 : CollatzResearch.WordTrace tailWord_3009561 prefixEnd_3009561 515117117342001604148929 := by
  unfold tailWord_3009561
  simp only [CollatzResearch.WordTrace]
  refine ⟨109767707449881963942908537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73178471633254642628605691 109767707449881963942908537)
  ·
    refine ⟨82325780587411472957181403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109767707449881963942908537 82325780587411472957181403)
    ·
      refine ⟨123488670881117209435772105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82325780587411472957181403 123488670881117209435772105)
      ·
        refine ⟨92616503160837907076829079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123488670881117209435772105 92616503160837907076829079)
        ·
          refine ⟨138924754741256860615243619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92616503160837907076829079 138924754741256860615243619)
          ·
            refine ⟨208387132111885290922865429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138924754741256860615243619 208387132111885290922865429)
            ·
              refine ⟨9768146817744623012009317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 208387132111885290922865429 9768146817744623012009317)
              ·
                refine ⟨1831527528327116814751747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9768146817744623012009317 1831527528327116814751747)
                ·
                  refine ⟨2747291292490675222127621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1831527528327116814751747 2747291292490675222127621)
                  ·
                    refine ⟨515117117342001604148929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2747291292490675222127621 515117117342001604148929)
                    ·
                      rfl

theorem cell23_3009561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4, 1, 4].length) (baseStart_3009561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009561 prefixEnd_3009561 := by exact prefixLift 3009561
  have htrace : WordTrace (prefixWord ++ tailWord_3009561) baseStart_3009561 baseEnd_3009561 := by
    simpa [prefixWord, tailWord_3009561, baseEnd_3009561] using wordTrace_append hprefix tailTrace_3009561
  have hstable : (prefixWord ++ tailWord_3009561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009561).length < 2 ^ (prefixWord ++ tailWord_3009561).sum := by decide
  have hdescent : baseEnd_3009561 < baseStart_3009561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009618 : List Nat := [3, 2, 2, 1, 3, 1, 3, 1, 3, 1, 3]
def baseStart_3009618 : Nat := 118140960795 + 3009618 * 2 ^ 59
def prefixEnd_3009618 : Nat := 4983230072969 + 3 ^ 40 * 3009618 * 2
def baseEnd_3009618 : Nat := 1545380620423311089434025

theorem tailTrace_3009618 : CollatzResearch.WordTrace tailWord_3009618 prefixEnd_3009618 1545380620423311089434025 := by
  unfold tailWord_3009618
  simp only [CollatzResearch.WordTrace]
  refine ⟨27442446602668865669433377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73179857607116975118489005 27442446602668865669433377)
  ·
    refine ⟨20581834952001649252075033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27442446602668865669433377 20581834952001649252075033)
    ·
      refine ⟨15436376214001236939056275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20581834952001649252075033 15436376214001236939056275)
      ·
        refine ⟨23154564321001855408584413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15436376214001236939056275 23154564321001855408584413)
        ·
          refine ⟨8682961620375695778219155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23154564321001855408584413 8682961620375695778219155)
          ·
            refine ⟨13024442430563543667328733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8682961620375695778219155 13024442430563543667328733)
            ·
              refine ⟨4884165911461328875248275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13024442430563543667328733 4884165911461328875248275)
              ·
                refine ⟨7326248867191993312872413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4884165911461328875248275 7326248867191993312872413)
                ·
                  refine ⟨2747343325196997492327155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7326248867191993312872413 2747343325196997492327155)
                  ·
                    refine ⟨4121014987795496238490733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2747343325196997492327155 4121014987795496238490733)
                    ·
                      refine ⟨1545380620423311089434025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4121014987795496238490733 1545380620423311089434025)
                      ·
                        rfl

theorem cell23_3009618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_3009618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009618 prefixEnd_3009618 := by exact prefixLift 3009618
  have htrace : WordTrace (prefixWord ++ tailWord_3009618) baseStart_3009618 baseEnd_3009618 := by
    simpa [prefixWord, tailWord_3009618, baseEnd_3009618] using wordTrace_append hprefix tailTrace_3009618
  have hstable : (prefixWord ++ tailWord_3009618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009618).length < 2 ^ (prefixWord ++ tailWord_3009618).sum := by decide
  have hdescent : baseEnd_3009618 < baseStart_3009618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009624 : List Nat := [2, 1, 2, 2, 1, 3, 2, 2, 3, 1, 4]
def baseStart_3009624 : Nat := 118140960795 + 3009624 * 2 ^ 59
def prefixEnd_3009624 : Nat := 4983230072969 + 3 ^ 40 * 3009624 * 2
def baseEnd_3009624 : Nat := 1545383701307238065958997

theorem tailTrace_3009624 : CollatzResearch.WordTrace tailWord_3009624 prefixEnd_3009624 1545383701307238065958997 := by
  unfold tailWord_3009624
  simp only [CollatzResearch.WordTrace]
  refine ⟨54885002624326862851225963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73180003499102483801634617 54885002624326862851225963)
  ·
    refine ⟨82327503936490294276838945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54885002624326862851225963 82327503936490294276838945)
    ·
      refine ⟨61745627952367720707629209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82327503936490294276838945 61745627952367720707629209)
      ·
        refine ⟨46309220964275790530721907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61745627952367720707629209 46309220964275790530721907)
        ·
          refine ⟨69463831446413685796082861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46309220964275790530721907 69463831446413685796082861)
          ·
            refine ⟨26048936792405132173531073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69463831446413685796082861 26048936792405132173531073)
            ·
              refine ⟨19536702594303849130148305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26048936792405132173531073 19536702594303849130148305)
              ·
                refine ⟨14652526945727886847611229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19536702594303849130148305 14652526945727886847611229)
                ·
                  refine ⟨5494697604647957567854211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14652526945727886847611229 5494697604647957567854211)
                  ·
                    refine ⟨8242046406971936351781317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5494697604647957567854211 8242046406971936351781317)
                    ·
                      refine ⟨1545383701307238065958997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8242046406971936351781317 1545383701307238065958997)
                      ·
                        rfl

theorem cell23_3009624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_3009624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009624 prefixEnd_3009624 := by exact prefixLift 3009624
  have htrace : WordTrace (prefixWord ++ tailWord_3009624) baseStart_3009624 baseEnd_3009624 := by
    simpa [prefixWord, tailWord_3009624, baseEnd_3009624] using wordTrace_append hprefix tailTrace_3009624
  have hstable : (prefixWord ++ tailWord_3009624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009624).length < 2 ^ (prefixWord ++ tailWord_3009624).sum := by decide
  have hdescent : baseEnd_3009624 < baseStart_3009624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009641 : List Nat := [1, 2, 1, 1, 1, 6, 3, 2, 1, 1, 4]
def baseStart_3009641 : Nat := 118140960795 + 3009641 * 2 ^ 59
def prefixEnd_3009641 : Nat := 4983230072969 + 3 ^ 40 * 3009641 * 2
def baseEnd_3009641 : Nat := 1545392430478364499446419

theorem tailTrace_3009641 : CollatzResearch.WordTrace tailWord_3009641 prefixEnd_3009641 1545392430478364499446419 := by
  unfold tailWord_3009641
  simp only [CollatzResearch.WordTrace]
  refine ⟨109770625289592137605820777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73180416859728091737213851 109770625289592137605820777)
  ·
    refine ⟨82327968967194103204365583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109770625289592137605820777 82327968967194103204365583)
    ·
      refine ⟨123491953450791154806548375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82327968967194103204365583 123491953450791154806548375)
      ·
        refine ⟨185237930176186732209822563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123491953450791154806548375 185237930176186732209822563)
        ·
          refine ⟨277856895264280098314733845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185237930176186732209822563 277856895264280098314733845)
          ·
            refine ⟨13024541965513129608503149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 277856895264280098314733845 13024541965513129608503149)
            ·
              refine ⟨4884203237067423603188681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13024541965513129608503149 4884203237067423603188681)
              ·
                refine ⟨3663152427800567702391511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4884203237067423603188681 3663152427800567702391511)
                ·
                  refine ⟨5494728641700851553587267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3663152427800567702391511 5494728641700851553587267)
                  ·
                    refine ⟨8242092962551277330380901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5494728641700851553587267 8242092962551277330380901)
                    ·
                      refine ⟨1545392430478364499446419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8242092962551277330380901 1545392430478364499446419)
                      ·
                        rfl

theorem cell23_3009641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 1, 4].length) (baseStart_3009641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009641 prefixEnd_3009641 := by exact prefixLift 3009641
  have htrace : WordTrace (prefixWord ++ tailWord_3009641) baseStart_3009641 baseEnd_3009641 := by
    simpa [prefixWord, tailWord_3009641, baseEnd_3009641] using wordTrace_append hprefix tailTrace_3009641
  have hstable : (prefixWord ++ tailWord_3009641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009641).length < 2 ^ (prefixWord ++ tailWord_3009641).sum := by decide
  have hdescent : baseEnd_3009641 < baseStart_3009641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009647 : List Nat := [1, 1, 2, 1, 3, 3, 1, 11]
def baseStart_3009647 : Nat := 118140960795 + 3009647 * 2 ^ 59
def prefixEnd_3009647 : Nat := 4983230072969 + 3 ^ 40 * 3009647 * 2
def baseEnd_3009647 : Nat := 57236870791195980591533

theorem tailTrace_3009647 : CollatzResearch.WordTrace tailWord_3009647 prefixEnd_3009647 57236870791195980591533 := by
  unfold tailWord_3009647
  simp only [CollatzResearch.WordTrace]
  refine ⟨109770844127570400630539195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73180562751713600420359463 109770844127570400630539195)
  ·
    refine ⟨164656266191355600945808793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109770844127570400630539195 164656266191355600945808793)
    ·
      refine ⟨123492199643516700709356595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164656266191355600945808793 123492199643516700709356595)
      ·
        refine ⟨185238299465275051064034893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123492199643516700709356595 185238299465275051064034893)
        ·
          refine ⟨69464362299478144149013085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185238299465275051064034893 69464362299478144149013085)
          ·
            refine ⟨26049135862304304055879907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69464362299478144149013085 26049135862304304055879907)
            ·
              refine ⟨39073703793456456083819861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26049135862304304055879907 39073703793456456083819861)
              ·
                refine ⟨57236870791195980591533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 39073703793456456083819861 57236870791195980591533)
                ·
                  rfl

theorem cell23_3009647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 11].length) (baseStart_3009647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009647 prefixEnd_3009647 := by exact prefixLift 3009647
  have htrace : WordTrace (prefixWord ++ tailWord_3009647) baseStart_3009647 baseEnd_3009647 := by
    simpa [prefixWord, tailWord_3009647, baseEnd_3009647] using wordTrace_append hprefix tailTrace_3009647
  have hstable : (prefixWord ++ tailWord_3009647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009647).length < 2 ^ (prefixWord ++ tailWord_3009647).sum := by decide
  have hdescent : baseEnd_3009647 < baseStart_3009647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009668 : List Nat := [2, 3, 2, 1, 2, 3, 2, 2, 2, 4]
def baseStart_3009668 : Nat := 118140960795 + 3009668 * 2 ^ 59
def prefixEnd_3009668 : Nat := 4983230072969 + 3 ^ 40 * 3009668 * 2
def baseEnd_3009668 : Nat := 515135431485345297936265

theorem tailTrace_3009668 : CollatzResearch.WordTrace tailWord_3009668 prefixEnd_3009668 515135431485345297936265 := by
  unfold tailWord_3009668
  simp only [CollatzResearch.WordTrace]
  refine ⟨54885805030247160608526829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73181073373662880811369105 54885805030247160608526829)
  ·
    refine ⟨20582176886342685228197561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54885805030247160608526829 20582176886342685228197561)
    ·
      refine ⟨15436632664757013921148171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20582176886342685228197561 15436632664757013921148171)
      ·
        refine ⟨23154948997135520881722257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15436632664757013921148171 23154948997135520881722257)
        ·
          refine ⟨17366211747851640661291693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23154948997135520881722257 17366211747851640661291693)
          ·
            refine ⟨6512329405444365247984385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17366211747851640661291693 6512329405444365247984385)
            ·
              refine ⟨4884247054083273935988289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6512329405444365247984385 4884247054083273935988289)
              ·
                refine ⟨3663185290562455451991217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4884247054083273935988289 3663185290562455451991217)
                ·
                  refine ⟨2747388967921841588993413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3663185290562455451991217 2747388967921841588993413)
                  ·
                    refine ⟨515135431485345297936265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2747388967921841588993413 515135431485345297936265)
                    ·
                      rfl

theorem cell23_3009668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_3009668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009668 prefixEnd_3009668 := by exact prefixLift 3009668
  have htrace : WordTrace (prefixWord ++ tailWord_3009668) baseStart_3009668 baseEnd_3009668 := by
    simpa [prefixWord, tailWord_3009668, baseEnd_3009668] using wordTrace_append hprefix tailTrace_3009668
  have hstable : (prefixWord ++ tailWord_3009668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009668).length < 2 ^ (prefixWord ++ tailWord_3009668).sum := by decide
  have hdescent : baseEnd_3009668 < baseStart_3009668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009669 : List Nat := [1, 3, 1, 1, 7, 1, 2, 2, 1, 1, 3]
def baseStart_3009669 : Nat := 118140960795 + 3009669 * 2 ^ 59
def prefixEnd_3009669 : Nat := 4983230072969 + 3 ^ 40 * 3009669 * 2
def baseEnd_3009669 : Nat := 1545406807936690389896291

theorem tailTrace_3009669 : CollatzResearch.WordTrace tailWord_3009669 prefixEnd_3009669 1545406807936690389896291 := by
  unfold tailWord_3009669
  simp only [CollatzResearch.WordTrace]
  refine ⟨109771646533490698387840061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73181097688993798925226707 109771646533490698387840061)
  ·
    refine ⟨41164367450059011895440023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109771646533490698387840061 41164367450059011895440023)
    ·
      refine ⟨61746551175088517843160035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41164367450059011895440023 61746551175088517843160035)
      ·
        refine ⟨92619826762632776764740053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61746551175088517843160035 92619826762632776764740053)
        ·
          refine ⟨2170777189749205705423595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 92619826762632776764740053 2170777189749205705423595)
          ·
            refine ⟨3256165784623808558135393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2170777189749205705423595 3256165784623808558135393)
            ·
              refine ⟨2442124338467856418601545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3256165784623808558135393 2442124338467856418601545)
              ·
                refine ⟨1831593253850892313951159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2442124338467856418601545 1831593253850892313951159)
                ·
                  refine ⟨2747389880776338470926739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1831593253850892313951159 2747389880776338470926739)
                  ·
                    refine ⟨4121084821164507706390109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2747389880776338470926739 4121084821164507706390109)
                    ·
                      refine ⟨1545406807936690389896291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4121084821164507706390109 1545406807936690389896291)
                      ·
                        rfl

theorem cell23_3009669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2, 1, 1, 3].length) (baseStart_3009669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009669 prefixEnd_3009669 := by exact prefixLift 3009669
  have htrace : WordTrace (prefixWord ++ tailWord_3009669) baseStart_3009669 baseEnd_3009669 := by
    simpa [prefixWord, tailWord_3009669, baseEnd_3009669] using wordTrace_append hprefix tailTrace_3009669
  have hstable : (prefixWord ++ tailWord_3009669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009669).length < 2 ^ (prefixWord ++ tailWord_3009669).sum := by decide
  have hdescent : baseEnd_3009669 < baseStart_3009669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009698 : List Nat := [3, 3, 1, 3, 2, 1, 3, 7]
def baseStart_3009698 : Nat := 118140960795 + 3009698 * 2 ^ 59
def prefixEnd_3009698 : Nat := 4983230072969 + 3 ^ 40 * 3009698 * 2
def baseEnd_3009698 : Nat := 57237840699098917645691

theorem tailTrace_3009698 : CollatzResearch.WordTrace tailWord_3009698 prefixEnd_3009698 57237840699098917645691 := by
  unfold tailWord_3009698
  simp only [CollatzResearch.WordTrace]
  refine ⟨27443176062596409085161437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73181802833590424227097165 27443176062596409085161437)
  ·
    refine ⟨10291191023473653406935539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27443176062596409085161437 10291191023473653406935539)
    ·
      refine ⟨15436786535210480110403309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10291191023473653406935539 15436786535210480110403309)
      ·
        refine ⟨5788794950703930041401241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15436786535210480110403309 5788794950703930041401241)
        ·
          refine ⟨4341596213027947531050931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5788794950703930041401241 4341596213027947531050931)
          ·
            refine ⟨6512394319541921296576397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4341596213027947531050931 6512394319541921296576397)
            ·
              refine ⟨2442147869828220486216149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6512394319541921296576397 2442147869828220486216149)
              ·
                refine ⟨57237840699098917645691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2442147869828220486216149 57237840699098917645691)
                ·
                  rfl

theorem cell23_3009698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 7].length) (baseStart_3009698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009698 prefixEnd_3009698 := by exact prefixLift 3009698
  have htrace : WordTrace (prefixWord ++ tailWord_3009698) baseStart_3009698 baseEnd_3009698 := by
    simpa [prefixWord, tailWord_3009698, baseEnd_3009698] using wordTrace_append hprefix tailTrace_3009698
  have hstable : (prefixWord ++ tailWord_3009698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009698).length < 2 ^ (prefixWord ++ tailWord_3009698).sum := by decide
  have hdescent : baseEnd_3009698 < baseStart_3009698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009709 : List Nat := [1, 5, 2, 1, 3, 1, 2, 3, 1, 2, 2]
def baseStart_3009709 : Nat := 118140960795 + 3009709 * 2 ^ 59
def prefixEnd_3009709 : Nat := 4983230072969 + 3 ^ 40 * 3009709 * 2
def baseEnd_3009709 : Nat := 1545427347162870233396107

theorem tailTrace_3009709 : CollatzResearch.WordTrace tailWord_3009709 prefixEnd_3009709 1545427347162870233396107 := by
  unfold tailWord_3009709
  simp only [CollatzResearch.WordTrace]
  refine ⟨109773105453345785219296181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73182070302230523479530787 109773105453345785219296181)
  ·
    refine ⟨10291228636251167364309017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109773105453345785219296181 10291228636251167364309017)
    ·
      refine ⟨7718421477188375523231763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10291228636251167364309017 7718421477188375523231763)
      ·
        refine ⟨11577632215782563284847645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7718421477188375523231763 11577632215782563284847645)
        ·
          refine ⟨4341612080918461231817867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11577632215782563284847645 4341612080918461231817867)
          ·
            refine ⟨6512418121377691847726801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4341612080918461231817867 6512418121377691847726801)
            ·
              refine ⟨4884313591033268885795101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6512418121377691847726801 4884313591033268885795101)
              ·
                refine ⟨1831617596637475832173163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4884313591033268885795101 1831617596637475832173163)
                ·
                  refine ⟨2747426394956213748259745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1831617596637475832173163 2747426394956213748259745)
                  ·
                    refine ⟨2060569796217160311194809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2747426394956213748259745 2060569796217160311194809)
                    ·
                      refine ⟨1545427347162870233396107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2060569796217160311194809 1545427347162870233396107)
                      ·
                        rfl

theorem cell23_3009709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_3009709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009709 prefixEnd_3009709 := by exact prefixLift 3009709
  have htrace : WordTrace (prefixWord ++ tailWord_3009709) baseStart_3009709 baseEnd_3009709 := by
    simpa [prefixWord, tailWord_3009709, baseEnd_3009709] using wordTrace_append hprefix tailTrace_3009709
  have hstable : (prefixWord ++ tailWord_3009709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009709).length < 2 ^ (prefixWord ++ tailWord_3009709).sum := by decide
  have hdescent : baseEnd_3009709 < baseStart_3009709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009742 : List Nat := [4, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3]
def baseStart_3009742 : Nat := 118140960795 + 3009742 * 2 ^ 59
def prefixEnd_3009742 : Nat := 4983230072969 + 3 ^ 40 * 3009742 * 2
def baseEnd_3009742 : Nat := 1545444292024468604283455

theorem tailTrace_3009742 : CollatzResearch.WordTrace tailWord_3009742 prefixEnd_3009742 1545444292024468604283455 := by
  unfold tailWord_3009742
  simp only [CollatzResearch.WordTrace]
  refine ⟨13721788632778278981905935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73182872708150821236831653 13721788632778278981905935)
  ·
    refine ⟨20582682949167418472858903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13721788632778278981905935 20582682949167418472858903)
    ·
      refine ⟨30874024423751127709288355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20582682949167418472858903 30874024423751127709288355)
      ·
        refine ⟨46311036635626691563932533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30874024423751127709288355 46311036635626691563932533)
        ·
          refine ⟨4341659684590002334118675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46311036635626691563932533 4341659684590002334118675)
          ·
            refine ⟨6512489526885003501178013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4341659684590002334118675 6512489526885003501178013)
            ·
              refine ⟨2442183572581876312941755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6512489526885003501178013 2442183572581876312941755)
              ·
                refine ⟨3663275358872814469412633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2442183572581876312941755 3663275358872814469412633)
                ·
                  refine ⟨2747456519154610852059475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3663275358872814469412633 2747456519154610852059475)
                  ·
                    refine ⟨4121184778731916278089213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2747456519154610852059475 4121184778731916278089213)
                    ·
                      refine ⟨1545444292024468604283455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4121184778731916278089213 1545444292024468604283455)
                      ·
                        rfl

theorem cell23_3009742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3].length) (baseStart_3009742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009742 prefixEnd_3009742 := by exact prefixLift 3009742
  have htrace : WordTrace (prefixWord ++ tailWord_3009742) baseStart_3009742 baseEnd_3009742 := by
    simpa [prefixWord, tailWord_3009742, baseEnd_3009742] using wordTrace_append hprefix tailTrace_3009742
  have hstable : (prefixWord ++ tailWord_3009742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009742).length < 2 ^ (prefixWord ++ tailWord_3009742).sum := by decide
  have hdescent : baseEnd_3009742 < baseStart_3009742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009788 : List Nat := [2, 2, 2, 1, 5, 2, 1, 1, 7]
def baseStart_3009788 : Nat := 118140960795 + 3009788 * 2 ^ 59
def prefixEnd_3009788 : Nat := 4983230072969 + 3 ^ 40 * 3009788 * 2
def baseEnd_3009788 : Nat := 171718656903841713812027

theorem tailTrace_3009788 : CollatzResearch.WordTrace tailWord_3009788 prefixEnd_3009788 171718656903841713812027 := by
  unfold tailWord_3009788
  simp only [CollatzResearch.WordTrace]
  refine ⟨54887993410029790855711009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73183991213373054474281345 54887993410029790855711009)
  ·
    refine ⟨41165995057522343141783257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54887993410029790855711009 41165995057522343141783257)
    ·
      refine ⟨30874496293141757356337443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41165995057522343141783257 30874496293141757356337443)
      ·
        refine ⟨46311744439712636034506165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30874496293141757356337443 46311744439712636034506165)
        ·
          refine ⟨4341726041223059628234953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46311744439712636034506165 4341726041223059628234953)
          ·
            refine ⟨3256294530917294721176215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4341726041223059628234953 3256294530917294721176215)
            ·
              refine ⟨4884441796375942081764323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3256294530917294721176215 4884441796375942081764323)
              ·
                refine ⟨7326662694563913122646485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4884441796375942081764323 7326662694563913122646485)
                ·
                  refine ⟨171718656903841713812027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7326662694563913122646485 171718656903841713812027)
                  ·
                    rfl

theorem cell23_3009788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 7].length) (baseStart_3009788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009788 prefixEnd_3009788 := by exact prefixLift 3009788
  have htrace : WordTrace (prefixWord ++ tailWord_3009788) baseStart_3009788 baseEnd_3009788 := by
    simpa [prefixWord, tailWord_3009788, baseEnd_3009788] using wordTrace_append hprefix tailTrace_3009788
  have hstable : (prefixWord ++ tailWord_3009788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009788).length < 2 ^ (prefixWord ++ tailWord_3009788).sum := by decide
  have hdescent : baseEnd_3009788 < baseStart_3009788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009818 : List Nat := [3, 1, 1, 3, 3, 2, 2, 1, 2, 5]
def baseStart_3009818 : Nat := 118140960795 + 3009818 * 2 ^ 59
def prefixEnd_3009818 : Nat := 4983230072969 + 3 ^ 40 * 3009818 * 2
def baseEnd_3009818 : Nat := 515161105518070102311035

theorem tailTrace_3009818 : CollatzResearch.WordTrace tailWord_3009818 prefixEnd_3009818 515161105518070102311035 := by
  unfold tailWord_3009818
  simp only [CollatzResearch.WordTrace]
  refine ⟨27444270252487724208753527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73184720673300597890009405 27444270252487724208753527)
  ·
    refine ⟨41166405378731586313130291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27444270252487724208753527 41166405378731586313130291)
    ·
      refine ⟨61749608068097379469695437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41166405378731586313130291 61749608068097379469695437)
      ·
        refine ⟨23156103025536517301135789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61749608068097379469695437 23156103025536517301135789)
        ·
          refine ⟨8683538634576193987925921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23156103025536517301135789 8683538634576193987925921)
          ·
            refine ⟨6512653975932145490944441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8683538634576193987925921 6512653975932145490944441)
            ·
              refine ⟨4884490481949109118208331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6512653975932145490944441 4884490481949109118208331)
              ·
                refine ⟨7326735722923663677312497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4884490481949109118208331 7326735722923663677312497)
                ·
                  refine ⟨5495051792192747757984373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7326735722923663677312497 5495051792192747757984373)
                  ·
                    refine ⟨515161105518070102311035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5495051792192747757984373 515161105518070102311035)
                    ·
                      rfl

theorem cell23_3009818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 2, 5].length) (baseStart_3009818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009818 prefixEnd_3009818 := by exact prefixLift 3009818
  have htrace : WordTrace (prefixWord ++ tailWord_3009818) baseStart_3009818 baseEnd_3009818 := by
    simpa [prefixWord, tailWord_3009818, baseEnd_3009818] using wordTrace_append hprefix tailTrace_3009818
  have hstable : (prefixWord ++ tailWord_3009818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009818).length < 2 ^ (prefixWord ++ tailWord_3009818).sum := by decide
  have hdescent : baseEnd_3009818 < baseStart_3009818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009869 : List Nat := [1, 6, 1, 3, 2, 1, 1, 1, 2, 5]
def baseStart_3009869 : Nat := 118140960795 + 3009869 * 2 ^ 59
def prefixEnd_3009869 : Nat := 4983230072969 + 3 ^ 40 * 3009869 * 2
def baseEnd_3009869 : Nat := 515169834689196535798457

theorem tailTrace_3009869 : CollatzResearch.WordTrace tailWord_3009869 prefixEnd_3009869 515169834689196535798457 := by
  unfold tailWord_3009869
  simp only [CollatzResearch.WordTrace]
  refine ⟨109778941132766132545120661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73185960755177421696747107 109778941132766132545120661)
  ·
    refine ⟨5145887865598412463052531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 109778941132766132545120661 5145887865598412463052531)
    ·
      refine ⟨7718831798397618694578797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5145887865598412463052531 7718831798397618694578797)
      ·
        refine ⟨2894561924399107010467049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7718831798397618694578797 2894561924399107010467049)
        ·
          refine ⟨2170921443299330257850287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2894561924399107010467049 2170921443299330257850287)
          ·
            refine ⟨3256382164948995386775431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2170921443299330257850287 3256382164948995386775431)
            ·
              refine ⟨4884573247423493080163147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3256382164948995386775431 4884573247423493080163147)
              ·
                refine ⟨7326859871135239620244721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4884573247423493080163147 7326859871135239620244721)
                ·
                  refine ⟨5495144903351429715183541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7326859871135239620244721 5495144903351429715183541)
                  ·
                    refine ⟨515169834689196535798457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5495144903351429715183541 515169834689196535798457)
                    ·
                      rfl

theorem cell23_3009869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_3009869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009869 prefixEnd_3009869 := by exact prefixLift 3009869
  have htrace : WordTrace (prefixWord ++ tailWord_3009869) baseStart_3009869 baseEnd_3009869 := by
    simpa [prefixWord, tailWord_3009869, baseEnd_3009869] using wordTrace_append hprefix tailTrace_3009869
  have hstable : (prefixWord ++ tailWord_3009869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009869).length < 2 ^ (prefixWord ++ tailWord_3009869).sum := by decide
  have hdescent : baseEnd_3009869 < baseStart_3009869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009895 : List Nat := [1, 1, 5, 1, 4, 2, 1, 2, 6]
def baseStart_3009895 : Nat := 118140960795 + 3009895 * 2 ^ 59
def prefixEnd_3009895 : Nat := 4983230072969 + 3 ^ 40 * 3009895 * 2
def baseEnd_3009895 : Nat := 171724761618289611741139

theorem tailTrace_3009895 : CollatzResearch.WordTrace tailWord_3009895 prefixEnd_3009895 171724761618289611741139 := by
  unfold tailWord_3009895
  simp only [CollatzResearch.WordTrace]
  refine ⟨109779889430671938985567139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73186592953781292657044759 109779889430671938985567139)
  ·
    refine ⟨164669834146007908478350709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109779889430671938985567139 164669834146007908478350709)
    ·
      refine ⟨15437796951188241419845379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164669834146007908478350709 15437796951188241419845379)
      ·
        refine ⟨23156695426782362129768069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15437796951188241419845379 23156695426782362129768069)
        ·
          refine ⟨4341880392521692899331513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23156695426782362129768069 4341880392521692899331513)
          ·
            refine ⟨3256410294391269674498635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4341880392521692899331513 3256410294391269674498635)
            ·
              refine ⟨4884615441586904511747953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3256410294391269674498635 4884615441586904511747953)
              ·
                refine ⟨3663461581190178383810965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4884615441586904511747953 3663461581190178383810965)
                ·
                  refine ⟨171724761618289611741139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3663461581190178383810965 171724761618289611741139)
                  ·
                    rfl

theorem cell23_3009895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 6].length) (baseStart_3009895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009895 prefixEnd_3009895 := by exact prefixLift 3009895
  have htrace : WordTrace (prefixWord ++ tailWord_3009895) baseStart_3009895 baseEnd_3009895 := by
    simpa [prefixWord, tailWord_3009895, baseEnd_3009895] using wordTrace_append hprefix tailTrace_3009895
  have hstable : (prefixWord ++ tailWord_3009895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009895).length < 2 ^ (prefixWord ++ tailWord_3009895).sum := by decide
  have hdescent : baseEnd_3009895 < baseStart_3009895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009931 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 5]
def baseStart_3009931 : Nat := 118140960795 + 3009931 * 2 ^ 59
def prefixEnd_3009931 : Nat := 4983230072969 + 3 ^ 40 * 3009931 * 2
def baseEnd_3009931 : Nat := 1545541339868168364820085

theorem tailTrace_3009931 : CollatzResearch.WordTrace tailWord_3009931 prefixEnd_3009931 1545541339868168364820085 := by
  unfold tailWord_3009931
  simp only [CollatzResearch.WordTrace]
  refine ⟨109781202458541517133877647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73187468305694344755918431 109781202458541517133877647)
  ·
    refine ⟨164671803687812275700816471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109781202458541517133877647 164671803687812275700816471)
    ·
      refine ⟨247007705531718413551224707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164671803687812275700816471 247007705531718413551224707)
      ·
        refine ⟨370511558297577620326837061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247007705531718413551224707 370511558297577620326837061)
        ·
          refine ⟨69470917180795803811281949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 370511558297577620326837061 69470917180795803811281949)
          ·
            refine ⟨26051593942798426429230731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69470917180795803811281949 26051593942798426429230731)
            ·
              refine ⟨39077390914197639643846097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26051593942798426429230731 39077390914197639643846097)
              ·
                refine ⟨29308043185648229732884573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39077390914197639643846097 29308043185648229732884573)
                ·
                  refine ⟨10990516194618086149831715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29308043185648229732884573 10990516194618086149831715)
                  ·
                    refine ⟨16485774291927129224747573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10990516194618086149831715 16485774291927129224747573)
                    ·
                      refine ⟨1545541339868168364820085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16485774291927129224747573 1545541339868168364820085)
                      ·
                        rfl

theorem cell23_3009931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 5].length) (baseStart_3009931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009931 prefixEnd_3009931 := by exact prefixLift 3009931
  have htrace : WordTrace (prefixWord ++ tailWord_3009931) baseStart_3009931 baseEnd_3009931 := by
    simpa [prefixWord, tailWord_3009931, baseEnd_3009931] using wordTrace_append hprefix tailTrace_3009931
  have hstable : (prefixWord ++ tailWord_3009931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009931).length < 2 ^ (prefixWord ++ tailWord_3009931).sum := by decide
  have hdescent : baseEnd_3009931 < baseStart_3009931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009951 : List Nat := [1, 1, 2, 5, 1, 2, 11]
def baseStart_3009951 : Nat := 118140960795 + 3009951 * 2 ^ 59
def prefixEnd_3009951 : Nat := 4983230072969 + 3 ^ 40 * 3009951 * 2
def baseEnd_3009951 : Nat := 19080884067669855389753

theorem tailTrace_3009951 : CollatzResearch.WordTrace tailWord_3009951 prefixEnd_3009951 19080884067669855389753 := by
  unfold tailWord_3009951
  simp only [CollatzResearch.WordTrace]
  refine ⟨109781931918469060549605707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73187954612312707033070471 109781931918469060549605707)
  ·
    refine ⟨164672897877703590824408561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109781931918469060549605707 164672897877703590824408561)
    ·
      refine ⟨123504673408277693118306421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164672897877703590824408561 123504673408277693118306421)
      ·
        refine ⟨11578563132026033729841227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123504673408277693118306421 11578563132026033729841227)
        ·
          refine ⟨17367844698039050594761841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11578563132026033729841227 17367844698039050594761841)
          ·
            refine ⟨13025883523529287946071381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17367844698039050594761841 13025883523529287946071381)
            ·
              refine ⟨19080884067669855389753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 13025883523529287946071381 19080884067669855389753)
              ·
                rfl

theorem cell23_3009951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 11].length) (baseStart_3009951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009951 prefixEnd_3009951 := by exact prefixLift 3009951
  have htrace : WordTrace (prefixWord ++ tailWord_3009951) baseStart_3009951 baseEnd_3009951 := by
    simpa [prefixWord, tailWord_3009951, baseEnd_3009951] using wordTrace_append hprefix tailTrace_3009951
  have hstable : (prefixWord ++ tailWord_3009951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009951).length < 2 ^ (prefixWord ++ tailWord_3009951).sum := by decide
  have hdescent : baseEnd_3009951 < baseStart_3009951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3009965 : List Nat := [1, 5, 2, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_3009965 : Nat := 118140960795 + 3009965 * 2 ^ 59
def prefixEnd_3009965 : Nat := 4983230072969 + 3 ^ 40 * 3009965 * 2
def baseEnd_3009965 : Nat := 1545558798210421231794929

theorem tailTrace_3009965 : CollatzResearch.WordTrace tailWord_3009965 prefixEnd_3009965 1545558798210421231794929 := by
  unfold tailWord_3009965
  simp only [CollatzResearch.WordTrace]
  refine ⟨109782442540418340940615349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73188295026945560627076899 109782442540418340940615349)
  ·
    refine ⟨10292103988164219463182689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109782442540418340940615349 10292103988164219463182689)
    ·
      refine ⟨7719077991123164597387017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10292103988164219463182689 7719077991123164597387017)
      ·
        refine ⟨5789308493342373448040263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7719077991123164597387017 5789308493342373448040263)
        ·
          refine ⟨8683962740013560172060395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5789308493342373448040263 8683962740013560172060395)
          ·
            refine ⟨13025944110020340258090593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8683962740013560172060395 13025944110020340258090593)
            ·
              refine ⟨9769458082515255193567945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13025944110020340258090593 9769458082515255193567945)
              ·
                refine ⟨7327093561886441395175959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9769458082515255193567945 7327093561886441395175959)
                ·
                  refine ⟨10990640342829662092763939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7327093561886441395175959 10990640342829662092763939)
                  ·
                    refine ⟨16485960514244493139145909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10990640342829662092763939 16485960514244493139145909)
                    ·
                      refine ⟨1545558798210421231794929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16485960514244493139145909 1545558798210421231794929)
                      ·
                        rfl

theorem cell23_3009965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_3009965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3009965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3009965 prefixEnd_3009965 := by exact prefixLift 3009965
  have htrace : WordTrace (prefixWord ++ tailWord_3009965) baseStart_3009965 baseEnd_3009965 := by
    simpa [prefixWord, tailWord_3009965, baseEnd_3009965] using wordTrace_append hprefix tailTrace_3009965
  have hstable : (prefixWord ++ tailWord_3009965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3009965).length < 2 ^ (prefixWord ++ tailWord_3009965).sum := by decide
  have hdescent : baseEnd_3009965 < baseStart_3009965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3009965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010011 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 8, 6]
def baseStart_3010011 : Nat := 118140960795 + 3010011 * 2 ^ 59
def prefixEnd_3010011 : Nat := 4983230072969 + 3 ^ 40 * 3010011 * 2
def baseEnd_3010011 : Nat := 515194139440176017273239

theorem tailTrace_3010011 : CollatzResearch.WordTrace tailWord_3010011 prefixEnd_3010011 515194139440176017273239 := by
  unfold tailWord_3010011
  simp only [CollatzResearch.WordTrace]
  refine ⟨109784120298251690796789887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73189413532167793864526591 109784120298251690796789887)
  ·
    refine ⟨164676180447377536195184831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109784120298251690796789887 164676180447377536195184831)
    ·
      refine ⟨247014270671066304292777247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164676180447377536195184831 247014270671066304292777247)
      ·
        refine ⟨370521406006599456439165871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247014270671066304292777247 370521406006599456439165871)
        ·
          refine ⟨555782109009899184658748807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370521406006599456439165871 555782109009899184658748807)
          ·
            refine ⟨833673163514848776988123211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555782109009899184658748807 833673163514848776988123211)
            ·
              refine ⟨1250509745272273165482184817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 833673163514848776988123211 1250509745272273165482184817)
              ·
                refine ⟨937882308954204874111638613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1250509745272273165482184817 937882308954204874111638613)
                ·
                  refine ⟨10990808308057088368495765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 937882308954204874111638613 10990808308057088368495765)
                  ·
                    refine ⟨515194139440176017273239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10990808308057088368495765 515194139440176017273239)
                    ·
                      rfl

theorem cell23_3010011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 6].length) (baseStart_3010011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010011 prefixEnd_3010011 := by exact prefixLift 3010011
  have htrace : WordTrace (prefixWord ++ tailWord_3010011) baseStart_3010011 baseEnd_3010011 := by
    simpa [prefixWord, tailWord_3010011, baseEnd_3010011] using wordTrace_append hprefix tailTrace_3010011
  have hstable : (prefixWord ++ tailWord_3010011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010011).length < 2 ^ (prefixWord ++ tailWord_3010011).sum := by decide
  have hdescent : baseEnd_3010011 < baseStart_3010011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010013 : List Nat := [1, 4, 3, 1, 1, 4, 2, 2, 1, 2, 2]
def baseStart_3010013 : Nat := 118140960795 + 3010013 * 2 ^ 59
def prefixEnd_3010013 : Nat := 4983230072969 + 3 ^ 40 * 3010013 * 2
def baseEnd_3010013 : Nat := 1545583445281837043994709

theorem tailTrace_3010013 : CollatzResearch.WordTrace tailWord_3010013 prefixEnd_3010013 1545583445281837043994709 := by
  unfold tailWord_3010013
  simp only [CollatzResearch.WordTrace]
  refine ⟨109784193244244445138362693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73189462162829630092241795 109784193244244445138362693)
  ·
    refine ⟨20584536233295833463443005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109784193244244445138362693 20584536233295833463443005)
    ·
      refine ⟨7719201087485937548791127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20584536233295833463443005 7719201087485937548791127)
      ·
        refine ⟨11578801631228906323186691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7719201087485937548791127 11578801631228906323186691)
        ·
          refine ⟨17368202446843359484780037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11578801631228906323186691 17368202446843359484780037)
          ·
            refine ⟨3256537958783129903396257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17368202446843359484780037 3256537958783129903396257)
            ·
              refine ⟨2442403469087347427547193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3256537958783129903396257 2442403469087347427547193)
              ·
                refine ⟨1831802601815510570660395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2442403469087347427547193 1831802601815510570660395)
                ·
                  refine ⟨2747703902723265855990593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1831802601815510570660395 2747703902723265855990593)
                  ·
                    refine ⟨2060777927042449391992945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2747703902723265855990593 2060777927042449391992945)
                    ·
                      refine ⟨1545583445281837043994709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2060777927042449391992945 1545583445281837043994709)
                      ·
                        rfl

theorem cell23_3010013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_3010013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010013 prefixEnd_3010013 := by exact prefixLift 3010013
  have htrace : WordTrace (prefixWord ++ tailWord_3010013) baseStart_3010013 baseEnd_3010013 := by
    simpa [prefixWord, tailWord_3010013, baseEnd_3010013] using wordTrace_append hprefix tailTrace_3010013
  have hstable : (prefixWord ++ tailWord_3010013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010013).length < 2 ^ (prefixWord ++ tailWord_3010013).sum := by decide
  have hdescent : baseEnd_3010013 < baseStart_3010013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010069 : List Nat := [1, 3, 2, 1, 3, 2, 3, 2, 2, 2, 2]
def baseStart_3010069 : Nat := 118140960795 + 3010069 * 2 ^ 59
def prefixEnd_3010069 : Nat := 4983230072969 + 3 ^ 40 * 3010069 * 2
def baseEnd_3010069 : Nat := 1545612200198488824894451

theorem tailTrace_3010069 : CollatzResearch.WordTrace tailWord_3010069 prefixEnd_3010069 1545612200198488824894451 := by
  unfold tailWord_3010069
  simp only [CollatzResearch.WordTrace]
  refine ⟨109786235732041566702401261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73190823821361044468267507 109786235732041566702401261)
  ·
    refine ⟨41169838399515587513400473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109786235732041566702401261 41169838399515587513400473)
    ·
      refine ⟨30877378799636690635050355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41169838399515587513400473 30877378799636690635050355)
      ·
        refine ⟨46316068199455035952575533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30877378799636690635050355 46316068199455035952575533)
        ·
          refine ⟨17368525574795638482215825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46316068199455035952575533 17368525574795638482215825)
          ·
            refine ⟨13026394181096728861661869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17368525574795638482215825 13026394181096728861661869)
            ·
              refine ⟨4884897817911273323123201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13026394181096728861661869 4884897817911273323123201)
              ·
                refine ⟨3663673363433454992342401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4884897817911273323123201 3663673363433454992342401)
                ·
                  refine ⟨2747755022575091244256801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3663673363433454992342401 2747755022575091244256801)
                  ·
                    refine ⟨2060816266931318433192601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2747755022575091244256801 2060816266931318433192601)
                    ·
                      refine ⟨1545612200198488824894451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2060816266931318433192601 1545612200198488824894451)
                      ·
                        rfl

theorem cell23_3010069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2, 2, 2].length) (baseStart_3010069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010069 prefixEnd_3010069 := by exact prefixLift 3010069
  have htrace : WordTrace (prefixWord ++ tailWord_3010069) baseStart_3010069 baseEnd_3010069 := by
    simpa [prefixWord, tailWord_3010069, baseEnd_3010069] using wordTrace_append hprefix tailTrace_3010069
  have hstable : (prefixWord ++ tailWord_3010069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010069).length < 2 ^ (prefixWord ++ tailWord_3010069).sum := by decide
  have hdescent : baseEnd_3010069 < baseStart_3010069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010098 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5]
def baseStart_3010098 : Nat := 118140960795 + 3010098 * 2 ^ 59
def prefixEnd_3010098 : Nat := 4983230072969 + 3 ^ 40 * 3010098 * 2
def baseEnd_3010098 : Nat := 1545627091137469211431817

theorem tailTrace_3010098 : CollatzResearch.WordTrace tailWord_3010098 prefixEnd_3010098 1545627091137469211431817 := by
  unfold tailWord_3010098
  simp only [CollatzResearch.WordTrace]
  refine ⟨27446823362234126163801737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73191528965957669770137965 27446823362234126163801737)
  ·
    refine ⟨20585117521675594622851303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27446823362234126163801737 20585117521675594622851303)
    ·
      refine ⟨30877676282513391934276955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20585117521675594622851303 30877676282513391934276955)
      ·
        refine ⟨46316514423770087901415433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30877676282513391934276955 46316514423770087901415433)
        ·
          refine ⟨34737385817827565926061575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46316514423770087901415433 34737385817827565926061575)
          ·
            refine ⟨52106078726741348889092363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34737385817827565926061575 52106078726741348889092363)
            ·
              refine ⟨78159118090112023333638545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52106078726741348889092363 78159118090112023333638545)
              ·
                refine ⟨58619338567584017500228909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78159118090112023333638545 58619338567584017500228909)
                ·
                  refine ⟨21982251962844006562585841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58619338567584017500228909 21982251962844006562585841)
                  ·
                    refine ⟨16486688972133004921939381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21982251962844006562585841 16486688972133004921939381)
                    ·
                      refine ⟨1545627091137469211431817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16486688972133004921939381 1545627091137469211431817)
                      ·
                        rfl

theorem cell23_3010098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_3010098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010098 prefixEnd_3010098 := by exact prefixLift 3010098
  have htrace : WordTrace (prefixWord ++ tailWord_3010098) baseStart_3010098 baseEnd_3010098 := by
    simpa [prefixWord, tailWord_3010098, baseEnd_3010098] using wordTrace_append hprefix tailTrace_3010098
  have hstable : (prefixWord ++ tailWord_3010098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010098).length < 2 ^ (prefixWord ++ tailWord_3010098).sum := by decide
  have hdescent : baseEnd_3010098 < baseStart_3010098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010109 : List Nat := [1, 4, 1, 3, 3, 2, 1, 3, 5]
def baseStart_3010109 : Nat := 118140960795 + 3010109 * 2 ^ 59
def prefixEnd_3010109 : Nat := 4983230072969 + 3 ^ 40 * 3010109 * 2
def baseEnd_3010109 : Nat := 171736971047185407599363

theorem tailTrace_3010109 : CollatzResearch.WordTrace tailWord_3010109 prefixEnd_3010109 171736971047185407599363 := by
  unfold tailWord_3010109
  simp only [CollatzResearch.WordTrace]
  refine ⟨109787694651896653533857381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73191796434597769022571587 109787694651896653533857381)
  ·
    refine ⟨20585192747230622537598259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109787694651896653533857381 20585192747230622537598259)
    ·
      refine ⟨30877789120845933806397389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20585192747230622537598259 30877789120845933806397389)
      ·
        refine ⟨11579170920317225177399021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30877789120845933806397389 11579170920317225177399021)
        ·
          refine ⟨4342189095118959441524633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11579170920317225177399021 4342189095118959441524633)
          ·
            refine ⟨3256641821339219581143475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4342189095118959441524633 3256641821339219581143475)
            ·
              refine ⟨4884962732008829371715213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3256641821339219581143475 4884962732008829371715213)
              ·
                refine ⟨1831861024503311014393205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4884962732008829371715213 1831861024503311014393205)
                ·
                  refine ⟨171736971047185407599363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1831861024503311014393205 171736971047185407599363)
                  ·
                    rfl

theorem cell23_3010109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3, 5].length) (baseStart_3010109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010109 prefixEnd_3010109 := by exact prefixLift 3010109
  have htrace : WordTrace (prefixWord ++ tailWord_3010109) baseStart_3010109 baseEnd_3010109 := by
    simpa [prefixWord, tailWord_3010109, baseEnd_3010109] using wordTrace_append hprefix tailTrace_3010109
  have hstable : (prefixWord ++ tailWord_3010109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010109).length < 2 ^ (prefixWord ++ tailWord_3010109).sum := by decide
  have hdescent : baseEnd_3010109 < baseStart_3010109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010138 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6]
def baseStart_3010138 : Nat := 118140960795 + 3010138 * 2 ^ 59
def prefixEnd_3010138 : Nat := 4983230072969 + 3 ^ 40 * 3010138 * 2
def baseEnd_3010138 : Nat := 1545647630363649054931633

theorem tailTrace_3010138 : CollatzResearch.WordTrace tailWord_3010138 prefixEnd_3010138 1545647630363649054931633 := by
  unfold tailWord_3010138
  simp only [CollatzResearch.WordTrace]
  refine ⟨27447188092197897871665767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73192501579194394324442045 27447188092197897871665767)
  ·
    refine ⟨41170782138296846807498651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27447188092197897871665767 41170782138296846807498651)
    ·
      refine ⟨61756173207445270211247977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41170782138296846807498651 61756173207445270211247977)
      ·
        refine ⟨46317129905583952658435983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61756173207445270211247977 46317129905583952658435983)
        ·
          refine ⟨69475694858375928987653975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46317129905583952658435983 69475694858375928987653975)
          ·
            refine ⟨104213542287563893481480963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69475694858375928987653975 104213542287563893481480963)
            ·
              refine ⟨156320313431345840222221445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104213542287563893481480963 156320313431345840222221445)
              ·
                refine ⟨29310058768377345041666521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 156320313431345840222221445 29310058768377345041666521)
                ·
                  refine ⟨21982544076283008781249891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29310058768377345041666521 21982544076283008781249891)
                  ·
                    refine ⟨32973816114424513171874837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21982544076283008781249891 32973816114424513171874837)
                    ·
                      refine ⟨1545647630363649054931633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32973816114424513171874837 1545647630363649054931633)
                      ·
                        rfl

theorem cell23_3010138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_3010138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010138 prefixEnd_3010138 := by exact prefixLift 3010138
  have htrace : WordTrace (prefixWord ++ tailWord_3010138) baseStart_3010138 baseEnd_3010138 := by
    simpa [prefixWord, tailWord_3010138, baseEnd_3010138] using wordTrace_append hprefix tailTrace_3010138
  have hstable : (prefixWord ++ tailWord_3010138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010138).length < 2 ^ (prefixWord ++ tailWord_3010138).sum := by decide
  have hdescent : baseEnd_3010138 < baseStart_3010138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010145 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 4, 2, 3]
def baseStart_3010145 : Nat := 118140960795 + 3010145 * 2 ^ 59
def prefixEnd_3010145 : Nat := 4983230072969 + 3 ^ 40 * 3010145 * 2
def baseEnd_3010145 : Nat := 1545651224728230527544101

theorem tailTrace_3010145 : CollatzResearch.WordTrace tailWord_3010145 prefixEnd_3010145 1545651224728230527544101 := by
  unfold tailWord_3010145
  simp only [CollatzResearch.WordTrace]
  refine ⟨109789007679766231682167889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73192671786510821121445259 109789007679766231682167889)
  ·
    refine ⟨82341755759824673761625917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109789007679766231682167889 82341755759824673761625917)
    ·
      refine ⟨30878158409934252660609719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82341755759824673761625917 30878158409934252660609719)
      ·
        refine ⟨46317237614901378990914579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30878158409934252660609719 46317237614901378990914579)
        ·
          refine ⟨69475856422352068486371869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46317237614901378990914579 69475856422352068486371869)
          ·
            refine ⟨26053446158382025682389451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69475856422352068486371869 26053446158382025682389451)
            ·
              refine ⟨39080169237573038523584177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26053446158382025682389451 39080169237573038523584177)
              ·
                refine ⟨29310126928179778892688133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39080169237573038523584177 29310126928179778892688133)
                ·
                  refine ⟨5495648799033708542379025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29310126928179778892688133 5495648799033708542379025)
                  ·
                    refine ⟨4121736599275281406784269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5495648799033708542379025 4121736599275281406784269)
                    ·
                      refine ⟨1545651224728230527544101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4121736599275281406784269 1545651224728230527544101)
                      ·
                        rfl

theorem cell23_3010145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_3010145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010145 prefixEnd_3010145 := by exact prefixLift 3010145
  have htrace : WordTrace (prefixWord ++ tailWord_3010145) baseStart_3010145 baseEnd_3010145 := by
    simpa [prefixWord, tailWord_3010145, baseEnd_3010145] using wordTrace_append hprefix tailTrace_3010145
  have hstable : (prefixWord ++ tailWord_3010145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010145).length < 2 ^ (prefixWord ++ tailWord_3010145).sum := by decide
  have hdescent : baseEnd_3010145 < baseStart_3010145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010162 : List Nat := [3, 2, 1, 2, 3, 1, 1, 3, 2, 2, 3]
def baseStart_3010162 : Nat := 118140960795 + 3010162 * 2 ^ 59
def prefixEnd_3010162 : Nat := 4983230072969 + 3 ^ 40 * 3010162 * 2
def baseEnd_3010162 : Nat := 1545659953899356961031523

theorem tailTrace_3010162 : CollatzResearch.WordTrace tailWord_3010162 prefixEnd_3010162 1545659953899356961031523 := by
  unfold tailWord_3010162
  simp only [CollatzResearch.WordTrace]
  refine ⟨27447406930176160896384185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73193085147136429057024493 27447406930176160896384185)
  ·
    refine ⟨20585555197632120672288139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27447406930176160896384185 20585555197632120672288139)
    ·
      refine ⟨30878332796448181008432209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20585555197632120672288139 30878332796448181008432209)
      ·
        refine ⟨23158749597336135756324157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30878332796448181008432209 23158749597336135756324157)
        ·
          refine ⟨8684531099001050908621559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23158749597336135756324157 8684531099001050908621559)
          ·
            refine ⟨13026796648501576362932339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8684531099001050908621559 13026796648501576362932339)
            ·
              refine ⟨19540194972752364544398509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13026796648501576362932339 19540194972752364544398509)
              ·
                refine ⟨7327573114782136704149441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19540194972752364544398509 7327573114782136704149441)
                ·
                  refine ⟨5495679836086602528112081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7327573114782136704149441 5495679836086602528112081)
                  ·
                    refine ⟨4121759877064951896084061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5495679836086602528112081 4121759877064951896084061)
                    ·
                      refine ⟨1545659953899356961031523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4121759877064951896084061 1545659953899356961031523)
                      ·
                        rfl

theorem cell23_3010162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_3010162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010162 prefixEnd_3010162 := by exact prefixLift 3010162
  have htrace : WordTrace (prefixWord ++ tailWord_3010162) baseStart_3010162 baseEnd_3010162 := by
    simpa [prefixWord, tailWord_3010162, baseEnd_3010162] using wordTrace_append hprefix tailTrace_3010162
  have hstable : (prefixWord ++ tailWord_3010162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010162).length < 2 ^ (prefixWord ++ tailWord_3010162).sum := by decide
  have hdescent : baseEnd_3010162 < baseStart_3010162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010186 : List Nat := [3, 1, 2, 3, 2, 1, 4, 2, 1, 4]
def baseStart_3010186 : Nat := 118140960795 + 3010186 * 2 ^ 59
def prefixEnd_3010186 : Nat := 4983230072969 + 3 ^ 40 * 3010186 * 2
def baseEnd_3010186 : Nat := 515224092478354955710471

theorem tailTrace_3010186 : CollatzResearch.WordTrace tailWord_3010186 prefixEnd_3010186 515224092478354955710471 := by
  unfold tailWord_3010186
  simp only [CollatzResearch.WordTrace]
  refine ⟨27447625768154423921102603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73193668715078463789606941 27447625768154423921102603)
  ·
    refine ⟨41171438652231635881653905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27447625768154423921102603 41171438652231635881653905)
    ·
      refine ⟨30878578989173726911240429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41171438652231635881653905 30878578989173726911240429)
      ·
        refine ⟨11579467120940147591715161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30878578989173726911240429 11579467120940147591715161)
        ·
          refine ⟨8684600340705110693786371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11579467120940147591715161 8684600340705110693786371)
          ·
            refine ⟨13026900511057666040679557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8684600340705110693786371 13026900511057666040679557)
            ·
              refine ⟨2442543845823312382627417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13026900511057666040679557 2442543845823312382627417)
              ·
                refine ⟨1831907884367484286970563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2442543845823312382627417 1831907884367484286970563)
                ·
                  refine ⟨2747861826551226430455845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1831907884367484286970563 2747861826551226430455845)
                  ·
                    refine ⟨515224092478354955710471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2747861826551226430455845 515224092478354955710471)
                    ·
                      rfl

theorem cell23_3010186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_3010186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010186 prefixEnd_3010186 := by exact prefixLift 3010186
  have htrace : WordTrace (prefixWord ++ tailWord_3010186) baseStart_3010186 baseEnd_3010186 := by
    simpa [prefixWord, tailWord_3010186, baseEnd_3010186] using wordTrace_append hprefix tailTrace_3010186
  have hstable : (prefixWord ++ tailWord_3010186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010186).length < 2 ^ (prefixWord ++ tailWord_3010186).sum := by decide
  have hdescent : baseEnd_3010186 < baseStart_3010186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010209 : List Nat := [1, 2, 3, 3, 2, 2, 1, 2, 3, 1, 3]
def baseStart_3010209 : Nat := 118140960795 + 3010209 * 2 ^ 59
def prefixEnd_3010209 : Nat := 4983230072969 + 3 ^ 40 * 3010209 * 2
def baseEnd_3010209 : Nat := 1545684087490118277143807

theorem tailTrace_3010209 : CollatzResearch.WordTrace tailWord_3010209 prefixEnd_3010209 1545684087490118277143807 := by
  unfold tailWord_3010209
  simp only [CollatzResearch.WordTrace]
  refine ⟨109791341951534370612497681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73194227967689580408331787 109791341951534370612497681)
  ·
    refine ⟨82343506463650777959373261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109791341951534370612497681 82343506463650777959373261)
    ·
      refine ⟨30878814923869041734764973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82343506463650777959373261 30878814923869041734764973)
      ·
        refine ⟨11579555596450890650536865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30878814923869041734764973 11579555596450890650536865)
        ·
          refine ⟨8684666697338167987902649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11579555596450890650536865 8684666697338167987902649)
          ·
            refine ⟨6513500023003625990926987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8684666697338167987902649 6513500023003625990926987)
            ·
              refine ⟨9770250034505438986390481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6513500023003625990926987 9770250034505438986390481)
              ·
                refine ⟨7327687525879079239792861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9770250034505438986390481 7327687525879079239792861)
                ·
                  refine ⟨2747882822204654714922323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7327687525879079239792861 2747882822204654714922323)
                  ·
                    refine ⟨4121824233306982072383485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2747882822204654714922323 4121824233306982072383485)
                    ·
                      refine ⟨1545684087490118277143807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4121824233306982072383485 1545684087490118277143807)
                      ·
                        rfl

theorem cell23_3010209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_3010209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010209 prefixEnd_3010209 := by exact prefixLift 3010209
  have htrace : WordTrace (prefixWord ++ tailWord_3010209) baseStart_3010209 baseEnd_3010209 := by
    simpa [prefixWord, tailWord_3010209, baseEnd_3010209] using wordTrace_append hprefix tailTrace_3010209
  have hstable : (prefixWord ++ tailWord_3010209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010209).length < 2 ^ (prefixWord ++ tailWord_3010209).sum := by decide
  have hdescent : baseEnd_3010209 < baseStart_3010209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010229 : List Nat := [1, 3, 3, 3, 2, 1, 1, 3, 1, 5]
def baseStart_3010229 : Nat := 118140960795 + 3010229 * 2 ^ 59
def prefixEnd_3010229 : Nat := 4983230072969 + 3 ^ 40 * 3010229 * 2
def baseEnd_3010229 : Nat := 515231452367736066297905

theorem tailTrace_3010229 : CollatzResearch.WordTrace tailWord_3010229 prefixEnd_3010229 515231452367736066297905 := by
  unfold tailWord_3010229
  simp only [CollatzResearch.WordTrace]
  refine ⟨109792071411461914028225741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73194714274307942685483827 109792071411461914028225741)
  ·
    refine ⟨41172026779298217760584653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109792071411461914028225741 41172026779298217760584653)
    ·
      refine ⟨15439510042236831660219245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41172026779298217760584653 15439510042236831660219245)
      ·
        refine ⟨5789816265838811872582217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15439510042236831660219245 5789816265838811872582217)
        ·
          refine ⟨4342362199379108904436663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5789816265838811872582217 4342362199379108904436663)
          ·
            refine ⟨6513543299068663356654995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4342362199379108904436663 6513543299068663356654995)
            ·
              refine ⟨9770314948602995034982493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6513543299068663356654995 9770314948602995034982493)
              ·
                refine ⟨3663868105726123138118435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9770314948602995034982493 3663868105726123138118435)
                ·
                  refine ⟨5495802158589184707177653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3663868105726123138118435 5495802158589184707177653)
                  ·
                    refine ⟨515231452367736066297905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5495802158589184707177653 515231452367736066297905)
                    ·
                      rfl

theorem cell23_3010229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_3010229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010229 prefixEnd_3010229 := by exact prefixLift 3010229
  have htrace : WordTrace (prefixWord ++ tailWord_3010229) baseStart_3010229 baseEnd_3010229 := by
    simpa [prefixWord, tailWord_3010229, baseEnd_3010229] using wordTrace_append hprefix tailTrace_3010229
  have hstable : (prefixWord ++ tailWord_3010229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010229).length < 2 ^ (prefixWord ++ tailWord_3010229).sum := by decide
  have hdescent : baseEnd_3010229 < baseStart_3010229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010282 : List Nat := [3, 1, 3, 1, 1, 1, 2, 4, 1, 3, 3]
def baseStart_3010282 : Nat := 118140960795 + 3010282 * 2 ^ 59
def prefixEnd_3010282 : Nat := 4983230072969 + 3 ^ 40 * 3010282 * 2
def baseEnd_3010282 : Nat := 1545721571577896491530971

theorem tailTrace_3010282 : CollatzResearch.WordTrace tailWord_3010282 prefixEnd_3010282 1545721571577896491530971 := by
  unfold tailWord_3010282
  simp only [CollatzResearch.WordTrace]
  refine ⟨27448501120067476019976275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73196002986846602719936733 27448501120067476019976275)
  ·
    refine ⟨41172751680101214029964413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27448501120067476019976275 41172751680101214029964413)
    ·
      refine ⟨15439781880037955261236655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41172751680101214029964413 15439781880037955261236655)
      ·
        refine ⟨23159672820056932891854983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15439781880037955261236655 23159672820056932891854983)
        ·
          refine ⟨34739509230085399337782475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23159672820056932891854983 34739509230085399337782475)
          ·
            refine ⟨52109263845128099006673713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34739509230085399337782475 52109263845128099006673713)
            ·
              refine ⟨39081947883846074255005285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52109263845128099006673713 39081947883846074255005285)
              ·
                refine ⟨7327865228221138922813491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39081947883846074255005285 7327865228221138922813491)
                ·
                  refine ⟨10991797842331708384220237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7327865228221138922813491 10991797842331708384220237)
                  ·
                    refine ⟨4121924190874390644082589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10991797842331708384220237 4121924190874390644082589)
                    ·
                      refine ⟨1545721571577896491530971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4121924190874390644082589 1545721571577896491530971)
                      ·
                        rfl

theorem cell23_3010282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_3010282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010282 prefixEnd_3010282 := by exact prefixLift 3010282
  have htrace : WordTrace (prefixWord ++ tailWord_3010282) baseStart_3010282 baseEnd_3010282 := by
    simpa [prefixWord, tailWord_3010282, baseEnd_3010282] using wordTrace_append hprefix tailTrace_3010282
  have hstable : (prefixWord ++ tailWord_3010282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010282).length < 2 ^ (prefixWord ++ tailWord_3010282).sum := by decide
  have hdescent : baseEnd_3010282 < baseStart_3010282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010315 : List Nat := [1, 1, 1, 1, 5, 1, 2, 3, 2, 6]
def baseStart_3010315 : Nat := 118140960795 + 3010315 * 2 ^ 59
def prefixEnd_3010315 : Nat := 4983230072969 + 3 ^ 40 * 3010315 * 2
def baseEnd_3010315 : Nat := 515246172146498287472773

theorem tailTrace_3010315 : CollatzResearch.WordTrace tailWord_3010315 prefixEnd_3010315 515246172146498287472773 := by
  unfold tailWord_3010315
  simp only [CollatzResearch.WordTrace]
  refine ⟨109795208089150350715856399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73196805392766900477237599 109795208089150350715856399)
  ·
    refine ⟨164692812133725526073784599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109795208089150350715856399 164692812133725526073784599)
    ·
      refine ⟨247039218200588289110676899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164692812133725526073784599 247039218200588289110676899)
      ·
        refine ⟨370558827300882433666015349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247039218200588289110676899 370558827300882433666015349)
        ·
          refine ⟨34739890059457728156188939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 370558827300882433666015349 34739890059457728156188939)
          ·
            refine ⟨52109835089186592234283409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34739890059457728156188939 52109835089186592234283409)
            ·
              refine ⟨39082376316889944175712557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52109835089186592234283409 39082376316889944175712557)
              ·
                refine ⟨14655891118833729065892209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39082376316889944175712557 14655891118833729065892209)
                ·
                  refine ⟨10991918339125296799419157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14655891118833729065892209 10991918339125296799419157)
                  ·
                    refine ⟨515246172146498287472773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10991918339125296799419157 515246172146498287472773)
                    ·
                      rfl

theorem cell23_3010315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 6].length) (baseStart_3010315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010315 prefixEnd_3010315 := by exact prefixLift 3010315
  have htrace : WordTrace (prefixWord ++ tailWord_3010315) baseStart_3010315 baseEnd_3010315 := by
    simpa [prefixWord, tailWord_3010315, baseEnd_3010315] using wordTrace_append hprefix tailTrace_3010315
  have hstable : (prefixWord ++ tailWord_3010315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010315).length < 2 ^ (prefixWord ++ tailWord_3010315).sum := by decide
  have hdescent : baseEnd_3010315 < baseStart_3010315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010316 : List Nat := [2, 2, 1, 2, 2, 1, 6, 1, 2, 1, 3]
def baseStart_3010316 : Nat := 118140960795 + 3010316 * 2 ^ 59
def prefixEnd_3010316 : Nat := 4983230072969 + 3 ^ 40 * 3010316 * 2
def baseEnd_3010316 : Nat := 1545739029920149358505815

theorem tailTrace_3010316 : CollatzResearch.WordTrace tailWord_3010316 prefixEnd_3010316 1545739029920149358505815 := by
  unfold tailWord_3010316
  simp only [CollatzResearch.WordTrace]
  refine ⟨54897622281073363943321401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73196829708097818591095201 54897622281073363943321401)
  ·
    refine ⟨41173216710805022957491051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54897622281073363943321401 41173216710805022957491051)
    ·
      refine ⟨61759825066207534436236577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41173216710805022957491051 61759825066207534436236577)
      ·
        refine ⟨46319868799655650827177433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61759825066207534436236577 46319868799655650827177433)
        ·
          refine ⟨34739901599741738120383075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46319868799655650827177433 34739901599741738120383075)
          ·
            refine ⟨52109852399612607180574613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34739901599741738120383075 52109852399612607180574613)
            ·
              refine ⟨2442649331231840961589435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52109852399612607180574613 2442649331231840961589435)
              ·
                refine ⟨3663973996847761442384153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2442649331231840961589435 3663973996847761442384153)
                ·
                  refine ⟨2747980497635821081788115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3663973996847761442384153 2747980497635821081788115)
                  ·
                    refine ⟨4121970746453731622682173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2747980497635821081788115 4121970746453731622682173)
                    ·
                      refine ⟨1545739029920149358505815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4121970746453731622682173 1545739029920149358505815)
                      ·
                        rfl

theorem cell23_3010316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 2, 1, 3].length) (baseStart_3010316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010316 prefixEnd_3010316 := by exact prefixLift 3010316
  have htrace : WordTrace (prefixWord ++ tailWord_3010316) baseStart_3010316 baseEnd_3010316 := by
    simpa [prefixWord, tailWord_3010316, baseEnd_3010316] using wordTrace_append hprefix tailTrace_3010316
  have hstable : (prefixWord ++ tailWord_3010316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010316).length < 2 ^ (prefixWord ++ tailWord_3010316).sum := by decide
  have hdescent : baseEnd_3010316 < baseStart_3010316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010317 : List Nat := [1, 7, 2, 1, 1, 2, 1, 2, 1, 1, 4]
def baseStart_3010317 : Nat := 118140960795 + 3010317 * 2 ^ 59
def prefixEnd_3010317 : Nat := 4983230072969 + 3 ^ 40 * 3010317 * 2
def baseEnd_3010317 : Nat := 1545739543400803854593311

theorem tailTrace_3010317 : CollatzResearch.WordTrace tailWord_3010317 prefixEnd_3010317 1545739543400803854593311 := by
  unfold tailWord_3010317
  simp only [CollatzResearch.WordTrace]
  refine ⟨109795281035143105057429205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73196854023428736704952803 109795281035143105057429205)
  ·
    refine ⟨2573326899261166524783497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 109795281035143105057429205 2573326899261166524783497)
    ·
      refine ⟨1929995174445874893587623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2573326899261166524783497 1929995174445874893587623)
      ·
        refine ⟨2894992761668812340381435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1929995174445874893587623 2894992761668812340381435)
        ·
          refine ⟨4342489142503218510572153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2894992761668812340381435 4342489142503218510572153)
          ·
            refine ⟨3256866856877413882929115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4342489142503218510572153 3256866856877413882929115)
            ·
              refine ⟨4885300285316120824393673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3256866856877413882929115 4885300285316120824393673)
              ·
                refine ⟨3663975213987090618295255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4885300285316120824393673 3663975213987090618295255)
                ·
                  refine ⟨5495962820980635927442883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3663975213987090618295255 5495962820980635927442883)
                  ·
                    refine ⟨8243944231470953891164325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5495962820980635927442883 8243944231470953891164325)
                    ·
                      refine ⟨1545739543400803854593311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8243944231470953891164325 1545739543400803854593311)
                      ·
                        rfl

theorem cell23_3010317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_3010317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010317 prefixEnd_3010317 := by exact prefixLift 3010317
  have htrace : WordTrace (prefixWord ++ tailWord_3010317) baseStart_3010317 baseEnd_3010317 := by
    simpa [prefixWord, tailWord_3010317, baseEnd_3010317] using wordTrace_append hprefix tailTrace_3010317
  have hstable : (prefixWord ++ tailWord_3010317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010317).length < 2 ^ (prefixWord ++ tailWord_3010317).sum := by decide
  have hdescent : baseEnd_3010317 < baseStart_3010317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010339 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 6, 2, 2]
def baseStart_3010339 : Nat := 118140960795 + 3010339 * 2 ^ 59
def prefixEnd_3010339 : Nat := 4983230072969 + 3 ^ 40 * 3010339 * 2
def baseEnd_3010339 : Nat := 1545750839975202768518209

theorem tailTrace_3010339 : CollatzResearch.WordTrace tailWord_3010339 prefixEnd_3010339 1545750839975202768518209 := by
  unfold tailWord_3010339
  simp only [CollatzResearch.WordTrace]
  refine ⟨109796083441063402814730071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73197388960708935209820047 109796083441063402814730071)
  ·
    refine ⟨164694125161595104222095107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109796083441063402814730071 164694125161595104222095107)
    ·
      refine ⟨247041187742392656333142661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164694125161595104222095107 247041187742392656333142661)
      ·
        refine ⟨46320222701698623062464249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 247041187742392656333142661 46320222701698623062464249)
        ·
          refine ⟨34740167026273967296848187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46320222701698623062464249 34740167026273967296848187)
          ·
            refine ⟨52110250539410950945272281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34740167026273967296848187 52110250539410950945272281)
            ·
              refine ⟨39082687904558213208954211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52110250539410950945272281 39082687904558213208954211)
              ·
                refine ⟨58624031856837319813431317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39082687904558213208954211 58624031856837319813431317)
                ·
                  refine ⟨2748001493289249366254593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58624031856837319813431317 2748001493289249366254593)
                  ·
                    refine ⟨2061001119966937024690945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2748001493289249366254593 2061001119966937024690945)
                    ·
                      refine ⟨1545750839975202768518209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2061001119966937024690945 1545750839975202768518209)
                      ·
                        rfl

theorem cell23_3010339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6, 2, 2].length) (baseStart_3010339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010339 prefixEnd_3010339 := by exact prefixLift 3010339
  have htrace : WordTrace (prefixWord ++ tailWord_3010339) baseStart_3010339 baseEnd_3010339 := by
    simpa [prefixWord, tailWord_3010339, baseEnd_3010339] using wordTrace_append hprefix tailTrace_3010339
  have hstable : (prefixWord ++ tailWord_3010339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010339).length < 2 ^ (prefixWord ++ tailWord_3010339).sum := by decide
  have hdescent : baseEnd_3010339 < baseStart_3010339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010432 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 3]
def baseStart_3010432 : Nat := 118140960795 + 3010432 * 2 ^ 59
def prefixEnd_3010432 : Nat := 4983230072969 + 3 ^ 40 * 3010432 * 2
def baseEnd_3010432 : Nat := 1545798593676070904655281

theorem tailTrace_3010432 : CollatzResearch.WordTrace tailWord_3010432 prefixEnd_3010432 1545798593676070904655281 := by
  unfold tailWord_3010432
  simp only [CollatzResearch.WordTrace]
  refine ⟨54899737714863239848932775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73199650286484319798577033 54899737714863239848932775)
  ·
    refine ⟨82349606572294859773399163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54899737714863239848932775 82349606572294859773399163)
    ·
      refine ⟨123524409858442289660098745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82349606572294859773399163 123524409858442289660098745)
      ·
        refine ⟨92643307393831717245074059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123524409858442289660098745 92643307393831717245074059)
        ·
          refine ⟨138964961090747575867611089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92643307393831717245074059 138964961090747575867611089)
          ·
            refine ⟨104223720818060681900708317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138964961090747575867611089 104223720818060681900708317)
            ·
              refine ⟨39083895306772755712765619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104223720818060681900708317 39083895306772755712765619)
              ·
                refine ⟨58625842960159133569148429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39083895306772755712765619 58625842960159133569148429)
                ·
                  refine ⟨21984691110059675088430661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58625842960159133569148429 21984691110059675088430661)
                  ·
                    refine ⟨4122129583136189079080749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21984691110059675088430661 4122129583136189079080749)
                    ·
                      refine ⟨1545798593676070904655281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4122129583136189079080749 1545798593676070904655281)
                      ·
                        rfl

theorem cell23_3010432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 3].length) (baseStart_3010432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010432 prefixEnd_3010432 := by exact prefixLift 3010432
  have htrace : WordTrace (prefixWord ++ tailWord_3010432) baseStart_3010432 baseEnd_3010432 := by
    simpa [prefixWord, tailWord_3010432, baseEnd_3010432] using wordTrace_append hprefix tailTrace_3010432
  have hstable : (prefixWord ++ tailWord_3010432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010432).length < 2 ^ (prefixWord ++ tailWord_3010432).sum := by decide
  have hdescent : baseEnd_3010432 < baseStart_3010432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010506 : List Nat := [3, 1, 2, 1, 2, 1, 3, 3, 2, 3, 2]
def baseStart_3010506 : Nat := 118140960795 + 3010506 * 2 ^ 59
def prefixEnd_3010506 : Nat := 4983230072969 + 3 ^ 40 * 3010506 * 2
def baseEnd_3010506 : Nat := 1545836591244503615129941

theorem tailTrace_3010506 : CollatzResearch.WordTrace tailWord_3010506 prefixEnd_3010506 1545836591244503615129941 := by
  unfold tailWord_3010506
  simp only [CollatzResearch.WordTrace]
  refine ⟨27450543607864597584014843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73201449620972260224039581 27450543607864597584014843)
  ·
    refine ⟨41175815411796896376022265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27450543607864597584014843 41175815411796896376022265)
    ·
      refine ⟨30881861558847672282016699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41175815411796896376022265 30881861558847672282016699)
      ·
        refine ⟨46322792338271508423025049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30881861558847672282016699 46322792338271508423025049)
        ·
          refine ⟨34742094253703631317268787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46322792338271508423025049 34742094253703631317268787)
          ·
            refine ⟨52113141380555446975903181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34742094253703631317268787 52113141380555446975903181)
            ·
              refine ⟨19542428017708292615963693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52113141380555446975903181 19542428017708292615963693)
              ·
                refine ⟨7328410506640609730986385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19542428017708292615963693 7328410506640609730986385)
                ·
                  refine ⟨5496307879980457298239789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7328410506640609730986385 5496307879980457298239789)
                  ·
                    refine ⟨2061115454992671486839921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5496307879980457298239789 2061115454992671486839921)
                    ·
                      refine ⟨1545836591244503615129941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2061115454992671486839921 1545836591244503615129941)
                      ·
                        rfl

theorem cell23_3010506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 2, 3, 2].length) (baseStart_3010506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010506 prefixEnd_3010506 := by exact prefixLift 3010506
  have htrace : WordTrace (prefixWord ++ tailWord_3010506) baseStart_3010506 baseEnd_3010506 := by
    simpa [prefixWord, tailWord_3010506, baseEnd_3010506] using wordTrace_append hprefix tailTrace_3010506
  have hstable : (prefixWord ++ tailWord_3010506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010506).length < 2 ^ (prefixWord ++ tailWord_3010506).sum := by decide
  have hdescent : baseEnd_3010506 < baseStart_3010506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010512 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 3, 6]
def baseStart_3010512 : Nat := 118140960795 + 3010512 * 2 ^ 59
def prefixEnd_3010512 : Nat := 4983230072969 + 3 ^ 40 * 3010512 * 2
def baseEnd_3010512 : Nat := 515279890709476863884971

theorem tailTrace_3010512 : CollatzResearch.WordTrace tailWord_3010512 prefixEnd_3010512 515279890709476863884971 := by
  unfold tailWord_3010512
  simp only [CollatzResearch.WordTrace]
  refine ⟨54901196634718326680388895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73201595512957768907185193 54901196634718326680388895)
  ·
    refine ⟨82351794952077490020583343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54901196634718326680388895 82351794952077490020583343)
    ·
      refine ⟨123527692428116235030875015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82351794952077490020583343 123527692428116235030875015)
      ·
        refine ⟨185291538642174352546312523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123527692428116235030875015 185291538642174352546312523)
        ·
          refine ⟨277937307963261528819468785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185291538642174352546312523 277937307963261528819468785)
          ·
            refine ⟨208452980972446146614601589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277937307963261528819468785 208452980972446146614601589)
            ·
              refine ⟨19542466966166826245118899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 208452980972446146614601589 19542466966166826245118899)
              ·
                refine ⟨29313700449250239367678349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19542466966166826245118899 29313700449250239367678349)
                ·
                  refine ⟨10992637668468839762879381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29313700449250239367678349 10992637668468839762879381)
                  ·
                    refine ⟨515279890709476863884971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10992637668468839762879381 515279890709476863884971)
                    ·
                      rfl

theorem cell23_3010512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 3, 6].length) (baseStart_3010512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010512 prefixEnd_3010512 := by exact prefixLift 3010512
  have htrace : WordTrace (prefixWord ++ tailWord_3010512) baseStart_3010512 baseEnd_3010512 := by
    simpa [prefixWord, tailWord_3010512, baseEnd_3010512] using wordTrace_append hprefix tailTrace_3010512
  have hstable : (prefixWord ++ tailWord_3010512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010512).length < 2 ^ (prefixWord ++ tailWord_3010512).sum := by decide
  have hdescent : baseEnd_3010512 < baseStart_3010512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010529 : List Nat := [1, 2, 3, 1, 2, 1, 2, 3, 4, 4]
def baseStart_3010529 : Nat := 118140960795 + 3010529 * 2 ^ 59
def prefixEnd_3010529 : Nat := 4983230072969 + 3 ^ 40 * 3010529 * 2
def baseEnd_3010529 : Nat := 515282800433185675047445

theorem tailTrace_3010529 : CollatzResearch.WordTrace tailWord_3010529 prefixEnd_3010529 515282800433185675047445 := by
  unfold tailWord_3010529
  simp only [CollatzResearch.WordTrace]
  refine ⟨109803013310375065264146641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73202008873583376842764427 109803013310375065264146641)
  ·
    refine ⟨82352259982781298948109981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109803013310375065264146641 82352259982781298948109981)
    ·
      refine ⟨30882097493542987105541243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82352259982781298948109981 30882097493542987105541243)
      ·
        refine ⟨46323146240314480658311865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30882097493542987105541243 46323146240314480658311865)
        ·
          refine ⟨34742359680235860493733899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46323146240314480658311865 34742359680235860493733899)
          ·
            refine ⟨52113539520353790740600849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34742359680235860493733899 52113539520353790740600849)
            ·
              refine ⟨39085154640265343055450637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52113539520353790740600849 39085154640265343055450637)
              ·
                refine ⟨14656932990099503645793989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39085154640265343055450637 14656932990099503645793989)
                ·
                  refine ⟨2748174935643656933586373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14656932990099503645793989 2748174935643656933586373)
                  ·
                    refine ⟨515282800433185675047445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2748174935643656933586373 515282800433185675047445)
                    ·
                      rfl

theorem cell23_3010529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_3010529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010529 prefixEnd_3010529 := by exact prefixLift 3010529
  have htrace : WordTrace (prefixWord ++ tailWord_3010529) baseStart_3010529 baseEnd_3010529 := by
    simpa [prefixWord, tailWord_3010529, baseEnd_3010529] using wordTrace_append hprefix tailTrace_3010529
  have hstable : (prefixWord ++ tailWord_3010529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010529).length < 2 ^ (prefixWord ++ tailWord_3010529).sum := by decide
  have hdescent : baseEnd_3010529 < baseStart_3010529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010553 : List Nat := [1, 2, 1, 3, 1, 5, 1, 2, 3, 2, 2]
def baseStart_3010553 : Nat := 118140960795 + 3010553 * 2 ^ 59
def prefixEnd_3010553 : Nat := 4983230072969 + 3 ^ 40 * 3010553 * 2
def baseEnd_3010553 : Nat := 1545860724835264931242225

theorem tailTrace_3010553 : CollatzResearch.WordTrace tailWord_3010553 prefixEnd_3010553 1545860724835264931242225 := by
  unfold tailWord_3010553
  simp only [CollatzResearch.WordTrace]
  refine ⟨109803888662288117363020313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73202592441525411575346875 109803888662288117363020313)
  ·
    refine ⟨82352916496716088022265235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109803888662288117363020313 82352916496716088022265235)
    ·
      refine ⟨123529374745074132033397853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82352916496716088022265235 123529374745074132033397853)
      ·
        refine ⟨46323515529402799512524195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123529374745074132033397853 46323515529402799512524195)
        ·
          refine ⟨69485273294104199268786293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46323515529402799512524195 69485273294104199268786293)
          ·
            refine ⟨6514244371322268681448715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69485273294104199268786293 6514244371322268681448715)
            ·
              refine ⟨9771366556983403022173073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6514244371322268681448715 9771366556983403022173073)
              ·
                refine ⟨7328524917737552266629805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9771366556983403022173073 7328524917737552266629805)
                ·
                  refine ⟨2748196844151582099986177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7328524917737552266629805 2748196844151582099986177)
                  ·
                    refine ⟨2061147633113686574989633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2748196844151582099986177 2061147633113686574989633)
                    ·
                      refine ⟨1545860724835264931242225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2061147633113686574989633 1545860724835264931242225)
                      ·
                        rfl

theorem cell23_3010553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3, 2, 2].length) (baseStart_3010553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010553 prefixEnd_3010553 := by exact prefixLift 3010553
  have htrace : WordTrace (prefixWord ++ tailWord_3010553) baseStart_3010553 baseEnd_3010553 := by
    simpa [prefixWord, tailWord_3010553, baseEnd_3010553] using wordTrace_append hprefix tailTrace_3010553
  have hstable : (prefixWord ++ tailWord_3010553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010553).length < 2 ^ (prefixWord ++ tailWord_3010553).sum := by decide
  have hdescent : baseEnd_3010553 < baseStart_3010553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010556 : List Nat := [2, 2, 2, 1, 2, 2, 2, 4, 1, 2, 3]
def baseStart_3010556 : Nat := 118140960795 + 3010556 * 2 ^ 59
def prefixEnd_3010556 : Nat := 4983230072969 + 3 ^ 40 * 3010556 * 2
def baseEnd_3010556 : Nat := 1545862265277228419504711

theorem tailTrace_3010556 : CollatzResearch.WordTrace tailWord_3010556 prefixEnd_3010556 1545862265277228419504711 := by
  unfold tailWord_3010556
  simp only [CollatzResearch.WordTrace]
  refine ⟨54901999040638624437689761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73202665387518165916919681 54901999040638624437689761)
  ·
    refine ⟨41176499280478968328267321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54901999040638624437689761 41176499280478968328267321)
    ·
      refine ⟨30882374460359226246200491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41176499280478968328267321 30882374460359226246200491)
      ·
        refine ⟨46323561690538839369300737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30882374460359226246200491 46323561690538839369300737)
        ·
          refine ⟨34742671267904129526975553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46323561690538839369300737 34742671267904129526975553)
          ·
            refine ⟨26057003450928097145231665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34742671267904129526975553 26057003450928097145231665)
            ·
              refine ⟨19542752588196072858923749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26057003450928097145231665 19542752588196072858923749)
              ·
                refine ⟨3664266110286763661048203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19542752588196072858923749 3664266110286763661048203)
                ·
                  refine ⟨5496399165430145491572305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3664266110286763661048203 5496399165430145491572305)
                  ·
                    refine ⟨4122299374072609118679229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5496399165430145491572305 4122299374072609118679229)
                    ·
                      refine ⟨1545862265277228419504711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4122299374072609118679229 1545862265277228419504711)
                      ·
                        rfl

theorem cell23_3010556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_3010556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010556 prefixEnd_3010556 := by exact prefixLift 3010556
  have htrace : WordTrace (prefixWord ++ tailWord_3010556) baseStart_3010556 baseEnd_3010556 := by
    simpa [prefixWord, tailWord_3010556, baseEnd_3010556] using wordTrace_append hprefix tailTrace_3010556
  have hstable : (prefixWord ++ tailWord_3010556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010556).length < 2 ^ (prefixWord ++ tailWord_3010556).sum := by decide
  have hdescent : baseEnd_3010556 < baseStart_3010556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010570 : List Nat := [3, 1, 2, 2, 4, 2, 2, 1, 1, 1, 4]
def baseStart_3010570 : Nat := 118140960795 + 3010570 * 2 ^ 59
def prefixEnd_3010570 : Nat := 4983230072969 + 3 ^ 40 * 3010570 * 2
def baseEnd_3010570 : Nat := 1545869454006391364729647

theorem tailTrace_3010570 : CollatzResearch.WordTrace tailWord_3010570 prefixEnd_3010570 1545869454006391364729647 := by
  unfold tailWord_3010570
  simp only [CollatzResearch.WordTrace]
  refine ⟨27451127175806632316597291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73203005802151019510926109 27451127175806632316597291)
  ·
    refine ⟨41176690763709948474895937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27451127175806632316597291 41176690763709948474895937)
    ·
      refine ⟨30882518072782461356171953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41176690763709948474895937 30882518072782461356171953)
      ·
        refine ⟨23161888554586846017128965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30882518072782461356171953 23161888554586846017128965)
        ·
          refine ⟨4342854103985033628211681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23161888554586846017128965 4342854103985033628211681)
          ·
            refine ⟨3257140577988775221158761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4342854103985033628211681 3257140577988775221158761)
            ·
              refine ⟨2442855433491581415869071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3257140577988775221158761 2442855433491581415869071)
              ·
                refine ⟨3664283150237372123803607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2442855433491581415869071 3664283150237372123803607)
                ·
                  refine ⟨5496424725356058185705411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3664283150237372123803607 5496424725356058185705411)
                  ·
                    refine ⟨8244637088034087278558117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5496424725356058185705411 8244637088034087278558117)
                    ·
                      refine ⟨1545869454006391364729647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8244637088034087278558117 1545869454006391364729647)
                      ·
                        rfl

theorem cell23_3010570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_3010570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010570 prefixEnd_3010570 := by exact prefixLift 3010570
  have htrace : WordTrace (prefixWord ++ tailWord_3010570) baseStart_3010570 baseEnd_3010570 := by
    simpa [prefixWord, tailWord_3010570, baseEnd_3010570] using wordTrace_append hprefix tailTrace_3010570
  have hstable : (prefixWord ++ tailWord_3010570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010570).length < 2 ^ (prefixWord ++ tailWord_3010570).sum := by decide
  have hdescent : baseEnd_3010570 < baseStart_3010570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010580 : List Nat := [2, 4, 3, 2, 1, 1, 1, 1, 4, 4]
def baseStart_3010580 : Nat := 118140960795 + 3010580 * 2 ^ 59
def prefixEnd_3010580 : Nat := 4983230072969 + 3 ^ 40 * 3010580 * 2
def baseEnd_3010580 : Nat := 515291529604312108534867

theorem tailTrace_3010580 : CollatzResearch.WordTrace tailWord_3010580 prefixEnd_3010580 515291529604312108534867 := by
  unfold tailWord_3010580
  simp only [CollatzResearch.WordTrace]
  refine ⟨54902436716595150487126597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73203248955460200649502129 54902436716595150487126597)
  ·
    refine ⟨10294206884361590716336237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54902436716595150487126597 10294206884361590716336237)
    ·
      refine ⟨3860327581635596518626089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10294206884361590716336237 3860327581635596518626089)
      ·
        refine ⟨2895245686226697388969567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3860327581635596518626089 2895245686226697388969567)
        ·
          refine ⟨4342868529340046083454351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2895245686226697388969567 4342868529340046083454351)
          ·
            refine ⟨6514302794010069125181527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4342868529340046083454351 6514302794010069125181527)
            ·
              refine ⟨9771454191015103687772291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6514302794010069125181527 9771454191015103687772291)
              ·
                refine ⟨14657181286522655531658437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9771454191015103687772291 14657181286522655531658437)
                ·
                  refine ⟨2748221491222997912185957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14657181286522655531658437 2748221491222997912185957)
                  ·
                    refine ⟨515291529604312108534867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2748221491222997912185957 515291529604312108534867)
                    ·
                      rfl

theorem cell23_3010580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_3010580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010580 prefixEnd_3010580 := by exact prefixLift 3010580
  have htrace : WordTrace (prefixWord ++ tailWord_3010580) baseStart_3010580 baseEnd_3010580 := by
    simpa [prefixWord, tailWord_3010580, baseEnd_3010580] using wordTrace_append hprefix tailTrace_3010580
  have hstable : (prefixWord ++ tailWord_3010580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010580).length < 2 ^ (prefixWord ++ tailWord_3010580).sum := by decide
  have hdescent : baseEnd_3010580 < baseStart_3010580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010600 : List Nat := [2, 1, 5, 3, 1, 2, 1, 1, 1, 2, 4]
def baseStart_3010600 : Nat := 118140960795 + 3010600 * 2 ^ 59
def prefixEnd_3010600 : Nat := 4983230072969 + 3 ^ 40 * 3010600 * 2
def baseEnd_3010600 : Nat := 1545884858426026247354509

theorem tailTrace_3010600 : CollatzResearch.WordTrace tailWord_3010600 prefixEnd_3010600 1545884858426026247354509 := by
  unfold tailWord_3010600
  simp only [CollatzResearch.WordTrace]
  refine ⟨54902801446558922194990627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73203735262078562926654169 54902801446558922194990627)
  ·
    refine ⟨82354202169838383292485941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54902801446558922194990627 82354202169838383292485941)
    ·
      refine ⟨7720706453422348433670557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82354202169838383292485941 7720706453422348433670557)
      ·
        refine ⟨2895264920033380662626459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7720706453422348433670557 2895264920033380662626459)
        ·
          refine ⟨4342897380050070993939689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2895264920033380662626459 4342897380050070993939689)
          ·
            refine ⟨3257173035037553245454767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4342897380050070993939689 3257173035037553245454767)
            ·
              refine ⟨4885759552556329868182151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3257173035037553245454767 4885759552556329868182151)
              ·
                refine ⟨7328639328834494802273227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4885759552556329868182151 7328639328834494802273227)
                ·
                  refine ⟨10992958993251742203409841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7328639328834494802273227 10992958993251742203409841)
                  ·
                    refine ⟨8244719244938806652557381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10992958993251742203409841 8244719244938806652557381)
                    ·
                      refine ⟨1545884858426026247354509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8244719244938806652557381 1545884858426026247354509)
                      ·
                        rfl

theorem cell23_3010600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_3010600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010600 prefixEnd_3010600 := by exact prefixLift 3010600
  have htrace : WordTrace (prefixWord ++ tailWord_3010600) baseStart_3010600 baseEnd_3010600 := by
    simpa [prefixWord, tailWord_3010600, baseEnd_3010600] using wordTrace_append hprefix tailTrace_3010600
  have hstable : (prefixWord ++ tailWord_3010600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010600).length < 2 ^ (prefixWord ++ tailWord_3010600).sum := by decide
  have hdescent : baseEnd_3010600 < baseStart_3010600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010613 : List Nat := [1, 3, 3, 1, 1, 1, 3, 4, 1, 3, 2]
def baseStart_3010613 : Nat := 118140960795 + 3010613 * 2 ^ 59
def prefixEnd_3010613 : Nat := 4983230072969 + 3 ^ 40 * 3010613 * 2
def baseEnd_3010613 : Nat := 1545891533674534696491949

theorem tailTrace_3010613 : CollatzResearch.WordTrace tailWord_3010613 prefixEnd_3010613 1545891533674534696491949 := by
  unfold tailWord_3010613
  simp only [CollatzResearch.WordTrace]
  refine ⟨109806077042070747610204493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73204051361380498406802995 109806077042070747610204493)
  ·
    refine ⟨41177278890776530353826685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109806077042070747610204493 41177278890776530353826685)
    ·
      refine ⟨15441479584041198882685007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41177278890776530353826685 15441479584041198882685007)
      ·
        refine ⟨23162219376061798324027511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15441479584041198882685007 23162219376061798324027511)
        ·
          refine ⟨34743329064092697486041267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23162219376061798324027511 34743329064092697486041267)
          ·
            refine ⟨52114993596139046229061901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34743329064092697486041267 52114993596139046229061901)
            ·
              refine ⟨19543122598552142335898213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52114993596139046229061901 19543122598552142335898213)
              ·
                refine ⟨3664335487228526687980915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19543122598552142335898213 3664335487228526687980915)
                ·
                  refine ⟨5496503230842790031971373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3664335487228526687980915 5496503230842790031971373)
                  ·
                    refine ⟨2061188711566046261989265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5496503230842790031971373 2061188711566046261989265)
                    ·
                      refine ⟨1545891533674534696491949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2061188711566046261989265 1545891533674534696491949)
                      ·
                        rfl

theorem cell23_3010613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_3010613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010613 prefixEnd_3010613 := by exact prefixLift 3010613
  have htrace : WordTrace (prefixWord ++ tailWord_3010613) baseStart_3010613 baseEnd_3010613 := by
    simpa [prefixWord, tailWord_3010613, baseEnd_3010613] using wordTrace_append hprefix tailTrace_3010613
  have hstable : (prefixWord ++ tailWord_3010613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010613).length < 2 ^ (prefixWord ++ tailWord_3010613).sum := by decide
  have hdescent : baseEnd_3010613 < baseStart_3010613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010629 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 1, 6, 3]
def baseStart_3010629 : Nat := 118140960795 + 3010629 * 2 ^ 59
def prefixEnd_3010629 : Nat := 4983230072969 + 3 ^ 40 * 3010629 * 2
def baseEnd_3010629 : Nat := 1545899749365006633891875

theorem tailTrace_3010629 : CollatzResearch.WordTrace tailWord_3010629 prefixEnd_3010629 1545899749365006633891875 := by
  unfold tailWord_3010629
  simp only [CollatzResearch.WordTrace]
  refine ⟨109806660610012782342786941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73204440406675188228524627 109806660610012782342786941)
  ·
    refine ⟨41177497728754793378545103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109806660610012782342786941 41177497728754793378545103)
    ·
      refine ⟨61766246593132190067817655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41177497728754793378545103 61766246593132190067817655)
      ·
        refine ⟨92649369889698285101726483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61766246593132190067817655 92649369889698285101726483)
        ·
          refine ⟨138974054834547427652589725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92649369889698285101726483 138974054834547427652589725)
          ·
            refine ⟨52115270562955285369721147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138974054834547427652589725 52115270562955285369721147)
            ·
              refine ⟨78172905844432928054581721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52115270562955285369721147 78172905844432928054581721)
              ·
                refine ⟨58629679383324696040936291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78172905844432928054581721 58629679383324696040936291)
                ·
                  refine ⟨87944519074987044061404437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58629679383324696040936291 87944519074987044061404437)
                  ·
                    refine ⟨4122399331640017690378333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87944519074987044061404437 4122399331640017690378333)
                    ·
                      refine ⟨1545899749365006633891875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4122399331640017690378333 1545899749365006633891875)
                      ·
                        rfl

theorem cell23_3010629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 6, 3].length) (baseStart_3010629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010629 prefixEnd_3010629 := by exact prefixLift 3010629
  have htrace : WordTrace (prefixWord ++ tailWord_3010629) baseStart_3010629 baseEnd_3010629 := by
    simpa [prefixWord, tailWord_3010629, baseEnd_3010629] using wordTrace_append hprefix tailTrace_3010629
  have hstable : (prefixWord ++ tailWord_3010629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010629).length < 2 ^ (prefixWord ++ tailWord_3010629).sum := by decide
  have hdescent : baseEnd_3010629 < baseStart_3010629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010654 : List Nat := [4, 4, 1, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_3010654 : Nat := 118140960795 + 3010654 * 2 ^ 59
def prefixEnd_3010654 : Nat := 4983230072969 + 3 ^ 40 * 3010654 * 2
def baseEnd_3010654 : Nat := 1545912586381369036079261

theorem tailTrace_3010654 : CollatzResearch.WordTrace tailWord_3010654 prefixEnd_3010654 1545912586381369036079261 := by
  unfold tailWord_3010654
  simp only [CollatzResearch.WordTrace]
  refine ⟨13725946554365276451555877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73205048289948141074964677 13725946554365276451555877)
  ·
    refine ⟨2573614978943489334666727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13725946554365276451555877 2573614978943489334666727)
    ·
      refine ⟨3860422468415234002000091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2573614978943489334666727 3860422468415234002000091)
      ·
        refine ⟨5790633702622851003000137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3860422468415234002000091 5790633702622851003000137)
        ·
          refine ⟨4342975276967138252250103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5790633702622851003000137 4342975276967138252250103)
          ·
            refine ⟨6514462915450707378375155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4342975276967138252250103 6514462915450707378375155)
            ·
              refine ⟨9771694373176061067562733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6514462915450707378375155 9771694373176061067562733)
              ·
                refine ⟨3664385389941022900336025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9771694373176061067562733 3664385389941022900336025)
                ·
                  refine ⟨2748289042455767175252019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3664385389941022900336025 2748289042455767175252019)
                  ·
                    refine ⟨4122433563683650762878029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2748289042455767175252019 4122433563683650762878029)
                    ·
                      refine ⟨1545912586381369036079261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4122433563683650762878029 1545912586381369036079261)
                      ·
                        rfl

theorem cell23_3010654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_3010654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010654 prefixEnd_3010654 := by exact prefixLift 3010654
  have htrace : WordTrace (prefixWord ++ tailWord_3010654) baseStart_3010654 baseEnd_3010654 := by
    simpa [prefixWord, tailWord_3010654, baseEnd_3010654] using wordTrace_append hprefix tailTrace_3010654
  have hstable : (prefixWord ++ tailWord_3010654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010654).length < 2 ^ (prefixWord ++ tailWord_3010654).sum := by decide
  have hdescent : baseEnd_3010654 < baseStart_3010654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010699 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 4]
def baseStart_3010699 : Nat := 118140960795 + 3010699 * 2 ^ 59
def prefixEnd_3010699 : Nat := 4983230072969 + 3 ^ 40 * 3010699 * 2
def baseEnd_3010699 : Nat := 1545935693010821360016553

theorem tailTrace_3010699 : CollatzResearch.WordTrace tailWord_3010699 prefixEnd_3010699 1545935693010821360016553 := by
  unfold tailWord_3010699
  simp only [CollatzResearch.WordTrace]
  refine ⟨109809213719759184297835151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73206142479839456198556767 109809213719759184297835151)
  ·
    refine ⟨164713820579638776446752727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109809213719759184297835151 164713820579638776446752727)
    ·
      refine ⟨247070730869458164670129091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164713820579638776446752727 247070730869458164670129091)
      ·
        refine ⟨370606096304187247005193637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247070730869458164670129091 370606096304187247005193637)
        ·
          refine ⟨69488643057035108813473807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 370606096304187247005193637 69488643057035108813473807)
          ·
            refine ⟨104232964585552663220210711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69488643057035108813473807 104232964585552663220210711)
            ·
              refine ⟨156349446878328994830316067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104232964585552663220210711 156349446878328994830316067)
              ·
                refine ⟨234524170317493492245474101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156349446878328994830316067 234524170317493492245474101)
                ·
                  refine ⟨21986640967265014898013197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 234524170317493492245474101 21986640967265014898013197)
                  ·
                    refine ⟨8244990362724380586754949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21986640967265014898013197 8244990362724380586754949)
                    ·
                      refine ⟨1545935693010821360016553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8244990362724380586754949 1545935693010821360016553)
                      ·
                        rfl

theorem cell23_3010699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 4].length) (baseStart_3010699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010699 prefixEnd_3010699 := by exact prefixLift 3010699
  have htrace : WordTrace (prefixWord ++ tailWord_3010699) baseStart_3010699 baseEnd_3010699 := by
    simpa [prefixWord, tailWord_3010699, baseEnd_3010699] using wordTrace_append hprefix tailTrace_3010699
  have hstable : (prefixWord ++ tailWord_3010699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010699).length < 2 ^ (prefixWord ++ tailWord_3010699).sum := by decide
  have hdescent : baseEnd_3010699 < baseStart_3010699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010706 : List Nat := [3, 2, 3, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_3010706 : Nat := 118140960795 + 3010706 * 2 ^ 59
def prefixEnd_3010706 : Nat := 4983230072969 + 3 ^ 40 * 3010706 * 2
def baseEnd_3010706 : Nat := 1545939287375402832629021

theorem tailTrace_3010706 : CollatzResearch.WordTrace tailWord_3010706 prefixEnd_3010706 1545939287375402832629021 := by
  unfold tailWord_3010706
  simp only [CollatzResearch.WordTrace]
  refine ⟨27452367257683456123334993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73206312687155882995559981 27452367257683456123334993)
  ·
    refine ⟨20589275443262592092501245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27452367257683456123334993 20589275443262592092501245)
    ·
      refine ⟨7720978291223472034687967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20589275443262592092501245 7720978291223472034687967)
      ·
        refine ⟨11581467436835208052031951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7720978291223472034687967 11581467436835208052031951)
        ·
          refine ⟨17372201155252812078047927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11581467436835208052031951 17372201155252812078047927)
          ·
            refine ⟨26058301732879218117071891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17372201155252812078047927 26058301732879218117071891)
            ·
              refine ⟨39087452599318827175607837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26058301732879218117071891 39087452599318827175607837)
              ·
                refine ⟨14657794724744560190852939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39087452599318827175607837 14657794724744560190852939)
                ·
                  refine ⟨21986692087116840286279409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14657794724744560190852939 21986692087116840286279409)
                  ·
                    refine ⟨16490019065337630214709557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21986692087116840286279409 16490019065337630214709557)
                    ·
                      refine ⟨1545939287375402832629021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16490019065337630214709557 1545939287375402832629021)
                      ·
                        rfl

theorem cell23_3010706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_3010706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010706 prefixEnd_3010706 := by exact prefixLift 3010706
  have htrace : WordTrace (prefixWord ++ tailWord_3010706) baseStart_3010706 baseEnd_3010706 := by
    simpa [prefixWord, tailWord_3010706, baseEnd_3010706] using wordTrace_append hprefix tailTrace_3010706
  have hstable : (prefixWord ++ tailWord_3010706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010706).length < 2 ^ (prefixWord ++ tailWord_3010706).sum := by decide
  have hdescent : baseEnd_3010706 < baseStart_3010706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3010716 : List Nat := [2, 2, 3, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_3010716 : Nat := 118140960795 + 3010716 * 2 ^ 59
def prefixEnd_3010716 : Nat := 4983230072969 + 3 ^ 40 * 3010716 * 2
def baseEnd_3010716 : Nat := 1545944422181947793503975

theorem tailTrace_3010716 : CollatzResearch.WordTrace tailWord_3010716 prefixEnd_3010716 1545944422181947793503975 := by
  unfold tailWord_3010716
  simp only [CollatzResearch.WordTrace]
  refine ⟨54904916880348798100602001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73206555840465064134136001 54904916880348798100602001)
  ·
    refine ⟨41178687660261598575451501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54904916880348798100602001 41178687660261598575451501)
    ·
      refine ⟨15442007872598099465794313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41178687660261598575451501 15442007872598099465794313)
      ·
        refine ⟨11581505904448574599345735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15442007872598099465794313 11581505904448574599345735)
        ·
          refine ⟨17372258856672861899018603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11581505904448574599345735 17372258856672861899018603)
          ·
            refine ⟨26058388285009292848527905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17372258856672861899018603 26058388285009292848527905)
            ·
              refine ⟨19543791213756969636395929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26058388285009292848527905 19543791213756969636395929)
              ·
                refine ⟨14657843410317727227296947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19543791213756969636395929 14657843410317727227296947)
                ·
                  refine ⟨21986765115476590840945421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14657843410317727227296947 21986765115476590840945421)
                  ·
                    refine ⟨8245036918303721565354533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21986765115476590840945421 8245036918303721565354533)
                    ·
                      refine ⟨1545944422181947793503975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8245036918303721565354533 1545944422181947793503975)
                      ·
                        rfl

theorem cell23_3010716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_3010716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3010716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3010716 prefixEnd_3010716 := by exact prefixLift 3010716
  have htrace : WordTrace (prefixWord ++ tailWord_3010716) baseStart_3010716 baseEnd_3010716 := by
    simpa [prefixWord, tailWord_3010716, baseEnd_3010716] using wordTrace_append hprefix tailTrace_3010716
  have hstable : (prefixWord ++ tailWord_3010716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3010716).length < 2 ^ (prefixWord ++ tailWord_3010716).sum := by decide
  have hdescent : baseEnd_3010716 < baseStart_3010716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3010716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
