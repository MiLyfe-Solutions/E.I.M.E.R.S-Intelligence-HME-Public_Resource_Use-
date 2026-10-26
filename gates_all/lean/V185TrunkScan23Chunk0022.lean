import V185TrunkScan23Chunk0021

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_130280 : List Nat := [2, 1, 4, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_130280 : Nat := 118140960795 + 130280 * 2 ^ 59
def prefixEnd_130280 : Nat := 4983230072969 + 3 ^ 40 * 130280 * 2
def baseEnd_130280 : Nat := 66896259667855512600859

theorem tailTrace_130280 : CollatzResearch.WordTrace tailWord_130280 prefixEnd_130280 66896259667855512600859 := by
  unfold tailWord_130280
  simp only [CollatzResearch.WordTrace]
  refine ⟨2375850984012642448846147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3167801312016856598461529 2375850984012642448846147)
  ·
    refine ⟨3563776476018963673269221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2375850984012642448846147 3563776476018963673269221)
    ·
      refine ⟨668208089253555688737979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3563776476018963673269221 668208089253555688737979)
      ·
        refine ⟨1002312133880333533106969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668208089253555688737979 1002312133880333533106969)
        ·
          refine ⟨751734100410250149830227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1002312133880333533106969 751734100410250149830227)
          ·
            refine ⟨1127601150615375224745341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751734100410250149830227 1127601150615375224745341)
            ·
              refine ⟨422850431480765709279503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1127601150615375224745341 422850431480765709279503)
              ·
                refine ⟨634275647221148563919255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422850431480765709279503 634275647221148563919255)
                ·
                  refine ⟨951413470831722845878883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 634275647221148563919255 951413470831722845878883)
                  ·
                    refine ⟨1427120206247584268818325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 951413470831722845878883 1427120206247584268818325)
                    ·
                      refine ⟨66896259667855512600859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1427120206247584268818325 66896259667855512600859)
                      ·
                        rfl

theorem cell23_130280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_130280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130280 prefixEnd_130280 := by exact prefixLift 130280
  have htrace : WordTrace (prefixWord ++ tailWord_130280) baseStart_130280 baseEnd_130280 := by
    simpa [prefixWord, tailWord_130280, baseEnd_130280] using wordTrace_append hprefix tailTrace_130280
  have hstable : (prefixWord ++ tailWord_130280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130280).length < 2 ^ (prefixWord ++ tailWord_130280).sum := by decide
  have hdescent : baseEnd_130280 < baseStart_130280 := by decide
  rcases family_descends (prefixWord ++ tailWord_130280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130284 : List Nat := [2, 2, 1, 1, 2, 4, 2, 2, 3, 2, 2]
def baseStart_130284 : Nat := 118140960795 + 130284 * 2 ^ 59
def prefixEnd_130284 : Nat := 4983230072969 + 3 ^ 40 * 130284 * 2
def baseEnd_130284 : Nat := 66898313590473496950841

theorem tailTrace_130284 : CollatzResearch.WordTrace tailWord_130284 prefixEnd_130284 66898313590473496950841 := by
  unfold tailWord_130284
  simp only [CollatzResearch.WordTrace]
  refine ⟨2375923930005396790418953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3167898573340529053891937 2375923930005396790418953)
  ·
    refine ⟨1781942947504047592814215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2375923930005396790418953 1781942947504047592814215)
    ·
      refine ⟨2672914421256071389221323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1781942947504047592814215 2672914421256071389221323)
      ·
        refine ⟨4009371631884107083831985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2672914421256071389221323 4009371631884107083831985)
        ·
          refine ⟨3007028723913080312873989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4009371631884107083831985 3007028723913080312873989)
          ·
            refine ⟨563817885733702558663873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3007028723913080312873989 563817885733702558663873)
            ·
              refine ⟨422863414300276918997905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 563817885733702558663873 422863414300276918997905)
              ·
                refine ⟨317147560725207689248429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422863414300276918997905 317147560725207689248429)
                ·
                  refine ⟨118930335271952883468161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 317147560725207689248429 118930335271952883468161)
                  ·
                    refine ⟨89197751453964662601121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118930335271952883468161 89197751453964662601121)
                    ·
                      refine ⟨66898313590473496950841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 89197751453964662601121 66898313590473496950841)
                      ·
                        rfl

theorem cell23_130284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 2, 2].length) (baseStart_130284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130284 prefixEnd_130284 := by exact prefixLift 130284
  have htrace : WordTrace (prefixWord ++ tailWord_130284) baseStart_130284 baseEnd_130284 := by
    simpa [prefixWord, tailWord_130284, baseEnd_130284] using wordTrace_append hprefix tailTrace_130284
  have hstable : (prefixWord ++ tailWord_130284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130284).length < 2 ^ (prefixWord ++ tailWord_130284).sum := by decide
  have hdescent : baseEnd_130284 < baseStart_130284 := by decide
  rcases family_descends (prefixWord ++ tailWord_130284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130338 : List Nat := [3, 3, 1, 1, 5, 1, 1, 2, 1, 2, 3]
def baseStart_130338 : Nat := 118140960795 + 130338 * 2 ^ 59
def prefixEnd_130338 : Nat := 4983230072969 + 3 ^ 40 * 130338 * 2
def baseEnd_130338 : Nat := 66926041545816285675593

theorem tailTrace_130338 : CollatzResearch.WordTrace tailWord_130338 prefixEnd_130338 66926041545816285675593 := by
  unfold tailWord_130338
  simp only [CollatzResearch.WordTrace]
  refine ⟨1188454350453790200825917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3169211601210107202202445 1188454350453790200825917)
  ·
    refine ⟨445670381420171325309719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1188454350453790200825917 445670381420171325309719)
    ·
      refine ⟨668505572130256987964579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445670381420171325309719 668505572130256987964579)
      ·
        refine ⟨1002758358195385481946869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668505572130256987964579 1002758358195385481946869)
        ·
          refine ⟨94008596080817388932519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1002758358195385481946869 94008596080817388932519)
          ·
            refine ⟨141012894121226083398779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94008596080817388932519 141012894121226083398779)
            ·
              refine ⟨211519341181839125098169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141012894121226083398779 211519341181839125098169)
              ·
                refine ⟨158639505886379343823627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211519341181839125098169 158639505886379343823627)
                ·
                  refine ⟨237959258829569015735441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158639505886379343823627 237959258829569015735441)
                  ·
                    refine ⟨178469444122176761801581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 237959258829569015735441 178469444122176761801581)
                    ·
                      refine ⟨66926041545816285675593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 178469444122176761801581 66926041545816285675593)
                      ·
                        rfl

theorem cell23_130338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_130338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130338 prefixEnd_130338 := by exact prefixLift 130338
  have htrace : WordTrace (prefixWord ++ tailWord_130338) baseStart_130338 baseEnd_130338 := by
    simpa [prefixWord, tailWord_130338, baseEnd_130338] using wordTrace_append hprefix tailTrace_130338
  have hstable : (prefixWord ++ tailWord_130338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130338).length < 2 ^ (prefixWord ++ tailWord_130338).sum := by decide
  have hdescent : baseEnd_130338 < baseStart_130338 := by decide
  rcases family_descends (prefixWord ++ tailWord_130338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130391 : List Nat := [1, 1, 3, 2, 3, 2, 2, 3, 2, 2, 2]
def baseStart_130391 : Nat := 118140960795 + 130391 * 2 ^ 59
def prefixEnd_130391 : Nat := 4983230072969 + 3 ^ 40 * 130391 * 2
def baseEnd_130391 : Nat := 66953256020504578312849

theorem tailTrace_130391 : CollatzResearch.WordTrace tailWord_130391 prefixEnd_130391 66953256020504578312849 := by
  unfold tailWord_130391
  simp only [CollatzResearch.WordTrace]
  refine ⟨4755750470623150854983027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3170500313748767236655351 4755750470623150854983027)
  ·
    refine ⟨7133625705934726282474541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4755750470623150854983027 7133625705934726282474541)
    ·
      refine ⟨2675109639725522355927953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7133625705934726282474541 2675109639725522355927953)
      ·
        refine ⟨2006332229794141766945965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2675109639725522355927953 2006332229794141766945965)
        ·
          refine ⟨752374586172803162604737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2006332229794141766945965 752374586172803162604737)
          ·
            refine ⟨564280939629602371953553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 752374586172803162604737 564280939629602371953553)
            ·
              refine ⟨423210704722201778965165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 564280939629602371953553 423210704722201778965165)
              ·
                refine ⟨158704014270825667111937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 423210704722201778965165 158704014270825667111937)
                ·
                  refine ⟨119028010703119250333953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158704014270825667111937 119028010703119250333953)
                  ·
                    refine ⟨89271008027339437750465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119028010703119250333953 89271008027339437750465)
                    ·
                      refine ⟨66953256020504578312849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 89271008027339437750465 66953256020504578312849)
                      ·
                        rfl

theorem cell23_130391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2, 2, 2].length) (baseStart_130391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130391 prefixEnd_130391 := by exact prefixLift 130391
  have htrace : WordTrace (prefixWord ++ tailWord_130391) baseStart_130391 baseEnd_130391 := by
    simpa [prefixWord, tailWord_130391, baseEnd_130391] using wordTrace_append hprefix tailTrace_130391
  have hstable : (prefixWord ++ tailWord_130391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130391).length < 2 ^ (prefixWord ++ tailWord_130391).sum := by decide
  have hdescent : baseEnd_130391 < baseStart_130391 := by decide
  rcases family_descends (prefixWord ++ tailWord_130391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130467 : List Nat := [1, 1, 1, 4, 1, 3, 1, 3, 1, 4, 3]
def baseStart_130467 : Nat := 118140960795 + 130467 * 2 ^ 59
def prefixEnd_130467 : Nat := 4983230072969 + 3 ^ 40 * 130467 * 2
def baseEnd_130467 : Nat := 66992280550246280962499

theorem tailTrace_130467 : CollatzResearch.WordTrace tailWord_130467 prefixEnd_130467 66992280550246280962499 := by
  unfold tailWord_130467
  simp only [CollatzResearch.WordTrace]
  refine ⟨4758522418347815834749655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3172348278898543889833103 4758522418347815834749655)
  ·
    refine ⟨7137783627521723752124483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4758522418347815834749655 7137783627521723752124483)
    ·
      refine ⟨10706675441282585628186725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7137783627521723752124483 10706675441282585628186725)
      ·
        refine ⟨2007501645240484805285011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10706675441282585628186725 2007501645240484805285011)
        ·
          refine ⟨3011252467860727207927517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2007501645240484805285011 3011252467860727207927517)
          ·
            refine ⟨1129219675447772702972819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3011252467860727207927517 1129219675447772702972819)
            ·
              refine ⟨1693829513171659054459229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1129219675447772702972819 1693829513171659054459229)
              ·
                refine ⟨635186067439372145422211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1693829513171659054459229 635186067439372145422211)
                ·
                  refine ⟨952779101159058218133317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 635186067439372145422211 952779101159058218133317)
                  ·
                    refine ⟨178646081467323415899997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 952779101159058218133317 178646081467323415899997)
                    ·
                      refine ⟨66992280550246280962499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 178646081467323415899997 66992280550246280962499)
                      ·
                        rfl

theorem cell23_130467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_130467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130467 prefixEnd_130467 := by exact prefixLift 130467
  have htrace : WordTrace (prefixWord ++ tailWord_130467) baseStart_130467 baseEnd_130467 := by
    simpa [prefixWord, tailWord_130467, baseEnd_130467] using wordTrace_append hprefix tailTrace_130467
  have hstable : (prefixWord ++ tailWord_130467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130467).length < 2 ^ (prefixWord ++ tailWord_130467).sum := by decide
  have hdescent : baseEnd_130467 < baseStart_130467 := by decide
  rcases family_descends (prefixWord ++ tailWord_130467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130487 : List Nat := [1, 1, 3, 1, 3, 2, 2, 4, 6]
def baseStart_130487 : Nat := 118140960795 + 130487 * 2 ^ 59
def prefixEnd_130487 : Nat := 4983230072969 + 3 ^ 40 * 130487 * 2
def baseEnd_130487 : Nat := 7444727795926244745823

theorem tailTrace_130487 : CollatzResearch.WordTrace tailWord_130487 prefixEnd_130487 7444727795926244745823 := by
  unfold tailWord_130487
  simp only [CollatzResearch.WordTrace]
  refine ⟨4759251878275359250477715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3172834585516906166985143 4759251878275359250477715)
  ·
    refine ⟨7138877817413038875716573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4759251878275359250477715 7138877817413038875716573)
    ·
      refine ⟨2677079181529889578393715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7138877817413038875716573 2677079181529889578393715)
      ·
        refine ⟨4015618772294834367590573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2677079181529889578393715 4015618772294834367590573)
        ·
          refine ⟨1505857039610562887846465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4015618772294834367590573 1505857039610562887846465)
          ·
            refine ⟨1129392779707922165884849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1505857039610562887846465 1129392779707922165884849)
            ·
              refine ⟨847044584780941624413637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1129392779707922165884849 847044584780941624413637)
              ·
                refine ⟨158820859646426554577557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 847044584780941624413637 158820859646426554577557)
                ·
                  refine ⟨7444727795926244745823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158820859646426554577557 7444727795926244745823)
                  ·
                    rfl

theorem cell23_130487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 6].length) (baseStart_130487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130487 prefixEnd_130487 := by exact prefixLift 130487
  have htrace : WordTrace (prefixWord ++ tailWord_130487) baseStart_130487 baseEnd_130487 := by
    simpa [prefixWord, tailWord_130487, baseEnd_130487] using wordTrace_append hprefix tailTrace_130487
  have hstable : (prefixWord ++ tailWord_130487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130487).length < 2 ^ (prefixWord ++ tailWord_130487).sum := by decide
  have hdescent : baseEnd_130487 < baseStart_130487 := by decide
  rcases family_descends (prefixWord ++ tailWord_130487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130518 : List Nat := [5, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_130518 : Nat := 118140960795 + 130518 * 2 ^ 59
def prefixEnd_130518 : Nat := 4983230072969 + 3 ^ 40 * 130518 * 2
def baseEnd_130518 : Nat := 67018468063625581424765

theorem tailTrace_130518 : CollatzResearch.WordTrace tailWord_130518 prefixEnd_130518 67018468063625581424765 := by
  unfold tailWord_130518
  simp only [CollatzResearch.WordTrace]
  refine ⟨297523908822690721553513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3173588360775367696570805 297523908822690721553513)
  ·
    refine ⟨223142931617018041165135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297523908822690721553513 223142931617018041165135)
    ·
      refine ⟨334714397425527061747703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223142931617018041165135 334714397425527061747703)
      ·
        refine ⟨502071596138290592621555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334714397425527061747703 502071596138290592621555)
        ·
          refine ⟨753107394207435888932333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502071596138290592621555 753107394207435888932333)
          ·
            refine ⟨282415272827788458349625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 753107394207435888932333 282415272827788458349625)
            ·
              refine ⟨211811454620841343762219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282415272827788458349625 211811454620841343762219)
              ·
                refine ⟨317717181931262015643329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211811454620841343762219 317717181931262015643329)
                ·
                  refine ⟨238287886448446511732497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317717181931262015643329 238287886448446511732497)
                  ·
                    refine ⟨178715914836334883799373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 238287886448446511732497 178715914836334883799373)
                    ·
                      refine ⟨67018468063625581424765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 178715914836334883799373 67018468063625581424765)
                      ·
                        rfl

theorem cell23_130518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_130518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130518 prefixEnd_130518 := by exact prefixLift 130518
  have htrace : WordTrace (prefixWord ++ tailWord_130518) baseStart_130518 baseEnd_130518 := by
    simpa [prefixWord, tailWord_130518, baseEnd_130518] using wordTrace_append hprefix tailTrace_130518
  have hstable : (prefixWord ++ tailWord_130518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130518).length < 2 ^ (prefixWord ++ tailWord_130518).sum := by decide
  have hdescent : baseEnd_130518 < baseStart_130518 := by decide
  rcases family_descends (prefixWord ++ tailWord_130518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130597 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 2, 2, 6]
def baseStart_130597 : Nat := 118140960795 + 130597 * 2 ^ 59
def prefixEnd_130597 : Nat := 4983230072969 + 3 ^ 40 * 130597 * 2
def baseEnd_130597 : Nat := 67059033035330772336901

theorem tailTrace_130597 : CollatzResearch.WordTrace tailWord_130597 prefixEnd_130597 67059033035330772336901 := by
  unfold tailWord_130597
  simp only [CollatzResearch.WordTrace]
  refine ⟨4763263907876848036982045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3175509271917898691321363 4763263907876848036982045)
  ·
    refine ⟨1786223965453818013868267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4763263907876848036982045 1786223965453818013868267)
    ·
      refine ⟨2679335948180727020802401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1786223965453818013868267 2679335948180727020802401)
      ·
        refine ⟨2009501961135545265601801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2679335948180727020802401 2009501961135545265601801)
        ·
          refine ⟨1507126470851658949201351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2009501961135545265601801 1507126470851658949201351)
          ·
            refine ⟨2260689706277488423802027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1507126470851658949201351 2260689706277488423802027)
            ·
              refine ⟨3391034559416232635703041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2260689706277488423802027 3391034559416232635703041)
              ·
                refine ⟨2543275919562174476777281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3391034559416232635703041 2543275919562174476777281)
                ·
                  refine ⟨1907456939671630857582961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2543275919562174476777281 1907456939671630857582961)
                  ·
                    refine ⟨1430592704753723143187221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1907456939671630857582961 1430592704753723143187221)
                    ·
                      refine ⟨67059033035330772336901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1430592704753723143187221 67059033035330772336901)
                      ·
                        rfl

theorem cell23_130597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_130597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130597 prefixEnd_130597 := by exact prefixLift 130597
  have htrace : WordTrace (prefixWord ++ tailWord_130597) baseStart_130597 baseEnd_130597 := by
    simpa [prefixWord, tailWord_130597, baseEnd_130597] using wordTrace_append hprefix tailTrace_130597
  have hstable : (prefixWord ++ tailWord_130597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130597).length < 2 ^ (prefixWord ++ tailWord_130597).sum := by decide
  have hdescent : baseEnd_130597 < baseStart_130597 := by decide
  rcases family_descends (prefixWord ++ tailWord_130597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130748 : List Nat := [2, 2, 2, 3, 1, 4, 1, 1, 2, 5]
def baseStart_130748 : Nat := 118140960795 + 130748 * 2 ^ 59
def prefixEnd_130748 : Nat := 4983230072969 + 3 ^ 40 * 130748 * 2
def baseEnd_130748 : Nat := 22378856204719893849569

theorem tailTrace_130748 : CollatzResearch.WordTrace tailWord_130748 prefixEnd_130748 22378856204719893849569 := by
  unfold tailWord_130748
  simp only [CollatzResearch.WordTrace]
  refine ⟨2384385665164900412864449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3179180886886533883819265 2384385665164900412864449)
  ·
    refine ⟨1788289248873675309648337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2384385665164900412864449 1788289248873675309648337)
    ·
      refine ⟨1341216936655256482236253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1788289248873675309648337 1341216936655256482236253)
      ·
        refine ⟨502956351245721180838595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1341216936655256482236253 502956351245721180838595)
        ·
          refine ⟨754434526868581771257893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502956351245721180838595 754434526868581771257893)
          ·
            refine ⟨141456473787859082110855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 754434526868581771257893 141456473787859082110855)
            ·
              refine ⟨212184710681788623166283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141456473787859082110855 212184710681788623166283)
              ·
                refine ⟨318277066022682934749425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212184710681788623166283 318277066022682934749425)
                ·
                  refine ⟨238707799517012201062069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 318277066022682934749425 238707799517012201062069)
                  ·
                    refine ⟨22378856204719893849569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 238707799517012201062069 22378856204719893849569)
                    ·
                      rfl

theorem cell23_130748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_130748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130748 prefixEnd_130748 := by exact prefixLift 130748
  have htrace : WordTrace (prefixWord ++ tailWord_130748) baseStart_130748 baseEnd_130748 := by
    simpa [prefixWord, tailWord_130748, baseEnd_130748] using wordTrace_append hprefix tailTrace_130748
  have hstable : (prefixWord ++ tailWord_130748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130748).length < 2 ^ (prefixWord ++ tailWord_130748).sum := by decide
  have hdescent : baseEnd_130748 < baseStart_130748 := by decide
  rcases family_descends (prefixWord ++ tailWord_130748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130751 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 1, 6, 2]
def baseStart_130751 : Nat := 118140960795 + 130751 * 2 ^ 59
def prefixEnd_130751 : Nat := 4983230072969 + 3 ^ 40 * 130751 * 2
def baseEnd_130751 : Nat := 67138109056123169811193

theorem tailTrace_130751 : CollatzResearch.WordTrace tailWord_130751 prefixEnd_130751 67138109056123169811193 := by
  unfold tailWord_130751
  simp only [CollatzResearch.WordTrace]
  refine ⟨4768880749318932338088107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3179253832879288225392071 4768880749318932338088107)
  ·
    refine ⟨7153321123978398507132161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4768880749318932338088107 7153321123978398507132161)
    ·
      refine ⟨5364990842983798880349121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7153321123978398507132161 5364990842983798880349121)
      ·
        refine ⟨4023743132237849160261841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5364990842983798880349121 4023743132237849160261841)
        ·
          refine ⟨3017807349178386870196381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4023743132237849160261841 3017807349178386870196381)
          ·
            refine ⟨1131677755941895076323643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3017807349178386870196381 1131677755941895076323643)
            ·
              refine ⟨1697516633912842614485465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1131677755941895076323643 1697516633912842614485465)
              ·
                refine ⟨1273137475434631960864099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1697516633912842614485465 1273137475434631960864099)
                ·
                  refine ⟨1909706213151947941296149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1273137475434631960864099 1909706213151947941296149)
                  ·
                    refine ⟨89517478741497559748257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1909706213151947941296149 89517478741497559748257)
                    ·
                      refine ⟨67138109056123169811193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 89517478741497559748257 67138109056123169811193)
                      ·
                        rfl

theorem cell23_130751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 6, 2].length) (baseStart_130751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130751 prefixEnd_130751 := by exact prefixLift 130751
  have htrace : WordTrace (prefixWord ++ tailWord_130751) baseStart_130751 baseEnd_130751 := by
    simpa [prefixWord, tailWord_130751, baseEnd_130751] using wordTrace_append hprefix tailTrace_130751
  have hstable : (prefixWord ++ tailWord_130751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130751).length < 2 ^ (prefixWord ++ tailWord_130751).sum := by decide
  have hdescent : baseEnd_130751 < baseStart_130751 := by decide
  rcases family_descends (prefixWord ++ tailWord_130751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130778 : List Nat := [3, 1, 1, 2, 2, 4, 2, 1, 3, 4]
def baseStart_130778 : Nat := 118140960795 + 130778 * 2 ^ 59
def prefixEnd_130778 : Nat := 4983230072969 + 3 ^ 40 * 130778 * 2
def baseEnd_130778 : Nat := 22383991011264854724523

theorem tailTrace_130778 : CollatzResearch.WordTrace tailWord_130778 prefixEnd_130778 22383991011264854724523 := by
  unfold tailWord_130778
  simp only [CollatzResearch.WordTrace]
  refine ⟨1192466380055278987330247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3179910346814077299547325 1192466380055278987330247)
  ·
    refine ⟨1788699570082918480995371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1192466380055278987330247 1788699570082918480995371)
    ·
      refine ⟨2683049355124377721493057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1788699570082918480995371 2683049355124377721493057)
      ·
        refine ⟨2012287016343283291119793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2683049355124377721493057 2012287016343283291119793)
        ·
          refine ⟨1509215262257462468339845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2012287016343283291119793 1509215262257462468339845)
          ·
            refine ⟨282977861673274212813721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1509215262257462468339845 282977861673274212813721)
            ·
              refine ⟨212233396254955659610291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282977861673274212813721 212233396254955659610291)
              ·
                refine ⟨318350094382433489415437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212233396254955659610291 318350094382433489415437)
                ·
                  refine ⟨119381285393412558530789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 318350094382433489415437 119381285393412558530789)
                  ·
                    refine ⟨22383991011264854724523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119381285393412558530789 22383991011264854724523)
                    ·
                      rfl

theorem cell23_130778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 3, 4].length) (baseStart_130778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130778 prefixEnd_130778 := by exact prefixLift 130778
  have htrace : WordTrace (prefixWord ++ tailWord_130778) baseStart_130778 baseEnd_130778 := by
    simpa [prefixWord, tailWord_130778, baseEnd_130778] using wordTrace_append hprefix tailTrace_130778
  have hstable : (prefixWord ++ tailWord_130778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130778).length < 2 ^ (prefixWord ++ tailWord_130778).sum := by decide
  have hdescent : baseEnd_130778 < baseStart_130778 := by decide
  rcases family_descends (prefixWord ++ tailWord_130778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130828 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 4, 3, 2]
def baseStart_130828 : Nat := 118140960795 + 130828 * 2 ^ 59
def prefixEnd_130828 : Nat := 4983230072969 + 3 ^ 40 * 130828 * 2
def baseEnd_130828 : Nat := 67177647066519368548339

theorem tailTrace_130828 : CollatzResearch.WordTrace tailWord_130828 prefixEnd_130828 67177647066519368548339 := by
  unfold tailWord_130828
  simp only [CollatzResearch.WordTrace]
  refine ⟨2385844585019987244320569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3181126113359982992427425 2385844585019987244320569)
  ·
    refine ⟨1789383438764990433240427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2385844585019987244320569 1789383438764990433240427)
    ·
      refine ⟨2684075158147485649860641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1789383438764990433240427 2684075158147485649860641)
      ·
        refine ⟨2013056368610614237395481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2684075158147485649860641 2013056368610614237395481)
        ·
          refine ⟨1509792276457960678046611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2013056368610614237395481 1509792276457960678046611)
          ·
            refine ⟨2264688414686941017069917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1509792276457960678046611 2264688414686941017069917)
            ·
              refine ⟨849258155507602881401219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2264688414686941017069917 849258155507602881401219)
              ·
                refine ⟨1273887233261404322101829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849258155507602881401219 1273887233261404322101829)
                ·
                  refine ⟨238853856236513310394093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1273887233261404322101829 238853856236513310394093)
                  ·
                    refine ⟨89570196088692491397785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 238853856236513310394093 89570196088692491397785)
                    ·
                      refine ⟨67177647066519368548339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 89570196088692491397785 67177647066519368548339)
                      ·
                        rfl

theorem cell23_130828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 4, 3, 2].length) (baseStart_130828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130828 prefixEnd_130828 := by exact prefixLift 130828
  have htrace : WordTrace (prefixWord ++ tailWord_130828) baseStart_130828 baseEnd_130828 := by
    simpa [prefixWord, tailWord_130828, baseEnd_130828] using wordTrace_append hprefix tailTrace_130828
  have hstable : (prefixWord ++ tailWord_130828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130828).length < 2 ^ (prefixWord ++ tailWord_130828).sum := by decide
  have hdescent : baseEnd_130828 < baseStart_130828 := by decide
  rcases family_descends (prefixWord ++ tailWord_130828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130868 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_130868 : Nat := 118140960795 + 130868 * 2 ^ 59
def prefixEnd_130868 : Nat := 4983230072969 + 3 ^ 40 * 130868 * 2
def baseEnd_130868 : Nat := 22399395430899737349385

theorem tailTrace_130868 : CollatzResearch.WordTrace tailWord_130868 prefixEnd_130868 22399395430899737349385 := by
  unfold tailWord_130868
  simp only [CollatzResearch.WordTrace]
  refine ⟨2386574044947530660048629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3182098726596707546731505 2386574044947530660048629)
  ·
    refine ⟨223741316713830999379559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2386574044947530660048629 223741316713830999379559)
    ·
      refine ⟨335611975070746499069339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223741316713830999379559 335611975070746499069339)
      ·
        refine ⟨503417962606119748604009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335611975070746499069339 503417962606119748604009)
        ·
          refine ⟨377563471954589811453007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503417962606119748604009 377563471954589811453007)
          ·
            refine ⟨566345207931884717179511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377563471954589811453007 566345207931884717179511)
            ·
              refine ⟨849517811897827075769267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566345207931884717179511 849517811897827075769267)
              ·
                refine ⟨1274276717846740613653901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849517811897827075769267 1274276717846740613653901)
                ·
                  refine ⟨477853769192527730120213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1274276717846740613653901 477853769192527730120213)
                  ·
                    refine ⟨22399395430899737349385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 477853769192527730120213 22399395430899737349385)
                    ·
                      rfl

theorem cell23_130868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_130868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130868 prefixEnd_130868 := by exact prefixLift 130868
  have htrace : WordTrace (prefixWord ++ tailWord_130868) baseStart_130868 baseEnd_130868 := by
    simpa [prefixWord, tailWord_130868, baseEnd_130868] using wordTrace_append hprefix tailTrace_130868
  have hstable : (prefixWord ++ tailWord_130868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130868).length < 2 ^ (prefixWord ++ tailWord_130868).sum := by decide
  have hdescent : baseEnd_130868 < baseStart_130868 := by decide
  rcases family_descends (prefixWord ++ tailWord_130868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130886 : List Nat := [6, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3]
def baseStart_130886 : Nat := 118140960795 + 130886 * 2 ^ 59
def prefixEnd_130886 : Nat := 4983230072969 + 3 ^ 40 * 130886 * 2
def baseEnd_130886 : Nat := 67207428944480141623073

theorem tailTrace_130886 : CollatzResearch.WordTrace tailWord_130886 prefixEnd_130886 67207428944480141623073 := by
  unfold tailWord_130886
  simp only [CollatzResearch.WordTrace]
  refine ⟨149181393869682824820391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3182536402553233596168341 149181393869682824820391)
  ·
    refine ⟨223772090804524237230587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149181393869682824820391 223772090804524237230587)
    ·
      refine ⟨335658136206786355845881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223772090804524237230587 335658136206786355845881)
      ·
        refine ⟨251743602155089766884411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335658136206786355845881 251743602155089766884411)
        ·
          refine ⟨377615403232634650326617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251743602155089766884411 377615403232634650326617)
          ·
            refine ⟨283211552424475987744963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377615403232634650326617 283211552424475987744963)
            ·
              refine ⟨424817328636713981617445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283211552424475987744963 424817328636713981617445)
              ·
                refine ⟨79653249119383871553271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 424817328636713981617445 79653249119383871553271)
                ·
                  refine ⟨119479873679075807329907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79653249119383871553271 119479873679075807329907)
                  ·
                    refine ⟨179219810518613710994861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119479873679075807329907 179219810518613710994861)
                    ·
                      refine ⟨67207428944480141623073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 179219810518613710994861 67207428944480141623073)
                      ·
                        rfl

theorem cell23_130886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_130886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130886 prefixEnd_130886 := by exact prefixLift 130886
  have htrace : WordTrace (prefixWord ++ tailWord_130886) baseStart_130886 baseEnd_130886 := by
    simpa [prefixWord, tailWord_130886, baseEnd_130886] using wordTrace_append hprefix tailTrace_130886
  have hstable : (prefixWord ++ tailWord_130886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130886).length < 2 ^ (prefixWord ++ tailWord_130886).sum := by decide
  have hdescent : baseEnd_130886 < baseStart_130886 := by decide
  rcases family_descends (prefixWord ++ tailWord_130886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130898 : List Nat := [3, 2, 2, 1, 1, 5, 1, 8]
def baseStart_130898 : Nat := 118140960795 + 130898 * 2 ^ 59
def prefixEnd_130898 : Nat := 4983230072969 + 3 ^ 40 * 130898 * 2
def baseEnd_130898 : Nat := 2489392248604966469371

theorem tailTrace_130898 : CollatzResearch.WordTrace tailWord_130898 prefixEnd_130898 2489392248604966469371 := by
  unfold tailWord_130898
  simp only [CollatzResearch.WordTrace]
  refine ⟨1193560569946594110922337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3182828186524250962459565 1193560569946594110922337)
  ·
    refine ⟨895170427459945583191753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1193560569946594110922337 895170427459945583191753)
    ·
      refine ⟨671377820594959187393815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 895170427459945583191753 671377820594959187393815)
      ·
        refine ⟨1007066730892438781090723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671377820594959187393815 1007066730892438781090723)
        ·
          refine ⟨1510600096338658171636085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1007066730892438781090723 1510600096338658171636085)
          ·
            refine ⟨141618759031749203590883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1510600096338658171636085 141618759031749203590883)
            ·
              refine ⟨212428138547623805386325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141618759031749203590883 212428138547623805386325)
              ·
                refine ⟨2489392248604966469371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 212428138547623805386325 2489392248604966469371)
                ·
                  rfl

theorem cell23_130898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 8].length) (baseStart_130898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130898 prefixEnd_130898 := by exact prefixLift 130898
  have htrace : WordTrace (prefixWord ++ tailWord_130898) baseStart_130898 baseEnd_130898 := by
    simpa [prefixWord, tailWord_130898, baseEnd_130898] using wordTrace_append hprefix tailTrace_130898
  have hstable : (prefixWord ++ tailWord_130898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130898).length < 2 ^ (prefixWord ++ tailWord_130898).sum := by decide
  have hdescent : baseEnd_130898 < baseStart_130898 := by decide
  rcases family_descends (prefixWord ++ tailWord_130898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130926 : List Nat := [4, 1, 2, 3, 1, 2, 2, 3, 1, 2, 2]
def baseStart_130926 : Nat := 118140960795 + 130926 * 2 ^ 59
def prefixEnd_130926 : Nat := 4983230072969 + 3 ^ 40 * 130926 * 2
def baseEnd_130926 : Nat := 67227968170659985122889

theorem tailTrace_130926 : CollatzResearch.WordTrace tailWord_130926 prefixEnd_130926 67227968170659985122889 := by
  unfold tailWord_130926
  simp only [CollatzResearch.WordTrace]
  refine ⟨596907940460617153213579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3183509015789958150472421 596907940460617153213579)
  ·
    refine ⟨895361910690925729820369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 596907940460617153213579 895361910690925729820369)
    ·
      refine ⟨671521433018194297365277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 895361910690925729820369 671521433018194297365277)
      ·
        refine ⟨251820537381822861511979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 671521433018194297365277 251820537381822861511979)
        ·
          refine ⟨377730806072734292267969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251820537381822861511979 377730806072734292267969)
          ·
            refine ⟨283298104554550719200977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377730806072734292267969 283298104554550719200977)
            ·
              refine ⟨212473578415913039400733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283298104554550719200977 212473578415913039400733)
              ·
                refine ⟨79677591905967389775275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212473578415913039400733 79677591905967389775275)
                ·
                  refine ⟨119516387858951084662913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79677591905967389775275 119516387858951084662913)
                  ·
                    refine ⟨89637290894213313497185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119516387858951084662913 89637290894213313497185)
                    ·
                      refine ⟨67227968170659985122889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 89637290894213313497185 67227968170659985122889)
                      ·
                        rfl

theorem cell23_130926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_130926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130926 prefixEnd_130926 := by exact prefixLift 130926
  have htrace : WordTrace (prefixWord ++ tailWord_130926) baseStart_130926 baseEnd_130926 := by
    simpa [prefixWord, tailWord_130926, baseEnd_130926] using wordTrace_append hprefix tailTrace_130926
  have hstable : (prefixWord ++ tailWord_130926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130926).length < 2 ^ (prefixWord ++ tailWord_130926).sum := by decide
  have hdescent : baseEnd_130926 < baseStart_130926 := by decide
  rcases family_descends (prefixWord ++ tailWord_130926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130966 : List Nat := [5, 3, 1, 1, 3, 1, 2, 7]
def baseStart_130966 : Nat := 118140960795 + 130966 * 2 ^ 59
def prefixEnd_130966 : Nat := 4983230072969 + 3 ^ 40 * 130966 * 2
def baseEnd_130966 : Nat := 2490685459142215874915

theorem tailTrace_130966 : CollatzResearch.WordTrace tailWord_130966 prefixEnd_130966 2490685459142215874915 := by
  unfold tailWord_130966
  simp only [CollatzResearch.WordTrace]
  refine ⟨298545152721251503572797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3184481629026682704776501 298545152721251503572797)
  ·
    refine ⟨111954432270469313839799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298545152721251503572797 111954432270469313839799)
    ·
      refine ⟨167931648405703970759699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111954432270469313839799 167931648405703970759699)
      ·
        refine ⟨251897472608555956139549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167931648405703970759699 251897472608555956139549)
        ·
          refine ⟨94461552228208483552331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251897472608555956139549 94461552228208483552331)
          ·
            refine ⟨141692328342312725328497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94461552228208483552331 141692328342312725328497)
            ·
              refine ⟨106269246256734543996373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141692328342312725328497 106269246256734543996373)
              ·
                refine ⟨2490685459142215874915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 106269246256734543996373 2490685459142215874915)
                ·
                  rfl

theorem cell23_130966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 7].length) (baseStart_130966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130966 prefixEnd_130966 := by exact prefixLift 130966
  have htrace : WordTrace (prefixWord ++ tailWord_130966) baseStart_130966 baseEnd_130966 := by
    simpa [prefixWord, tailWord_130966, baseEnd_130966] using wordTrace_append hprefix tailTrace_130966
  have hstable : (prefixWord ++ tailWord_130966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130966).length < 2 ^ (prefixWord ++ tailWord_130966).sum := by decide
  have hdescent : baseEnd_130966 < baseStart_130966 := by decide
  rcases family_descends (prefixWord ++ tailWord_130966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131005 : List Nat := [1, 4, 1, 2, 3, 3, 1, 1, 7]
def baseStart_131005 : Nat := 118140960795 + 131005 * 2 ^ 59
def prefixEnd_131005 : Nat := 4983230072969 + 3 ^ 40 * 131005 * 2
def baseEnd_131005 : Nat := 7474281460262797337225

theorem tailTrace_131005 : CollatzResearch.WordTrace tailWord_131005 prefixEnd_131005 7474281460262797337225 := by
  unfold tailWord_131005
  simp only [CollatzResearch.WordTrace]
  refine ⟨4778144890398733717834469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3185429926932489145222979 4778144890398733717834469)
  ·
    refine ⟨895902166949762572093963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4778144890398733717834469 895902166949762572093963)
    ·
      refine ⟨1343853250424643858140945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 895902166949762572093963 1343853250424643858140945)
      ·
        refine ⟨1007889937818482893605709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1343853250424643858140945 1007889937818482893605709)
        ·
          refine ⟨377958726681931085102141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1007889937818482893605709 377958726681931085102141)
          ·
            refine ⟨141734522505724156913303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 377958726681931085102141 141734522505724156913303)
            ·
              refine ⟨212601783758586235369955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141734522505724156913303 212601783758586235369955)
              ·
                refine ⟨318902675637879353054933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212601783758586235369955 318902675637879353054933)
                ·
                  refine ⟨7474281460262797337225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 318902675637879353054933 7474281460262797337225)
                  ·
                    rfl

theorem cell23_131005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 7].length) (baseStart_131005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131005 prefixEnd_131005 := by exact prefixLift 131005
  have htrace : WordTrace (prefixWord ++ tailWord_131005) baseStart_131005 baseEnd_131005 := by
    simpa [prefixWord, tailWord_131005, baseEnd_131005] using wordTrace_append hprefix tailTrace_131005
  have hstable : (prefixWord ++ tailWord_131005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131005).length < 2 ^ (prefixWord ++ tailWord_131005).sum := by decide
  have hdescent : baseEnd_131005 < baseStart_131005 := by decide
  rcases family_descends (prefixWord ++ tailWord_131005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131016 : List Nat := [2, 1, 3, 1, 4, 3, 2, 1, 2, 2, 2]
def baseStart_131016 : Nat := 118140960795 + 131016 * 2 ^ 59
def prefixEnd_131016 : Nat := 4983230072969 + 3 ^ 40 * 131016 * 2
def baseEnd_131016 : Nat := 67274181429564632997475

theorem tailTrace_131016 : CollatzResearch.WordTrace tailWord_131016 prefixEnd_131016 67274181429564632997475 := by
  unfold tailWord_131016
  simp only [CollatzResearch.WordTrace]
  refine ⟨2389273046679441298242451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3185697395572588397656601 2389273046679441298242451)
  ·
    refine ⟨3583909570019161947363677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2389273046679441298242451 3583909570019161947363677)
    ·
      refine ⟨1343966088757185730261379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3583909570019161947363677 1343966088757185730261379)
      ·
        refine ⟨2015949133135778595392069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1343966088757185730261379 2015949133135778595392069)
        ·
          refine ⟨377990462462958486636013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2015949133135778595392069 377990462462958486636013)
          ·
            refine ⟨141746423423609432488505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 377990462462958486636013 141746423423609432488505)
            ·
              refine ⟨106309817567707074366379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141746423423609432488505 106309817567707074366379)
              ·
                refine ⟨159464726351560611549569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106309817567707074366379 159464726351560611549569)
                ·
                  refine ⟨119598544763670458662177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159464726351560611549569 119598544763670458662177)
                  ·
                    refine ⟨89698908572752843996633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119598544763670458662177 89698908572752843996633)
                    ·
                      refine ⟨67274181429564632997475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 89698908572752843996633 67274181429564632997475)
                      ·
                        rfl

theorem cell23_131016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 2, 2, 2].length) (baseStart_131016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131016 prefixEnd_131016 := by exact prefixLift 131016
  have htrace : WordTrace (prefixWord ++ tailWord_131016) baseStart_131016 baseEnd_131016 := by
    simpa [prefixWord, tailWord_131016, baseEnd_131016] using wordTrace_append hprefix tailTrace_131016
  have hstable : (prefixWord ++ tailWord_131016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131016).length < 2 ^ (prefixWord ++ tailWord_131016).sum := by decide
  have hdescent : baseEnd_131016 < baseStart_131016 := by decide
  rcases family_descends (prefixWord ++ tailWord_131016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131028 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_131028 : Nat := 118140960795 + 131028 * 2 ^ 59
def prefixEnd_131028 : Nat := 4983230072969 + 3 ^ 40 * 131028 * 2
def baseEnd_131028 : Nat := 67280343197418586047419

theorem tailTrace_131028 : CollatzResearch.WordTrace tailWord_131028 prefixEnd_131028 67280343197418586047419 := by
  unfold tailWord_131028
  simp only [CollatzResearch.WordTrace]
  refine ⟨2389491884657704322960869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3185989179543605763947825 2389491884657704322960869)
  ·
    refine ⟨448029728373319560555163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2389491884657704322960869 448029728373319560555163)
    ·
      refine ⟨672044592559979340832745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448029728373319560555163 672044592559979340832745)
      ·
        refine ⟨504033444419984505624559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 672044592559979340832745 504033444419984505624559)
        ·
          refine ⟨756050166629976758436839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504033444419984505624559 756050166629976758436839)
          ·
            refine ⟨1134075249944965137655259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 756050166629976758436839 1134075249944965137655259)
            ·
              refine ⟨1701112874917447706482889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1134075249944965137655259 1701112874917447706482889)
              ·
                refine ⟨1275834656188085779862167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1701112874917447706482889 1275834656188085779862167)
                ·
                  refine ⟨1913751984282128669793251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1275834656188085779862167 1913751984282128669793251)
                  ·
                    refine ⟨2870627976423193004689877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1913751984282128669793251 2870627976423193004689877)
                    ·
                      refine ⟨67280343197418586047419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 2870627976423193004689877 67280343197418586047419)
                      ·
                        rfl

theorem cell23_131028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_131028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131028 prefixEnd_131028 := by exact prefixLift 131028
  have htrace : WordTrace (prefixWord ++ tailWord_131028) baseStart_131028 baseEnd_131028 := by
    simpa [prefixWord, tailWord_131028, baseEnd_131028] using wordTrace_append hprefix tailTrace_131028
  have hstable : (prefixWord ++ tailWord_131028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131028).length < 2 ^ (prefixWord ++ tailWord_131028).sum := by decide
  have hdescent : baseEnd_131028 < baseStart_131028 := by decide
  rcases family_descends (prefixWord ++ tailWord_131028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131055 : List Nat := [1, 1, 2, 1, 4, 2, 2, 2, 2, 4, 2]
def baseStart_131055 : Nat := 118140960795 + 131055 * 2 ^ 59
def prefixEnd_131055 : Nat := 4983230072969 + 3 ^ 40 * 131055 * 2
def baseEnd_131055 : Nat := 67294207175089980409795

theorem tailTrace_131055 : CollatzResearch.WordTrace tailWord_131055 prefixEnd_131055 67294207175089980409795 := by
  unfold tailWord_131055
  simp only [CollatzResearch.WordTrace]
  refine ⟨4779968540217592257154619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3186645693478394838103079 4779968540217592257154619)
  ·
    refine ⟨7169952810326388385731929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4779968540217592257154619 7169952810326388385731929)
    ·
      refine ⟨5377464607744791289298947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7169952810326388385731929 5377464607744791289298947)
      ·
        refine ⟨8066196911617186933948421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5377464607744791289298947 8066196911617186933948421)
        ·
          refine ⟨1512411920928222550115329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8066196911617186933948421 1512411920928222550115329)
          ·
            refine ⟨1134308940696166912586497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1512411920928222550115329 1134308940696166912586497)
            ·
              refine ⟨850731705522125184439873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1134308940696166912586497 850731705522125184439873)
              ·
                refine ⟨638048779141593888329905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 850731705522125184439873 638048779141593888329905)
                ·
                  refine ⟨478536584356195416247429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 638048779141593888329905 478536584356195416247429)
                  ·
                    refine ⟨89725609566786640546393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 478536584356195416247429 89725609566786640546393)
                    ·
                      refine ⟨67294207175089980409795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 89725609566786640546393 67294207175089980409795)
                      ·
                        rfl

theorem cell23_131055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 4, 2].length) (baseStart_131055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131055 prefixEnd_131055 := by exact prefixLift 131055
  have htrace : WordTrace (prefixWord ++ tailWord_131055) baseStart_131055 baseEnd_131055 := by
    simpa [prefixWord, tailWord_131055, baseEnd_131055] using wordTrace_append hprefix tailTrace_131055
  have hstable : (prefixWord ++ tailWord_131055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131055).length < 2 ^ (prefixWord ++ tailWord_131055).sum := by decide
  have hdescent : baseEnd_131055 < baseStart_131055 := by decide
  rcases family_descends (prefixWord ++ tailWord_131055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131082 : List Nat := [3, 1, 2, 2, 4, 1, 1, 2, 3, 4]
def baseStart_131082 : Nat := 118140960795 + 131082 * 2 ^ 59
def prefixEnd_131082 : Nat := 4983230072969 + 3 ^ 40 * 131082 * 2
def baseEnd_131082 : Nat := 22436023717587124924057

theorem tailTrace_131082 : CollatzResearch.WordTrace tailWord_131082 prefixEnd_131082 22436023717587124924057 := by
  unfold tailWord_131082
  simp only [CollatzResearch.WordTrace]
  refine ⟨1195238327779943967096875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3187302207413183912258333 1195238327779943967096875)
  ·
    refine ⟨1792857491669915950645313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1195238327779943967096875 1792857491669915950645313)
    ·
      refine ⟨1344643118752436962983985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1792857491669915950645313 1344643118752436962983985)
      ·
        refine ⟨1008482339064327722237989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1344643118752436962983985 1008482339064327722237989)
        ·
          refine ⟨189090438574561447919623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1008482339064327722237989 189090438574561447919623)
          ·
            refine ⟨283635657861842171879435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189090438574561447919623 283635657861842171879435)
            ·
              refine ⟨425453486792763257819153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283635657861842171879435 425453486792763257819153)
              ·
                refine ⟨319090115094572443364365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 425453486792763257819153 319090115094572443364365)
                ·
                  refine ⟨119658793160464666261637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 319090115094572443364365 119658793160464666261637)
                  ·
                    refine ⟨22436023717587124924057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119658793160464666261637 22436023717587124924057)
                    ·
                      rfl

theorem cell23_131082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_131082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131082 prefixEnd_131082 := by exact prefixLift 131082
  have htrace : WordTrace (prefixWord ++ tailWord_131082) baseStart_131082 baseEnd_131082 := by
    simpa [prefixWord, tailWord_131082, baseEnd_131082] using wordTrace_append hprefix tailTrace_131082
  have hstable : (prefixWord ++ tailWord_131082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131082).length < 2 ^ (prefixWord ++ tailWord_131082).sum := by decide
  have hdescent : baseEnd_131082 < baseStart_131082 := by decide
  rcases family_descends (prefixWord ++ tailWord_131082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131088 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 3]
def baseStart_131088 : Nat := 118140960795 + 131088 * 2 ^ 59
def prefixEnd_131088 : Nat := 4983230072969 + 3 ^ 40 * 131088 * 2
def baseEnd_131088 : Nat := 67311152036688351297143

theorem tailTrace_131088 : CollatzResearch.WordTrace tailWord_131088 prefixEnd_131088 67311152036688351297143 := by
  unfold tailWord_131088
  simp only [CollatzResearch.WordTrace]
  refine ⟨2390586074549019446552959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3187448099398692595403945 2390586074549019446552959)
  ·
    refine ⟨3585879111823529169829439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2390586074549019446552959 3585879111823529169829439)
    ·
      refine ⟨5378818667735293754744159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3585879111823529169829439 5378818667735293754744159)
      ·
        refine ⟨8068228001602940632116239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5378818667735293754744159 8068228001602940632116239)
        ·
          refine ⟨12102342002404410948174359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8068228001602940632116239 12102342002404410948174359)
          ·
            refine ⟨18153513003606616422261539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12102342002404410948174359 18153513003606616422261539)
            ·
              refine ⟨27230269505409924633392309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18153513003606616422261539 27230269505409924633392309)
              ·
                refine ⟨2552837766132180434380529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27230269505409924633392309 2552837766132180434380529)
                ·
                  refine ⟨1914628324599135325785397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2552837766132180434380529 1914628324599135325785397)
                  ·
                    refine ⟨179496405431168936792381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1914628324599135325785397 179496405431168936792381)
                    ·
                      refine ⟨67311152036688351297143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 179496405431168936792381 67311152036688351297143)
                      ·
                        rfl

theorem cell23_131088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 3].length) (baseStart_131088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131088 prefixEnd_131088 := by exact prefixLift 131088
  have htrace : WordTrace (prefixWord ++ tailWord_131088) baseStart_131088 baseEnd_131088 := by
    simpa [prefixWord, tailWord_131088, baseEnd_131088] using wordTrace_append hprefix tailTrace_131088
  have hstable : (prefixWord ++ tailWord_131088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131088).length < 2 ^ (prefixWord ++ tailWord_131088).sum := by decide
  have hdescent : baseEnd_131088 < baseStart_131088 := by decide
  rcases family_descends (prefixWord ++ tailWord_131088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131112 : List Nat := [2, 1, 5, 3, 1, 1, 1, 1, 8]
def baseStart_131112 : Nat := 118140960795 + 131112 * 2 ^ 59
def prefixEnd_131112 : Nat := 4983230072969 + 3 ^ 40 * 131112 * 2
def baseEnd_131112 : Nat := 7480386174710695266337

theorem tailTrace_131112 : CollatzResearch.WordTrace tailWord_131112 prefixEnd_131112 7480386174710695266337 := by
  unfold tailWord_131112
  simp only [CollatzResearch.WordTrace]
  refine ⟨2391023750505545495989795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3188031667340727327986393 2391023750505545495989795)
  ·
    refine ⟨3586535625758318243984693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2391023750505545495989795 3586535625758318243984693)
    ·
      refine ⟨336237714914842335373565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3586535625758318243984693 336237714914842335373565)
      ·
        refine ⟨126089143093065875765087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336237714914842335373565 126089143093065875765087)
        ·
          refine ⟨189133714639598813647631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126089143093065875765087 189133714639598813647631)
          ·
            refine ⟨283700571959398220471447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189133714639598813647631 283700571959398220471447)
            ·
              refine ⟨425550857939097330707171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283700571959398220471447 425550857939097330707171)
              ·
                refine ⟨638326286908645996060757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425550857939097330707171 638326286908645996060757)
                ·
                  refine ⟨7480386174710695266337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 638326286908645996060757 7480386174710695266337)
                  ·
                    rfl

theorem cell23_131112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 8].length) (baseStart_131112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131112 prefixEnd_131112 := by exact prefixLift 131112
  have htrace : WordTrace (prefixWord ++ tailWord_131112) baseStart_131112 baseEnd_131112 := by
    simpa [prefixWord, tailWord_131112, baseEnd_131112] using wordTrace_append hprefix tailTrace_131112
  have hstable : (prefixWord ++ tailWord_131112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131112).length < 2 ^ (prefixWord ++ tailWord_131112).sum := by decide
  have hdescent : baseEnd_131112 < baseStart_131112 := by decide
  rcases family_descends (prefixWord ++ tailWord_131112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131122 : List Nat := [3, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3]
def baseStart_131122 : Nat := 118140960795 + 131122 * 2 ^ 59
def prefixEnd_131122 : Nat := 4983230072969 + 3 ^ 40 * 131122 * 2
def baseEnd_131122 : Nat := 67328610378941218271987

theorem tailTrace_131122 : CollatzResearch.WordTrace tailWord_131122 prefixEnd_131122 67328610378941218271987 := by
  unfold tailWord_131122
  simp only [CollatzResearch.WordTrace]
  refine ⟨1195603057743715674960905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3188274820649908466562413 1195603057743715674960905)
  ·
    refine ⟨896702293307786756220679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1195603057743715674960905 896702293307786756220679)
    ·
      refine ⟨1345053439961680134331019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 896702293307786756220679 1345053439961680134331019)
      ·
        refine ⟨2017580159942520201496529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1345053439961680134331019 2017580159942520201496529)
        ·
          refine ⟨1513185119956890151122397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2017580159942520201496529 1513185119956890151122397)
          ·
            refine ⟨567444419983833806670899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1513185119956890151122397 567444419983833806670899)
            ·
              refine ⟨851166629975750710006349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567444419983833806670899 851166629975750710006349)
              ·
                refine ⟨319187486240906516252381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 851166629975750710006349 319187486240906516252381)
                ·
                  refine ⟨119695307340339943594643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 319187486240906516252381 119695307340339943594643)
                  ·
                    refine ⟨179542961010509915391965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119695307340339943594643 179542961010509915391965)
                    ·
                      refine ⟨67328610378941218271987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 179542961010509915391965 67328610378941218271987)
                      ·
                        rfl

theorem cell23_131122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_131122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131122 prefixEnd_131122 := by exact prefixLift 131122
  have htrace : WordTrace (prefixWord ++ tailWord_131122) baseStart_131122 baseEnd_131122 := by
    simpa [prefixWord, tailWord_131122, baseEnd_131122] using wordTrace_append hprefix tailTrace_131122
  have hstable : (prefixWord ++ tailWord_131122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131122).length < 2 ^ (prefixWord ++ tailWord_131122).sum := by decide
  have hdescent : baseEnd_131122 < baseStart_131122 := by decide
  rcases family_descends (prefixWord ++ tailWord_131122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131145 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 2, 6, 2]
def baseStart_131145 : Nat := 118140960795 + 131145 * 2 ^ 59
def prefixEnd_131145 : Nat := 4983230072969 + 3 ^ 40 * 131145 * 2
def baseEnd_131145 : Nat := 67340420433994628284381

theorem tailTrace_131145 : CollatzResearch.WordTrace tailWord_131145 prefixEnd_131145 67340420433994628284381 := by
  unfold tailWord_131145
  simp only [CollatzResearch.WordTrace]
  refine ⟨4783251109891537627930889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3188834073261025085287259 4783251109891537627930889)
  ·
    refine ⟨3587438332418653220948167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4783251109891537627930889 3587438332418653220948167)
    ·
      refine ⟨5381157498627979831422251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3587438332418653220948167 5381157498627979831422251)
      ·
        refine ⟨8071736247941969747133377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5381157498627979831422251 8071736247941969747133377)
        ·
          refine ⟨6053802185956477310350033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8071736247941969747133377 6053802185956477310350033)
          ·
            refine ⟨4540351639467357982762525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6053802185956477310350033 4540351639467357982762525)
            ·
              refine ⟨1702631864800259243535947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4540351639467357982762525 1702631864800259243535947)
              ·
                refine ⟨2553947797200388865303921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1702631864800259243535947 2553947797200388865303921)
                ·
                  refine ⟨1915460847900291648977941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2553947797200388865303921 1915460847900291648977941)
                  ·
                    refine ⟨89787227245326171045841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1915460847900291648977941 89787227245326171045841)
                    ·
                      refine ⟨67340420433994628284381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 89787227245326171045841 67340420433994628284381)
                      ·
                        rfl

theorem cell23_131145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 6, 2].length) (baseStart_131145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131145 prefixEnd_131145 := by exact prefixLift 131145
  have htrace : WordTrace (prefixWord ++ tailWord_131145) baseStart_131145 baseEnd_131145 := by
    simpa [prefixWord, tailWord_131145, baseEnd_131145] using wordTrace_append hprefix tailTrace_131145
  have hstable : (prefixWord ++ tailWord_131145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131145).length < 2 ^ (prefixWord ++ tailWord_131145).sum := by decide
  have hdescent : baseEnd_131145 < baseStart_131145 := by decide
  rcases family_descends (prefixWord ++ tailWord_131145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131149 : List Nat := [1, 6, 1, 1, 1, 1, 2, 3, 2, 3, 2]
def baseStart_131149 : Nat := 118140960795 + 131149 * 2 ^ 59
def prefixEnd_131149 : Nat := 4983230072969 + 3 ^ 40 * 131149 * 2
def baseEnd_131149 : Nat := 67342474356612612634363

theorem tailTrace_131149 : CollatzResearch.WordTrace tailWord_131149 prefixEnd_131149 67342474356612612634363 := by
  unfold tailWord_131149
  simp only [CollatzResearch.WordTrace]
  refine ⟨4783397001877046311076501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3188931334584697540717667 4783397001877046311076501)
  ·
    refine ⟨224221734462986545831711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4783397001877046311076501 224221734462986545831711)
    ·
      refine ⟨336332601694479818747567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224221734462986545831711 336332601694479818747567)
      ·
        refine ⟨504498902541719728121351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336332601694479818747567 504498902541719728121351)
        ·
          refine ⟨756748353812579592182027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504498902541719728121351 756748353812579592182027)
          ·
            refine ⟨1135122530718869388273041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 756748353812579592182027 1135122530718869388273041)
            ·
              refine ⟨851341898039152041204781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1135122530718869388273041 851341898039152041204781)
              ·
                refine ⟨319253211764682015451793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 851341898039152041204781 319253211764682015451793)
                ·
                  refine ⟨239439908823511511588845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319253211764682015451793 239439908823511511588845)
                  ·
                    refine ⟨89789965808816816845817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 239439908823511511588845 89789965808816816845817)
                    ·
                      refine ⟨67342474356612612634363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 89789965808816816845817 67342474356612612634363)
                      ·
                        rfl

theorem cell23_131149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_131149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131149 prefixEnd_131149 := by exact prefixLift 131149
  have htrace : WordTrace (prefixWord ++ tailWord_131149) baseStart_131149 baseEnd_131149 := by
    simpa [prefixWord, tailWord_131149, baseEnd_131149] using wordTrace_append hprefix tailTrace_131149
  have hstable : (prefixWord ++ tailWord_131149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131149).length < 2 ^ (prefixWord ++ tailWord_131149).sum := by decide
  have hdescent : baseEnd_131149 < baseStart_131149 := by decide
  rcases family_descends (prefixWord ++ tailWord_131149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131168 : List Nat := [2, 1, 1, 3, 2, 3, 11]
def baseStart_131168 : Nat := 118140960795 + 131168 * 2 ^ 59
def prefixEnd_131168 : Nat := 4983230072969 + 3 ^ 40 * 131168 * 2
def baseEnd_131168 : Nat := 831509018383309114775

theorem tailTrace_131168 : CollatzResearch.WordTrace tailWord_131168 prefixEnd_131168 831509018383309114775 := by
  unfold tailWord_131168
  simp only [CollatzResearch.WordTrace]
  refine ⟨2392044994404106278009079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3189393325872141704012105 2392044994404106278009079)
  ·
    refine ⟨3588067491606159417013619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2392044994404106278009079 3588067491606159417013619)
    ·
      refine ⟨5382101237409239125520429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3588067491606159417013619 5382101237409239125520429)
      ·
        refine ⟨2018287964028464672070161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5382101237409239125520429 2018287964028464672070161)
        ·
          refine ⟨1513715973021348504052621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2018287964028464672070161 1513715973021348504052621)
          ·
            refine ⟨567643489883005689019733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1513715973021348504052621 567643489883005689019733)
            ·
              refine ⟨831509018383309114775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 567643489883005689019733 831509018383309114775)
              ·
                rfl

theorem cell23_131168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 11].length) (baseStart_131168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131168 prefixEnd_131168 := by exact prefixLift 131168
  have htrace : WordTrace (prefixWord ++ tailWord_131168) baseStart_131168 baseEnd_131168 := by
    simpa [prefixWord, tailWord_131168, baseEnd_131168] using wordTrace_append hprefix tailTrace_131168
  have hstable : (prefixWord ++ tailWord_131168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131168).length < 2 ^ (prefixWord ++ tailWord_131168).sum := by decide
  have hdescent : baseEnd_131168 < baseStart_131168 := by decide
  rcases family_descends (prefixWord ++ tailWord_131168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131182 : List Nat := [4, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3]
def baseStart_131182 : Nat := 118140960795 + 131182 * 2 ^ 59
def prefixEnd_131182 : Nat := 4983230072969 + 3 ^ 40 * 131182 * 2
def baseEnd_131182 : Nat := 67359419218210983521711

theorem tailTrace_131182 : CollatzResearch.WordTrace tailWord_131182 prefixEnd_131182 67359419218210983521711 := by
  unfold tailWord_131182
  simp only [CollatzResearch.WordTrace]
  refine ⟨598075076344686618378475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3189733740504995298018533 598075076344686618378475)
  ·
    refine ⟨897112614517029927567713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 598075076344686618378475 897112614517029927567713)
    ·
      refine ⟨672834460887772445675785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 897112614517029927567713 672834460887772445675785)
      ·
        refine ⟨504625845665829334256839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 672834460887772445675785 504625845665829334256839)
        ·
          refine ⟨756938768498744001385259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504625845665829334256839 756938768498744001385259)
          ·
            refine ⟨1135408152748116002077889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 756938768498744001385259 1135408152748116002077889)
            ·
              refine ⟨851556114561087001558417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1135408152748116002077889 851556114561087001558417)
              ·
                refine ⟨638667085920815251168813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 851556114561087001558417 638667085920815251168813)
                ·
                  refine ⟨239500157220305719188305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 638667085920815251168813 239500157220305719188305)
                  ·
                    refine ⟨179625117915229289391229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 239500157220305719188305 179625117915229289391229)
                    ·
                      refine ⟨67359419218210983521711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 179625117915229289391229 67359419218210983521711)
                      ·
                        rfl

theorem cell23_131182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_131182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131182 prefixEnd_131182 := by exact prefixLift 131182
  have htrace : WordTrace (prefixWord ++ tailWord_131182) baseStart_131182 baseEnd_131182 := by
    simpa [prefixWord, tailWord_131182, baseEnd_131182] using wordTrace_append hprefix tailTrace_131182
  have hstable : (prefixWord ++ tailWord_131182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131182).length < 2 ^ (prefixWord ++ tailWord_131182).sum := by decide
  have hdescent : baseEnd_131182 < baseStart_131182 := by decide
  rcases family_descends (prefixWord ++ tailWord_131182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131229 : List Nat := [1, 4, 2, 1, 1, 3, 1, 4, 2, 1, 3]
def baseStart_131229 : Nat := 118140960795 + 131229 * 2 ^ 59
def prefixEnd_131229 : Nat := 4983230072969 + 3 ^ 40 * 131229 * 2
def baseEnd_131229 : Nat := 67383552808972299633995

theorem tailTrace_131229 : CollatzResearch.WordTrace tailWord_131229 prefixEnd_131229 67383552808972299633995 := by
  unfold tailWord_131229
  simp only [CollatzResearch.WordTrace]
  refine ⟨4786314841587219973988741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3190876561058146649325827 4786314841587219973988741)
  ·
    refine ⟨897434032797603745122889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4786314841587219973988741 897434032797603745122889)
    ·
      refine ⟨673075524598202808842167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 897434032797603745122889 673075524598202808842167)
      ·
        refine ⟨1009613286897304213263251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673075524598202808842167 1009613286897304213263251)
        ·
          refine ⟨1514419930345956319894877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1009613286897304213263251 1514419930345956319894877)
          ·
            refine ⟨567907473879733619960579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1514419930345956319894877 567907473879733619960579)
            ·
              refine ⟨851861210819600429940869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567907473879733619960579 851861210819600429940869)
              ·
                refine ⟨159723977028675080613913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 851861210819600429940869 159723977028675080613913)
                ·
                  refine ⟨119792982771506310460435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159723977028675080613913 119792982771506310460435)
                  ·
                    refine ⟨179689474157259465690653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119792982771506310460435 179689474157259465690653)
                    ·
                      refine ⟨67383552808972299633995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 179689474157259465690653 67383552808972299633995)
                      ·
                        rfl

theorem cell23_131229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_131229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131229 prefixEnd_131229 := by exact prefixLift 131229
  have htrace : WordTrace (prefixWord ++ tailWord_131229) baseStart_131229 baseEnd_131229 := by
    simpa [prefixWord, tailWord_131229, baseEnd_131229] using wordTrace_append hprefix tailTrace_131229
  have hstable : (prefixWord ++ tailWord_131229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131229).length < 2 ^ (prefixWord ++ tailWord_131229).sum := by decide
  have hdescent : baseEnd_131229 < baseStart_131229 := by decide
  rcases family_descends (prefixWord ++ tailWord_131229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131230 : List Nat := [4, 3, 1, 1, 3, 1, 1, 4, 1, 2, 2]
def baseStart_131230 : Nat := 118140960795 + 131230 * 2 ^ 59
def prefixEnd_131230 : Nat := 4983230072969 + 3 ^ 40 * 131230 * 2
def baseEnd_131230 : Nat := 67384066289626795721491

theorem tailTrace_131230 : CollatzResearch.WordTrace tailWord_131230 prefixEnd_131230 67384066289626795721491 := by
  unfold tailWord_131230
  simp only [CollatzResearch.WordTrace]
  refine ⟨598293914322949643096893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3190900876389064763183429 598293914322949643096893)
  ·
    refine ⟨224360217871106116161335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 598293914322949643096893 224360217871106116161335)
    ·
      refine ⟨336540326806659174242003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224360217871106116161335 336540326806659174242003)
      ·
        refine ⟨504810490209988761363005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336540326806659174242003 504810490209988761363005)
        ·
          refine ⟨189303933828745785511127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 504810490209988761363005 189303933828745785511127)
          ·
            refine ⟨283955900743118678266691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189303933828745785511127 283955900743118678266691)
            ·
              refine ⟨425933851114678017400037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283955900743118678266691 425933851114678017400037)
              ·
                refine ⟨79862597084002128262507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 425933851114678017400037 79862597084002128262507)
                ·
                  refine ⟨119793895626003192393761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79862597084002128262507 119793895626003192393761)
                  ·
                    refine ⟨89845421719502394295321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119793895626003192393761 89845421719502394295321)
                    ·
                      refine ⟨67384066289626795721491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 89845421719502394295321 67384066289626795721491)
                      ·
                        rfl

theorem cell23_131230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_131230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131230 prefixEnd_131230 := by exact prefixLift 131230
  have htrace : WordTrace (prefixWord ++ tailWord_131230) baseStart_131230 baseEnd_131230 := by
    simpa [prefixWord, tailWord_131230, baseEnd_131230] using wordTrace_append hprefix tailTrace_131230
  have hstable : (prefixWord ++ tailWord_131230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131230).length < 2 ^ (prefixWord ++ tailWord_131230).sum := by decide
  have hdescent : baseEnd_131230 < baseStart_131230 := by decide
  rcases family_descends (prefixWord ++ tailWord_131230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131282 : List Nat := [3, 2, 2, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_131282 : Nat := 118140960795 + 131282 * 2 ^ 59
def prefixEnd_131282 : Nat := 4983230072969 + 3 ^ 40 * 131282 * 2
def baseEnd_131282 : Nat := 67410767283660592271251

theorem tailTrace_131282 : CollatzResearch.WordTrace tailWord_131282 prefixEnd_131282 67410767283660592271251 := by
  unfold tailWord_131282
  simp only [CollatzResearch.WordTrace]
  refine ⟨1197061977598802506417025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3192165273596806683778733 1197061977598802506417025)
  ·
    refine ⟨897796483199101879812769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1197061977598802506417025 897796483199101879812769)
    ·
      refine ⟨673347362399326409859577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 897796483199101879812769 673347362399326409859577)
      ·
        refine ⟨505010521799494807394683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 673347362399326409859577 505010521799494807394683)
        ·
          refine ⟨757515782699242211092025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505010521799494807394683 757515782699242211092025)
          ·
            refine ⟨568136837024431658319019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 757515782699242211092025 568136837024431658319019)
            ·
              refine ⟨852205255536647487478529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568136837024431658319019 852205255536647487478529)
              ·
                refine ⟨639153941652485615608897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 852205255536647487478529 639153941652485615608897)
                ·
                  refine ⟨479365456239364211706673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 639153941652485615608897 479365456239364211706673)
                  ·
                    refine ⟨359524092179523158780005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 479365456239364211706673 359524092179523158780005)
                    ·
                      refine ⟨67410767283660592271251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 359524092179523158780005 67410767283660592271251)
                      ·
                        rfl

theorem cell23_131282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_131282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131282 prefixEnd_131282 := by exact prefixLift 131282
  have htrace : WordTrace (prefixWord ++ tailWord_131282) baseStart_131282 baseEnd_131282 := by
    simpa [prefixWord, tailWord_131282, baseEnd_131282] using wordTrace_append hprefix tailTrace_131282
  have hstable : (prefixWord ++ tailWord_131282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131282).length < 2 ^ (prefixWord ++ tailWord_131282).sum := by decide
  have hdescent : baseEnd_131282 < baseStart_131282 := by decide
  rcases family_descends (prefixWord ++ tailWord_131282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131305 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 4, 5]
def baseStart_131305 : Nat := 118140960795 + 131305 * 2 ^ 59
def prefixEnd_131305 : Nat := 4983230072969 + 3 ^ 40 * 131305 * 2
def baseEnd_131305 : Nat := 22474192446238000761215

theorem tailTrace_131305 : CollatzResearch.WordTrace tailWord_131305 prefixEnd_131305 22474192446238000761215 := by
  unfold tailWord_131305
  simp only [CollatzResearch.WordTrace]
  refine ⟨4789086789311884953755369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3192724526207923302503579 4789086789311884953755369)
  ·
    refine ⟨3591815091983913715316527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4789086789311884953755369 3591815091983913715316527)
    ·
      refine ⟨5387722637975870572974791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3591815091983913715316527 5387722637975870572974791)
      ·
        refine ⟨8081583956963805859462187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5387722637975870572974791 8081583956963805859462187)
        ·
          refine ⟨12122375935445708789193281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8081583956963805859462187 12122375935445708789193281)
          ·
            refine ⟨9091781951584281591894961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12122375935445708789193281 9091781951584281591894961)
            ·
              refine ⟨6818836463688211193921221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9091781951584281591894961 6818836463688211193921221)
              ·
                refine ⟨1278531836941539598860229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6818836463688211193921221 1278531836941539598860229)
                ·
                  refine ⟨239724719426538674786293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1278531836941539598860229 239724719426538674786293)
                  ·
                    refine ⟨22474192446238000761215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 239724719426538674786293 22474192446238000761215)
                    ·
                      rfl

theorem cell23_131305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 5].length) (baseStart_131305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131305 prefixEnd_131305 := by exact prefixLift 131305
  have htrace : WordTrace (prefixWord ++ tailWord_131305) baseStart_131305 baseEnd_131305 := by
    simpa [prefixWord, tailWord_131305, baseEnd_131305] using wordTrace_append hprefix tailTrace_131305
  have hstable : (prefixWord ++ tailWord_131305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131305).length < 2 ^ (prefixWord ++ tailWord_131305).sum := by decide
  have hdescent : baseEnd_131305 < baseStart_131305 := by decide
  rcases family_descends (prefixWord ++ tailWord_131305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131312 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 2, 5, 2]
def baseStart_131312 : Nat := 118140960795 + 131312 * 2 ^ 59
def prefixEnd_131312 : Nat := 4983230072969 + 3 ^ 40 * 131312 * 2
def baseEnd_131312 : Nat := 67426171703295474896113

theorem tailTrace_131312 : CollatzResearch.WordTrace tailWord_131312 prefixEnd_131312 67426171703295474896113 := by
  unfold tailWord_131312
  simp only [CollatzResearch.WordTrace]
  refine ⟨2394671050143262574630095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3192894733524350099506793 2394671050143262574630095)
  ·
    refine ⟨3592006575214893861945143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2394671050143262574630095 3592006575214893861945143)
    ·
      refine ⟨5388009862822340792917715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3592006575214893861945143 5388009862822340792917715)
      ·
        refine ⟨8082014794233511189376573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5388009862822340792917715 8082014794233511189376573)
        ·
          refine ⟨3030755547837566696016215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8082014794233511189376573 3030755547837566696016215)
          ·
            refine ⟨4546133321756350044024323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3030755547837566696016215 4546133321756350044024323)
            ·
              refine ⟨6819199982634525066036485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4546133321756350044024323 6819199982634525066036485)
              ·
                refine ⟨1278599996743973449881841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6819199982634525066036485 1278599996743973449881841)
                ·
                  refine ⟨958949997557980087411381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1278599996743973449881841 958949997557980087411381)
                  ·
                    refine ⟨89901562271060633194817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 958949997557980087411381 89901562271060633194817)
                    ·
                      refine ⟨67426171703295474896113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 89901562271060633194817 67426171703295474896113)
                      ·
                        rfl

theorem cell23_131312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 2, 5, 2].length) (baseStart_131312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131312 prefixEnd_131312 := by exact prefixLift 131312
  have htrace : WordTrace (prefixWord ++ tailWord_131312) baseStart_131312 baseEnd_131312 := by
    simpa [prefixWord, tailWord_131312, baseEnd_131312] using wordTrace_append hprefix tailTrace_131312
  have hstable : (prefixWord ++ tailWord_131312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131312).length < 2 ^ (prefixWord ++ tailWord_131312).sum := by decide
  have hdescent : baseEnd_131312 < baseStart_131312 := by decide
  rcases family_descends (prefixWord ++ tailWord_131312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131355 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 6]
def baseStart_131355 : Nat := 118140960795 + 131355 * 2 ^ 59
def prefixEnd_131355 : Nat := 4983230072969 + 3 ^ 40 * 131355 * 2
def baseEnd_131355 : Nat := 67448251371438806658415

theorem tailTrace_131355 : CollatzResearch.WordTrace tailWord_131355 prefixEnd_131355 67448251371438806658415 := by
  unfold tailWord_131355
  simp only [CollatzResearch.WordTrace]
  refine ⟨4790910439130743493075519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3193940292753828995383679 4790910439130743493075519)
  ·
    refine ⟨7186365658696115239613279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4790910439130743493075519 7186365658696115239613279)
    ·
      refine ⟨10779548488044172859419919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7186365658696115239613279 10779548488044172859419919)
      ·
        refine ⟨16169322732066259289129879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10779548488044172859419919 16169322732066259289129879)
        ·
          refine ⟨24253984098099388933694819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16169322732066259289129879 24253984098099388933694819)
          ·
            refine ⟨36380976147149083400542229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24253984098099388933694819 36380976147149083400542229)
            ·
              refine ⟨1705358256897613284400417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36380976147149083400542229 1705358256897613284400417)
              ·
                refine ⟨1279018692673209963300313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1705358256897613284400417 1279018692673209963300313)
                ·
                  refine ⟨959264019504907472475235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1279018692673209963300313 959264019504907472475235)
                  ·
                    refine ⟨1438896029257361208712853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 959264019504907472475235 1438896029257361208712853)
                    ·
                      refine ⟨67448251371438806658415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1438896029257361208712853 67448251371438806658415)
                      ·
                        rfl

theorem cell23_131355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 6].length) (baseStart_131355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131355 prefixEnd_131355 := by exact prefixLift 131355
  have htrace : WordTrace (prefixWord ++ tailWord_131355) baseStart_131355 baseEnd_131355 := by
    simpa [prefixWord, tailWord_131355, baseEnd_131355] using wordTrace_append hprefix tailTrace_131355
  have hstable : (prefixWord ++ tailWord_131355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131355).length < 2 ^ (prefixWord ++ tailWord_131355).sum := by decide
  have hdescent : baseEnd_131355 < baseStart_131355 := by decide
  rcases family_descends (prefixWord ++ tailWord_131355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131379 : List Nat := [1, 1, 1, 2, 5, 1, 4, 1, 2, 2, 3]
def baseStart_131379 : Nat := 118140960795 + 131379 * 2 ^ 59
def prefixEnd_131379 : Nat := 4983230072969 + 3 ^ 40 * 131379 * 2
def baseEnd_131379 : Nat := 67460574907146712758305

theorem tailTrace_131379 : CollatzResearch.WordTrace tailWord_131379 prefixEnd_131379 67460574907146712758305 := by
  unfold tailWord_131379
  simp only [CollatzResearch.WordTrace]
  refine ⟨4791785791043795591949191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3194523860695863727966127 4791785791043795591949191)
  ·
    refine ⟨7187678686565693387923787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4791785791043795591949191 7187678686565693387923787)
    ·
      refine ⟨10781518029848540081885681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7187678686565693387923787 10781518029848540081885681)
      ·
        refine ⟨8086138522386405061414261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10781518029848540081885681 8086138522386405061414261)
        ·
          refine ⟨758075486473725474507587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8086138522386405061414261 758075486473725474507587)
          ·
            refine ⟨1137113229710588211761381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758075486473725474507587 1137113229710588211761381)
            ·
              refine ⟨213208730570735289705259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1137113229710588211761381 213208730570735289705259)
              ·
                refine ⟨319813095856102934557889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213208730570735289705259 319813095856102934557889)
                ·
                  refine ⟨239859821892077200918417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319813095856102934557889 239859821892077200918417)
                  ·
                    refine ⟨179894866419057900688813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 239859821892077200918417 179894866419057900688813)
                    ·
                      refine ⟨67460574907146712758305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 179894866419057900688813 67460574907146712758305)
                      ·
                        rfl

theorem cell23_131379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2, 3].length) (baseStart_131379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131379 prefixEnd_131379 := by exact prefixLift 131379
  have htrace : WordTrace (prefixWord ++ tailWord_131379) baseStart_131379 baseEnd_131379 := by
    simpa [prefixWord, tailWord_131379, baseEnd_131379] using wordTrace_append hprefix tailTrace_131379
  have hstable : (prefixWord ++ tailWord_131379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131379).length < 2 ^ (prefixWord ++ tailWord_131379).sum := by decide
  have hdescent : baseEnd_131379 < baseStart_131379 := by decide
  rcases family_descends (prefixWord ++ tailWord_131379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131426 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 5, 1, 3]
def baseStart_131426 : Nat := 118140960795 + 131426 * 2 ^ 59
def prefixEnd_131426 : Nat := 4983230072969 + 3 ^ 40 * 131426 * 2
def baseEnd_131426 : Nat := 67484708497908028870589

theorem tailTrace_131426 : CollatzResearch.WordTrace tailWord_131426 prefixEnd_131426 67484708497908028870589 := by
  unfold tailWord_131426
  simp only [CollatzResearch.WordTrace]
  refine ⟨1198375005468380654727533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3195666681249015079273421 1198375005468380654727533)
  ·
    refine ⟨449390627050642745522825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1198375005468380654727533 449390627050642745522825)
    ·
      refine ⟨337042970287982059142119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449390627050642745522825 337042970287982059142119)
      ·
        refine ⟨505564455431973088713179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337042970287982059142119 505564455431973088713179)
        ·
          refine ⟨758346683147959633069769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505564455431973088713179 758346683147959633069769)
          ·
            refine ⟨568760012360969724802327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 758346683147959633069769 568760012360969724802327)
            ·
              refine ⟨853140018541454587203491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568760012360969724802327 853140018541454587203491)
              ·
                refine ⟨1279710027812181880805237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 853140018541454587203491 1279710027812181880805237)
                ·
                  refine ⟨119972815107392051325491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1279710027812181880805237 119972815107392051325491)
                  ·
                    refine ⟨179959222661088076988237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119972815107392051325491 179959222661088076988237)
                    ·
                      refine ⟨67484708497908028870589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 179959222661088076988237 67484708497908028870589)
                      ·
                        rfl

theorem cell23_131426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_131426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131426 prefixEnd_131426 := by exact prefixLift 131426
  have htrace : WordTrace (prefixWord ++ tailWord_131426) baseStart_131426 baseEnd_131426 := by
    simpa [prefixWord, tailWord_131426, baseEnd_131426] using wordTrace_append hprefix tailTrace_131426
  have hstable : (prefixWord ++ tailWord_131426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131426).length < 2 ^ (prefixWord ++ tailWord_131426).sum := by decide
  have hdescent : baseEnd_131426 < baseStart_131426 := by decide
  rcases family_descends (prefixWord ++ tailWord_131426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131436 : List Nat := [2, 2, 1, 1, 6, 1, 1, 1, 1, 5, 2]
def baseStart_131436 : Nat := 118140960795 + 131436 * 2 ^ 59
def prefixEnd_131436 : Nat := 4983230072969 + 3 ^ 40 * 131436 * 2
def baseEnd_131436 : Nat := 67489843304452989745543

theorem tailTrace_131436 : CollatzResearch.WordTrace tailWord_131436 prefixEnd_131436 67489843304452989745543 := by
  unfold tailWord_131436
  simp only [CollatzResearch.WordTrace]
  refine ⟨2396932375918647163387081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3195909834558196217849441 2396932375918647163387081)
  ·
    refine ⟨1797699281938985372540311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2396932375918647163387081 1797699281938985372540311)
    ·
      refine ⟨2696548922908478058810467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1797699281938985372540311 2696548922908478058810467)
      ·
        refine ⟨4044823384362717088215701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2696548922908478058810467 4044823384362717088215701)
        ·
          refine ⟨189601096142002363510111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4044823384362717088215701 189601096142002363510111)
          ·
            refine ⟨284401644213003545265167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189601096142002363510111 284401644213003545265167)
            ·
              refine ⟨426602466319505317897751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284401644213003545265167 426602466319505317897751)
              ·
                refine ⟨639903699479257976846627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426602466319505317897751 639903699479257976846627)
                ·
                  refine ⟨959855549218886965269941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 639903699479257976846627 959855549218886965269941)
                  ·
                    refine ⟨89986457739270652994057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 959855549218886965269941 89986457739270652994057)
                    ·
                      refine ⟨67489843304452989745543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 89986457739270652994057 67489843304452989745543)
                      ·
                        rfl

theorem cell23_131436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 5, 2].length) (baseStart_131436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131436 prefixEnd_131436 := by exact prefixLift 131436
  have htrace : WordTrace (prefixWord ++ tailWord_131436) baseStart_131436 baseEnd_131436 := by
    simpa [prefixWord, tailWord_131436, baseEnd_131436] using wordTrace_append hprefix tailTrace_131436
  have hstable : (prefixWord ++ tailWord_131436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131436).length < 2 ^ (prefixWord ++ tailWord_131436).sum := by decide
  have hdescent : baseEnd_131436 < baseStart_131436 := by decide
  rcases family_descends (prefixWord ++ tailWord_131436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131479 : List Nat := [1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 4]
def baseStart_131479 : Nat := 118140960795 + 131479 * 2 ^ 59
def prefixEnd_131479 : Nat := 4983230072969 + 3 ^ 40 * 131479 * 2
def baseEnd_131479 : Nat := 67511922972596321507845

theorem tailTrace_131479 : CollatzResearch.WordTrace tailWord_131479 prefixEnd_131479 67511922972596321507845 := by
  unfold tailWord_131479
  simp only [CollatzResearch.WordTrace]
  refine ⟨4795433090681512670589491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3196955393787675113726327 4795433090681512670589491)
  ·
    refine ⟨7193149636022269005884237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4795433090681512670589491 7193149636022269005884237)
    ·
      refine ⟨2697431113508350877206589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7193149636022269005884237 2697431113508350877206589)
      ·
        refine ⟨1011536667565631578952471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2697431113508350877206589 1011536667565631578952471)
        ·
          refine ⟨1517305001348447368428707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1011536667565631578952471 1517305001348447368428707)
          ·
            refine ⟨2275957502022671052643061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1517305001348447368428707 2275957502022671052643061)
            ·
              refine ⟨213371015814625411185287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2275957502022671052643061 213371015814625411185287)
              ·
                refine ⟨320056523721938116777931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213371015814625411185287 320056523721938116777931)
                ·
                  refine ⟨480084785582907175166897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 320056523721938116777931 480084785582907175166897)
                  ·
                    refine ⟨360063589187180381375173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 480084785582907175166897 360063589187180381375173)
                    ·
                      refine ⟨67511922972596321507845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 360063589187180381375173 67511922972596321507845)
                      ·
                        rfl

theorem cell23_131479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_131479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131479 prefixEnd_131479 := by exact prefixLift 131479
  have htrace : WordTrace (prefixWord ++ tailWord_131479) baseStart_131479 baseEnd_131479 := by
    simpa [prefixWord, tailWord_131479, baseEnd_131479] using wordTrace_append hprefix tailTrace_131479
  have hstable : (prefixWord ++ tailWord_131479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131479).length < 2 ^ (prefixWord ++ tailWord_131479).sum := by decide
  have hdescent : baseEnd_131479 < baseStart_131479 := by decide
  rcases family_descends (prefixWord ++ tailWord_131479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131512 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 4, 2, 5]
def baseStart_131512 : Nat := 118140960795 + 131512 * 2 ^ 59
def prefixEnd_131512 : Nat := 4983230072969 + 3 ^ 40 * 131512 * 2
def baseEnd_131512 : Nat := 67528867834194692395193

theorem tailTrace_131512 : CollatzResearch.WordTrace tailWord_131512 prefixEnd_131512 67528867834194692395193 := by
  unfold tailWord_131512
  simp only [CollatzResearch.WordTrace]
  refine ⟨2398318349780979653270395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3197757799707972871027193 2398318349780979653270395)
  ·
    refine ⟨3597477524671469479905593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2398318349780979653270395 3597477524671469479905593)
    ·
      refine ⟨2698108143503602109929195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3597477524671469479905593 2698108143503602109929195)
      ·
        refine ⟨4047162215255403164893793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2698108143503602109929195 4047162215255403164893793)
        ·
          refine ⟨3035371661441552373670345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4047162215255403164893793 3035371661441552373670345)
          ·
            refine ⟨2276528746081164280252759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3035371661441552373670345 2276528746081164280252759)
            ·
              refine ⟨3414793119121746420379139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2276528746081164280252759 3414793119121746420379139)
              ·
                refine ⟨5122189678682619630568709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3414793119121746420379139 5122189678682619630568709)
                ·
                  refine ⟨960410564752991180731633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5122189678682619630568709 960410564752991180731633)
                  ·
                    refine ⟨720307923564743385548725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 960410564752991180731633 720307923564743385548725)
                    ·
                      refine ⟨67528867834194692395193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 720307923564743385548725 67528867834194692395193)
                      ·
                        rfl

theorem cell23_131512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_131512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131512 prefixEnd_131512 := by exact prefixLift 131512
  have htrace : WordTrace (prefixWord ++ tailWord_131512) baseStart_131512 baseEnd_131512 := by
    simpa [prefixWord, tailWord_131512, baseEnd_131512] using wordTrace_append hprefix tailTrace_131512
  have hstable : (prefixWord ++ tailWord_131512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131512).length < 2 ^ (prefixWord ++ tailWord_131512).sum := by decide
  have hdescent : baseEnd_131512 < baseStart_131512 := by decide
  rcases family_descends (prefixWord ++ tailWord_131512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131517 : List Nat := [1, 4, 1, 2, 2, 3, 3, 2, 1, 2, 2]
def baseStart_131517 : Nat := 118140960795 + 131517 * 2 ^ 59
def prefixEnd_131517 : Nat := 4983230072969 + 3 ^ 40 * 131517 * 2
def baseEnd_131517 : Nat := 67531435237467172832671

theorem tailTrace_131517 : CollatzResearch.WordTrace tailWord_131517 prefixEnd_131517 67531435237467172832671 := by
  unfold tailWord_131517
  simp only [CollatzResearch.WordTrace]
  refine ⟨4796819064543845160472805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3197879376362563440315203 4796819064543845160472805)
  ·
    refine ⟨899403574601970967588651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4796819064543845160472805 899403574601970967588651)
    ·
      refine ⟨1349105361902956451382977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 899403574601970967588651 1349105361902956451382977)
      ·
        refine ⟨1011829021427217338537233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1349105361902956451382977 1011829021427217338537233)
        ·
          refine ⟨758871766070413003902925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1011829021427217338537233 758871766070413003902925)
          ·
            refine ⟨284576912276404876463597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 758871766070413003902925 284576912276404876463597)
            ·
              refine ⟨106716342103651828673849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284576912276404876463597 106716342103651828673849)
              ·
                refine ⟨80037256577738871505387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106716342103651828673849 80037256577738871505387)
                ·
                  refine ⟨120055884866608307258081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80037256577738871505387 120055884866608307258081)
                  ·
                    refine ⟨90041913649956230443561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120055884866608307258081 90041913649956230443561)
                    ·
                      refine ⟨67531435237467172832671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 90041913649956230443561 67531435237467172832671)
                      ·
                        rfl

theorem cell23_131517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_131517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131517 prefixEnd_131517 := by exact prefixLift 131517
  have htrace : WordTrace (prefixWord ++ tailWord_131517) baseStart_131517 baseEnd_131517 := by
    simpa [prefixWord, tailWord_131517, baseEnd_131517] using wordTrace_append hprefix tailTrace_131517
  have hstable : (prefixWord ++ tailWord_131517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131517).length < 2 ^ (prefixWord ++ tailWord_131517).sum := by decide
  have hdescent : baseEnd_131517 < baseStart_131517 := by decide
  rcases family_descends (prefixWord ++ tailWord_131517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131559 : List Nat := [1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_131559 : Nat := 118140960795 + 131559 * 2 ^ 59
def prefixEnd_131559 : Nat := 4983230072969 + 3 ^ 40 * 131559 * 2
def baseEnd_131559 : Nat := 67553001424956008507477

theorem tailTrace_131559 : CollatzResearch.WordTrace tailWord_131559 prefixEnd_131559 67553001424956008507477 := by
  unfold tailWord_131559
  simp only [CollatzResearch.WordTrace]
  refine ⟨4798350930391686333501731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3198900620261124222334487 4798350930391686333501731)
  ·
    refine ⟨7197526395587529500252597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4798350930391686333501731 7197526395587529500252597)
    ·
      refine ⟨674768099586330890648681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7197526395587529500252597 674768099586330890648681)
      ·
        refine ⟨506076074689748167986511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 674768099586330890648681 506076074689748167986511)
        ·
          refine ⟨759114112034622251979767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506076074689748167986511 759114112034622251979767)
          ·
            refine ⟨1138671168051933377969651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759114112034622251979767 1138671168051933377969651)
            ·
              refine ⟨1708006752077900066954477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1138671168051933377969651 1708006752077900066954477)
              ·
                refine ⟨640502532029212525107929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1708006752077900066954477 640502532029212525107929)
                ·
                  refine ⟨480376899021909393830947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 640502532029212525107929 480376899021909393830947)
                  ·
                    refine ⟨720565348532864090746421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 480376899021909393830947 720565348532864090746421)
                    ·
                      refine ⟨67553001424956008507477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 720565348532864090746421 67553001424956008507477)
                      ·
                        rfl

theorem cell23_131559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_131559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131559 prefixEnd_131559 := by exact prefixLift 131559
  have htrace : WordTrace (prefixWord ++ tailWord_131559) baseStart_131559 baseEnd_131559 := by
    simpa [prefixWord, tailWord_131559, baseEnd_131559] using wordTrace_append hprefix tailTrace_131559
  have hstable : (prefixWord ++ tailWord_131559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131559).length < 2 ^ (prefixWord ++ tailWord_131559).sum := by decide
  have hdescent : baseEnd_131559 < baseStart_131559 := by decide
  rcases family_descends (prefixWord ++ tailWord_131559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131560 : List Nat := [2, 1, 4, 1, 1, 4, 3, 1, 1, 3, 2]
def baseStart_131560 : Nat := 118140960795 + 131560 * 2 ^ 59
def prefixEnd_131560 : Nat := 4983230072969 + 3 ^ 40 * 131560 * 2
def baseEnd_131560 : Nat := 67553514905610504594973

theorem tailTrace_131560 : CollatzResearch.WordTrace tailWord_131560 prefixEnd_131560 67553514905610504594973 := by
  unfold tailWord_131560
  simp only [CollatzResearch.WordTrace]
  refine ⟨2399193701694031752144067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3198924935592042336192089 2399193701694031752144067)
  ·
    refine ⟨3598790552541047628216101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2399193701694031752144067 3598790552541047628216101)
    ·
      refine ⟨674773228601446430290519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3598790552541047628216101 674773228601446430290519)
      ·
        refine ⟨1012159842902169645435779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674773228601446430290519 1012159842902169645435779)
        ·
          refine ⟨1518239764353254468153669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1012159842902169645435779 1518239764353254468153669)
          ·
            refine ⟨284669955816235212778813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1518239764353254468153669 284669955816235212778813)
            ·
              refine ⟨106751233431088204792055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284669955816235212778813 106751233431088204792055)
              ·
                refine ⟨160126850146632307188083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106751233431088204792055 160126850146632307188083)
                ·
                  refine ⟨240190275219948460782125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160126850146632307188083 240190275219948460782125)
                  ·
                    refine ⟨90071353207480672793297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 240190275219948460782125 90071353207480672793297)
                    ·
                      refine ⟨67553514905610504594973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 90071353207480672793297 67553514905610504594973)
                      ·
                        rfl

theorem cell23_131560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_131560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131560 prefixEnd_131560 := by exact prefixLift 131560
  have htrace : WordTrace (prefixWord ++ tailWord_131560) baseStart_131560 baseEnd_131560 := by
    simpa [prefixWord, tailWord_131560, baseEnd_131560] using wordTrace_append hprefix tailTrace_131560
  have hstable : (prefixWord ++ tailWord_131560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131560).length < 2 ^ (prefixWord ++ tailWord_131560).sum := by decide
  have hdescent : baseEnd_131560 < baseStart_131560 := by decide
  rcases family_descends (prefixWord ++ tailWord_131560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131569 : List Nat := [1, 2, 2, 2, 3, 1, 2, 2, 2, 2, 4]
def baseStart_131569 : Nat := 118140960795 + 131569 * 2 ^ 59
def prefixEnd_131569 : Nat := 4983230072969 + 3 ^ 40 * 131569 * 2
def baseEnd_131569 : Nat := 67558136231500969382431

theorem tailTrace_131569 : CollatzResearch.WordTrace tailWord_131569 prefixEnd_131569 67558136231500969382431 := by
  unfold tailWord_131569
  simp only [CollatzResearch.WordTrace]
  refine ⟨4798715660355458041365761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3199143773570305360910507 4798715660355458041365761)
  ·
    refine ⟨3599036745266593531024321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4798715660355458041365761 3599036745266593531024321)
    ·
      refine ⟨2699277558949945148268241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3599036745266593531024321 2699277558949945148268241)
      ·
        refine ⟨2024458169212458861201181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2699277558949945148268241 2024458169212458861201181)
        ·
          refine ⟨759171813454672072950443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2024458169212458861201181 759171813454672072950443)
          ·
            refine ⟨1138757720182008109425665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759171813454672072950443 1138757720182008109425665)
            ·
              refine ⟨854068290136506082069249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1138757720182008109425665 854068290136506082069249)
              ·
                refine ⟨640551217602379561551937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 854068290136506082069249 640551217602379561551937)
                ·
                  refine ⟨480413413201784671163953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 640551217602379561551937 480413413201784671163953)
                  ·
                    refine ⟨360310059901338503372965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 480413413201784671163953 360310059901338503372965)
                    ·
                      refine ⟨67558136231500969382431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 360310059901338503372965 67558136231500969382431)
                      ·
                        rfl

theorem cell23_131569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_131569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131569 prefixEnd_131569 := by exact prefixLift 131569
  have htrace : WordTrace (prefixWord ++ tailWord_131569) baseStart_131569 baseEnd_131569 := by
    simpa [prefixWord, tailWord_131569, baseEnd_131569] using wordTrace_append hprefix tailTrace_131569
  have hstable : (prefixWord ++ tailWord_131569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131569).length < 2 ^ (prefixWord ++ tailWord_131569).sum := by decide
  have hdescent : baseEnd_131569 < baseStart_131569 := by decide
  rcases family_descends (prefixWord ++ tailWord_131569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131589 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 1, 5, 3]
def baseStart_131589 : Nat := 118140960795 + 131589 * 2 ^ 59
def prefixEnd_131589 : Nat := 4983230072969 + 3 ^ 40 * 131589 * 2
def baseEnd_131589 : Nat := 67568405844590891132339

theorem tailTrace_131589 : CollatzResearch.WordTrace tailWord_131589 prefixEnd_131589 67568405844590891132339 := by
  unfold tailWord_131589
  simp only [CollatzResearch.WordTrace]
  refine ⟨4799445120283001457093821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3199630080188667638062547 4799445120283001457093821)
  ·
    refine ⟨1799791920106125546410183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4799445120283001457093821 1799791920106125546410183)
    ·
      refine ⟨2699687880159188319615275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1799791920106125546410183 2699687880159188319615275)
      ·
        refine ⟨4049531820238782479422913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2699687880159188319615275 4049531820238782479422913)
        ·
          refine ⟨3037148865179086859567185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4049531820238782479422913 3037148865179086859567185)
          ·
            refine ⟨2277861648884315144675389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3037148865179086859567185 2277861648884315144675389)
            ·
              refine ⟨854198118331618179253271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2277861648884315144675389 854198118331618179253271)
              ·
                refine ⟨1281297177497427268879907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 854198118331618179253271 1281297177497427268879907)
                ·
                  refine ⟨1921945766246140903319861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1281297177497427268879907 1921945766246140903319861)
                  ·
                    refine ⟨180182415585575709686237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1921945766246140903319861 180182415585575709686237)
                    ·
                      refine ⟨67568405844590891132339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 180182415585575709686237 67568405844590891132339)
                      ·
                        rfl

theorem cell23_131589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 5, 3].length) (baseStart_131589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131589 prefixEnd_131589 := by exact prefixLift 131589
  have htrace : WordTrace (prefixWord ++ tailWord_131589) baseStart_131589 baseEnd_131589 := by
    simpa [prefixWord, tailWord_131589, baseEnd_131589] using wordTrace_append hprefix tailTrace_131589
  have hstable : (prefixWord ++ tailWord_131589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131589).length < 2 ^ (prefixWord ++ tailWord_131589).sum := by decide
  have hdescent : baseEnd_131589 < baseStart_131589 := by decide
  rcases family_descends (prefixWord ++ tailWord_131589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131613 : List Nat := [1, 4, 2, 2, 1, 3, 2, 3, 5]
def baseStart_131613 : Nat := 118140960795 + 131613 * 2 ^ 59
def prefixEnd_131613 : Nat := 4983230072969 + 3 ^ 40 * 131613 * 2
def baseEnd_131613 : Nat := 7508969931144310803581

theorem tailTrace_131613 : CollatzResearch.WordTrace tailWord_131613 prefixEnd_131613 7508969931144310803581 := by
  unfold tailWord_131613
  simp only [CollatzResearch.WordTrace]
  refine ⟨4800320472196053555967493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3200213648130702370644995 4800320472196053555967493)
  ·
    refine ⟨900060088536760041743905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4800320472196053555967493 900060088536760041743905)
    ·
      refine ⟨675045066402570031307929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 900060088536760041743905 675045066402570031307929)
      ·
        refine ⟨506283799801927523480947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 675045066402570031307929 506283799801927523480947)
        ·
          refine ⟨759425699702891285221421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506283799801927523480947 759425699702891285221421)
          ·
            refine ⟨284784637388584231958033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 759425699702891285221421 284784637388584231958033)
            ·
              refine ⟨213588478041438173968525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284784637388584231958033 213588478041438173968525)
              ·
                refine ⟨80095679265539315238197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213588478041438173968525 80095679265539315238197)
                ·
                  refine ⟨7508969931144310803581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80095679265539315238197 7508969931144310803581)
                  ·
                    rfl

theorem cell23_131613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3, 5].length) (baseStart_131613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131613 prefixEnd_131613 := by exact prefixLift 131613
  have htrace : WordTrace (prefixWord ++ tailWord_131613) baseStart_131613 baseEnd_131613 := by
    simpa [prefixWord, tailWord_131613, baseEnd_131613] using wordTrace_append hprefix tailTrace_131613
  have hstable : (prefixWord ++ tailWord_131613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131613).length < 2 ^ (prefixWord ++ tailWord_131613).sum := by decide
  have hdescent : baseEnd_131613 < baseStart_131613 := by decide
  rcases family_descends (prefixWord ++ tailWord_131613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131666 : List Nat := [3, 2, 2, 1, 2, 1, 1, 3, 1, 4, 3]
def baseStart_131666 : Nat := 118140960795 + 131666 * 2 ^ 59
def prefixEnd_131666 : Nat := 4983230072969 + 3 ^ 40 * 131666 * 2
def baseEnd_131666 : Nat := 67607943854987089869485

theorem tailTrace_131666 : CollatzResearch.WordTrace tailWord_131666 prefixEnd_131666 67607943854987089869485 := by
  unfold tailWord_131666
  simp only [CollatzResearch.WordTrace]
  refine ⟨1200563385251010901911713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3201502360669362405097901 1200563385251010901911713)
  ·
    refine ⟨900422538938258176433785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1200563385251010901911713 900422538938258176433785)
    ·
      refine ⟨675316904203693632325339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 900422538938258176433785 675316904203693632325339)
      ·
        refine ⟨1012975356305540448488009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675316904203693632325339 1012975356305540448488009)
        ·
          refine ⟨759731517229155336366007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1012975356305540448488009 759731517229155336366007)
          ·
            refine ⟨1139597275843733004549011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759731517229155336366007 1139597275843733004549011)
            ·
              refine ⟨1709395913765599506823517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1139597275843733004549011 1709395913765599506823517)
              ·
                refine ⟨641023467662099815058819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1709395913765599506823517 641023467662099815058819)
                ·
                  refine ⟨961535201493149722588229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 641023467662099815058819 961535201493149722588229)
                  ·
                    refine ⟨180287850279965572985293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 961535201493149722588229 180287850279965572985293)
                    ·
                      refine ⟨67607943854987089869485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 180287850279965572985293 67607943854987089869485)
                      ·
                        rfl

theorem cell23_131666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_131666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131666 prefixEnd_131666 := by exact prefixLift 131666
  have htrace : WordTrace (prefixWord ++ tailWord_131666) baseStart_131666 baseEnd_131666 := by
    simpa [prefixWord, tailWord_131666, baseEnd_131666] using wordTrace_append hprefix tailTrace_131666
  have hstable : (prefixWord ++ tailWord_131666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131666).length < 2 ^ (prefixWord ++ tailWord_131666).sum := by decide
  have hdescent : baseEnd_131666 < baseStart_131666 := by decide
  rcases family_descends (prefixWord ++ tailWord_131666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131669 : List Nat := [1, 3, 2, 2, 1, 1, 3, 2, 8]
def baseStart_131669 : Nat := 118140960795 + 131669 * 2 ^ 59
def prefixEnd_131669 : Nat := 4983230072969 + 3 ^ 40 * 131669 * 2
def baseEnd_131669 : Nat := 7512164921883397570219

theorem tailTrace_131669 : CollatzResearch.WordTrace tailWord_131669 prefixEnd_131669 7512164921883397570219 := by
  unfold tailWord_131669
  simp only [CollatzResearch.WordTrace]
  refine ⟨4802362959993175120006061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3201575306662116746670707 4802362959993175120006061)
  ·
    refine ⟨1800886109997440670002273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4802362959993175120006061 1800886109997440670002273)
    ·
      refine ⟨1350664582498080502501705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1800886109997440670002273 1350664582498080502501705)
      ·
        refine ⟨1012998436873560376876279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1350664582498080502501705 1012998436873560376876279)
        ·
          refine ⟨1519497655310340565314419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1012998436873560376876279 1519497655310340565314419)
          ·
            refine ⟨2279246482965510847971629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1519497655310340565314419 2279246482965510847971629)
            ·
              refine ⟨854717431112066567989361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2279246482965510847971629 854717431112066567989361)
              ·
                refine ⟨641038073334049925992021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 854717431112066567989361 641038073334049925992021)
                ·
                  refine ⟨7512164921883397570219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 641038073334049925992021 7512164921883397570219)
                  ·
                    rfl

theorem cell23_131669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 8].length) (baseStart_131669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131669 prefixEnd_131669 := by exact prefixLift 131669
  have htrace : WordTrace (prefixWord ++ tailWord_131669) baseStart_131669 baseEnd_131669 := by
    simpa [prefixWord, tailWord_131669, baseEnd_131669] using wordTrace_append hprefix tailTrace_131669
  have hstable : (prefixWord ++ tailWord_131669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131669).length < 2 ^ (prefixWord ++ tailWord_131669).sum := by decide
  have hdescent : baseEnd_131669 < baseStart_131669 := by decide
  rcases family_descends (prefixWord ++ tailWord_131669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131713 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 5, 1, 3]
def baseStart_131713 : Nat := 118140960795 + 131713 * 2 ^ 59
def prefixEnd_131713 : Nat := 4983230072969 + 3 ^ 40 * 131713 * 2
def baseEnd_131713 : Nat := 67632077445748405981769

theorem tailTrace_131713 : CollatzResearch.WordTrace tailWord_131713 prefixEnd_131713 67632077445748405981769 := by
  unfold tailWord_131713
  simp only [CollatzResearch.WordTrace]
  refine ⟨4803967771833770634607793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3202645181222513756405195 4803967771833770634607793)
  ·
    refine ⟨3602975828875327975955845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4803967771833770634607793 3602975828875327975955845)
    ·
      refine ⟨675557967914123995491721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3602975828875327975955845 675557967914123995491721)
      ·
        refine ⟨506668475935592996618791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 675557967914123995491721 506668475935592996618791)
        ·
          refine ⟨760002713903389494928187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506668475935592996618791 760002713903389494928187)
          ·
            refine ⟨1140004070855084242392281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760002713903389494928187 1140004070855084242392281)
            ·
              refine ⟨855003053141313181794211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1140004070855084242392281 855003053141313181794211)
              ·
                refine ⟨1282504579711969772691317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 855003053141313181794211 1282504579711969772691317)
                ·
                  refine ⟨120234804347997166189811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1282504579711969772691317 120234804347997166189811)
                  ·
                    refine ⟨180352206521995749284717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120234804347997166189811 180352206521995749284717)
                    ·
                      refine ⟨67632077445748405981769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 180352206521995749284717 67632077445748405981769)
                      ·
                        rfl

theorem cell23_131713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_131713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131713 prefixEnd_131713 := by exact prefixLift 131713
  have htrace : WordTrace (prefixWord ++ tailWord_131713) baseStart_131713 baseEnd_131713 := by
    simpa [prefixWord, tailWord_131713, baseEnd_131713] using wordTrace_append hprefix tailTrace_131713
  have hstable : (prefixWord ++ tailWord_131713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131713).length < 2 ^ (prefixWord ++ tailWord_131713).sum := by decide
  have hdescent : baseEnd_131713 < baseStart_131713 := by decide
  rcases family_descends (prefixWord ++ tailWord_131713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131714 : List Nat := [3, 4, 3, 1, 1, 1, 2, 1, 2, 1, 4]
def baseStart_131714 : Nat := 118140960795 + 131714 * 2 ^ 59
def prefixEnd_131714 : Nat := 4983230072969 + 3 ^ 40 * 131714 * 2
def baseEnd_131714 : Nat := 67632590926402902069265

theorem tailTrace_131714 : CollatzResearch.WordTrace tailWord_131714 prefixEnd_131714 67632590926402902069265 := by
  unfold tailWord_131714
  simp only [CollatzResearch.WordTrace]
  refine ⟨1201001061207536951348549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3202669496553431870262797 1201001061207536951348549)
  ·
    refine ⟨225187698976413178377853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1201001061207536951348549 225187698976413178377853)
    ·
      refine ⟨84445387116154941891695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225187698976413178377853 84445387116154941891695)
      ·
        refine ⟨126668080674232412837543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84445387116154941891695 126668080674232412837543)
        ·
          refine ⟨190002121011348619256315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126668080674232412837543 190002121011348619256315)
          ·
            refine ⟨285003181517022928884473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190002121011348619256315 285003181517022928884473)
            ·
              refine ⟨213752386137767196663355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285003181517022928884473 213752386137767196663355)
              ·
                refine ⟨320628579206650794995033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213752386137767196663355 320628579206650794995033)
                ·
                  refine ⟨240471434404988096246275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320628579206650794995033 240471434404988096246275)
                  ·
                    refine ⟨360707151607482144369413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 240471434404988096246275 360707151607482144369413)
                    ·
                      refine ⟨67632590926402902069265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 360707151607482144369413 67632590926402902069265)
                      ·
                        rfl

theorem cell23_131714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_131714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131714 prefixEnd_131714 := by exact prefixLift 131714
  have htrace : WordTrace (prefixWord ++ tailWord_131714) baseStart_131714 baseEnd_131714 := by
    simpa [prefixWord, tailWord_131714, baseEnd_131714] using wordTrace_append hprefix tailTrace_131714
  have hstable : (prefixWord ++ tailWord_131714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131714).length < 2 ^ (prefixWord ++ tailWord_131714).sum := by decide
  have hdescent : baseEnd_131714 < baseStart_131714 := by decide
  rcases family_descends (prefixWord ++ tailWord_131714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131740 : List Nat := [2, 2, 3, 2, 2, 1, 2, 2, 2, 3, 2]
def baseStart_131740 : Nat := 118140960795 + 131740 * 2 ^ 59
def prefixEnd_131740 : Nat := 4983230072969 + 3 ^ 40 * 131740 * 2
def baseEnd_131740 : Nat := 67645941423419800344145

theorem tailTrace_131740 : CollatzResearch.WordTrace tailWord_131740 prefixEnd_131740 67645941423419800344145 := by
  unfold tailWord_131740
  simp only [CollatzResearch.WordTrace]
  refine ⟨2402476271367977122920337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3203301695157302830560449 2402476271367977122920337)
  ·
    refine ⟨1801857203525982842190253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2402476271367977122920337 1801857203525982842190253)
    ·
      refine ⟨675696451322243565821345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1801857203525982842190253 675696451322243565821345)
      ·
        refine ⟨506772338491682674366009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 675696451322243565821345 506772338491682674366009)
        ·
          refine ⟨380079253868762005774507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506772338491682674366009 380079253868762005774507)
          ·
            refine ⟨570118880803143008661761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380079253868762005774507 570118880803143008661761)
            ·
              refine ⟨427589160602357256496321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570118880803143008661761 427589160602357256496321)
              ·
                refine ⟨320691870451767942372241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427589160602357256496321 320691870451767942372241)
                ·
                  refine ⟨240518902838825956779181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320691870451767942372241 240518902838825956779181)
                  ·
                    refine ⟨90194588564559733792193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 240518902838825956779181 90194588564559733792193)
                    ·
                      refine ⟨67645941423419800344145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 90194588564559733792193 67645941423419800344145)
                      ·
                        rfl

theorem cell23_131740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_131740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131740 prefixEnd_131740 := by exact prefixLift 131740
  have htrace : WordTrace (prefixWord ++ tailWord_131740) baseStart_131740 baseEnd_131740 := by
    simpa [prefixWord, tailWord_131740, baseEnd_131740] using wordTrace_append hprefix tailTrace_131740
  have hstable : (prefixWord ++ tailWord_131740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131740).length < 2 ^ (prefixWord ++ tailWord_131740).sum := by decide
  have hdescent : baseEnd_131740 < baseStart_131740 := by decide
  rcases family_descends (prefixWord ++ tailWord_131740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131763 : List Nat := [1, 1, 1, 2, 3, 4, 2, 3, 2, 4]
def baseStart_131763 : Nat := 118140960795 + 131763 * 2 ^ 59
def prefixEnd_131763 : Nat := 4983230072969 + 3 ^ 40 * 131763 * 2
def baseEnd_131763 : Nat := 22552583826157736785513

theorem tailTrace_131763 : CollatzResearch.WordTrace tailWord_131763 prefixEnd_131763 22552583826157736785513 := by
  unfold tailWord_131763
  simp only [CollatzResearch.WordTrace]
  refine ⟨4805791421652629173927943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3203860947768419449285295 4805791421652629173927943)
  ·
    refine ⟨7208687132478943760891915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4805791421652629173927943 7208687132478943760891915)
    ·
      refine ⟨10813030698718415641337873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7208687132478943760891915 10813030698718415641337873)
      ·
        refine ⟨8109773024038811731003405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10813030698718415641337873 8109773024038811731003405)
        ·
          refine ⟨3041164884014554399126277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8109773024038811731003405 3041164884014554399126277)
          ·
            refine ⟨570218415752728949836177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3041164884014554399126277 570218415752728949836177)
            ·
              refine ⟨427663811814546712377133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570218415752728949836177 427663811814546712377133)
              ·
                refine ⟨160373929430455017141425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 427663811814546712377133 160373929430455017141425)
                ·
                  refine ⟨120280447072841262856069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160373929430455017141425 120280447072841262856069)
                  ·
                    refine ⟨22552583826157736785513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120280447072841262856069 22552583826157736785513)
                    ·
                      rfl

theorem cell23_131763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2, 4].length) (baseStart_131763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131763 prefixEnd_131763 := by exact prefixLift 131763
  have htrace : WordTrace (prefixWord ++ tailWord_131763) baseStart_131763 baseEnd_131763 := by
    simpa [prefixWord, tailWord_131763, baseEnd_131763] using wordTrace_append hprefix tailTrace_131763
  have hstable : (prefixWord ++ tailWord_131763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131763).length < 2 ^ (prefixWord ++ tailWord_131763).sum := by decide
  have hdescent : baseEnd_131763 < baseStart_131763 := by decide
  rcases family_descends (prefixWord ++ tailWord_131763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131770 : List Nat := [3, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2]
def baseStart_131770 : Nat := 118140960795 + 131770 * 2 ^ 59
def prefixEnd_131770 : Nat := 4983230072969 + 3 ^ 40 * 131770 * 2
def baseEnd_131770 : Nat := 67661345843054682969007

theorem tailTrace_131770 : CollatzResearch.WordTrace tailWord_131770 prefixEnd_131770 67661345843054682969007 := by
  unfold tailWord_131770
  simp only [CollatzResearch.WordTrace]
  refine ⟨1201511683156817342358191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3204031155084846246288509 1201511683156817342358191)
  ·
    refine ⟨1802267524735226013537287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1201511683156817342358191 1802267524735226013537287)
    ·
      refine ⟨2703401287102839020305931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1802267524735226013537287 2703401287102839020305931)
      ·
        refine ⟨4055101930654258530458897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2703401287102839020305931 4055101930654258530458897)
        ·
          refine ⟨3041326447990693897844173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4055101930654258530458897 3041326447990693897844173)
          ·
            refine ⟨1140497417996510211691565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3041326447990693897844173 1140497417996510211691565)
            ·
              refine ⟨427686531748691329384337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1140497417996510211691565 427686531748691329384337)
              ·
                refine ⟨320764898811518497038253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427686531748691329384337 320764898811518497038253)
                ·
                  refine ⟨120286837054319436389345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320764898811518497038253 120286837054319436389345)
                  ·
                    refine ⟨90215127790739577292009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120286837054319436389345 90215127790739577292009)
                    ·
                      refine ⟨67661345843054682969007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 90215127790739577292009 67661345843054682969007)
                      ·
                        rfl

theorem cell23_131770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2].length) (baseStart_131770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131770 prefixEnd_131770 := by exact prefixLift 131770
  have htrace : WordTrace (prefixWord ++ tailWord_131770) baseStart_131770 baseEnd_131770 := by
    simpa [prefixWord, tailWord_131770, baseEnd_131770] using wordTrace_append hprefix tailTrace_131770
  have hstable : (prefixWord ++ tailWord_131770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131770).length < 2 ^ (prefixWord ++ tailWord_131770).sum := by decide
  have hdescent : baseEnd_131770 < baseStart_131770 := by decide
  rcases family_descends (prefixWord ++ tailWord_131770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131773 : List Nat := [1, 4, 1, 2, 1, 3, 2, 1, 3, 2, 3]
def baseStart_131773 : Nat := 118140960795 + 131773 * 2 ^ 59
def prefixEnd_131773 : Nat := 4983230072969 + 3 ^ 40 * 131773 * 2
def baseEnd_131773 : Nat := 67662886285018171231493

theorem tailTrace_131773 : CollatzResearch.WordTrace tailWord_131773 prefixEnd_131773 67662886285018171231493 := by
  unfold tailWord_131773
  simp only [CollatzResearch.WordTrace]
  refine ⟨4806156151616400881791973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3204104101077600587861315 4806156151616400881791973)
  ·
    refine ⟨901154278428075165335995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4806156151616400881791973 901154278428075165335995)
    ·
      refine ⟨1351731417642112748003993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 901154278428075165335995 1351731417642112748003993)
      ·
        refine ⟨1013798563231584561002995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1351731417642112748003993 1013798563231584561002995)
        ·
          refine ⟨1520697844847376841504493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1013798563231584561002995 1520697844847376841504493)
          ·
            refine ⟨570261691817766315564185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1520697844847376841504493 570261691817766315564185)
            ·
              refine ⟨427696268863324736673139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570261691817766315564185 427696268863324736673139)
              ·
                refine ⟨641544403294987105009709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427696268863324736673139 641544403294987105009709)
                ·
                  refine ⟨240579151235620164378641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 641544403294987105009709 240579151235620164378641)
                  ·
                    refine ⟨180434363426715123283981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 240579151235620164378641 180434363426715123283981)
                    ·
                      refine ⟨67662886285018171231493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 180434363426715123283981 67662886285018171231493)
                      ·
                        rfl

theorem cell23_131773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_131773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131773 prefixEnd_131773 := by exact prefixLift 131773
  have htrace : WordTrace (prefixWord ++ tailWord_131773) baseStart_131773 baseEnd_131773 := by
    simpa [prefixWord, tailWord_131773, baseEnd_131773] using wordTrace_append hprefix tailTrace_131773
  have hstable : (prefixWord ++ tailWord_131773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131773).length < 2 ^ (prefixWord ++ tailWord_131773).sum := by decide
  have hdescent : baseEnd_131773 < baseStart_131773 := by decide
  rcases family_descends (prefixWord ++ tailWord_131773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131790 : List Nat := [4, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3]
def baseStart_131790 : Nat := 118140960795 + 131790 * 2 ^ 59
def prefixEnd_131790 : Nat := 4983230072969 + 3 ^ 40 * 131790 * 2
def baseEnd_131790 : Nat := 67671615456144604718915

theorem tailTrace_131790 : CollatzResearch.WordTrace tailWord_131790 prefixEnd_131790 67671615456144604718915 := by
  unfold tailWord_131790
  simp only [CollatzResearch.WordTrace]
  refine ⟨600847024069351598145103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3204517461703208523440549 600847024069351598145103)
  ·
    refine ⟨901270536104027397217655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 600847024069351598145103 901270536104027397217655)
    ·
      refine ⟨1351905804156041095826483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 901270536104027397217655 1351905804156041095826483)
      ·
        refine ⟨2027858706234061643739725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1351905804156041095826483 2027858706234061643739725)
        ·
          refine ⟨760447014837773116402397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2027858706234061643739725 760447014837773116402397)
          ·
            refine ⟨285167630564164918650899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 760447014837773116402397 285167630564164918650899)
            ·
              refine ⟨427751445846247377976349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285167630564164918650899 427751445846247377976349)
              ·
                refine ⟨160406792192342766741131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 427751445846247377976349 160406792192342766741131)
                ·
                  refine ⟨240610188288514150111697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160406792192342766741131 240610188288514150111697)
                  ·
                    refine ⟨180457641216385612583773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 240610188288514150111697 180457641216385612583773)
                    ·
                      refine ⟨67671615456144604718915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 180457641216385612583773 67671615456144604718915)
                      ·
                        rfl

theorem cell23_131790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_131790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131790 prefixEnd_131790 := by exact prefixLift 131790
  have htrace : WordTrace (prefixWord ++ tailWord_131790) baseStart_131790 baseEnd_131790 := by
    simpa [prefixWord, tailWord_131790, baseEnd_131790] using wordTrace_append hprefix tailTrace_131790
  have hstable : (prefixWord ++ tailWord_131790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131790).length < 2 ^ (prefixWord ++ tailWord_131790).sum := by decide
  have hdescent : baseEnd_131790 < baseStart_131790 := by decide
  rcases family_descends (prefixWord ++ tailWord_131790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131804 : List Nat := [2, 2, 5, 1, 1, 2, 2, 1, 3, 2, 2]
def baseStart_131804 : Nat := 118140960795 + 131804 * 2 ^ 59
def prefixEnd_131804 : Nat := 4983230072969 + 3 ^ 40 * 131804 * 2
def baseEnd_131804 : Nat := 67678804185307549943851

theorem tailTrace_131804 : CollatzResearch.WordTrace tailWord_131804 prefixEnd_131804 67678804185307549943851 := by
  unfold tailWord_131804
  simp only [CollatzResearch.WordTrace]
  refine ⟨2403643407252046588085233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3204857876336062117446977 2403643407252046588085233)
  ·
    refine ⟨1802732555439034941063925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2403643407252046588085233 1802732555439034941063925)
    ·
      refine ⟨169006177072409525724743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1802732555439034941063925 169006177072409525724743)
      ·
        refine ⟨253509265608614288587115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169006177072409525724743 253509265608614288587115)
        ·
          refine ⟨380263898412921432880673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253509265608614288587115 380263898412921432880673)
          ·
            refine ⟨285197923809691074660505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380263898412921432880673 285197923809691074660505)
            ·
              refine ⟨213898442857268305995379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285197923809691074660505 213898442857268305995379)
              ·
                refine ⟨320847664285902458993069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213898442857268305995379 320847664285902458993069)
                ·
                  refine ⟨120317874107213422122401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320847664285902458993069 120317874107213422122401)
                  ·
                    refine ⟨90238405580410066591801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120317874107213422122401 90238405580410066591801)
                    ·
                      refine ⟨67678804185307549943851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 90238405580410066591801 67678804185307549943851)
                      ·
                        rfl

theorem cell23_131804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_131804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131804 prefixEnd_131804 := by exact prefixLift 131804
  have htrace : WordTrace (prefixWord ++ tailWord_131804) baseStart_131804 baseEnd_131804 := by
    simpa [prefixWord, tailWord_131804, baseEnd_131804] using wordTrace_append hprefix tailTrace_131804
  have hstable : (prefixWord ++ tailWord_131804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131804).length < 2 ^ (prefixWord ++ tailWord_131804).sum := by decide
  have hdescent : baseEnd_131804 < baseStart_131804 := by decide
  rcases family_descends (prefixWord ++ tailWord_131804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131843 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 3, 4, 2]
def baseStart_131843 : Nat := 118140960795 + 131843 * 2 ^ 59
def prefixEnd_131843 : Nat := 4983230072969 + 3 ^ 40 * 131843 * 2
def baseEnd_131843 : Nat := 67698829930832897356171

theorem tailTrace_131843 : CollatzResearch.WordTrace tailWord_131843 prefixEnd_131843 67698829930832897356171 := by
  unfold tailWord_131843
  simp only [CollatzResearch.WordTrace]
  refine ⟨4808709261362802836840183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3205806174241868557893455 4808709261362802836840183)
  ·
    refine ⟨7213063892044204255260275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4808709261362802836840183 7213063892044204255260275)
    ·
      refine ⟨10819595838066306382890413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7213063892044204255260275 10819595838066306382890413)
      ·
        refine ⟨4057348439274864893583905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10819595838066306382890413 4057348439274864893583905)
        ·
          refine ⟨3043011329456148670187929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4057348439274864893583905 3043011329456148670187929)
          ·
            refine ⟨2282258497092111502640947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3043011329456148670187929 2282258497092111502640947)
            ·
              refine ⟨3423387745638167253961421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2282258497092111502640947 3423387745638167253961421)
              ·
                refine ⟨1283770404614312720235533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3423387745638167253961421 1283770404614312720235533)
                ·
                  refine ⟨481413901730367270088325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1283770404614312720235533 481413901730367270088325)
                  ·
                    refine ⟨90265106574443863141561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 481413901730367270088325 90265106574443863141561)
                    ·
                      refine ⟨67698829930832897356171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 90265106574443863141561 67698829930832897356171)
                      ·
                        rfl

theorem cell23_131843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 4, 2].length) (baseStart_131843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131843 prefixEnd_131843 := by exact prefixLift 131843
  have htrace : WordTrace (prefixWord ++ tailWord_131843) baseStart_131843 baseEnd_131843 := by
    simpa [prefixWord, tailWord_131843, baseEnd_131843] using wordTrace_append hprefix tailTrace_131843
  have hstable : (prefixWord ++ tailWord_131843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131843).length < 2 ^ (prefixWord ++ tailWord_131843).sum := by decide
  have hdescent : baseEnd_131843 < baseStart_131843 := by decide
  rcases family_descends (prefixWord ++ tailWord_131843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131847 : List Nat := [1, 1, 4, 4, 1, 1, 2, 3, 1, 3, 2]
def baseStart_131847 : Nat := 118140960795 + 131847 * 2 ^ 59
def prefixEnd_131847 : Nat := 4983230072969 + 3 ^ 40 * 131847 * 2
def baseEnd_131847 : Nat := 67700883853450881706153

theorem tailTrace_131847 : CollatzResearch.WordTrace tailWord_131847 prefixEnd_131847 67700883853450881706153 := by
  unfold tailWord_131847
  simp only [CollatzResearch.WordTrace]
  refine ⟨4808855153348311519985795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3205903435565541013323863 4808855153348311519985795)
  ·
    refine ⟨7213282730022467279978693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4808855153348311519985795 7213282730022467279978693)
    ·
      refine ⟨1352490511879212614996005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7213282730022467279978693 1352490511879212614996005)
      ·
        refine ⟨253591970977352365311751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1352490511879212614996005 253591970977352365311751)
        ·
          refine ⟨380387956466028547967627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253591970977352365311751 380387956466028547967627)
          ·
            refine ⟨570581934699042821951441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380387956466028547967627 570581934699042821951441)
            ·
              refine ⟨427936451024282116463581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570581934699042821951441 427936451024282116463581)
              ·
                refine ⟨160476169134105793673843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 427936451024282116463581 160476169134105793673843)
                ·
                  refine ⟨240714253701158690510765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160476169134105793673843 240714253701158690510765)
                  ·
                    refine ⟨90267845137934508941537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 240714253701158690510765 90267845137934508941537)
                    ·
                      refine ⟨67700883853450881706153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 90267845137934508941537 67700883853450881706153)
                      ·
                        rfl

theorem cell23_131847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_131847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131847 prefixEnd_131847 := by exact prefixLift 131847
  have htrace : WordTrace (prefixWord ++ tailWord_131847) baseStart_131847 baseEnd_131847 := by
    simpa [prefixWord, tailWord_131847, baseEnd_131847] using wordTrace_append hprefix tailTrace_131847
  have hstable : (prefixWord ++ tailWord_131847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131847).length < 2 ^ (prefixWord ++ tailWord_131847).sum := by decide
  have hdescent : baseEnd_131847 < baseStart_131847 := by decide
  rcases family_descends (prefixWord ++ tailWord_131847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131877 : List Nat := [1, 3, 1, 2, 3, 1, 3, 3, 2, 2, 2]
def baseStart_131877 : Nat := 118140960795 + 131877 * 2 ^ 59
def prefixEnd_131877 : Nat := 4983230072969 + 3 ^ 40 * 131877 * 2
def baseEnd_131877 : Nat := 67716288273085764331015

theorem tailTrace_131877 : CollatzResearch.WordTrace tailWord_131877 prefixEnd_131877 67716288273085764331015 := by
  unfold tailWord_131877
  simp only [CollatzResearch.WordTrace]
  refine ⟨4809949343239626643577885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3206632895493084429051923 4809949343239626643577885)
  ·
    refine ⟨1803731003714859991341707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4809949343239626643577885 1803731003714859991341707)
    ·
      refine ⟨2705596505572289987012561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1803731003714859991341707 2705596505572289987012561)
      ·
        refine ⟨2029197379179217490259421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2705596505572289987012561 2029197379179217490259421)
        ·
          refine ⟨760949017192206558847283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2029197379179217490259421 760949017192206558847283)
          ·
            refine ⟨1141423525788309838270925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760949017192206558847283 1141423525788309838270925)
            ·
              refine ⟨428033822170616189351597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1141423525788309838270925 428033822170616189351597)
              ·
                refine ⟨160512683313981071006849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 428033822170616189351597 160512683313981071006849)
                ·
                  refine ⟨120384512485485803255137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160512683313981071006849 120384512485485803255137)
                  ·
                    refine ⟨90288384364114352441353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120384512485485803255137 90288384364114352441353)
                    ·
                      refine ⟨67716288273085764331015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 90288384364114352441353 67716288273085764331015)
                      ·
                        rfl

theorem cell23_131877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2, 2, 2].length) (baseStart_131877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131877 prefixEnd_131877 := by exact prefixLift 131877
  have htrace : WordTrace (prefixWord ++ tailWord_131877) baseStart_131877 baseEnd_131877 := by
    simpa [prefixWord, tailWord_131877, baseEnd_131877] using wordTrace_append hprefix tailTrace_131877
  have hstable : (prefixWord ++ tailWord_131877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131877).length < 2 ^ (prefixWord ++ tailWord_131877).sum := by decide
  have hdescent : baseEnd_131877 < baseStart_131877 := by decide
  rcases family_descends (prefixWord ++ tailWord_131877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131894 : List Nat := [5, 1, 2, 2, 2, 1, 1, 2, 1, 4, 2]
def baseStart_131894 : Nat := 118140960795 + 131894 * 2 ^ 59
def prefixEnd_131894 : Nat := 4983230072969 + 3 ^ 40 * 131894 * 2
def baseEnd_131894 : Nat := 67725017444212197818437

theorem tailTrace_131894 : CollatzResearch.WordTrace tailWord_131894 prefixEnd_131894 67725017444212197818437 := by
  unfold tailWord_131894
  simp only [CollatzResearch.WordTrace]
  refine ⟨300660586511127409184171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3207046256118692364631157 300660586511127409184171)
  ·
    refine ⟨450990879766691113776257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300660586511127409184171 450990879766691113776257)
    ·
      refine ⟨338243159825018335332193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450990879766691113776257 338243159825018335332193)
      ·
        refine ⟨253682369868763751499145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338243159825018335332193 253682369868763751499145)
        ·
          refine ⟨190261777401572813624359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253682369868763751499145 190261777401572813624359)
          ·
            refine ⟨285392666102359220436539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190261777401572813624359 285392666102359220436539)
            ·
              refine ⟨428088999153538830654809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285392666102359220436539 428088999153538830654809)
              ·
                refine ⟨321066749365154122991107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428088999153538830654809 321066749365154122991107)
                ·
                  refine ⟨481600124047731184486661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 321066749365154122991107 481600124047731184486661)
                  ·
                    refine ⟨90300023258949597091249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 481600124047731184486661 90300023258949597091249)
                    ·
                      refine ⟨67725017444212197818437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 90300023258949597091249 67725017444212197818437)
                      ·
                        rfl

theorem cell23_131894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_131894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131894 prefixEnd_131894 := by exact prefixLift 131894
  have htrace : WordTrace (prefixWord ++ tailWord_131894) baseStart_131894 baseEnd_131894 := by
    simpa [prefixWord, tailWord_131894, baseEnd_131894] using wordTrace_append hprefix tailTrace_131894
  have hstable : (prefixWord ++ tailWord_131894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131894).length < 2 ^ (prefixWord ++ tailWord_131894).sum := by decide
  have hdescent : baseEnd_131894 < baseStart_131894 := by decide
  rcases family_descends (prefixWord ++ tailWord_131894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131913 : List Nat := [1, 2, 1, 1, 2, 5, 2, 2, 2, 5]
def baseStart_131913 : Nat := 118140960795 + 131913 * 2 ^ 59
def prefixEnd_131913 : Nat := 4983230072969 + 3 ^ 40 * 131913 * 2
def baseEnd_131913 : Nat := 22578257858882541160283

theorem tailTrace_131913 : CollatzResearch.WordTrace tailWord_131913 prefixEnd_131913 22578257858882541160283 := by
  unfold tailWord_131913
  simp only [CollatzResearch.WordTrace]
  refine ⟨4811262371109204791888393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3207508247406136527925595 4811262371109204791888393)
  ·
    refine ⟨3608446778331903593916295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4811262371109204791888393 3608446778331903593916295)
    ·
      refine ⟨5412670167497855390874443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3608446778331903593916295 5412670167497855390874443)
      ·
        refine ⟨8119005251246783086311665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5412670167497855390874443 8119005251246783086311665)
        ·
          refine ⟨6089253938435087314733749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8119005251246783086311665 6089253938435087314733749)
          ·
            refine ⟨570867556728289435756289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6089253938435087314733749 570867556728289435756289)
            ·
              refine ⟨428150667546217076817217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570867556728289435756289 428150667546217076817217)
              ·
                refine ⟨321113000659662807612913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428150667546217076817217 321113000659662807612913)
                ·
                  refine ⟨240834750494747105709685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321113000659662807612913 240834750494747105709685)
                  ·
                    refine ⟨22578257858882541160283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 240834750494747105709685 22578257858882541160283)
                    ·
                      rfl

theorem cell23_131913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 5].length) (baseStart_131913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131913 prefixEnd_131913 := by exact prefixLift 131913
  have htrace : WordTrace (prefixWord ++ tailWord_131913) baseStart_131913 baseEnd_131913 := by
    simpa [prefixWord, tailWord_131913, baseEnd_131913] using wordTrace_append hprefix tailTrace_131913
  have hstable : (prefixWord ++ tailWord_131913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131913).length < 2 ^ (prefixWord ++ tailWord_131913).sum := by decide
  have hdescent : baseEnd_131913 < baseStart_131913 := by decide
  rcases family_descends (prefixWord ++ tailWord_131913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131973 : List Nat := [1, 3, 1, 1, 3, 4, 1, 1, 8]
def baseStart_131973 : Nat := 118140960795 + 131973 * 2 ^ 59
def prefixEnd_131973 : Nat := 4983230072969 + 3 ^ 40 * 131973 * 2
def baseEnd_131973 : Nat := 7529509157324154303397

theorem tailTrace_131973 : CollatzResearch.WordTrace tailWord_131973 prefixEnd_131973 7529509157324154303397 := by
  unfold tailWord_131973
  simp only [CollatzResearch.WordTrace]
  refine ⟨4813450750891835039072573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3208967167261223359381715 4813450750891835039072573)
  ·
    refine ⟨1805044031584438139652215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4813450750891835039072573 1805044031584438139652215)
    ·
      refine ⟨2707566047376657209478323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1805044031584438139652215 2707566047376657209478323)
      ·
        refine ⟨4061349071064985814217485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2707566047376657209478323 4061349071064985814217485)
        ·
          refine ⟨1523005901649369680331557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4061349071064985814217485 1523005901649369680331557)
          ·
            refine ⟨285563606559256815062167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1523005901649369680331557 285563606559256815062167)
            ·
              refine ⟨428345409838885222593251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285563606559256815062167 428345409838885222593251)
              ·
                refine ⟨642518114758327833889877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428345409838885222593251 642518114758327833889877)
                ·
                  refine ⟨7529509157324154303397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 642518114758327833889877 7529509157324154303397)
                  ·
                    rfl

theorem cell23_131973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 8].length) (baseStart_131973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131973 prefixEnd_131973 := by exact prefixLift 131973
  have htrace : WordTrace (prefixWord ++ tailWord_131973) baseStart_131973 baseEnd_131973 := by
    simpa [prefixWord, tailWord_131973, baseEnd_131973] using wordTrace_append hprefix tailTrace_131973
  have hstable : (prefixWord ++ tailWord_131973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131973).length < 2 ^ (prefixWord ++ tailWord_131973).sum := by decide
  have hdescent : baseEnd_131973 < baseStart_131973 := by decide
  rcases family_descends (prefixWord ++ tailWord_131973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131977 : List Nat := [1, 2, 1, 1, 5, 2, 2, 4, 1, 4]
def baseStart_131977 : Nat := 118140960795 + 131977 * 2 ^ 59
def prefixEnd_131977 : Nat := 4983230072969 + 3 ^ 40 * 131977 * 2
def baseEnd_131977 : Nat := 22589212112845124360185

theorem tailTrace_131977 : CollatzResearch.WordTrace tailWord_131977 prefixEnd_131977 22589212112845124360185 := by
  unfold tailWord_131977
  simp only [CollatzResearch.WordTrace]
  refine ⟨4813596642877343722218185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3209064428584895814812123 4813596642877343722218185)
  ·
    refine ⟨3610197482158007791663639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4813596642877343722218185 3610197482158007791663639)
    ·
      refine ⟨5415296223237011687495459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3610197482158007791663639 5415296223237011687495459)
      ·
        refine ⟨8122944334855517531243189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5415296223237011687495459 8122944334855517531243189)
        ·
          refine ⟨761526031392704768554049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8122944334855517531243189 761526031392704768554049)
          ·
            refine ⟨571144523544528576415537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 761526031392704768554049 571144523544528576415537)
            ·
              refine ⟨428358392658396432311653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 571144523544528576415537 428358392658396432311653)
              ·
                refine ⟨80317198623449331058435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 428358392658396432311653 80317198623449331058435)
                ·
                  refine ⟨120475797935173996587653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80317198623449331058435 120475797935173996587653)
                  ·
                    refine ⟨22589212112845124360185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120475797935173996587653 22589212112845124360185)
                    ·
                      rfl

theorem cell23_131977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4, 1, 4].length) (baseStart_131977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_131977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_131977 prefixEnd_131977 := by exact prefixLift 131977
  have htrace : WordTrace (prefixWord ++ tailWord_131977) baseStart_131977 baseEnd_131977 := by
    simpa [prefixWord, tailWord_131977, baseEnd_131977] using wordTrace_append hprefix tailTrace_131977
  have hstable : (prefixWord ++ tailWord_131977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131977).length < 2 ^ (prefixWord ++ tailWord_131977).sum := by decide
  have hdescent : baseEnd_131977 < baseStart_131977 := by decide
  rcases family_descends (prefixWord ++ tailWord_131977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132003 : List Nat := [1, 1, 1, 4, 1, 2, 2, 3, 3, 5]
def baseStart_132003 : Nat := 118140960795 + 132003 * 2 ^ 59
def prefixEnd_132003 : Nat := 4983230072969 + 3 ^ 40 * 132003 * 2
def baseEnd_132003 : Nat := 22593662278517423785145

theorem tailTrace_132003 : CollatzResearch.WordTrace tailWord_132003 prefixEnd_132003 22593662278517423785145 := by
  unfold tailWord_132003
  simp only [CollatzResearch.WordTrace]
  refine ⟨4814544940783150162664663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3209696627188766775109775 4814544940783150162664663)
  ·
    refine ⟨7221817411174725243996995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4814544940783150162664663 7221817411174725243996995)
    ·
      refine ⟨10832726116762087865995493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7221817411174725243996995 10832726116762087865995493)
      ·
        refine ⟨2031136146892891474874155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10832726116762087865995493 2031136146892891474874155)
        ·
          refine ⟨3046704220339337212311233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2031136146892891474874155 3046704220339337212311233)
          ·
            refine ⟨2285028165254502909233425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3046704220339337212311233 2285028165254502909233425)
            ·
              refine ⟨1713771123940877181925069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2285028165254502909233425 1713771123940877181925069)
              ·
                refine ⟨642664171477828943221901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1713771123940877181925069 642664171477828943221901)
                ·
                  refine ⟨240999064304185853708213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 642664171477828943221901 240999064304185853708213)
                  ·
                    refine ⟨22593662278517423785145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 240999064304185853708213 22593662278517423785145)
                    ·
                      rfl

theorem cell23_132003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 5].length) (baseStart_132003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132003 prefixEnd_132003 := by exact prefixLift 132003
  have htrace : WordTrace (prefixWord ++ tailWord_132003) baseStart_132003 baseEnd_132003 := by
    simpa [prefixWord, tailWord_132003, baseEnd_132003] using wordTrace_append hprefix tailTrace_132003
  have hstable : (prefixWord ++ tailWord_132003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132003).length < 2 ^ (prefixWord ++ tailWord_132003).sum := by decide
  have hdescent : baseEnd_132003 < baseStart_132003 := by decide
  rcases family_descends (prefixWord ++ tailWord_132003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132054 : List Nat := [5, 2, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_132054 : Nat := 118140960795 + 132054 * 2 ^ 59
def prefixEnd_132054 : Nat := 4983230072969 + 3 ^ 40 * 132054 * 2
def baseEnd_132054 : Nat := 22602391449643857272567

theorem tailTrace_132054 : CollatzResearch.WordTrace tailWord_132054 prefixEnd_132054 22602391449643857272567 := by
  unfold tailWord_132054
  simp only [CollatzResearch.WordTrace]
  refine ⟨301025316474899117048201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3210936709065590581847477 301025316474899117048201)
  ·
    refine ⟨225768987356174337786151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301025316474899117048201 225768987356174337786151)
    ·
      refine ⟨338653481034261506679227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225768987356174337786151 338653481034261506679227)
      ·
        refine ⟨507980221551392260018841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338653481034261506679227 507980221551392260018841)
        ·
          refine ⟨380985166163544195014131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507980221551392260018841 380985166163544195014131)
          ·
            refine ⟨571477749245316292521197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380985166163544195014131 571477749245316292521197)
            ·
              refine ⟨214304155966993609695449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 571477749245316292521197 214304155966993609695449)
              ·
                refine ⟨160728116975245207271587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214304155966993609695449 160728116975245207271587)
                ·
                  refine ⟨241092175462867810907381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160728116975245207271587 241092175462867810907381)
                  ·
                    refine ⟨22602391449643857272567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 241092175462867810907381 22602391449643857272567)
                    ·
                      rfl

theorem cell23_132054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_132054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132054 prefixEnd_132054 := by exact prefixLift 132054
  have htrace : WordTrace (prefixWord ++ tailWord_132054) baseStart_132054 baseEnd_132054 := by
    simpa [prefixWord, tailWord_132054, baseEnd_132054] using wordTrace_append hprefix tailTrace_132054
  have hstable : (prefixWord ++ tailWord_132054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132054).length < 2 ^ (prefixWord ++ tailWord_132054).sum := by decide
  have hdescent : baseEnd_132054 < baseStart_132054 := by decide
  rcases family_descends (prefixWord ++ tailWord_132054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132057 : List Nat := [1, 2, 1, 2, 5, 1, 3, 2, 1, 1, 4]
def baseStart_132057 : Nat := 118140960795 + 132057 * 2 ^ 59
def prefixEnd_132057 : Nat := 4983230072969 + 3 ^ 40 * 132057 * 2
def baseEnd_132057 : Nat := 67808714790895060080187

theorem tailTrace_132057 : CollatzResearch.WordTrace tailWord_132057 prefixEnd_132057 67808714790895060080187 := by
  unfold tailWord_132057
  simp only [CollatzResearch.WordTrace]
  refine ⟨4816514482587517385130425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3211009655058344923420283 4816514482587517385130425)
  ·
    refine ⟨3612385861940638038847819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4816514482587517385130425 3612385861940638038847819)
    ·
      refine ⟨5418578792910957058271729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3612385861940638038847819 5418578792910957058271729)
      ·
        refine ⟨4063934094683217793703797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5418578792910957058271729 4063934094683217793703797)
        ·
          refine ⟨380993821376551668159731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4063934094683217793703797 380993821376551668159731)
          ·
            refine ⟨571490732064827502239597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380993821376551668159731 571490732064827502239597)
            ·
              refine ⟨214309024524310313339849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 571490732064827502239597 214309024524310313339849)
              ·
                refine ⟨160731768393232735004887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214309024524310313339849 160731768393232735004887)
                ·
                  refine ⟨241097652589849102507331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160731768393232735004887 241097652589849102507331)
                  ·
                    refine ⟨361646478884773653760997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 241097652589849102507331 361646478884773653760997)
                    ·
                      refine ⟨67808714790895060080187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 361646478884773653760997 67808714790895060080187)
                      ·
                        rfl

theorem cell23_132057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 1, 4].length) (baseStart_132057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132057 prefixEnd_132057 := by exact prefixLift 132057
  have htrace : WordTrace (prefixWord ++ tailWord_132057) baseStart_132057 baseEnd_132057 := by
    simpa [prefixWord, tailWord_132057, baseEnd_132057] using wordTrace_append hprefix tailTrace_132057
  have hstable : (prefixWord ++ tailWord_132057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132057).length < 2 ^ (prefixWord ++ tailWord_132057).sum := by decide
  have hdescent : baseEnd_132057 < baseStart_132057 := by decide
  rcases family_descends (prefixWord ++ tailWord_132057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132074 : List Nat := [3, 1, 3, 1, 2, 3, 3, 1, 1, 1, 4]
def baseStart_132074 : Nat := 118140960795 + 132074 * 2 ^ 59
def prefixEnd_132074 : Nat := 4983230072969 + 3 ^ 40 * 132074 * 2
def baseEnd_132074 : Nat := 67817443962021493567609

theorem tailTrace_132074 : CollatzResearch.WordTrace tailWord_132074 prefixEnd_132074 67817443962021493567609 := by
  unfold tailWord_132074
  simp only [CollatzResearch.WordTrace]
  refine ⟨1204283630881482322124819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3211423015683952858999517 1204283630881482322124819)
  ·
    refine ⟨1806425446322223483187229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1204283630881482322124819 1806425446322223483187229)
    ·
      refine ⟨677409542370833806195211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1806425446322223483187229 677409542370833806195211)
      ·
        refine ⟨1016114313556250709292817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677409542370833806195211 1016114313556250709292817)
        ·
          refine ⟨762085735167188031969613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1016114313556250709292817 762085735167188031969613)
          ·
            refine ⟨285782150687695511988605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 762085735167188031969613 285782150687695511988605)
            ·
              refine ⟨107168306507885816995727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285782150687695511988605 107168306507885816995727)
              ·
                refine ⟨160752459761828725493591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107168306507885816995727 160752459761828725493591)
                ·
                  refine ⟨241128689642743088240387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160752459761828725493591 241128689642743088240387)
                  ·
                    refine ⟨361693034464114632360581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 241128689642743088240387 361693034464114632360581)
                    ·
                      refine ⟨67817443962021493567609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 361693034464114632360581 67817443962021493567609)
                      ·
                        rfl

theorem cell23_132074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_132074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132074 prefixEnd_132074 := by exact prefixLift 132074
  have htrace : WordTrace (prefixWord ++ tailWord_132074) baseStart_132074 baseEnd_132074 := by
    simpa [prefixWord, tailWord_132074, baseEnd_132074] using wordTrace_append hprefix tailTrace_132074
  have hstable : (prefixWord ++ tailWord_132074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132074).length < 2 ^ (prefixWord ++ tailWord_132074).sum := by decide
  have hdescent : baseEnd_132074 < baseStart_132074 := by decide
  rcases family_descends (prefixWord ++ tailWord_132074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132107 : List Nat := [1, 1, 1, 1, 6, 3, 2, 1, 1, 3, 3]
def baseStart_132107 : Nat := 118140960795 + 132107 * 2 ^ 59
def prefixEnd_132107 : Nat := 4983230072969 + 3 ^ 40 * 132107 * 2
def baseEnd_132107 : Nat := 67834388823619864454957

theorem tailTrace_132107 : CollatzResearch.WordTrace tailWord_132107 prefixEnd_132107 67834388823619864454957 := by
  unfold tailWord_132107
  simp only [CollatzResearch.WordTrace]
  refine ⟨4818338132406375924450575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3212225421604250616300383 4818338132406375924450575)
  ·
    refine ⟨7227507198609563886675863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4818338132406375924450575 7227507198609563886675863)
    ·
      refine ⟨10841260797914345830013795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7227507198609563886675863 10841260797914345830013795)
      ·
        refine ⟨16261891196871518745020693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10841260797914345830013795 16261891196871518745020693)
        ·
          refine ⟨762276149853352441172845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16261891196871518745020693 762276149853352441172845)
          ·
            refine ⟨285853556195007165439817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 762276149853352441172845 285853556195007165439817)
            ·
              refine ⟨214390167146255374079863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285853556195007165439817 214390167146255374079863)
              ·
                refine ⟨321585250719383061119795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214390167146255374079863 321585250719383061119795)
                ·
                  refine ⟨482377876079074591679693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 321585250719383061119795 482377876079074591679693)
                  ·
                    refine ⟨180891703529652971879885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 482377876079074591679693 180891703529652971879885)
                    ·
                      refine ⟨67834388823619864454957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 180891703529652971879885 67834388823619864454957)
                      ·
                        rfl

theorem cell23_132107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3, 3].length) (baseStart_132107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132107 prefixEnd_132107 := by exact prefixLift 132107
  have htrace : WordTrace (prefixWord ++ tailWord_132107) baseStart_132107 baseEnd_132107 := by
    simpa [prefixWord, tailWord_132107, baseEnd_132107] using wordTrace_append hprefix tailTrace_132107
  have hstable : (prefixWord ++ tailWord_132107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132107).length < 2 ^ (prefixWord ++ tailWord_132107).sum := by decide
  have hdescent : baseEnd_132107 < baseStart_132107 := by decide
  rcases family_descends (prefixWord ++ tailWord_132107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132128 : List Nat := [2, 1, 1, 7, 1, 2, 2, 1, 1, 2, 3]
def baseStart_132128 : Nat := 118140960795 + 132128 * 2 ^ 59
def prefixEnd_132128 : Nat := 4983230072969 + 3 ^ 40 * 132128 * 2
def baseEnd_132128 : Nat := 67845171917364282292361

theorem tailTrace_132128 : CollatzResearch.WordTrace tailWord_132128 prefixEnd_132128 67845171917364282292361 := by
  unfold tailWord_132128
  simp only [CollatzResearch.WordTrace]
  refine ⟨2409552032665148255482519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3212736043553531007310025 2409552032665148255482519)
  ·
    refine ⟨3614328048997722383223779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2409552032665148255482519 3614328048997722383223779)
    ·
      refine ⟨5421492073496583574835669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3614328048997722383223779 5421492073496583574835669)
      ·
        refine ⟨127066220472576177535211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 5421492073496583574835669 127066220472576177535211)
        ·
          refine ⟨190599330708864266302817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127066220472576177535211 190599330708864266302817)
          ·
            refine ⟨142949498031648199727113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190599330708864266302817 142949498031648199727113)
            ·
              refine ⟨107212123523736149795335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142949498031648199727113 107212123523736149795335)
              ·
                refine ⟨160818185285604224693003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107212123523736149795335 160818185285604224693003)
                ·
                  refine ⟨241227277928406337039505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160818185285604224693003 241227277928406337039505)
                  ·
                    refine ⟨180920458446304752779629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 241227277928406337039505 180920458446304752779629)
                    ·
                      refine ⟨67845171917364282292361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 180920458446304752779629 67845171917364282292361)
                      ·
                        rfl

theorem cell23_132128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_132128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132128 prefixEnd_132128 := by exact prefixLift 132128
  have htrace : WordTrace (prefixWord ++ tailWord_132128) baseStart_132128 baseEnd_132128 := by
    simpa [prefixWord, tailWord_132128, baseEnd_132128] using wordTrace_append hprefix tailTrace_132128
  have hstable : (prefixWord ++ tailWord_132128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132128).length < 2 ^ (prefixWord ++ tailWord_132128).sum := by decide
  have hdescent : baseEnd_132128 < baseStart_132128 := by decide
  rcases family_descends (prefixWord ++ tailWord_132128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132158 : List Nat := [4, 2, 1, 3, 1, 2, 3, 1, 2, 1, 3]
def baseStart_132158 : Nat := 118140960795 + 132158 * 2 ^ 59
def prefixEnd_132158 : Nat := 4983230072969 + 3 ^ 40 * 132158 * 2
def baseEnd_132158 : Nat := 67860576336999164917223

theorem tailTrace_132158 : CollatzResearch.WordTrace tailWord_132158 prefixEnd_132158 67860576336999164917223 := by
  unfold tailWord_132158
  simp only [CollatzResearch.WordTrace]
  refine ⟨602524781902701454319641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3213465503481074423038085 602524781902701454319641)
  ·
    refine ⟨451893586427026090739731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 602524781902701454319641 451893586427026090739731)
    ·
      refine ⟨677840379640539136109597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451893586427026090739731 677840379640539136109597)
      ·
        refine ⟨254190142365202176041099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 677840379640539136109597 254190142365202176041099)
        ·
          refine ⟨381285213547803264061649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254190142365202176041099 381285213547803264061649)
          ·
            refine ⟨285963910160852448046237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381285213547803264061649 285963910160852448046237)
            ·
              refine ⟨107236466310319668017339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285963910160852448046237 107236466310319668017339)
              ·
                refine ⟨160854699465479502026009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107236466310319668017339 160854699465479502026009)
                ·
                  refine ⟨120641024599109626519507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160854699465479502026009 120641024599109626519507)
                  ·
                    refine ⟨180961536898664439779261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120641024599109626519507 180961536898664439779261)
                    ·
                      refine ⟨67860576336999164917223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 180961536898664439779261 67860576336999164917223)
                      ·
                        rfl

theorem cell23_132158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_132158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132158 prefixEnd_132158 := by exact prefixLift 132158
  have htrace : WordTrace (prefixWord ++ tailWord_132158) baseStart_132158 baseEnd_132158 := by
    simpa [prefixWord, tailWord_132158, baseEnd_132158] using wordTrace_append hprefix tailTrace_132158
  have hstable : (prefixWord ++ tailWord_132158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132158).length < 2 ^ (prefixWord ++ tailWord_132158).sum := by decide
  have hdescent : baseEnd_132158 < baseStart_132158 := by decide
  rcases family_descends (prefixWord ++ tailWord_132158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132160 : List Nat := [2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 4]
def baseStart_132160 : Nat := 118140960795 + 132160 * 2 ^ 59
def prefixEnd_132160 : Nat := 4983230072969 + 3 ^ 40 * 132160 * 2
def baseEnd_132160 : Nat := 67861603298308157092213

theorem tailTrace_132160 : CollatzResearch.WordTrace tailWord_132160 prefixEnd_132160 67861603298308157092213 := by
  unfold tailWord_132160
  simp only [CollatzResearch.WordTrace]
  refine ⟨2410135600607182988064967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3213514134142910650753289 2410135600607182988064967)
  ·
    refine ⟨3615203400910774482097451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2410135600607182988064967 3615203400910774482097451)
    ·
      refine ⟨5422805101366161723146177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3615203400910774482097451 5422805101366161723146177)
      ·
        refine ⟨4067103826024621292359633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5422805101366161723146177 4067103826024621292359633)
        ·
          refine ⟨3050327869518465969269725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4067103826024621292359633 3050327869518465969269725)
          ·
            refine ⟨1143872951069424738476147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3050327869518465969269725 1143872951069424738476147)
            ·
              refine ⟨1715809426604137107714221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1143872951069424738476147 1715809426604137107714221)
              ·
                refine ⟨643428534976551415392833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1715809426604137107714221 643428534976551415392833)
                ·
                  refine ⟨482571401232413561544625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 643428534976551415392833 482571401232413561544625)
                  ·
                    refine ⟨361928550924310171158469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 482571401232413561544625 361928550924310171158469)
                    ·
                      refine ⟨67861603298308157092213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 361928550924310171158469 67861603298308157092213)
                      ·
                        rfl

theorem cell23_132160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_132160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132160 prefixEnd_132160 := by exact prefixLift 132160
  have htrace : WordTrace (prefixWord ++ tailWord_132160) baseStart_132160 baseEnd_132160 := by
    simpa [prefixWord, tailWord_132160, baseEnd_132160] using wordTrace_append hprefix tailTrace_132160
  have hstable : (prefixWord ++ tailWord_132160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132160).length < 2 ^ (prefixWord ++ tailWord_132160).sum := by decide
  have hdescent : baseEnd_132160 < baseStart_132160 := by decide
  rcases family_descends (prefixWord ++ tailWord_132160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132170 : List Nat := [3, 1, 2, 1, 1, 2, 4, 2, 7]
def baseStart_132170 : Nat := 118140960795 + 132170 * 2 ^ 59
def prefixEnd_132170 : Nat := 4983230072969 + 3 ^ 40 * 132170 * 2
def baseEnd_132170 : Nat := 7540748678317013107463

theorem tailTrace_132170 : CollatzResearch.WordTrace tailWord_132170 prefixEnd_132170 7540748678317013107463 := by
  unfold tailWord_132170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1205158982794534420998491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3213757287452091789329309 1205158982794534420998491)
  ·
    refine ⟨1807738474191801631497737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1205158982794534420998491 1807738474191801631497737)
    ·
      refine ⟨1355803855643851223623303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1807738474191801631497737 1355803855643851223623303)
      ·
        refine ⟨2033705783465776835434955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1355803855643851223623303 2033705783465776835434955)
        ·
          refine ⟨3050558675198665253152433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2033705783465776835434955 3050558675198665253152433)
          ·
            refine ⟨2287919006398998939864325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3050558675198665253152433 2287919006398998939864325)
            ·
              refine ⟨428984813699812301224561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2287919006398998939864325 428984813699812301224561)
              ·
                refine ⟨321738610274859225918421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428984813699812301224561 321738610274859225918421)
                ·
                  refine ⟨7540748678317013107463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 321738610274859225918421 7540748678317013107463)
                  ·
                    rfl

theorem cell23_132170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 7].length) (baseStart_132170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132170 prefixEnd_132170 := by exact prefixLift 132170
  have htrace : WordTrace (prefixWord ++ tailWord_132170) baseStart_132170 baseEnd_132170 := by
    simpa [prefixWord, tailWord_132170, baseEnd_132170] using wordTrace_append hprefix tailTrace_132170
  have hstable : (prefixWord ++ tailWord_132170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132170).length < 2 ^ (prefixWord ++ tailWord_132170).sum := by decide
  have hdescent : baseEnd_132170 < baseStart_132170 := by decide
  rcases family_descends (prefixWord ++ tailWord_132170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132204 : List Nat := [2, 2, 1, 1, 3, 2, 5, 2, 5]
def baseStart_132204 : Nat := 118140960795 + 132204 * 2 ^ 59
def prefixEnd_132204 : Nat := 4983230072969 + 3 ^ 40 * 132204 * 2
def baseEnd_132204 : Nat := 7542688494122887215779

theorem tailTrace_132204 : CollatzResearch.WordTrace tailWord_132204 prefixEnd_132204 7542688494122887215779 := by
  unfold tailWord_132204
  simp only [CollatzResearch.WordTrace]
  refine ⟨2410938006527480745365833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3214584008703307660487777 2410938006527480745365833)
  ·
    refine ⟨1808203504895610559024375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2410938006527480745365833 1808203504895610559024375)
    ·
      refine ⟨2712305257343415838536563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1808203504895610559024375 2712305257343415838536563)
      ·
        refine ⟨4068457886015123757804845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2712305257343415838536563 4068457886015123757804845)
        ·
          refine ⟨1525671707255671409176817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4068457886015123757804845 1525671707255671409176817)
          ·
            refine ⟨1144253780441753556882613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1525671707255671409176817 1144253780441753556882613)
            ·
              refine ⟨107273791916414395957745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1144253780441753556882613 107273791916414395957745)
              ·
                refine ⟨80455343937310796968309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107273791916414395957745 80455343937310796968309)
                ·
                  refine ⟨7542688494122887215779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80455343937310796968309 7542688494122887215779)
                  ·
                    rfl

theorem cell23_132204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2, 5].length) (baseStart_132204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132204 prefixEnd_132204 := by exact prefixLift 132204
  have htrace : WordTrace (prefixWord ++ tailWord_132204) baseStart_132204 baseEnd_132204 := by
    simpa [prefixWord, tailWord_132204, baseEnd_132204] using wordTrace_append hprefix tailTrace_132204
  have hstable : (prefixWord ++ tailWord_132204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132204).length < 2 ^ (prefixWord ++ tailWord_132204).sum := by decide
  have hdescent : baseEnd_132204 < baseStart_132204 := by decide
  rcases family_descends (prefixWord ++ tailWord_132204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132207 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 2, 5, 2]
def baseStart_132207 : Nat := 118140960795 + 132207 * 2 ^ 59
def prefixEnd_132207 : Nat := 4983230072969 + 3 ^ 40 * 132207 * 2
def baseEnd_132207 : Nat := 67885736889069473204497

theorem tailTrace_132207 : CollatzResearch.WordTrace tailWord_132207 prefixEnd_132207 67885736889069473204497 := by
  unfold tailWord_132207
  simp only [CollatzResearch.WordTrace]
  refine ⟨4821985432044093003090875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3214656954696062002060583 4821985432044093003090875)
  ·
    refine ⟨7232978148066139504636313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4821985432044093003090875 7232978148066139504636313)
    ·
      refine ⟨5424733611049604628477235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7232978148066139504636313 5424733611049604628477235)
      ·
        refine ⟨8137100416574406942715853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5424733611049604628477235 8137100416574406942715853)
        ·
          refine ⟨3051412656215402603518445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8137100416574406942715853 3051412656215402603518445)
          ·
            refine ⟨1144279746080775976319417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3051412656215402603518445 1144279746080775976319417)
            ·
              refine ⟨858209809560581982239563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1144279746080775976319417 858209809560581982239563)
              ·
                refine ⟨1287314714340872973359345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 858209809560581982239563 1287314714340872973359345)
                ·
                  refine ⟨965486035755654730019509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1287314714340872973359345 965486035755654730019509)
                  ·
                    refine ⟨90514315852092630939329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 965486035755654730019509 90514315852092630939329)
                    ·
                      refine ⟨67885736889069473204497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 90514315852092630939329 67885736889069473204497)
                      ·
                        rfl

theorem cell23_132207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 5, 2].length) (baseStart_132207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132207 prefixEnd_132207 := by exact prefixLift 132207
  have htrace : WordTrace (prefixWord ++ tailWord_132207) baseStart_132207 baseEnd_132207 := by
    simpa [prefixWord, tailWord_132207, baseEnd_132207] using wordTrace_append hprefix tailTrace_132207
  have hstable : (prefixWord ++ tailWord_132207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132207).length < 2 ^ (prefixWord ++ tailWord_132207).sum := by decide
  have hdescent : baseEnd_132207 < baseStart_132207 := by decide
  rcases family_descends (prefixWord ++ tailWord_132207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132280 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 3, 2, 6]
def baseStart_132280 : Nat := 118140960795 + 132280 * 2 ^ 59
def prefixEnd_132280 : Nat := 4983230072969 + 3 ^ 40 * 132280 * 2
def baseEnd_132280 : Nat := 67923220976847687591661

theorem tailTrace_132280 : CollatzResearch.WordTrace tailWord_132280 prefixEnd_132280 67923220976847687591661 := by
  unfold tailWord_132280
  simp only [CollatzResearch.WordTrace]
  refine ⟨2412323980389813235249147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3216431973853084313665529 2412323980389813235249147)
  ·
    refine ⟨3618485970584719852873721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2412323980389813235249147 3618485970584719852873721)
    ·
      refine ⟨2713864477938539889655291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3618485970584719852873721 2713864477938539889655291)
      ·
        refine ⟨4070796716907809834482937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2713864477938539889655291 4070796716907809834482937)
        ·
          refine ⟨3053097537680857375862203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4070796716907809834482937 3053097537680857375862203)
          ·
            refine ⟨4579646306521286063793305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3053097537680857375862203 4579646306521286063793305)
            ·
              refine ⟨3434734729890964547844979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4579646306521286063793305 3434734729890964547844979)
              ·
                refine ⟨5152102094836446821767469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3434734729890964547844979 5152102094836446821767469)
                ·
                  refine ⟨1932038285563667558162801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5152102094836446821767469 1932038285563667558162801)
                  ·
                    refine ⟨1449028714172750668622101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1932038285563667558162801 1449028714172750668622101)
                    ·
                      refine ⟨67923220976847687591661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1449028714172750668622101 67923220976847687591661)
                      ·
                        rfl

theorem cell23_132280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_132280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132280 prefixEnd_132280 := by exact prefixLift 132280
  have htrace : WordTrace (prefixWord ++ tailWord_132280) baseStart_132280 baseEnd_132280 := by
    simpa [prefixWord, tailWord_132280, baseEnd_132280] using wordTrace_append hprefix tailTrace_132280
  have hstable : (prefixWord ++ tailWord_132280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132280).length < 2 ^ (prefixWord ++ tailWord_132280).sum := by decide
  have hdescent : baseEnd_132280 < baseStart_132280 := by decide
  rcases family_descends (prefixWord ++ tailWord_132280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132307 : List Nat := [1, 1, 1, 2, 1, 1, 1, 9, 1, 5]
def baseStart_132307 : Nat := 118140960795 + 132307 * 2 ^ 59
def prefixEnd_132307 : Nat := 4983230072969 + 3 ^ 40 * 132307 * 2
def baseEnd_132307 : Nat := 22645694984839693984679

theorem tailTrace_132307 : CollatzResearch.WordTrace tailWord_132307 prefixEnd_132307 22645694984839693984679 := by
  unfold tailWord_132307
  simp only [CollatzResearch.WordTrace]
  refine ⟨4825632731681810081731175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3217088487787873387820783 4825632731681810081731175)
  ·
    refine ⟨7238449097522715122596763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4825632731681810081731175 7238449097522715122596763)
    ·
      refine ⟨10857673646284072683895145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7238449097522715122596763 10857673646284072683895145)
      ·
        refine ⟨8143255234713054512921359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10857673646284072683895145 8143255234713054512921359)
        ·
          refine ⟨12214882852069581769382039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8143255234713054512921359 12214882852069581769382039)
          ·
            refine ⟨18322324278104372654073059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12214882852069581769382039 18322324278104372654073059)
            ·
              refine ⟨27483486417156558981109589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18322324278104372654073059 27483486417156558981109589)
              ·
                refine ⟨161036053225526712779939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 27483486417156558981109589 161036053225526712779939)
                ·
                  refine ⟨241554079838290069169909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161036053225526712779939 241554079838290069169909)
                  ·
                    refine ⟨22645694984839693984679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 241554079838290069169909 22645694984839693984679)
                    ·
                      rfl

theorem cell23_132307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 5].length) (baseStart_132307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132307 prefixEnd_132307 := by exact prefixLift 132307
  have htrace : WordTrace (prefixWord ++ tailWord_132307) baseStart_132307 baseEnd_132307 := by
    simpa [prefixWord, tailWord_132307, baseEnd_132307] using wordTrace_append hprefix tailTrace_132307
  have hstable : (prefixWord ++ tailWord_132307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132307).length < 2 ^ (prefixWord ++ tailWord_132307).sum := by decide
  have hdescent : baseEnd_132307 < baseStart_132307 := by decide
  rcases family_descends (prefixWord ++ tailWord_132307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132314 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2]
def baseStart_132314 : Nat := 118140960795 + 132314 * 2 ^ 59
def prefixEnd_132314 : Nat := 4983230072969 + 3 ^ 40 * 132314 * 2
def baseEnd_132314 : Nat := 67940679319100554566505

theorem tailTrace_132314 : CollatzResearch.WordTrace tailWord_132314 prefixEnd_132314 67940679319100554566505 := by
  unfold tailWord_132314
  simp only [CollatzResearch.WordTrace]
  refine ⟨1206472010664112569308999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3217258695104300184823997 1206472010664112569308999)
  ·
    refine ⟨1809708015996168853963499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1206472010664112569308999 1809708015996168853963499)
    ·
      refine ⟨2714562023994253280945249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1809708015996168853963499 2714562023994253280945249)
      ·
        refine ⟨2035921517995689960708937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2714562023994253280945249 2035921517995689960708937)
        ·
          refine ⟨1526941138496767470531703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2035921517995689960708937 1526941138496767470531703)
          ·
            refine ⟨2290411707745151205797555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1526941138496767470531703 2290411707745151205797555)
            ·
              refine ⟨3435617561617726808696333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2290411707745151205797555 3435617561617726808696333)
              ·
                refine ⟨1288356585606647553261125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3435617561617726808696333 1288356585606647553261125)
                ·
                  refine ⟨241566859801246416236461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1288356585606647553261125 241566859801246416236461)
                  ·
                    refine ⟨90587572425467406088673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 241566859801246416236461 90587572425467406088673)
                    ·
                      refine ⟨67940679319100554566505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 90587572425467406088673 67940679319100554566505)
                      ·
                        rfl

theorem cell23_132314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2].length) (baseStart_132314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132314 prefixEnd_132314 := by exact prefixLift 132314
  have htrace : WordTrace (prefixWord ++ tailWord_132314) baseStart_132314 baseEnd_132314 := by
    simpa [prefixWord, tailWord_132314, baseEnd_132314] using wordTrace_append hprefix tailTrace_132314
  have hstable : (prefixWord ++ tailWord_132314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132314).length < 2 ^ (prefixWord ++ tailWord_132314).sum := by decide
  have hdescent : baseEnd_132314 < baseStart_132314 := by decide
  rcases family_descends (prefixWord ++ tailWord_132314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132321 : List Nat := [1, 2, 3, 1, 3, 3, 2, 1, 3, 1, 3]
def baseStart_132321 : Nat := 118140960795 + 132321 * 2 ^ 59
def prefixEnd_132321 : Nat := 4983230072969 + 3 ^ 40 * 132321 * 2
def baseEnd_132321 : Nat := 67944273683682027178973

theorem tailTrace_132321 : CollatzResearch.WordTrace tailWord_132321 prefixEnd_132321 67944273683682027178973 := by
  unfold tailWord_132321
  simp only [CollatzResearch.WordTrace]
  refine ⟨4826143353631090472740817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3217428902420726981827211 4826143353631090472740817)
  ·
    refine ⟨3619607515223317854555613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4826143353631090472740817 3619607515223317854555613)
    ·
      refine ⟨1357352818208744195458355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3619607515223317854555613 1357352818208744195458355)
      ·
        refine ⟨2036029227313116293187533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1357352818208744195458355 2036029227313116293187533)
        ·
          refine ⟨763510960242418609945325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2036029227313116293187533 763510960242418609945325)
          ·
            refine ⟨286316610090906978729497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 763510960242418609945325 286316610090906978729497)
            ·
              refine ⟨214737457568180234047123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286316610090906978729497 214737457568180234047123)
              ·
                refine ⟨322106186352270351070685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214737457568180234047123 322106186352270351070685)
                ·
                  refine ⟨120789819882101381651507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322106186352270351070685 120789819882101381651507)
                  ·
                    refine ⟨181184729823152072477261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120789819882101381651507 181184729823152072477261)
                    ·
                      refine ⟨67944273683682027178973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 181184729823152072477261 67944273683682027178973)
                      ·
                        rfl

theorem cell23_132321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_132321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132321 prefixEnd_132321 := by exact prefixLift 132321
  have htrace : WordTrace (prefixWord ++ tailWord_132321) baseStart_132321 baseEnd_132321 := by
    simpa [prefixWord, tailWord_132321, baseEnd_132321] using wordTrace_append hprefix tailTrace_132321
  have hstable : (prefixWord ++ tailWord_132321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132321).length < 2 ^ (prefixWord ++ tailWord_132321).sum := by decide
  have hdescent : baseEnd_132321 < baseStart_132321 := by decide
  rcases family_descends (prefixWord ++ tailWord_132321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132357 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 3, 2, 4]
def baseStart_132357 : Nat := 118140960795 + 132357 * 2 ^ 59
def prefixEnd_132357 : Nat := 4983230072969 + 3 ^ 40 * 132357 * 2
def baseEnd_132357 : Nat := 67962758987243886328807

theorem tailTrace_132357 : CollatzResearch.WordTrace tailWord_132357 prefixEnd_132357 67962758987243886328807 := by
  unfold tailWord_132357
  simp only [CollatzResearch.WordTrace]
  refine ⟨4827456381500668621051325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3218304254333779080700883 4827456381500668621051325)
  ·
    refine ⟨1810296143062750732894247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4827456381500668621051325 1810296143062750732894247)
    ·
      refine ⟨2715444214594126099341371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1810296143062750732894247 2715444214594126099341371)
      ·
        refine ⟨4073166321891189149012057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2715444214594126099341371 4073166321891189149012057)
        ·
          refine ⟨3054874741418391861759043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4073166321891189149012057 3054874741418391861759043)
          ·
            refine ⟨4582312112127587792638565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3054874741418391861759043 4582312112127587792638565)
            ·
              refine ⟨859183521023922711119731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4582312112127587792638565 859183521023922711119731)
              ·
                refine ⟨1288775281535884066679597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 859183521023922711119731 1288775281535884066679597)
                ·
                  refine ⟨483290730575956525004849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1288775281535884066679597 483290730575956525004849)
                  ·
                    refine ⟨362468047931967393753637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 483290730575956525004849 362468047931967393753637)
                    ·
                      refine ⟨67962758987243886328807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 362468047931967393753637 67962758987243886328807)
                      ·
                        rfl

theorem cell23_132357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_132357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132357 prefixEnd_132357 := by exact prefixLift 132357
  have htrace : WordTrace (prefixWord ++ tailWord_132357) baseStart_132357 baseEnd_132357 := by
    simpa [prefixWord, tailWord_132357, baseEnd_132357] using wordTrace_append hprefix tailTrace_132357
  have hstable : (prefixWord ++ tailWord_132357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132357).length < 2 ^ (prefixWord ++ tailWord_132357).sum := by decide
  have hdescent : baseEnd_132357 < baseStart_132357 := by decide
  rcases family_descends (prefixWord ++ tailWord_132357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132364 : List Nat := [2, 2, 1, 2, 2, 4, 2, 1, 1, 1, 5]
def baseStart_132364 : Nat := 118140960795 + 132364 * 2 ^ 59
def prefixEnd_132364 : Nat := 4983230072969 + 3 ^ 40 * 132364 * 2
def baseEnd_132364 : Nat := 67966353351825358941275

theorem tailTrace_132364 : CollatzResearch.WordTrace tailWord_132364 prefixEnd_132364 67966353351825358941275 := by
  unfold tailWord_132364
  simp only [CollatzResearch.WordTrace]
  refine ⟨2413855846237654408278073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3218474461650205877704097 2413855846237654408278073)
  ·
    refine ⟨1810391884678240806208555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2413855846237654408278073 1810391884678240806208555)
    ·
      refine ⟨2715587827017361209312833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1810391884678240806208555 2715587827017361209312833)
      ·
        refine ⟨2036690870263020906984625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2715587827017361209312833 2036690870263020906984625)
        ·
          refine ⟨1527518152697265680238469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2036690870263020906984625 1527518152697265680238469)
          ·
            refine ⟨286409653630737315044713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1527518152697265680238469 286409653630737315044713)
            ·
              refine ⟨214807240223052986283535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286409653630737315044713 214807240223052986283535)
              ·
                refine ⟨322210860334579479425303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214807240223052986283535 322210860334579479425303)
                ·
                  refine ⟨483316290501869219137955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322210860334579479425303 483316290501869219137955)
                  ·
                    refine ⟨724974435752803828706933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 483316290501869219137955 724974435752803828706933)
                    ·
                      refine ⟨67966353351825358941275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 724974435752803828706933 67966353351825358941275)
                      ·
                        rfl

theorem cell23_132364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_132364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132364 prefixEnd_132364 := by exact prefixLift 132364
  have htrace : WordTrace (prefixWord ++ tailWord_132364) baseStart_132364 baseEnd_132364 := by
    simpa [prefixWord, tailWord_132364, baseEnd_132364] using wordTrace_append hprefix tailTrace_132364
  have hstable : (prefixWord ++ tailWord_132364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132364).length < 2 ^ (prefixWord ++ tailWord_132364).sum := by decide
  have hdescent : baseEnd_132364 < baseStart_132364 := by decide
  rcases family_descends (prefixWord ++ tailWord_132364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132378 : List Nat := [3, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2]
def baseStart_132378 : Nat := 118140960795 + 132378 * 2 ^ 59
def prefixEnd_132378 : Nat := 4983230072969 + 3 ^ 40 * 132378 * 2
def baseEnd_132378 : Nat := 67973542080988304166211

theorem tailTrace_132378 : CollatzResearch.WordTrace tailWord_132378 prefixEnd_132378 67973542080988304166211 := by
  unfold tailWord_132378
  simp only [CollatzResearch.WordTrace]
  refine ⟨1207055578606147301891447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3218814876283059471710525 1207055578606147301891447)
  ·
    refine ⟨1810583367909220952837171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1207055578606147301891447 1810583367909220952837171)
    ·
      refine ⟨2715875051863831429255757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1810583367909220952837171 2715875051863831429255757)
      ·
        refine ⟨1018453144448936785970909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2715875051863831429255757 1018453144448936785970909)
        ·
          refine ⟨381919929168351294739091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1018453144448936785970909 381919929168351294739091)
          ·
            refine ⟨572879893752526942108637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381919929168351294739091 572879893752526942108637)
            ·
              refine ⟨214829960157197603290739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 572879893752526942108637 214829960157197603290739)
              ·
                refine ⟨322244940235796404936109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214829960157197603290739 322244940235796404936109)
                ·
                  refine ⟨120841852588423651851041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322244940235796404936109 120841852588423651851041)
                  ·
                    refine ⟨90631389441317738888281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120841852588423651851041 90631389441317738888281)
                    ·
                      refine ⟨67973542080988304166211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 90631389441317738888281 67973542080988304166211)
                      ·
                        rfl

theorem cell23_132378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_132378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132378 prefixEnd_132378 := by exact prefixLift 132378
  have htrace : WordTrace (prefixWord ++ tailWord_132378) baseStart_132378 baseEnd_132378 := by
    simpa [prefixWord, tailWord_132378, baseEnd_132378] using wordTrace_append hprefix tailTrace_132378
  have hstable : (prefixWord ++ tailWord_132378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132378).length < 2 ^ (prefixWord ++ tailWord_132378).sum := by decide
  have hdescent : baseEnd_132378 < baseStart_132378 := by decide
  rcases family_descends (prefixWord ++ tailWord_132378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132384 : List Nat := [2, 1, 1, 5, 3, 1, 2, 8]
def baseStart_132384 : Nat := 118140960795 + 132384 * 2 ^ 59
def prefixEnd_132384 : Nat := 4983230072969 + 3 ^ 40 * 132384 * 2
def baseEnd_132384 : Nat := 2517652702404269655229

theorem tailTrace_132384 : CollatzResearch.WordTrace tailWord_132384 prefixEnd_132384 2517652702404269655229 := by
  unfold tailWord_132384
  simp only [CollatzResearch.WordTrace]
  refine ⟨2414220576201426116142103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3218960768268568154856137 2414220576201426116142103)
  ·
    refine ⟨3621330864302139174213155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2414220576201426116142103 3621330864302139174213155)
    ·
      refine ⟨5431996296453208761319733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3621330864302139174213155 5431996296453208761319733)
      ·
        refine ⟨509249652792488321373725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5431996296453208761319733 509249652792488321373725)
        ·
          refine ⟨190968619797183120515147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 509249652792488321373725 190968619797183120515147)
          ·
            refine ⟨286452929695774680772721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190968619797183120515147 286452929695774680772721)
            ·
              refine ⟨214839697271831010579541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286452929695774680772721 214839697271831010579541)
              ·
                refine ⟨2517652702404269655229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 214839697271831010579541 2517652702404269655229)
                ·
                  rfl

theorem cell23_132384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 8].length) (baseStart_132384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132384 prefixEnd_132384 := by exact prefixLift 132384
  have htrace : WordTrace (prefixWord ++ tailWord_132384) baseStart_132384 baseEnd_132384 := by
    simpa [prefixWord, tailWord_132384, baseEnd_132384] using wordTrace_append hprefix tailTrace_132384
  have hstable : (prefixWord ++ tailWord_132384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132384).length < 2 ^ (prefixWord ++ tailWord_132384).sum := by decide
  have hdescent : baseEnd_132384 < baseStart_132384 := by decide
  rcases family_descends (prefixWord ++ tailWord_132384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132421 : List Nat := [1, 3, 1, 1, 1, 2, 1, 7, 1, 3, 2]
def baseStart_132421 : Nat := 118140960795 + 132421 * 2 ^ 59
def prefixEnd_132421 : Nat := 4983230072969 + 3 ^ 40 * 132421 * 2
def baseEnd_132421 : Nat := 67995621749131635928513

theorem tailTrace_132421 : CollatzResearch.WordTrace tailWord_132421 prefixEnd_132421 67995621749131635928513 := by
  unfold tailWord_132421
  simp only [CollatzResearch.WordTrace]
  refine ⟨4829790653268807551381117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3219860435512538367587411 4829790653268807551381117)
  ·
    refine ⟨1811171494975802831767919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4829790653268807551381117 1811171494975802831767919)
    ·
      refine ⟨2716757242463704247651879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1811171494975802831767919 2716757242463704247651879)
      ·
        refine ⟨4075135863695556371477819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2716757242463704247651879 4075135863695556371477819)
        ·
          refine ⟨6112703795543334557216729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4075135863695556371477819 6112703795543334557216729)
          ·
            refine ⟨4584527846657500917912547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6112703795543334557216729 4584527846657500917912547)
            ·
              refine ⟨6876791769986251376868821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4584527846657500917912547 6876791769986251376868821)
              ·
                refine ⟨161174807109052766645363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6876791769986251376868821 161174807109052766645363)
                ·
                  refine ⟨241762210663579149968045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161174807109052766645363 241762210663579149968045)
                  ·
                    refine ⟨90660828998842181238017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 241762210663579149968045 90660828998842181238017)
                    ·
                      refine ⟨67995621749131635928513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 90660828998842181238017 67995621749131635928513)
                      ·
                        rfl

theorem cell23_132421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 3, 2].length) (baseStart_132421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132421 prefixEnd_132421 := by exact prefixLift 132421
  have htrace : WordTrace (prefixWord ++ tailWord_132421) baseStart_132421 baseEnd_132421 := by
    simpa [prefixWord, tailWord_132421, baseEnd_132421] using wordTrace_append hprefix tailTrace_132421
  have hstable : (prefixWord ++ tailWord_132421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132421).length < 2 ^ (prefixWord ++ tailWord_132421).sum := by decide
  have hdescent : baseEnd_132421 < baseStart_132421 := by decide
  rcases family_descends (prefixWord ++ tailWord_132421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132422 : List Nat := [6, 1, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_132422 : Nat := 118140960795 + 132422 * 2 ^ 59
def prefixEnd_132422 : Nat := 4983230072969 + 3 ^ 40 * 132422 * 2
def baseEnd_132422 : Nat := 22665378409928710672003

theorem tailTrace_132422 : CollatzResearch.WordTrace tailWord_132422 prefixEnd_132422 22665378409928710672003 := by
  unfold tailWord_132422
  simp only [CollatzResearch.WordTrace]
  refine ⟨150932097695787022567735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3219884750843456481445013 150932097695787022567735)
  ·
    refine ⟨226398146543680533851603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150932097695787022567735 226398146543680533851603)
    ·
      refine ⟨339597219815520800777405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226398146543680533851603 339597219815520800777405)
      ·
        refine ⟨127348957430820300291527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339597219815520800777405 127348957430820300291527)
        ·
          refine ⟨191023436146230450437291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127348957430820300291527 191023436146230450437291)
          ·
            refine ⟨286535154219345675655937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191023436146230450437291 286535154219345675655937)
            ·
              refine ⟨214901365664509256741953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286535154219345675655937 214901365664509256741953)
              ·
                refine ⟨161176024248381942556465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214901365664509256741953 161176024248381942556465)
                ·
                  refine ⟨120882018186286456917349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161176024248381942556465 120882018186286456917349)
                  ·
                    refine ⟨22665378409928710672003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120882018186286456917349 22665378409928710672003)
                    ·
                      rfl

theorem cell23_132422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_132422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132422 prefixEnd_132422 := by exact prefixLift 132422
  have htrace : WordTrace (prefixWord ++ tailWord_132422) baseStart_132422 baseEnd_132422 := by
    simpa [prefixWord, tailWord_132422, baseEnd_132422] using wordTrace_append hprefix tailTrace_132422
  have hstable : (prefixWord ++ tailWord_132422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132422).length < 2 ^ (prefixWord ++ tailWord_132422).sum := by decide
  have hdescent : baseEnd_132422 < baseStart_132422 := by decide
  rcases family_descends (prefixWord ++ tailWord_132422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132428 : List Nat := [2, 2, 1, 3, 2, 3, 2, 2, 2, 1, 3]
def baseStart_132428 : Nat := 118140960795 + 132428 * 2 ^ 59
def prefixEnd_132428 : Nat := 4983230072969 + 3 ^ 40 * 132428 * 2
def baseEnd_132428 : Nat := 67999216113713108540981

theorem tailTrace_132428 : CollatzResearch.WordTrace tailWord_132428 prefixEnd_132428 67999216113713108540981 := by
  unfold tailWord_132428
  simp only [CollatzResearch.WordTrace]
  refine ⟨2415022982121723873442969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3220030642828965164590625 2415022982121723873442969)
  ·
    refine ⟨1811267236591292905082227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2415022982121723873442969 1811267236591292905082227)
    ·
      refine ⟨2716900854886939357623341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1811267236591292905082227 2716900854886939357623341)
      ·
        refine ⟨1018837820582602259108753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2716900854886939357623341 1018837820582602259108753)
        ·
          refine ⟨764128365436951694331565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1018837820582602259108753 764128365436951694331565)
          ·
            refine ⟨286548137038856885374337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 764128365436951694331565 286548137038856885374337)
            ·
              refine ⟨214911102779142664030753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286548137038856885374337 214911102779142664030753)
              ·
                refine ⟨161183327084356998023065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214911102779142664030753 161183327084356998023065)
                ·
                  refine ⟨120887495313267748517299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161183327084356998023065 120887495313267748517299)
                  ·
                    refine ⟨181331242969901622775949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120887495313267748517299 181331242969901622775949)
                    ·
                      refine ⟨67999216113713108540981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 181331242969901622775949 67999216113713108540981)
                      ·
                        rfl

theorem cell23_132428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_132428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132428 prefixEnd_132428 := by exact prefixLift 132428
  have htrace : WordTrace (prefixWord ++ tailWord_132428) baseStart_132428 baseEnd_132428 := by
    simpa [prefixWord, tailWord_132428, baseEnd_132428] using wordTrace_append hprefix tailTrace_132428
  have hstable : (prefixWord ++ tailWord_132428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132428).length < 2 ^ (prefixWord ++ tailWord_132428).sum := by decide
  have hdescent : baseEnd_132428 < baseStart_132428 := by decide
  rcases family_descends (prefixWord ++ tailWord_132428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132429 : List Nat := [1, 6, 1, 3, 1, 1, 1, 4, 1, 2, 2]
def baseStart_132429 : Nat := 118140960795 + 132429 * 2 ^ 59
def prefixEnd_132429 : Nat := 4983230072969 + 3 ^ 40 * 132429 * 2
def baseEnd_132429 : Nat := 67999729594367604628477

theorem tailTrace_132429 : CollatzResearch.WordTrace tailWord_132429 prefixEnd_132429 67999729594367604628477 := by
  unfold tailWord_132429
  simp only [CollatzResearch.WordTrace]
  refine ⟨4830082437239824917672341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3220054958159883278448227 4830082437239824917672341)
  ·
    refine ⟨226410114245616793015891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4830082437239824917672341 226410114245616793015891)
    ·
      refine ⟨339615171368425189523837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226410114245616793015891 339615171368425189523837)
      ·
        refine ⟨127355689263159446071439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339615171368425189523837 127355689263159446071439)
        ·
          refine ⟨191033533894739169107159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127355689263159446071439 191033533894739169107159)
          ·
            refine ⟨286550300842108753660739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191033533894739169107159 286550300842108753660739)
            ·
              refine ⟨429825451263163130491109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286550300842108753660739 429825451263163130491109)
              ·
                refine ⟨80592272111843086967083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 429825451263163130491109 80592272111843086967083)
                ·
                  refine ⟨120888408167764630450625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80592272111843086967083 120888408167764630450625)
                  ·
                    refine ⟨90666306125823472837969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120888408167764630450625 90666306125823472837969)
                    ·
                      refine ⟨67999729594367604628477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 90666306125823472837969 67999729594367604628477)
                      ·
                        rfl

theorem cell23_132429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_132429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132429 prefixEnd_132429 := by exact prefixLift 132429
  have htrace : WordTrace (prefixWord ++ tailWord_132429) baseStart_132429 baseEnd_132429 := by
    simpa [prefixWord, tailWord_132429, baseEnd_132429] using wordTrace_append hprefix tailTrace_132429
  have hstable : (prefixWord ++ tailWord_132429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132429).length < 2 ^ (prefixWord ++ tailWord_132429).sum := by decide
  have hdescent : baseEnd_132429 < baseStart_132429 := by decide
  rcases family_descends (prefixWord ++ tailWord_132429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132451 : List Nat := [1, 1, 1, 5, 2, 2, 1, 3, 1, 4, 2]
def baseStart_132451 : Nat := 118140960795 + 132451 * 2 ^ 59
def prefixEnd_132451 : Nat := 4983230072969 + 3 ^ 40 * 132451 * 2
def baseEnd_132451 : Nat := 68011026168766518553375

theorem tailTrace_132451 : CollatzResearch.WordTrace tailWord_132451 prefixEnd_132451 68011026168766518553375 := by
  unfold tailWord_132451
  simp only [CollatzResearch.WordTrace]
  refine ⟨4830884843160122674973207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3220589895440081783315471 4830884843160122674973207)
  ·
    refine ⟨7246327264740184012459811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4830884843160122674973207 7246327264740184012459811)
    ·
      refine ⟨10869490897110276018689717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7246327264740184012459811 10869490897110276018689717)
      ·
        refine ⟨1019014771604088376752161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10869490897110276018689717 1019014771604088376752161)
        ·
          refine ⟨764261078703066282564121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1019014771604088376752161 764261078703066282564121)
          ·
            refine ⟨573195809027299711923091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 764261078703066282564121 573195809027299711923091)
            ·
              refine ⟨859793713540949567884637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573195809027299711923091 859793713540949567884637)
              ·
                refine ⟨322422642577856087956739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 859793713540949567884637 322422642577856087956739)
                ·
                  refine ⟨483633963866784131935109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322422642577856087956739 483633963866784131935109)
                  ·
                    refine ⟨90681368225022024737833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 483633963866784131935109 90681368225022024737833)
                    ·
                      refine ⟨68011026168766518553375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 90681368225022024737833 68011026168766518553375)
                      ·
                        rfl

theorem cell23_132451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_132451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132451 prefixEnd_132451 := by exact prefixLift 132451
  have htrace : WordTrace (prefixWord ++ tailWord_132451) baseStart_132451 baseEnd_132451 := by
    simpa [prefixWord, tailWord_132451, baseEnd_132451] using wordTrace_append hprefix tailTrace_132451
  have hstable : (prefixWord ++ tailWord_132451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132451).length < 2 ^ (prefixWord ++ tailWord_132451).sum := by decide
  have hdescent : baseEnd_132451 < baseStart_132451 := by decide
  rcases family_descends (prefixWord ++ tailWord_132451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132524 : List Nat := [2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 4]
def baseStart_132524 : Nat := 118140960795 + 132524 * 2 ^ 59
def prefixEnd_132524 : Nat := 4983230072969 + 3 ^ 40 * 132524 * 2
def baseEnd_132524 : Nat := 68048510256544732940539

theorem tailTrace_132524 : CollatzResearch.WordTrace tailWord_132524 prefixEnd_132524 68048510256544732940539 := by
  unfold tailWord_132524
  simp only [CollatzResearch.WordTrace]
  refine ⟨2416773685947828071190313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3222364914597104094920417 2416773685947828071190313)
  ·
    refine ⟨1812580264460871053392735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2416773685947828071190313 1812580264460871053392735)
    ·
      refine ⟨2718870396691306580089103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1812580264460871053392735 2718870396691306580089103)
      ·
        refine ⟨4078305595036959870133655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2718870396691306580089103 4078305595036959870133655)
        ·
          refine ⟨6117458392555439805200483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4078305595036959870133655 6117458392555439805200483)
          ·
            refine ⟨9176187588833159707800725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6117458392555439805200483 9176187588833159707800725)
            ·
              refine ⟨430133793226554361303159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9176187588833159707800725 430133793226554361303159)
              ·
                refine ⟨645200689839831541954739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430133793226554361303159 645200689839831541954739)
                ·
                  refine ⟨967801034759747312932109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 645200689839831541954739 967801034759747312932109)
                  ·
                    refine ⟨362925388034905242349541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 967801034759747312932109 362925388034905242349541)
                    ·
                      refine ⟨68048510256544732940539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 362925388034905242349541 68048510256544732940539)
                      ·
                        rfl

theorem cell23_132524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_132524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132524 prefixEnd_132524 := by exact prefixLift 132524
  have htrace : WordTrace (prefixWord ++ tailWord_132524) baseStart_132524 baseEnd_132524 := by
    simpa [prefixWord, tailWord_132524, baseEnd_132524] using wordTrace_append hprefix tailTrace_132524
  have hstable : (prefixWord ++ tailWord_132524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132524).length < 2 ^ (prefixWord ++ tailWord_132524).sum := by decide
  have hdescent : baseEnd_132524 < baseStart_132524 := by decide
  rcases family_descends (prefixWord ++ tailWord_132524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132525 : List Nat := [1, 5, 2, 2, 1, 3, 1, 3, 5]
def baseStart_132525 : Nat := 118140960795 + 132525 * 2 ^ 59
def prefixEnd_132525 : Nat := 4983230072969 + 3 ^ 40 * 132525 * 2
def baseEnd_132525 : Nat := 7561002637466581003115

theorem tailTrace_132525 : CollatzResearch.WordTrace tailWord_132525 prefixEnd_132525 7561002637466581003115 := by
  unfold tailWord_132525
  simp only [CollatzResearch.WordTrace]
  refine ⟨4833583844892033313167029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3222389229928022208778019 4833583844892033313167029)
  ·
    refine ⟨453148485458628123109409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4833583844892033313167029 453148485458628123109409)
    ·
      refine ⟨339861364093971092332057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453148485458628123109409 339861364093971092332057)
      ·
        refine ⟨254896023070478319249043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339861364093971092332057 254896023070478319249043)
        ·
          refine ⟨382344034605717478873565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254896023070478319249043 382344034605717478873565)
          ·
            refine ⟨143379012977144054577587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382344034605717478873565 143379012977144054577587)
            ·
              refine ⟨215068519465716081866381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143379012977144054577587 215068519465716081866381)
              ·
                refine ⟨80650694799643530699893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215068519465716081866381 80650694799643530699893)
                ·
                  refine ⟨7561002637466581003115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80650694799643530699893 7561002637466581003115)
                  ·
                    rfl

theorem cell23_132525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_132525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132525 prefixEnd_132525 := by exact prefixLift 132525
  have htrace : WordTrace (prefixWord ++ tailWord_132525) baseStart_132525 baseEnd_132525 := by
    simpa [prefixWord, tailWord_132525, baseEnd_132525] using wordTrace_append hprefix tailTrace_132525
  have hstable : (prefixWord ++ tailWord_132525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132525).length < 2 ^ (prefixWord ++ tailWord_132525).sum := by decide
  have hdescent : baseEnd_132525 < baseStart_132525 := by decide
  rcases family_descends (prefixWord ++ tailWord_132525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132541 : List Nat := [1, 4, 1, 2, 2, 1, 3, 2, 2, 1, 4]
def baseStart_132541 : Nat := 118140960795 + 132541 * 2 ^ 59
def prefixEnd_132541 : Nat := 4983230072969 + 3 ^ 40 * 132541 * 2
def baseEnd_132541 : Nat := 68057239427671166427961

theorem tailTrace_132541 : CollatzResearch.WordTrace tailWord_132541 prefixEnd_132541 68057239427671166427961 := by
  unfold tailWord_132541
  simp only [CollatzResearch.WordTrace]
  refine ⟨4834167412834068045749477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3222778275222712030499651 4834167412834068045749477)
  ·
    refine ⟨906406389906387758578027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4834167412834068045749477 906406389906387758578027)
    ·
      refine ⟨1359609584859581637867041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 906406389906387758578027 1359609584859581637867041)
      ·
        refine ⟨1019707188644686228400281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1359609584859581637867041 1019707188644686228400281)
        ·
          refine ⟨764780391483514671300211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1019707188644686228400281 764780391483514671300211)
          ·
            refine ⟨1147170587225272006950317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764780391483514671300211 1147170587225272006950317)
            ·
              refine ⟨430188970209477002606369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1147170587225272006950317 430188970209477002606369)
              ·
                refine ⟨322641727657107751954777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430188970209477002606369 322641727657107751954777)
                ·
                  refine ⟨241981295742830813966083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322641727657107751954777 241981295742830813966083)
                  ·
                    refine ⟨362971943614246220949125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 241981295742830813966083 362971943614246220949125)
                    ·
                      refine ⟨68057239427671166427961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 362971943614246220949125 68057239427671166427961)
                      ·
                        rfl

theorem cell23_132541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_132541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132541 prefixEnd_132541 := by exact prefixLift 132541
  have htrace : WordTrace (prefixWord ++ tailWord_132541) baseStart_132541 baseEnd_132541 := by
    simpa [prefixWord, tailWord_132541, baseEnd_132541] using wordTrace_append hprefix tailTrace_132541
  have hstable : (prefixWord ++ tailWord_132541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132541).length < 2 ^ (prefixWord ++ tailWord_132541).sum := by decide
  have hdescent : baseEnd_132541 < baseStart_132541 := by decide
  rcases family_descends (prefixWord ++ tailWord_132541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132598 : List Nat := [5, 1, 1, 1, 2, 3, 2, 2, 6]
def baseStart_132598 : Nat := 118140960795 + 132598 * 2 ^ 59
def prefixEnd_132598 : Nat := 4983230072969 + 3 ^ 40 * 132598 * 2
def baseEnd_132598 : Nat := 7565167536108604823911

theorem tailTrace_132598 : CollatzResearch.WordTrace tailWord_132598 prefixEnd_132598 7565167536108604823911 := by
  unfold tailWord_132598
  simp only [CollatzResearch.WordTrace]
  refine ⟨302265398351722923785903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3224164249085044520382965 302265398351722923785903)
  ·
    refine ⟨453398097527584385678855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302265398351722923785903 453398097527584385678855)
    ·
      refine ⟨680097146291376578518283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453398097527584385678855 680097146291376578518283)
      ·
        refine ⟨1020145719437064867777425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680097146291376578518283 1020145719437064867777425)
        ·
          refine ⟨765109289577798650833069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1020145719437064867777425 765109289577798650833069)
          ·
            refine ⟨286915983591674494062401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 765109289577798650833069 286915983591674494062401)
            ·
              refine ⟨215186987693755870546801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286915983591674494062401 215186987693755870546801)
              ·
                refine ⟨161390240770316902910101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215186987693755870546801 161390240770316902910101)
                ·
                  refine ⟨7565167536108604823911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 161390240770316902910101 7565167536108604823911)
                  ·
                    rfl

theorem cell23_132598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_132598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132598 prefixEnd_132598 := by exact prefixLift 132598
  have htrace : WordTrace (prefixWord ++ tailWord_132598) baseStart_132598 baseEnd_132598 := by
    simpa [prefixWord, tailWord_132598, baseEnd_132598] using wordTrace_append hprefix tailTrace_132598
  have hstable : (prefixWord ++ tailWord_132598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132598).length < 2 ^ (prefixWord ++ tailWord_132598).sum := by decide
  have hdescent : baseEnd_132598 < baseStart_132598 := by decide
  rcases family_descends (prefixWord ++ tailWord_132598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132601 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 3, 5, 2]
def baseStart_132601 : Nat := 118140960795 + 132601 * 2 ^ 59
def prefixEnd_132601 : Nat := 4983230072969 + 3 ^ 40 * 132601 * 2
def baseEnd_132601 : Nat := 68088048266940931677685

theorem tailTrace_132601 : CollatzResearch.WordTrace tailWord_132601 prefixEnd_132601 68088048266940931677685 := by
  unfold tailWord_132601
  simp only [CollatzResearch.WordTrace]
  refine ⟨4836355792616698292933657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3224237195077798861955771 4836355792616698292933657)
  ·
    refine ⟨3627266844462523719700243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4836355792616698292933657 3627266844462523719700243)
    ·
      refine ⟨5440900266693785579550365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3627266844462523719700243 5440900266693785579550365)
      ·
        refine ⟨2040337600010169592331387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5440900266693785579550365 2040337600010169592331387)
        ·
          refine ⟨3060506400015254388497081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2040337600010169592331387 3060506400015254388497081)
          ·
            refine ⟨2295379800011440791372811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3060506400015254388497081 2295379800011440791372811)
            ·
              refine ⟨3443069700017161187059217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2295379800011440791372811 3443069700017161187059217)
              ·
                refine ⟨2582302275012870890294413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3443069700017161187059217 2582302275012870890294413)
                ·
                  refine ⟨968363353129826583860405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2582302275012870890294413 968363353129826583860405)
                  ·
                    refine ⟨90784064355921242236913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 968363353129826583860405 90784064355921242236913)
                    ·
                      refine ⟨68088048266940931677685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 90784064355921242236913 68088048266940931677685)
                      ·
                        rfl

theorem cell23_132601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 5, 2].length) (baseStart_132601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132601 prefixEnd_132601 := by exact prefixLift 132601
  have htrace : WordTrace (prefixWord ++ tailWord_132601) baseStart_132601 baseEnd_132601 := by
    simpa [prefixWord, tailWord_132601, baseEnd_132601] using wordTrace_append hprefix tailTrace_132601
  have hstable : (prefixWord ++ tailWord_132601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132601).length < 2 ^ (prefixWord ++ tailWord_132601).sum := by decide
  have hdescent : baseEnd_132601 < baseStart_132601 := by decide
  rcases family_descends (prefixWord ++ tailWord_132601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132641 : List Nat := [1, 2, 3, 2, 2, 2, 2, 2, 1, 6]
def baseStart_132641 : Nat := 118140960795 + 132641 * 2 ^ 59
def prefixEnd_132641 : Nat := 4983230072969 + 3 ^ 40 * 132641 * 2
def baseEnd_132641 : Nat := 22702862497706925059167

theorem tailTrace_132641 : CollatzResearch.WordTrace tailWord_132641 prefixEnd_132641 22702862497706925059167 := by
  unfold tailWord_132641
  simp only [CollatzResearch.WordTrace]
  refine ⟨4837814712471785124389777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3225209808314523416259851 4837814712471785124389777)
  ·
    refine ⟨3628361034353838843292333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4837814712471785124389777 3628361034353838843292333)
    ·
      refine ⟨1360635387882689566234625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3628361034353838843292333 1360635387882689566234625)
      ·
        refine ⟨1020476540912017174675969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1360635387882689566234625 1020476540912017174675969)
        ·
          refine ⟨765357405684012881006977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1020476540912017174675969 765357405684012881006977)
          ·
            refine ⟨574018054263009660755233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 765357405684012881006977 574018054263009660755233)
            ·
              refine ⟨430513540697257245566425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 574018054263009660755233 430513540697257245566425)
              ·
                refine ⟨322885155522942934174819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430513540697257245566425 322885155522942934174819)
                ·
                  refine ⟨484327733284414401262229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322885155522942934174819 484327733284414401262229)
                  ·
                    refine ⟨22702862497706925059167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 484327733284414401262229 22702862497706925059167)
                    ·
                      rfl

theorem cell23_132641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_132641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132641 prefixEnd_132641 := by exact prefixLift 132641
  have htrace : WordTrace (prefixWord ++ tailWord_132641) baseStart_132641 baseEnd_132641 := by
    simpa [prefixWord, tailWord_132641, baseEnd_132641] using wordTrace_append hprefix tailTrace_132641
  have hstable : (prefixWord ++ tailWord_132641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132641).length < 2 ^ (prefixWord ++ tailWord_132641).sum := by decide
  have hdescent : baseEnd_132641 < baseStart_132641 := by decide
  rcases family_descends (prefixWord ++ tailWord_132641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132665 : List Nat := [1, 2, 1, 5, 1, 2, 1, 3, 3, 2, 2]
def baseStart_132665 : Nat := 118140960795 + 132665 * 2 ^ 59
def prefixEnd_132665 : Nat := 4983230072969 + 3 ^ 40 * 132665 * 2
def baseEnd_132665 : Nat := 68120911028828681277391

theorem tailTrace_132665 : CollatzResearch.WordTrace tailWord_132665 prefixEnd_132665 68120911028828681277391 := by
  unfold tailWord_132665
  simp only [CollatzResearch.WordTrace]
  refine ⟨4838690064384837223263449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3225793376256558148842299 4838690064384837223263449)
  ·
    refine ⟨3629017548288627917447587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4838690064384837223263449 3629017548288627917447587)
    ·
      refine ⟨5443526322432941876171381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3629017548288627917447587 5443526322432941876171381)
      ·
        refine ⟨510330592728088300891067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5443526322432941876171381 510330592728088300891067)
        ·
          refine ⟨765495889092132451336601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510330592728088300891067 765495889092132451336601)
          ·
            refine ⟨574121916819099338502451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 765495889092132451336601 574121916819099338502451)
            ·
              refine ⟨861182875228649007753677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574121916819099338502451 861182875228649007753677)
              ·
                refine ⟨322943578210743377907629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 861182875228649007753677 322943578210743377907629)
                ·
                  refine ⟨121103841829028766715361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322943578210743377907629 121103841829028766715361)
                  ·
                    refine ⟨90827881371771575036521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121103841829028766715361 90827881371771575036521)
                    ·
                      refine ⟨68120911028828681277391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 90827881371771575036521 68120911028828681277391)
                      ·
                        rfl

theorem cell23_132665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_132665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132665 prefixEnd_132665 := by exact prefixLift 132665
  have htrace : WordTrace (prefixWord ++ tailWord_132665) baseStart_132665 baseEnd_132665 := by
    simpa [prefixWord, tailWord_132665, baseEnd_132665] using wordTrace_append hprefix tailTrace_132665
  have hstable : (prefixWord ++ tailWord_132665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132665).length < 2 ^ (prefixWord ++ tailWord_132665).sum := by decide
  have hdescent : baseEnd_132665 < baseStart_132665 := by decide
  rcases family_descends (prefixWord ++ tailWord_132665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132668 : List Nat := [2, 2, 2, 2, 4, 1, 1, 2, 1, 1, 5]
def baseStart_132668 : Nat := 118140960795 + 132668 * 2 ^ 59
def prefixEnd_132668 : Nat := 4983230072969 + 3 ^ 40 * 132668 * 2
def baseEnd_132668 : Nat := 68122451470792169539877

theorem tailTrace_132668 : CollatzResearch.WordTrace tailWord_132668 prefixEnd_132668 68122451470792169539877 := by
  unfold tailWord_132668
  simp only [CollatzResearch.WordTrace]
  refine ⟨2419399741686984367811329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3225866322249312490415105 2419399741686984367811329)
  ·
    refine ⟨1814549806265238275858497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2419399741686984367811329 1814549806265238275858497)
    ·
      refine ⟨1360912354698928706893873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1814549806265238275858497 1360912354698928706893873)
      ·
        refine ⟨1020684266024196530170405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1360912354698928706893873 1020684266024196530170405)
        ·
          refine ⟨191378299879536849406951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1020684266024196530170405 191378299879536849406951)
          ·
            refine ⟨287067449819305274110427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191378299879536849406951 287067449819305274110427)
            ·
              refine ⟨430601174728957911165641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287067449819305274110427 430601174728957911165641)
              ·
                refine ⟨322950881046718433374231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430601174728957911165641 322950881046718433374231)
                ·
                  refine ⟨484426321570077650061347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322950881046718433374231 484426321570077650061347)
                  ·
                    refine ⟨726639482355116475092021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 484426321570077650061347 726639482355116475092021)
                    ·
                      refine ⟨68122451470792169539877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 726639482355116475092021 68122451470792169539877)
                      ·
                        rfl

theorem cell23_132668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_132668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132668 prefixEnd_132668 := by exact prefixLift 132668
  have htrace : WordTrace (prefixWord ++ tailWord_132668) baseStart_132668 baseEnd_132668 := by
    simpa [prefixWord, tailWord_132668, baseEnd_132668] using wordTrace_append hprefix tailTrace_132668
  have hstable : (prefixWord ++ tailWord_132668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132668).length < 2 ^ (prefixWord ++ tailWord_132668).sum := by decide
  have hdescent : baseEnd_132668 < baseStart_132668 := by decide
  rcases family_descends (prefixWord ++ tailWord_132668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132741 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 4, 1, 5]
def baseStart_132741 : Nat := 118140960795 + 132741 * 2 ^ 59
def prefixEnd_132741 : Nat := 4983230072969 + 3 ^ 40 * 132741 * 2
def baseEnd_132741 : Nat := 68159935558570383927041

theorem tailTrace_132741 : CollatzResearch.WordTrace tailWord_132741 prefixEnd_132741 68159935558570383927041 := by
  unfold tailWord_132741
  simp only [CollatzResearch.WordTrace]
  refine ⟨4841462012109502203030077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3227641341406334802020051 4841462012109502203030077)
  ·
    refine ⟨1815548254541063326136279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4841462012109502203030077 1815548254541063326136279)
    ·
      refine ⟨2723322381811594989204419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1815548254541063326136279 2723322381811594989204419)
      ·
        refine ⟨4084983572717392483806629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2723322381811594989204419 4084983572717392483806629)
        ·
          refine ⟨765934419884511090713743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4084983572717392483806629 765934419884511090713743)
          ·
            refine ⟨1148901629826766636070615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765934419884511090713743 1148901629826766636070615)
            ·
              refine ⟨1723352444740149954105923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1148901629826766636070615 1723352444740149954105923)
              ·
                refine ⟨2585028667110224931158885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1723352444740149954105923 2585028667110224931158885)
                ·
                  refine ⟨484692875083167174592291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2585028667110224931158885 484692875083167174592291)
                  ·
                    refine ⟨727039312624750761888437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 484692875083167174592291 727039312624750761888437)
                    ·
                      refine ⟨68159935558570383927041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 727039312624750761888437 68159935558570383927041)
                      ·
                        rfl

theorem cell23_132741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_132741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132741 prefixEnd_132741 := by exact prefixLift 132741
  have htrace : WordTrace (prefixWord ++ tailWord_132741) baseStart_132741 baseEnd_132741 := by
    simpa [prefixWord, tailWord_132741, baseEnd_132741] using wordTrace_append hprefix tailTrace_132741
  have hstable : (prefixWord ++ tailWord_132741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132741).length < 2 ^ (prefixWord ++ tailWord_132741).sum := by decide
  have hdescent : baseEnd_132741 < baseStart_132741 := by decide
  rcases family_descends (prefixWord ++ tailWord_132741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132772 : List Nat := [2, 3, 1, 2, 2, 2, 1, 4, 2, 2, 2]
def baseStart_132772 : Nat := 118140960795 + 132772 * 2 ^ 59
def prefixEnd_132772 : Nat := 4983230072969 + 3 ^ 40 * 132772 * 2
def baseEnd_132772 : Nat := 68175853458859762639399

theorem tailTrace_132772 : CollatzResearch.WordTrace tailWord_132772 prefixEnd_132772 68175853458859762639399 := by
  unfold tailWord_132772
  simp only [CollatzResearch.WordTrace]
  refine ⟨2421296337498597248704285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3228395116664796331605713 2421296337498597248704285)
  ·
    refine ⟨907986126561973968264107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2421296337498597248704285 907986126561973968264107)
    ·
      refine ⟨1361979189842960952396161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 907986126561973968264107 1361979189842960952396161)
      ·
        refine ⟨1021484392382220714297121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1361979189842960952396161 1021484392382220714297121)
        ·
          refine ⟨766113294286665535722841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1021484392382220714297121 766113294286665535722841)
          ·
            refine ⟨574584970714999151792131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 766113294286665535722841 574584970714999151792131)
            ·
              refine ⟨861877456072498727688197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574584970714999151792131 861877456072498727688197)
              ·
                refine ⟨161602023013593511441537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 861877456072498727688197 161602023013593511441537)
                ·
                  refine ⟨121201517260195133581153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161602023013593511441537 121201517260195133581153)
                  ·
                    refine ⟨90901137945146350185865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121201517260195133581153 90901137945146350185865)
                    ·
                      refine ⟨68175853458859762639399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 90901137945146350185865 68175853458859762639399)
                      ·
                        rfl

theorem cell23_132772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_132772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132772 prefixEnd_132772 := by exact prefixLift 132772
  have htrace : WordTrace (prefixWord ++ tailWord_132772) baseStart_132772 baseEnd_132772 := by
    simpa [prefixWord, tailWord_132772, baseEnd_132772] using wordTrace_append hprefix tailTrace_132772
  have hstable : (prefixWord ++ tailWord_132772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132772).length < 2 ^ (prefixWord ++ tailWord_132772).sum := by decide
  have hdescent : baseEnd_132772 < baseStart_132772 := by decide
  rcases family_descends (prefixWord ++ tailWord_132772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132812 : List Nat := [2, 2, 1, 5, 2, 1, 2, 3, 5]
def baseStart_132812 : Nat := 118140960795 + 132812 * 2 ^ 59
def prefixEnd_132812 : Nat := 4983230072969 + 3 ^ 40 * 132812 * 2
def baseEnd_132812 : Nat := 7577376965004400682135

theorem tailTrace_132812 : CollatzResearch.WordTrace tailWord_132812 prefixEnd_132812 7577376965004400682135 := by
  unfold tailWord_132812
  simp only [CollatzResearch.WordTrace]
  refine ⟨2422025797426140664432345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3229367729901520885909793 2422025797426140664432345)
  ·
    refine ⟨1816519348069605498324259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2422025797426140664432345 1816519348069605498324259)
    ·
      refine ⟨2724779022104408247486389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1816519348069605498324259 2724779022104408247486389)
      ·
        refine ⟨255448033322288273201849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2724779022104408247486389 255448033322288273201849)
        ·
          refine ⟨191586024991716204901387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255448033322288273201849 191586024991716204901387)
          ·
            refine ⟨287379037487574307352081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191586024991716204901387 287379037487574307352081)
            ·
              refine ⟨215534278115680730514061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287379037487574307352081 215534278115680730514061)
              ·
                refine ⟨80825354293380273942773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215534278115680730514061 80825354293380273942773)
                ·
                  refine ⟨7577376965004400682135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80825354293380273942773 7577376965004400682135)
                  ·
                    rfl

theorem cell23_132812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3, 5].length) (baseStart_132812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132812 prefixEnd_132812 := by exact prefixLift 132812
  have htrace : WordTrace (prefixWord ++ tailWord_132812) baseStart_132812 baseEnd_132812 := by
    simpa [prefixWord, tailWord_132812, baseEnd_132812] using wordTrace_append hprefix tailTrace_132812
  have hstable : (prefixWord ++ tailWord_132812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132812).length < 2 ^ (prefixWord ++ tailWord_132812).sum := by decide
  have hdescent : baseEnd_132812 < baseStart_132812 := by decide
  rcases family_descends (prefixWord ++ tailWord_132812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132841 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 4, 1, 6]
def baseStart_132841 : Nat := 118140960795 + 132841 * 2 ^ 59
def prefixEnd_132841 : Nat := 4983230072969 + 3 ^ 40 * 132841 * 2
def baseEnd_132841 : Nat := 68211283624019992676581

theorem tailTrace_132841 : CollatzResearch.WordTrace tailWord_132841 prefixEnd_132841 68211283624019992676581 := by
  unfold tailWord_132841
  simp only [CollatzResearch.WordTrace]
  refine ⟨4845109311747219281670377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3230072874498146187780251 4845109311747219281670377)
  ·
    refine ⟨3633831983810414461252783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4845109311747219281670377 3633831983810414461252783)
    ·
      refine ⟨5450747975715621691879175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3633831983810414461252783 5450747975715621691879175)
      ·
        refine ⟨8176121963573432537818763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5450747975715621691879175 8176121963573432537818763)
        ·
          refine ⟨12264182945360148806728145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8176121963573432537818763 12264182945360148806728145)
          ·
            refine ⟨9198137209020111605046109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12264182945360148806728145 9198137209020111605046109)
            ·
              refine ⟨3449301453382541851892291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9198137209020111605046109 3449301453382541851892291)
              ·
                refine ⟨5173952180073812777838437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3449301453382541851892291 5173952180073812777838437)
                ·
                  refine ⟨970116033763839895844707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5173952180073812777838437 970116033763839895844707)
                  ·
                    refine ⟨1455174050645759843767061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 970116033763839895844707 1455174050645759843767061)
                    ·
                      refine ⟨68211283624019992676581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1455174050645759843767061 68211283624019992676581)
                      ·
                        rfl

theorem cell23_132841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 1, 6].length) (baseStart_132841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132841 prefixEnd_132841 := by exact prefixLift 132841
  have htrace : WordTrace (prefixWord ++ tailWord_132841) baseStart_132841 baseEnd_132841 := by
    simpa [prefixWord, tailWord_132841, baseEnd_132841] using wordTrace_append hprefix tailTrace_132841
  have hstable : (prefixWord ++ tailWord_132841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132841).length < 2 ^ (prefixWord ++ tailWord_132841).sum := by decide
  have hdescent : baseEnd_132841 < baseStart_132841 := by decide
  rcases family_descends (prefixWord ++ tailWord_132841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132848 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 3]
def baseStart_132848 : Nat := 118140960795 + 132848 * 2 ^ 59
def prefixEnd_132848 : Nat := 4983230072969 + 3 ^ 40 * 132848 * 2
def baseEnd_132848 : Nat := 68214877988601465289049

theorem tailTrace_132848 : CollatzResearch.WordTrace tailWord_132848 prefixEnd_132848 68214877988601465289049 := by
  unfold tailWord_132848
  simp only [CollatzResearch.WordTrace]
  refine ⟨2422682311360929738587599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3230243081814572984783465 2422682311360929738587599)
  ·
    refine ⟨3634023467041394607881399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2422682311360929738587599 3634023467041394607881399)
    ·
      refine ⟨5451035200562091911822099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3634023467041394607881399 5451035200562091911822099)
      ·
        refine ⟨8176552800843137867733149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5451035200562091911822099 8176552800843137867733149)
        ·
          refine ⟨3066207300316176700399931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8176552800843137867733149 3066207300316176700399931)
          ·
            refine ⟨4599310950474265050599897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3066207300316176700399931 4599310950474265050599897)
            ·
              refine ⟨3449483212855698787949923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4599310950474265050599897 3449483212855698787949923)
              ·
                refine ⟨5174224819283548181924885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3449483212855698787949923 5174224819283548181924885)
                ·
                  refine ⟨242541788403916321027729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5174224819283548181924885 242541788403916321027729)
                  ·
                    refine ⟨181906341302937240770797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 242541788403916321027729 181906341302937240770797)
                    ·
                      refine ⟨68214877988601465289049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 181906341302937240770797 68214877988601465289049)
                      ·
                        rfl

theorem cell23_132848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 3].length) (baseStart_132848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132848 prefixEnd_132848 := by exact prefixLift 132848
  have htrace : WordTrace (prefixWord ++ tailWord_132848) baseStart_132848 baseEnd_132848 := by
    simpa [prefixWord, tailWord_132848, baseEnd_132848] using wordTrace_append hprefix tailTrace_132848
  have hstable : (prefixWord ++ tailWord_132848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132848).length < 2 ^ (prefixWord ++ tailWord_132848).sum := by decide
  have hdescent : baseEnd_132848 < baseStart_132848 := by decide
  rcases family_descends (prefixWord ++ tailWord_132848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132868 : List Nat := [2, 3, 2, 2, 1, 2, 1, 2, 8]
def baseStart_132868 : Nat := 118140960795 + 132868 * 2 ^ 59
def prefixEnd_132868 : Nat := 4983230072969 + 3 ^ 40 * 132868 * 2
def baseEnd_132868 : Nat := 7580571955743487448773

theorem tailTrace_132868 : CollatzResearch.WordTrace tailWord_132868 prefixEnd_132868 7580571955743487448773 := by
  unfold tailWord_132868
  simp only [CollatzResearch.WordTrace]
  refine ⟨2423047041324701446451629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3230729388432935261935505 2423047041324701446451629)
  ·
    refine ⟨908642640496763042419361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2423047041324701446451629 908642640496763042419361)
    ·
      refine ⟨681481980372572281814521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 908642640496763042419361 681481980372572281814521)
      ·
        refine ⟨511111485279429211360891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 681481980372572281814521 511111485279429211360891)
        ·
          refine ⟨766667227919143817041337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511111485279429211360891 766667227919143817041337)
          ·
            refine ⟨575000420939357862781003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 766667227919143817041337 575000420939357862781003)
            ·
              refine ⟨862500631409036794171505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575000420939357862781003 862500631409036794171505)
              ·
                refine ⟨646875473556777595628629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 862500631409036794171505 646875473556777595628629)
                ·
                  refine ⟨7580571955743487448773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 646875473556777595628629 7580571955743487448773)
                  ·
                    rfl

theorem cell23_132868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 8].length) (baseStart_132868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132868 prefixEnd_132868 := by exact prefixLift 132868
  have htrace : WordTrace (prefixWord ++ tailWord_132868) baseStart_132868 baseEnd_132868 := by
    simpa [prefixWord, tailWord_132868, baseEnd_132868] using wordTrace_append hprefix tailTrace_132868
  have hstable : (prefixWord ++ tailWord_132868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132868).length < 2 ^ (prefixWord ++ tailWord_132868).sum := by decide
  have hdescent : baseEnd_132868 < baseStart_132868 := by decide
  rcases family_descends (prefixWord ++ tailWord_132868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132882 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_132882 : Nat := 118140960795 + 132882 * 2 ^ 59
def prefixEnd_132882 : Nat := 4983230072969 + 3 ^ 40 * 132882 * 2
def baseEnd_132882 : Nat := 68232336330854332263893

theorem tailTrace_132882 : CollatzResearch.WordTrace tailWord_132882 prefixEnd_132882 68232336330854332263893 := by
  unfold tailWord_132882
  simp only [CollatzResearch.WordTrace]
  refine ⟨1211651176149670820978225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3231069803065788855941933 1211651176149670820978225)
  ·
    refine ⟨908738382112253115733669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1211651176149670820978225 908738382112253115733669)
    ·
      refine ⟨170388446646047459200063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 908738382112253115733669 170388446646047459200063)
      ·
        refine ⟨255582669969071188800095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170388446646047459200063 255582669969071188800095)
        ·
          refine ⟨383374004953606783200143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255582669969071188800095 383374004953606783200143)
          ·
            refine ⟨575061007430410174800215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383374004953606783200143 575061007430410174800215)
            ·
              refine ⟨862591511145615262200323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575061007430410174800215 862591511145615262200323)
              ·
                refine ⟨1293887266718422893300485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 862591511145615262200323 1293887266718422893300485)
                ·
                  refine ⟨242603862509704292493841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1293887266718422893300485 242603862509704292493841)
                  ·
                    refine ⟨181952896882278219370381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 242603862509704292493841 181952896882278219370381)
                    ·
                      refine ⟨68232336330854332263893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 181952896882278219370381 68232336330854332263893)
                      ·
                        rfl

theorem cell23_132882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_132882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132882 prefixEnd_132882 := by exact prefixLift 132882
  have htrace : WordTrace (prefixWord ++ tailWord_132882) baseStart_132882 baseEnd_132882 := by
    simpa [prefixWord, tailWord_132882, baseEnd_132882] using wordTrace_append hprefix tailTrace_132882
  have hstable : (prefixWord ++ tailWord_132882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132882).length < 2 ^ (prefixWord ++ tailWord_132882).sum := by decide
  have hdescent : baseEnd_132882 < baseStart_132882 := by decide
  rcases family_descends (prefixWord ++ tailWord_132882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132915 : List Nat := [1, 1, 1, 2, 7, 1, 1, 1, 3, 5]
def baseStart_132915 : Nat := 118140960795 + 132915 * 2 ^ 59
def prefixEnd_132915 : Nat := 4983230072969 + 3 ^ 40 * 132915 * 2
def baseEnd_132915 : Nat := 22749760397484234383747

theorem tailTrace_132915 : CollatzResearch.WordTrace tailWord_132915 prefixEnd_132915 22749760397484234383747 := by
  unfold tailWord_132915
  simp only [CollatzResearch.WordTrace]
  refine ⟨4847808313479129919864199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3231872208986086613242799 4847808313479129919864199)
  ·
    refine ⟨7271712470218694879796299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4847808313479129919864199 7271712470218694879796299)
    ·
      refine ⟨10907568705328042319694449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7271712470218694879796299 10907568705328042319694449)
      ·
        refine ⟨8180676528996031739770837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10907568705328042319694449 8180676528996031739770837)
        ·
          refine ⟨191734606148344493900879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 8180676528996031739770837 191734606148344493900879)
          ·
            refine ⟨287601909222516740851319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191734606148344493900879 287601909222516740851319)
            ·
              refine ⟨431402863833775111276979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287601909222516740851319 431402863833775111276979)
              ·
                refine ⟨647104295750662666915469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431402863833775111276979 647104295750662666915469)
                ·
                  refine ⟨242664110906498500093301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 647104295750662666915469 242664110906498500093301)
                  ·
                    refine ⟨22749760397484234383747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 242664110906498500093301 22749760397484234383747)
                    ·
                      rfl

theorem cell23_132915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 5].length) (baseStart_132915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132915 prefixEnd_132915 := by exact prefixLift 132915
  have htrace : WordTrace (prefixWord ++ tailWord_132915) baseStart_132915 baseEnd_132915 := by
    simpa [prefixWord, tailWord_132915, baseEnd_132915] using wordTrace_append hprefix tailTrace_132915
  have hstable : (prefixWord ++ tailWord_132915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132915).length < 2 ^ (prefixWord ++ tailWord_132915).sum := by decide
  have hdescent : baseEnd_132915 < baseStart_132915 := by decide
  rcases family_descends (prefixWord ++ tailWord_132915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132922 : List Nat := [3, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2]
def baseStart_132922 : Nat := 118140960795 + 132922 * 2 ^ 59
def prefixEnd_132922 : Nat := 4983230072969 + 3 ^ 40 * 132922 * 2
def baseEnd_132922 : Nat := 68252875557034175763709

theorem tailTrace_132922 : CollatzResearch.WordTrace tailWord_132922 prefixEnd_132922 68252875557034175763709 := by
  unfold tailWord_132922
  simp only [CollatzResearch.WordTrace]
  refine ⟨1212015906113442528842255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3232042416302513410246013 1212015906113442528842255)
  ·
    refine ⟨1818023859170163793263383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1212015906113442528842255 1818023859170163793263383)
    ·
      refine ⟨2727035788755245689895075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1818023859170163793263383 2727035788755245689895075)
      ·
        refine ⟨4090553683132868534842613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2727035788755245689895075 4090553683132868534842613)
        ·
          refine ⟨383489407793706425141495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4090553683132868534842613 383489407793706425141495)
          ·
            refine ⟨575234111690559637712243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383489407793706425141495 575234111690559637712243)
            ·
              refine ⟨862851167535839456568365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575234111690559637712243 862851167535839456568365)
              ·
                refine ⟨323569187825939796213137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 862851167535839456568365 323569187825939796213137)
                ·
                  refine ⟨242676890869454847159853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 323569187825939796213137 242676890869454847159853)
                  ·
                    refine ⟨91003834076045567684945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 242676890869454847159853 91003834076045567684945)
                    ·
                      refine ⟨68252875557034175763709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 91003834076045567684945 68252875557034175763709)
                      ·
                        rfl

theorem cell23_132922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2].length) (baseStart_132922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132922 prefixEnd_132922 := by exact prefixLift 132922
  have htrace : WordTrace (prefixWord ++ tailWord_132922) baseStart_132922 baseEnd_132922 := by
    simpa [prefixWord, tailWord_132922, baseEnd_132922] using wordTrace_append hprefix tailTrace_132922
  have hstable : (prefixWord ++ tailWord_132922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132922).length < 2 ^ (prefixWord ++ tailWord_132922).sum := by decide
  have hdescent : baseEnd_132922 < baseStart_132922 := by decide
  rcases family_descends (prefixWord ++ tailWord_132922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132935 : List Nat := [1, 1, 4, 1, 2, 1, 2, 5, 1, 1, 4]
def baseStart_132935 : Nat := 118140960795 + 132935 * 2 ^ 59
def prefixEnd_132935 : Nat := 4983230072969 + 3 ^ 40 * 132935 * 2
def baseEnd_132935 : Nat := 68259550805542624901149

theorem tailTrace_132935 : CollatzResearch.WordTrace tailWord_132935 prefixEnd_132935 68259550805542624901149 := by
  unfold tailWord_132935
  simp only [CollatzResearch.WordTrace]
  refine ⟨4848537773406673335592259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3232358515604448890394839 4848537773406673335592259)
  ·
    refine ⟨7272806660110010003388389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4848537773406673335592259 7272806660110010003388389)
    ·
      refine ⟨1363651248770626875635323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7272806660110010003388389 1363651248770626875635323)
      ·
        refine ⟨2045476873155940313452985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1363651248770626875635323 2045476873155940313452985)
        ·
          refine ⟨1534107654866955235089739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2045476873155940313452985 1534107654866955235089739)
          ·
            refine ⟨2301161482300432852634609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1534107654866955235089739 2301161482300432852634609)
            ·
              refine ⟨1725871111725324639475957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2301161482300432852634609 1725871111725324639475957)
              ·
                refine ⟨161800416724249184950871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1725871111725324639475957 161800416724249184950871)
                ·
                  refine ⟨242700625086373777426307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161800416724249184950871 242700625086373777426307)
                  ·
                    refine ⟨364050937629560666139461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 242700625086373777426307 364050937629560666139461)
                    ·
                      refine ⟨68259550805542624901149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 364050937629560666139461 68259550805542624901149)
                      ·
                        rfl

theorem cell23_132935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_132935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132935 prefixEnd_132935 := by exact prefixLift 132935
  have htrace : WordTrace (prefixWord ++ tailWord_132935) baseStart_132935 baseEnd_132935 := by
    simpa [prefixWord, tailWord_132935, baseEnd_132935] using wordTrace_append hprefix tailTrace_132935
  have hstable : (prefixWord ++ tailWord_132935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132935).length < 2 ^ (prefixWord ++ tailWord_132935).sum := by decide
  have hdescent : baseEnd_132935 < baseStart_132935 := by decide
  rcases family_descends (prefixWord ++ tailWord_132935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132946 : List Nat := [3, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3]
def baseStart_132946 : Nat := 118140960795 + 132946 * 2 ^ 59
def prefixEnd_132946 : Nat := 4983230072969 + 3 ^ 40 * 132946 * 2
def baseEnd_132946 : Nat := 68265199092742081863599

theorem tailTrace_132946 : CollatzResearch.WordTrace tailWord_132946 prefixEnd_132946 68265199092742081863599 := by
  unfold tailWord_132946
  simp only [CollatzResearch.WordTrace]
  refine ⟨1212234744091705553560673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3232625984244548142828461 1212234744091705553560673)
  ·
    refine ⟨909176058068779165170505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1212234744091705553560673 909176058068779165170505)
    ·
      refine ⟨681882043551584373877879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 909176058068779165170505 681882043551584373877879)
      ·
        refine ⟨1022823065327376560816819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 681882043551584373877879 1022823065327376560816819)
        ·
          refine ⟨1534234597991064841225229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1022823065327376560816819 1534234597991064841225229)
          ·
            refine ⟨575337974246649315459461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1534234597991064841225229 575337974246649315459461)
            ·
              refine ⟨107875870171246746648649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 575337974246649315459461 107875870171246746648649)
              ·
                refine ⟨80906902628435059986487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107875870171246746648649 80906902628435059986487)
                ·
                  refine ⟨121360353942652589979731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80906902628435059986487 121360353942652589979731)
                  ·
                    refine ⟨182040530913978884969597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121360353942652589979731 182040530913978884969597)
                    ·
                      refine ⟨68265199092742081863599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 182040530913978884969597 68265199092742081863599)
                      ·
                        rfl

theorem cell23_132946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_132946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132946 prefixEnd_132946 := by exact prefixLift 132946
  have htrace : WordTrace (prefixWord ++ tailWord_132946) baseStart_132946 baseEnd_132946 := by
    simpa [prefixWord, tailWord_132946, baseEnd_132946] using wordTrace_append hprefix tailTrace_132946
  have hstable : (prefixWord ++ tailWord_132946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132946).length < 2 ^ (prefixWord ++ tailWord_132946).sum := by decide
  have hdescent : baseEnd_132946 < baseStart_132946 := by decide
  rcases family_descends (prefixWord ++ tailWord_132946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132962 : List Nat := [3, 3, 2, 1, 2, 2, 2, 1, 1, 6]
def baseStart_132962 : Nat := 118140960795 + 132962 * 2 ^ 59
def prefixEnd_132962 : Nat := 4983230072969 + 3 ^ 40 * 132962 * 2
def baseEnd_132962 : Nat := 22757804927738006421175

theorem tailTrace_132962 : CollatzResearch.WordTrace tailWord_132962 prefixEnd_132962 22757804927738006421175 := by
  unfold tailWord_132962
  simp only [CollatzResearch.WordTrace]
  refine ⟨1212380636077214236706285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3233015029539237964550093 1212380636077214236706285)
  ·
    refine ⟨454642738528955338764857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1212380636077214236706285 454642738528955338764857)
    ·
      refine ⟨340982053896716504073643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454642738528955338764857 340982053896716504073643)
      ·
        refine ⟨511473080845074756110465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340982053896716504073643 511473080845074756110465)
        ·
          refine ⟨383604810633806067082849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511473080845074756110465 383604810633806067082849)
          ·
            refine ⟨287703607975354550312137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383604810633806067082849 287703607975354550312137)
            ·
              refine ⟨215777705981515912734103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287703607975354550312137 215777705981515912734103)
              ·
                refine ⟨323666558972273869101155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215777705981515912734103 323666558972273869101155)
                ·
                  refine ⟨485499838458410803651733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 323666558972273869101155 485499838458410803651733)
                  ·
                    refine ⟨22757804927738006421175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 485499838458410803651733 22757804927738006421175)
                    ·
                      rfl

theorem cell23_132962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_132962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132962 prefixEnd_132962 := by exact prefixLift 132962
  have htrace : WordTrace (prefixWord ++ tailWord_132962) baseStart_132962 baseEnd_132962 := by
    simpa [prefixWord, tailWord_132962, baseEnd_132962] using wordTrace_append hprefix tailTrace_132962
  have hstable : (prefixWord ++ tailWord_132962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132962).length < 2 ^ (prefixWord ++ tailWord_132962).sum := by decide
  have hdescent : baseEnd_132962 < baseStart_132962 := by decide
  rcases family_descends (prefixWord ++ tailWord_132962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132985 : List Nat := [1, 2, 1, 3, 2, 2, 1, 4, 1, 3, 3]
def baseStart_132985 : Nat := 118140960795 + 132985 * 2 ^ 59
def prefixEnd_132985 : Nat := 4983230072969 + 3 ^ 40 * 132985 * 2
def baseEnd_132985 : Nat := 68285224838267429275919

theorem tailTrace_132985 : CollatzResearch.WordTrace tailWord_132985 prefixEnd_132985 68285224838267429275919 := by
  unfold tailWord_132985
  simp only [CollatzResearch.WordTrace]
  refine ⟨4850361423225531874912409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3233574282150354583274939 4850361423225531874912409)
  ·
    refine ⟨3637771067419148906184307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4850361423225531874912409 3637771067419148906184307)
    ·
      refine ⟨5456656601128723359276461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3637771067419148906184307 5456656601128723359276461)
      ·
        refine ⟨2046246225423271259728673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5456656601128723359276461 2046246225423271259728673)
        ·
          refine ⟨1534684669067453444796505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2046246225423271259728673 1534684669067453444796505)
          ·
            refine ⟨1151013501800590083597379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1534684669067453444796505 1151013501800590083597379)
            ·
              refine ⟨1726520252700885125396069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1151013501800590083597379 1726520252700885125396069)
              ·
                refine ⟨323722547381415961011763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1726520252700885125396069 323722547381415961011763)
                ·
                  refine ⟨485583821072123941517645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 323722547381415961011763 485583821072123941517645)
                  ·
                    refine ⟨182093932902046478069117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 485583821072123941517645 182093932902046478069117)
                    ·
                      refine ⟨68285224838267429275919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 182093932902046478069117 68285224838267429275919)
                      ·
                        rfl

theorem cell23_132985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_132985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_132985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_132985 prefixEnd_132985 := by exact prefixLift 132985
  have htrace : WordTrace (prefixWord ++ tailWord_132985) baseStart_132985 baseEnd_132985 := by
    simpa [prefixWord, tailWord_132985, baseEnd_132985] using wordTrace_append hprefix tailTrace_132985
  have hstable : (prefixWord ++ tailWord_132985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132985).length < 2 ^ (prefixWord ++ tailWord_132985).sum := by decide
  have hdescent : baseEnd_132985 < baseStart_132985 := by decide
  rcases family_descends (prefixWord ++ tailWord_132985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133016 : List Nat := [2, 1, 2, 6, 2, 1, 1, 1, 1, 2, 4]
def baseStart_133016 : Nat := 118140960795 + 133016 * 2 ^ 59
def prefixEnd_133016 : Nat := 4983230072969 + 3 ^ 40 * 133016 * 2
def baseEnd_133016 : Nat := 68301142738556807988277

theorem tailTrace_133016 : CollatzResearch.WordTrace tailWord_133016 prefixEnd_133016 68301142738556807988277 := by
  unfold tailWord_133016
  simp only [CollatzResearch.WordTrace]
  refine ⟨2425746043056612084645451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3234328057408816112860601 2425746043056612084645451)
  ·
    refine ⟨3638619064584918126968177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2425746043056612084645451 3638619064584918126968177)
    ·
      refine ⟨2728964298438688595226133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3638619064584918126968177 2728964298438688595226133)
      ·
        refine ⟨127920201489313527901225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2728964298438688595226133 127920201489313527901225)
        ·
          refine ⟨95940151116985145925919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127920201489313527901225 95940151116985145925919)
          ·
            refine ⟨143910226675477718888879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95940151116985145925919 143910226675477718888879)
            ·
              refine ⟨215865340013216578333319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143910226675477718888879 215865340013216578333319)
              ·
                refine ⟨323798010019824867499979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215865340013216578333319 323798010019824867499979)
                ·
                  refine ⟨485697015029737301249969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 323798010019824867499979 485697015029737301249969)
                  ·
                    refine ⟨364272761272302975937477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 485697015029737301249969 364272761272302975937477)
                    ·
                      refine ⟨68301142738556807988277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 364272761272302975937477 68301142738556807988277)
                      ·
                        rfl

theorem cell23_133016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_133016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133016 prefixEnd_133016 := by exact prefixLift 133016
  have htrace : WordTrace (prefixWord ++ tailWord_133016) baseStart_133016 baseEnd_133016 := by
    simpa [prefixWord, tailWord_133016, baseEnd_133016] using wordTrace_append hprefix tailTrace_133016
  have hstable : (prefixWord ++ tailWord_133016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133016).length < 2 ^ (prefixWord ++ tailWord_133016).sum := by decide
  have hdescent : baseEnd_133016 < baseStart_133016 := by decide
  rcases family_descends (prefixWord ++ tailWord_133016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133042 : List Nat := [3, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2]
def baseStart_133042 : Nat := 118140960795 + 133042 * 2 ^ 59
def prefixEnd_133042 : Nat := 4983230072969 + 3 ^ 40 * 133042 * 2
def baseEnd_133042 : Nat := 68314493235573706263157

theorem tailTrace_133042 : CollatzResearch.WordTrace tailWord_133042 prefixEnd_133042 68314493235573706263157 := by
  unfold tailWord_133042
  simp only [CollatzResearch.WordTrace]
  refine ⟨1213110096004757652434345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3234960256012687073158253 1213110096004757652434345)
  ·
    refine ⟨909832572003568239325759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1213110096004757652434345 909832572003568239325759)
    ·
      refine ⟨1364748858005352358988639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 909832572003568239325759 1364748858005352358988639)
      ·
        refine ⟨2047123287008028538482959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1364748858005352358988639 2047123287008028538482959)
        ·
          refine ⟨3070684930512042807724439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2047123287008028538482959 3070684930512042807724439)
          ·
            refine ⟨4606027395768064211586659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3070684930512042807724439 4606027395768064211586659)
            ·
              refine ⟨6909041093652096317379989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4606027395768064211586659 6909041093652096317379989)
              ·
                refine ⟨323861301264942014877187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6909041093652096317379989 323861301264942014877187)
                ·
                  refine ⟨485791951897413022315781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 323861301264942014877187 485791951897413022315781)
                  ·
                    refine ⟨91085990980764941684209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 485791951897413022315781 91085990980764941684209)
                    ·
                      refine ⟨68314493235573706263157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 91085990980764941684209 68314493235573706263157)
                      ·
                        rfl

theorem cell23_133042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2].length) (baseStart_133042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133042 prefixEnd_133042 := by exact prefixLift 133042
  have htrace : WordTrace (prefixWord ++ tailWord_133042) baseStart_133042 baseEnd_133042 := by
    simpa [prefixWord, tailWord_133042, baseEnd_133042] using wordTrace_append hprefix tailTrace_133042
  have hstable : (prefixWord ++ tailWord_133042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133042).length < 2 ^ (prefixWord ++ tailWord_133042).sum := by decide
  have hdescent : baseEnd_133042 < baseStart_133042 := by decide
  rcases family_descends (prefixWord ++ tailWord_133042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133045 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_133045 : Nat := 118140960795 + 133045 * 2 ^ 59
def prefixEnd_133045 : Nat := 4983230072969 + 3 ^ 40 * 133045 * 2
def baseEnd_133045 : Nat := 68316033677537194525643

theorem tailTrace_133045 : CollatzResearch.WordTrace tailWord_133045 prefixEnd_133045 68316033677537194525643 := by
  unfold tailWord_133045
  simp only [CollatzResearch.WordTrace]
  refine ⟨4852549803008162122096589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3235033202005441414731059 4852549803008162122096589)
  ·
    refine ⟨1819706176128060795786221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4852549803008162122096589 1819706176128060795786221)
    ·
      refine ⟨682389816048022798419833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1819706176128060795786221 682389816048022798419833)
      ·
        refine ⟨511792362036017098814875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 682389816048022798419833 511792362036017098814875)
        ·
          refine ⟨767688543054025648222313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511792362036017098814875 767688543054025648222313)
          ·
            refine ⟨575766407290519236166735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 767688543054025648222313 575766407290519236166735)
            ·
              refine ⟨863649610935778854250103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575766407290519236166735 863649610935778854250103)
              ·
                refine ⟨1295474416403668281375155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 863649610935778854250103 1295474416403668281375155)
                ·
                  refine ⟨1943211624605502422062733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1295474416403668281375155 1943211624605502422062733)
                  ·
                    refine ⟨728704359227063408273525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1943211624605502422062733 728704359227063408273525)
                    ·
                      refine ⟨68316033677537194525643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 728704359227063408273525 68316033677537194525643)
                      ·
                        rfl

theorem cell23_133045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_133045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133045 prefixEnd_133045 := by exact prefixLift 133045
  have htrace : WordTrace (prefixWord ++ tailWord_133045) baseStart_133045 baseEnd_133045 := by
    simpa [prefixWord, tailWord_133045, baseEnd_133045] using wordTrace_append hprefix tailTrace_133045
  have hstable : (prefixWord ++ tailWord_133045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133045).length < 2 ^ (prefixWord ++ tailWord_133045).sum := by decide
  have hdescent : baseEnd_133045 < baseStart_133045 := by decide
  rcases family_descends (prefixWord ++ tailWord_133045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133076 : List Nat := [2, 4, 1, 2, 1, 1, 3, 3, 2, 2, 2]
def baseStart_133076 : Nat := 118140960795 + 133076 * 2 ^ 59
def prefixEnd_133076 : Nat := 4983230072969 + 3 ^ 40 * 133076 * 2
def baseEnd_133076 : Nat := 68331951577826573238001

theorem tailTrace_133076 : CollatzResearch.WordTrace tailWord_133076 prefixEnd_133076 68331951577826573238001 := by
  unfold tailWord_133076
  simp only [CollatzResearch.WordTrace]
  refine ⟨2426840232947927208237541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3235786977263902944316721 2426840232947927208237541)
  ·
    refine ⟨455032543677736351544539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2426840232947927208237541 455032543677736351544539)
    ·
      refine ⟨682548815516604527316809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455032543677736351544539 682548815516604527316809)
      ·
        refine ⟨511911611637453395487607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 682548815516604527316809 511911611637453395487607)
        ·
          refine ⟨767867417456180093231411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511911611637453395487607 767867417456180093231411)
          ·
            refine ⟨1151801126184270139847117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767867417456180093231411 1151801126184270139847117)
            ·
              refine ⟨431925422319101302442669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1151801126184270139847117 431925422319101302442669)
              ·
                refine ⟨161972033369662988416001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 431925422319101302442669 161972033369662988416001)
                ·
                  refine ⟨121479025027247241312001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161972033369662988416001 121479025027247241312001)
                  ·
                    refine ⟨91109268770435430984001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121479025027247241312001 91109268770435430984001)
                    ·
                      refine ⟨68331951577826573238001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 91109268770435430984001 68331951577826573238001)
                      ·
                        rfl

theorem cell23_133076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_133076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133076 prefixEnd_133076 := by exact prefixLift 133076
  have htrace : WordTrace (prefixWord ++ tailWord_133076) baseStart_133076 baseEnd_133076 := by
    simpa [prefixWord, tailWord_133076, baseEnd_133076] using wordTrace_append hprefix tailTrace_133076
  have hstable : (prefixWord ++ tailWord_133076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133076).length < 2 ^ (prefixWord ++ tailWord_133076).sum := by decide
  have hdescent : baseEnd_133076 < baseStart_133076 := by decide
  rcases family_descends (prefixWord ++ tailWord_133076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133149 : List Nat := [1, 4, 2, 2, 2, 1, 3, 1, 2, 1, 4]
def baseStart_133149 : Nat := 118140960795 + 133149 * 2 ^ 59
def prefixEnd_133149 : Nat := 4983230072969 + 3 ^ 40 * 133149 * 2
def baseEnd_133149 : Nat := 68369435665604787625165

theorem tailTrace_133149 : CollatzResearch.WordTrace tailWord_133149 prefixEnd_133149 68369435665604787625165 := by
  unfold tailWord_133149
  simp only [CollatzResearch.WordTrace]
  refine ⟨4856342994631387883882501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3237561996420925255921667 4856342994631387883882501)
  ·
    refine ⟨910564311493385228227969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4856342994631387883882501 910564311493385228227969)
    ·
      refine ⟨682923233620038921170977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 910564311493385228227969 682923233620038921170977)
      ·
        refine ⟨512192425215029190878233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 682923233620038921170977 512192425215029190878233)
        ·
          refine ⟨384144318911271893158675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512192425215029190878233 384144318911271893158675)
          ·
            refine ⟨576216478366907839738013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384144318911271893158675 576216478366907839738013)
            ·
              refine ⟨216081179387590439901755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 576216478366907839738013 216081179387590439901755)
              ·
                refine ⟨324121769081385659852633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216081179387590439901755 324121769081385659852633)
                ·
                  refine ⟨243091326811039244889475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324121769081385659852633 243091326811039244889475)
                  ·
                    refine ⟨364636990216558867334213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 243091326811039244889475 364636990216558867334213)
                    ·
                      refine ⟨68369435665604787625165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 364636990216558867334213 68369435665604787625165)
                      ·
                        rfl

theorem cell23_133149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_133149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133149 prefixEnd_133149 := by exact prefixLift 133149
  have htrace : WordTrace (prefixWord ++ tailWord_133149) baseStart_133149 baseEnd_133149 := by
    simpa [prefixWord, tailWord_133149, baseEnd_133149] using wordTrace_append hprefix tailTrace_133149
  have hstable : (prefixWord ++ tailWord_133149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133149).length < 2 ^ (prefixWord ++ tailWord_133149).sum := by decide
  have hdescent : baseEnd_133149 < baseStart_133149 := by decide
  rcases family_descends (prefixWord ++ tailWord_133149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133155 : List Nat := [1, 1, 1, 4, 3, 1, 2, 2, 8]
def baseStart_133155 : Nat := 118140960795 + 133155 * 2 ^ 59
def prefixEnd_133155 : Nat := 4983230072969 + 3 ^ 40 * 133155 * 2
def baseEnd_133155 : Nat := 7596946283281307127793

theorem tailTrace_133155 : CollatzResearch.WordTrace tailWord_133155 prefixEnd_133155 7596946283281307127793 := by
  unfold tailWord_133155
  simp only [CollatzResearch.WordTrace]
  refine ⟨4856561832609650908600919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3237707888406433939067279 4856561832609650908600919)
  ·
    refine ⟨7284842748914476362901379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4856561832609650908600919 7284842748914476362901379)
    ·
      refine ⟨10927264123371714544352069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7284842748914476362901379 10927264123371714544352069)
      ·
        refine ⟨2048862023132196477066013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10927264123371714544352069 2048862023132196477066013)
        ·
          refine ⟨768323258674573678899755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2048862023132196477066013 768323258674573678899755)
          ·
            refine ⟨1152484888011860518349633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768323258674573678899755 1152484888011860518349633)
            ·
              refine ⟨864363666008895388762225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1152484888011860518349633 864363666008895388762225)
              ·
                refine ⟨648272749506671541571669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 864363666008895388762225 648272749506671541571669)
                ·
                  refine ⟨7596946283281307127793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 648272749506671541571669 7596946283281307127793)
                  ·
                    rfl

theorem cell23_133155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 8].length) (baseStart_133155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133155 prefixEnd_133155 := by exact prefixLift 133155
  have htrace : WordTrace (prefixWord ++ tailWord_133155) baseStart_133155 baseEnd_133155 := by
    simpa [prefixWord, tailWord_133155, baseEnd_133155] using wordTrace_append hprefix tailTrace_133155
  have hstable : (prefixWord ++ tailWord_133155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133155).length < 2 ^ (prefixWord ++ tailWord_133155).sum := by decide
  have hdescent : baseEnd_133155 < baseStart_133155 := by decide
  rcases family_descends (prefixWord ++ tailWord_133155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133162 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_133162 : Nat := 118140960795 + 133162 * 2 ^ 59
def prefixEnd_133162 : Nat := 4983230072969 + 3 ^ 40 * 133162 * 2
def baseEnd_133162 : Nat := 68376110914113236762605

theorem tailTrace_133162 : CollatzResearch.WordTrace tailWord_133162 prefixEnd_133162 68376110914113236762605 := by
  unfold tailWord_133162
  simp only [CollatzResearch.WordTrace]
  refine ⟨1214204285896072776026435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3237878095722860736070493 1214204285896072776026435)
  ·
    refine ⟨1821306428844109164039653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1214204285896072776026435 1821306428844109164039653)
    ·
      refine ⟨341494955408270468257435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1821306428844109164039653 341494955408270468257435)
      ·
        refine ⟨512242433112405702386153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341494955408270468257435 512242433112405702386153)
        ·
          refine ⟨384181824834304276789615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512242433112405702386153 384181824834304276789615)
          ·
            refine ⟨576272737251456415184423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384181824834304276789615 576272737251456415184423)
            ·
              refine ⟨864409105877184622776635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576272737251456415184423 864409105877184622776635)
              ·
                refine ⟨1296613658815776934164953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 864409105877184622776635 1296613658815776934164953)
                ·
                  refine ⟨972460244111832700623715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1296613658815776934164953 972460244111832700623715)
                  ·
                    refine ⟨1458690366167749050935573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 972460244111832700623715 1458690366167749050935573)
                    ·
                      refine ⟨68376110914113236762605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1458690366167749050935573 68376110914113236762605)
                      ·
                        rfl

theorem cell23_133162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_133162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133162 prefixEnd_133162 := by exact prefixLift 133162
  have htrace : WordTrace (prefixWord ++ tailWord_133162) baseStart_133162 baseEnd_133162 := by
    simpa [prefixWord, tailWord_133162, baseEnd_133162] using wordTrace_append hprefix tailTrace_133162
  have hstable : (prefixWord ++ tailWord_133162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133162).length < 2 ^ (prefixWord ++ tailWord_133162).sum := by decide
  have hdescent : baseEnd_133162 < baseStart_133162 := by decide
  rcases family_descends (prefixWord ++ tailWord_133162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133175 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 6]
def baseStart_133175 : Nat := 118140960795 + 133175 * 2 ^ 59
def prefixEnd_133175 : Nat := 4983230072969 + 3 ^ 40 * 133175 * 2
def baseEnd_133175 : Nat := 68382786162621685900045

theorem tailTrace_133175 : CollatzResearch.WordTrace tailWord_133175 prefixEnd_133175 68382786162621685900045 := by
  unfold tailWord_133175
  simp only [CollatzResearch.WordTrace]
  refine ⟨4857291292537194324328979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3238194195024796216219319 4857291292537194324328979)
  ·
    refine ⟨7285936938805791486493469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4857291292537194324328979 7285936938805791486493469)
    ·
      refine ⟨2732226352052171807435051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7285936938805791486493469 2732226352052171807435051)
      ·
        refine ⟨4098339528078257711152577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2732226352052171807435051 4098339528078257711152577)
        ·
          refine ⟨3073754646058693283364433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4098339528078257711152577 3073754646058693283364433)
          ·
            refine ⟨2305315984544019962523325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3073754646058693283364433 2305315984544019962523325)
            ·
              refine ⟨864493494204007485946247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2305315984544019962523325 864493494204007485946247)
              ·
                refine ⟨1296740241306011228919371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 864493494204007485946247 1296740241306011228919371)
                ·
                  refine ⟨1945110361959016843379057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1296740241306011228919371 1945110361959016843379057)
                  ·
                    refine ⟨1458832771469262632534293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1945110361959016843379057 1458832771469262632534293)
                    ·
                      refine ⟨68382786162621685900045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1458832771469262632534293 68382786162621685900045)
                      ·
                        rfl

theorem cell23_133175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_133175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133175 prefixEnd_133175 := by exact prefixLift 133175
  have htrace : WordTrace (prefixWord ++ tailWord_133175) baseStart_133175 baseEnd_133175 := by
    simpa [prefixWord, tailWord_133175, baseEnd_133175] using wordTrace_append hprefix tailTrace_133175
  have hstable : (prefixWord ++ tailWord_133175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133175).length < 2 ^ (prefixWord ++ tailWord_133175).sum := by decide
  have hdescent : baseEnd_133175 < baseStart_133175 := by decide
  rcases family_descends (prefixWord ++ tailWord_133175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133209 : List Nat := [1, 2, 1, 2, 2, 1, 4, 3, 2, 3, 2]
def baseStart_133209 : Nat := 118140960795 + 133209 * 2 ^ 59
def prefixEnd_133209 : Nat := 4983230072969 + 3 ^ 40 * 133209 * 2
def baseEnd_133209 : Nat := 68400244504874552874889

theorem tailTrace_133209 : CollatzResearch.WordTrace tailWord_133209 prefixEnd_133209 68400244504874552874889 := by
  unfold tailWord_133209
  simp only [CollatzResearch.WordTrace]
  refine ⟨4858531374414018131066681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3239020916276012087377787 4858531374414018131066681)
  ·
    refine ⟨3643898530810513598300011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4858531374414018131066681 3643898530810513598300011)
    ·
      refine ⟨5465847796215770397450017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3643898530810513598300011 5465847796215770397450017)
      ·
        refine ⟨4099385847161827798087513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5465847796215770397450017 4099385847161827798087513)
        ·
          refine ⟨3074539385371370848565635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4099385847161827798087513 3074539385371370848565635)
          ·
            refine ⟨4611809078057056272848453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3074539385371370848565635 4611809078057056272848453)
            ·
              refine ⟨864714202135698051159085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4611809078057056272848453 864714202135698051159085)
              ·
                refine ⟨324267825800886769184657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 864714202135698051159085 324267825800886769184657)
                ·
                  refine ⟨243200869350665076888493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324267825800886769184657 243200869350665076888493)
                  ·
                    refine ⟨91200326006499403833185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 243200869350665076888493 91200326006499403833185)
                    ·
                      refine ⟨68400244504874552874889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 91200326006499403833185 68400244504874552874889)
                      ·
                        rfl

theorem cell23_133209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 3, 2].length) (baseStart_133209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133209 prefixEnd_133209 := by exact prefixLift 133209
  have htrace : WordTrace (prefixWord ++ tailWord_133209) baseStart_133209 baseEnd_133209 := by
    simpa [prefixWord, tailWord_133209, baseEnd_133209] using wordTrace_append hprefix tailTrace_133209
  have hstable : (prefixWord ++ tailWord_133209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133209).length < 2 ^ (prefixWord ++ tailWord_133209).sum := by decide
  have hdescent : baseEnd_133209 < baseStart_133209 := by decide
  rcases family_descends (prefixWord ++ tailWord_133209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133233 : List Nat := [1, 2, 2, 2, 1, 1, 7, 2, 1, 1, 3]
def baseStart_133233 : Nat := 118140960795 + 133233 * 2 ^ 59
def prefixEnd_133233 : Nat := 4983230072969 + 3 ^ 40 * 133233 * 2
def baseEnd_133233 : Nat := 68412568040582458974779

theorem tailTrace_133233 : CollatzResearch.WordTrace tailWord_133233 prefixEnd_133233 68412568040582458974779 := by
  unfold tailWord_133233
  simp only [CollatzResearch.WordTrace]
  refine ⟨4859406726327070229940353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3239604484218046819960235 4859406726327070229940353)
  ·
    refine ⟨3644555044745302672455265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4859406726327070229940353 3644555044745302672455265)
    ·
      refine ⟨2733416283558977004341449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3644555044745302672455265 2733416283558977004341449)
      ·
        refine ⟨2050062212669232753256087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2733416283558977004341449 2050062212669232753256087)
        ·
          refine ⟨3075093319003849129884131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2050062212669232753256087 3075093319003849129884131)
          ·
            refine ⟨4612639978505773694826197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3075093319003849129884131 4612639978505773694826197)
            ·
              refine ⟨108108749496229070972489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 4612639978505773694826197 108108749496229070972489)
              ·
                refine ⟨81081562122171803229367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108108749496229070972489 81081562122171803229367)
                ·
                  refine ⟨121622343183257704844051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81081562122171803229367 121622343183257704844051)
                  ·
                    refine ⟨182433514774886557266077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121622343183257704844051 182433514774886557266077)
                    ·
                      refine ⟨68412568040582458974779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 182433514774886557266077 68412568040582458974779)
                      ·
                        rfl

theorem cell23_133233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2, 1, 1, 3].length) (baseStart_133233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133233 prefixEnd_133233 := by exact prefixLift 133233
  have htrace : WordTrace (prefixWord ++ tailWord_133233) baseStart_133233 baseEnd_133233 := by
    simpa [prefixWord, tailWord_133233, baseEnd_133233] using wordTrace_append hprefix tailTrace_133233
  have hstable : (prefixWord ++ tailWord_133233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133233).length < 2 ^ (prefixWord ++ tailWord_133233).sum := by decide
  have hdescent : baseEnd_133233 < baseStart_133233 := by decide
  rcases family_descends (prefixWord ++ tailWord_133233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133252 : List Nat := [2, 3, 2, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_133252 : Nat := 118140960795 + 133252 * 2 ^ 59
def prefixEnd_133252 : Nat := 4983230072969 + 3 ^ 40 * 133252 * 2
def baseEnd_133252 : Nat := 68422324173017884637191

theorem tailTrace_133252 : CollatzResearch.WordTrace tailWord_133252 prefixEnd_133252 68422324173017884637191 := by
  unfold tailWord_133252
  simp only [CollatzResearch.WordTrace]
  refine ⟨2430049856629118237441005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3240066475505490983254673 2430049856629118237441005)
  ·
    refine ⟨911268696235919339040377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2430049856629118237441005 911268696235919339040377)
    ·
      refine ⟨683451522176939504280283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 911268696235919339040377 683451522176939504280283)
      ·
        refine ⟨1025177283265409256420425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683451522176939504280283 1025177283265409256420425)
        ·
          refine ⟨768882962449056942315319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1025177283265409256420425 768882962449056942315319)
          ·
            refine ⟨1153324443673585413472979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768882962449056942315319 1153324443673585413472979)
            ·
              refine ⟨1729986665510378120209469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1153324443673585413472979 1729986665510378120209469)
              ·
                refine ⟨648744999566391795078551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1729986665510378120209469 648744999566391795078551)
                ·
                  refine ⟨973117499349587692617827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 648744999566391795078551 973117499349587692617827)
                  ·
                    refine ⟨1459676249024381538926741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 973117499349587692617827 1459676249024381538926741)
                    ·
                      refine ⟨68422324173017884637191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1459676249024381538926741 68422324173017884637191)
                      ·
                        rfl

theorem cell23_133252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_133252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133252 prefixEnd_133252 := by exact prefixLift 133252
  have htrace : WordTrace (prefixWord ++ tailWord_133252) baseStart_133252 baseEnd_133252 := by
    simpa [prefixWord, tailWord_133252, baseEnd_133252] using wordTrace_append hprefix tailTrace_133252
  have hstable : (prefixWord ++ tailWord_133252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133252).length < 2 ^ (prefixWord ++ tailWord_133252).sum := by decide
  have hdescent : baseEnd_133252 < baseStart_133252 := by decide
  rcases family_descends (prefixWord ++ tailWord_133252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133256 : List Nat := [2, 1, 3, 4, 1, 1, 3, 2, 1, 1, 4]
def baseStart_133256 : Nat := 118140960795 + 133256 * 2 ^ 59
def prefixEnd_133256 : Nat := 4983230072969 + 3 ^ 40 * 133256 * 2
def baseEnd_133256 : Nat := 68424378095635868987173

theorem tailTrace_133256 : CollatzResearch.WordTrace tailWord_133256 prefixEnd_133256 68424378095635868987173 := by
  unfold tailWord_133256
  simp only [CollatzResearch.WordTrace]
  refine ⟨2430122802621872579013811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3240163736829163438685081 2430122802621872579013811)
  ·
    refine ⟨3645184203932808868520717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2430122802621872579013811 3645184203932808868520717)
    ·
      refine ⟨1366944076474803325695269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3645184203932808868520717 1366944076474803325695269)
      ·
        refine ⟨256302014339025623567863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1366944076474803325695269 256302014339025623567863)
        ·
          refine ⟨384453021508538435351795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256302014339025623567863 384453021508538435351795)
          ·
            refine ⟨576679532262807653027693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384453021508538435351795 576679532262807653027693)
            ·
              refine ⟨216254824598552869885385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 576679532262807653027693 216254824598552869885385)
              ·
                refine ⟨162191118448914652414039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216254824598552869885385 162191118448914652414039)
                ·
                  refine ⟨243286677673371978621059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162191118448914652414039 243286677673371978621059)
                  ·
                    refine ⟨364930016510057967931589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 243286677673371978621059 364930016510057967931589)
                    ·
                      refine ⟨68424378095635868987173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 364930016510057967931589 68424378095635868987173)
                      ·
                        rfl

theorem cell23_133256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_133256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133256 prefixEnd_133256 := by exact prefixLift 133256
  have htrace : WordTrace (prefixWord ++ tailWord_133256) baseStart_133256 baseEnd_133256 := by
    simpa [prefixWord, tailWord_133256, baseEnd_133256] using wordTrace_append hprefix tailTrace_133256
  have hstable : (prefixWord ++ tailWord_133256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133256).length < 2 ^ (prefixWord ++ tailWord_133256).sum := by decide
  have hdescent : baseEnd_133256 < baseStart_133256 := by decide
  rcases family_descends (prefixWord ++ tailWord_133256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133300 : List Nat := [2, 5, 3, 1, 1, 1, 2, 1, 1, 6]
def baseStart_133300 : Nat := 118140960795 + 133300 * 2 ^ 59
def prefixEnd_133300 : Nat := 4983230072969 + 3 ^ 40 * 133300 * 2
def baseEnd_133300 : Nat := 22815657081477898945657

theorem tailTrace_133300 : CollatzResearch.WordTrace tailWord_133300 prefixEnd_133300 22815657081477898945657 := by
  unfold tailWord_133300
  simp only [CollatzResearch.WordTrace]
  refine ⟨2430925208542170336314677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3241233611389560448419569 2430925208542170336314677)
  ·
    refine ⟨227899238300828469029501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2430925208542170336314677 227899238300828469029501)
    ·
      refine ⟨85462214362810675886063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227899238300828469029501 85462214362810675886063)
      ·
        refine ⟨128193321544216013829095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85462214362810675886063 128193321544216013829095)
        ·
          refine ⟨192289982316324020743643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128193321544216013829095 192289982316324020743643)
          ·
            refine ⟨288434973474486031115465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192289982316324020743643 288434973474486031115465)
            ·
              refine ⟨216326230105864523336599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288434973474486031115465 216326230105864523336599)
              ·
                refine ⟨324489345158796785004899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216326230105864523336599 324489345158796785004899)
                ·
                  refine ⟨486734017738195177507349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324489345158796785004899 486734017738195177507349)
                  ·
                    refine ⟨22815657081477898945657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 486734017738195177507349 22815657081477898945657)
                    ·
                      rfl

theorem cell23_133300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_133300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133300 prefixEnd_133300 := by exact prefixLift 133300
  have htrace : WordTrace (prefixWord ++ tailWord_133300) baseStart_133300 baseEnd_133300 := by
    simpa [prefixWord, tailWord_133300, baseEnd_133300] using wordTrace_append hprefix tailTrace_133300
  have hstable : (prefixWord ++ tailWord_133300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133300).length < 2 ^ (prefixWord ++ tailWord_133300).sum := by decide
  have hdescent : baseEnd_133300 < baseStart_133300 := by decide
  rcases family_descends (prefixWord ++ tailWord_133300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133306 : List Nat := [3, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3]
def baseStart_133306 : Nat := 118140960795 + 133306 * 2 ^ 59
def prefixEnd_133306 : Nat := 4983230072969 + 3 ^ 40 * 133306 * 2
def baseEnd_133306 : Nat := 68450052128360673361943

theorem tailTrace_133306 : CollatzResearch.WordTrace tailWord_133306 prefixEnd_133306 68450052128360673361943 := by
  unfold tailWord_133306
  simp only [CollatzResearch.WordTrace]
  refine ⟨1215517313765650924336943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3241379503375069131565181 1215517313765650924336943)
  ·
    refine ⟨1823275970648476386505415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1215517313765650924336943 1823275970648476386505415)
    ·
      refine ⟨2734913955972714579758123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1823275970648476386505415 2734913955972714579758123)
      ·
        refine ⟨4102370933959071869637185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2734913955972714579758123 4102370933959071869637185)
        ·
          refine ⟨3076778200469303902227889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4102370933959071869637185 3076778200469303902227889)
          ·
            refine ⟨2307583650351977926670917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3076778200469303902227889 2307583650351977926670917)
            ·
              refine ⟨432671934440995861250797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2307583650351977926670917 432671934440995861250797)
              ·
                refine ⟨162251975415373447969049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 432671934440995861250797 162251975415373447969049)
                ·
                  refine ⟨121688981561530085976787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162251975415373447969049 121688981561530085976787)
                  ·
                    refine ⟨182533472342295128965181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121688981561530085976787 182533472342295128965181)
                    ·
                      refine ⟨68450052128360673361943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 182533472342295128965181 68450052128360673361943)
                      ·
                        rfl

theorem cell23_133306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3].length) (baseStart_133306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133306 prefixEnd_133306 := by exact prefixLift 133306
  have htrace : WordTrace (prefixWord ++ tailWord_133306) baseStart_133306 baseEnd_133306 := by
    simpa [prefixWord, tailWord_133306, baseEnd_133306] using wordTrace_append hprefix tailTrace_133306
  have hstable : (prefixWord ++ tailWord_133306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133306).length < 2 ^ (prefixWord ++ tailWord_133306).sum := by decide
  have hdescent : baseEnd_133306 < baseStart_133306 := by decide
  rcases family_descends (prefixWord ++ tailWord_133306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133322 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 1, 8]
def baseStart_133322 : Nat := 118140960795 + 133322 * 2 ^ 59
def prefixEnd_133322 : Nat := 4983230072969 + 3 ^ 40 * 133322 * 2
def baseEnd_133322 : Nat := 22819422606277536920623

theorem tailTrace_133322 : CollatzResearch.WordTrace tailWord_133322 prefixEnd_133322 22819422606277536920623 := by
  unfold tailWord_133322
  simp only [CollatzResearch.WordTrace]
  refine ⟨1215663205751159607482555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3241768548669758953286813 1215663205751159607482555)
  ·
    refine ⟨1823494808626739411223833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1215663205751159607482555 1823494808626739411223833)
    ·
      refine ⟨1367621106470054558417875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1823494808626739411223833 1367621106470054558417875)
      ·
        refine ⟨2051431659705081837626813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1367621106470054558417875 2051431659705081837626813)
        ·
          refine ⟨769286872389405689110055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2051431659705081837626813 769286872389405689110055)
          ·
            refine ⟨1153930308584108533665083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769286872389405689110055 1153930308584108533665083)
            ·
              refine ⟨1730895462876162800497625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1153930308584108533665083 1730895462876162800497625)
              ·
                refine ⟨1298171597157122100373219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1730895462876162800497625 1298171597157122100373219)
                ·
                  refine ⟨1947257395735683150559829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1298171597157122100373219 1947257395735683150559829)
                  ·
                    refine ⟨22819422606277536920623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1947257395735683150559829 22819422606277536920623)
                    ·
                      rfl

theorem cell23_133322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_133322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133322 prefixEnd_133322 := by exact prefixLift 133322
  have htrace : WordTrace (prefixWord ++ tailWord_133322) baseStart_133322 baseEnd_133322 := by
    simpa [prefixWord, tailWord_133322, baseEnd_133322] using wordTrace_append hprefix tailTrace_133322
  have hstable : (prefixWord ++ tailWord_133322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133322).length < 2 ^ (prefixWord ++ tailWord_133322).sum := by decide
  have hdescent : baseEnd_133322 < baseStart_133322 := by decide
  rcases family_descends (prefixWord ++ tailWord_133322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133340 : List Nat := [2, 2, 5, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_133340 : Nat := 118140960795 + 133340 * 2 ^ 59
def prefixEnd_133340 : Nat := 4983230072969 + 3 ^ 40 * 133340 * 2
def baseEnd_133340 : Nat := 68467510470613540336787

theorem tailTrace_133340 : CollatzResearch.WordTrace tailWord_133340 prefixEnd_133340 68467510470613540336787 := by
  unfold tailWord_133340
  simp only [CollatzResearch.WordTrace]
  refine ⟨2431654668469713752042737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3242206224626285002723649 2431654668469713752042737)
  ·
    refine ⟨1823741001352285314032053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2431654668469713752042737 1823741001352285314032053)
    ·
      refine ⟨170975718876776748190505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1823741001352285314032053 170975718876776748190505)
      ·
        refine ⟨128231789157582561142879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170975718876776748190505 128231789157582561142879)
        ·
          refine ⟨192347683736373841714319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128231789157582561142879 192347683736373841714319)
          ·
            refine ⟨288521525604560762571479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192347683736373841714319 288521525604560762571479)
            ·
              refine ⟨432782288406841143857219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288521525604560762571479 432782288406841143857219)
              ·
                refine ⟨649173432610261715785829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432782288406841143857219 649173432610261715785829)
                ·
                  refine ⟨121720018614424071709843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 649173432610261715785829 121720018614424071709843)
                  ·
                    refine ⟨182580027921636107564765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121720018614424071709843 182580027921636107564765)
                    ·
                      refine ⟨68467510470613540336787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 182580027921636107564765 68467510470613540336787)
                      ·
                        rfl

theorem cell23_133340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_133340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133340 prefixEnd_133340 := by exact prefixLift 133340
  have htrace : WordTrace (prefixWord ++ tailWord_133340) baseStart_133340 baseEnd_133340 := by
    simpa [prefixWord, tailWord_133340, baseEnd_133340] using wordTrace_append hprefix tailTrace_133340
  have hstable : (prefixWord ++ tailWord_133340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133340).length < 2 ^ (prefixWord ++ tailWord_133340).sum := by decide
  have hdescent : baseEnd_133340 < baseStart_133340 := by decide
  rcases family_descends (prefixWord ++ tailWord_133340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133359 : List Nat := [1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 4]
def baseStart_133359 : Nat := 118140960795 + 133359 * 2 ^ 59
def prefixEnd_133359 : Nat := 4983230072969 + 3 ^ 40 * 133359 * 2
def baseEnd_133359 : Nat := 68477266603048965999199

theorem tailTrace_133359 : CollatzResearch.WordTrace tailWord_133359 prefixEnd_133359 68477266603048965999199 := by
  unfold tailWord_133359
  simp only [CollatzResearch.WordTrace]
  refine ⟨4864002323870593749027131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3242668215913729166018087 4864002323870593749027131)
  ·
    refine ⟨7296003485805890623540697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4864002323870593749027131 7296003485805890623540697)
    ·
      refine ⟨5472002614354417967655523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7296003485805890623540697 5472002614354417967655523)
      ·
        refine ⟨8208003921531626951483285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5472002614354417967655523 8208003921531626951483285)
        ·
          refine ⟨384750183821795013350779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8208003921531626951483285 384750183821795013350779)
          ·
            refine ⟨577125275732692520026169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384750183821795013350779 577125275732692520026169)
            ·
              refine ⟨432843956799519390019627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577125275732692520026169 432843956799519390019627)
              ·
                refine ⟨649265935199279085029441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432843956799519390019627 649265935199279085029441)
                ·
                  refine ⟨486949451399459313772081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 649265935199279085029441 486949451399459313772081)
                  ·
                    refine ⟨365212088549594485329061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 486949451399459313772081 365212088549594485329061)
                    ·
                      refine ⟨68477266603048965999199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 365212088549594485329061 68477266603048965999199)
                      ·
                        rfl

theorem cell23_133359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 4].length) (baseStart_133359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133359 prefixEnd_133359 := by exact prefixLift 133359
  have htrace : WordTrace (prefixWord ++ tailWord_133359) baseStart_133359 baseEnd_133359 := by
    simpa [prefixWord, tailWord_133359, baseEnd_133359] using wordTrace_append hprefix tailTrace_133359
  have hstable : (prefixWord ++ tailWord_133359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133359).length < 2 ^ (prefixWord ++ tailWord_133359).sum := by decide
  have hdescent : baseEnd_133359 < baseStart_133359 := by decide
  rcases family_descends (prefixWord ++ tailWord_133359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133386 : List Nat := [3, 1, 2, 2, 1, 1, 5, 3, 5]
def baseStart_133386 : Nat := 118140960795 + 133386 * 2 ^ 59
def prefixEnd_133386 : Nat := 4983230072969 + 3 ^ 40 * 133386 * 2
def baseEnd_133386 : Nat := 7610125620080040040175

theorem tailTrace_133386 : CollatzResearch.WordTrace tailWord_133386 prefixEnd_133386 7610125620080040040175 := by
  unfold tailWord_133386
  simp only [CollatzResearch.WordTrace]
  refine ⟨1216246773693194340065003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3243324729848518240173341 1216246773693194340065003)
  ·
    refine ⟨1824370160539791510097505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1216246773693194340065003 1824370160539791510097505)
    ·
      refine ⟨1368277620404843632573129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1824370160539791510097505 1368277620404843632573129)
      ·
        refine ⟨1026208215303632724429847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1368277620404843632573129 1026208215303632724429847)
        ·
          refine ⟨1539312322955449086644771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1026208215303632724429847 1539312322955449086644771)
          ·
            refine ⟨2308968484433173629967157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1539312322955449086644771 2308968484433173629967157)
            ·
              refine ⟨216465795415610027809421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2308968484433173629967157 216465795415610027809421)
              ·
                refine ⟨81174673280853760428533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216465795415610027809421 81174673280853760428533)
                ·
                  refine ⟨7610125620080040040175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81174673280853760428533 7610125620080040040175)
                  ·
                    rfl

theorem cell23_133386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3, 5].length) (baseStart_133386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133386 prefixEnd_133386 := by exact prefixLift 133386
  have htrace : WordTrace (prefixWord ++ tailWord_133386) baseStart_133386 baseEnd_133386 := by
    simpa [prefixWord, tailWord_133386, baseEnd_133386] using wordTrace_append hprefix tailTrace_133386
  have hstable : (prefixWord ++ tailWord_133386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133386).length < 2 ^ (prefixWord ++ tailWord_133386).sum := by decide
  have hdescent : baseEnd_133386 < baseStart_133386 := by decide
  rcases family_descends (prefixWord ++ tailWord_133386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133399 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 4, 5]
def baseStart_133399 : Nat := 118140960795 + 133399 * 2 ^ 59
def prefixEnd_133399 : Nat := 4983230072969 + 3 ^ 40 * 133399 * 2
def baseEnd_133399 : Nat := 22832601943076269833005

theorem tailTrace_133399 : CollatzResearch.WordTrace tailWord_133399 prefixEnd_133399 22832601943076269833005 := by
  unfold tailWord_133399
  simp only [CollatzResearch.WordTrace]
  refine ⟨4865461243725680580483251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3243640829150453720322167 4865461243725680580483251)
  ·
    refine ⟨7298191865588520870724877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4865461243725680580483251 7298191865588520870724877)
    ·
      refine ⟨2736821949595695326521829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7298191865588520870724877 2736821949595695326521829)
      ·
        refine ⟨513154115549192873722843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2736821949595695326521829 513154115549192873722843)
        ·
          refine ⟨769731173323789310584265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513154115549192873722843 769731173323789310584265)
          ·
            refine ⟨577298379992841982938199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 769731173323789310584265 577298379992841982938199)
            ·
              refine ⟨865947569989262974407299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577298379992841982938199 865947569989262974407299)
              ·
                refine ⟨1298921354983894461610949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 865947569989262974407299 1298921354983894461610949)
                ·
                  refine ⟨243547754059480211552053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1298921354983894461610949 243547754059480211552053)
                  ·
                    refine ⟨22832601943076269833005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 243547754059480211552053 22832601943076269833005)
                    ·
                      rfl

theorem cell23_133399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 5].length) (baseStart_133399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133399 prefixEnd_133399 := by exact prefixLift 133399
  have htrace : WordTrace (prefixWord ++ tailWord_133399) baseStart_133399 baseEnd_133399 := by
    simpa [prefixWord, tailWord_133399, baseEnd_133399] using wordTrace_append hprefix tailTrace_133399
  have hstable : (prefixWord ++ tailWord_133399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133399).length < 2 ^ (prefixWord ++ tailWord_133399).sum := by decide
  have hdescent : baseEnd_133399 < baseStart_133399 := by decide
  rcases family_descends (prefixWord ++ tailWord_133399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133436 : List Nat := [2, 2, 2, 2, 1, 2, 4, 1, 2, 1, 4]
def baseStart_133436 : Nat := 118140960795 + 133436 * 2 ^ 59
def prefixEnd_133436 : Nat := 4983230072969 + 3 ^ 40 * 133436 * 2
def baseEnd_133436 : Nat := 68516804613445164736345

theorem tailTrace_133436 : CollatzResearch.WordTrace tailWord_133436 prefixEnd_133436 68516804613445164736345 := by
  unfold tailWord_133436
  simp only [CollatzResearch.WordTrace]
  refine ⟨2433405372295817949790081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3244540496394423933053441 2433405372295817949790081)
  ·
    refine ⟨1825054029221863462342561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2433405372295817949790081 1825054029221863462342561)
    ·
      refine ⟨1368790521916397596756921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1825054029221863462342561 1368790521916397596756921)
      ·
        refine ⟨1026592891437298197567691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1368790521916397596756921 1026592891437298197567691)
        ·
          refine ⟨1539889337155947296351537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1026592891437298197567691 1539889337155947296351537)
          ·
            refine ⟨1154917002866960472263653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1539889337155947296351537 1154917002866960472263653)
            ·
              refine ⟨216546938037555088549435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1154917002866960472263653 216546938037555088549435)
              ·
                refine ⟨324820407056332632824153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216546938037555088549435 324820407056332632824153)
                ·
                  refine ⟨243615305292249474618115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324820407056332632824153 243615305292249474618115)
                  ·
                    refine ⟨365422957938374211927173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 243615305292249474618115 365422957938374211927173)
                    ·
                      refine ⟨68516804613445164736345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 365422957938374211927173 68516804613445164736345)
                      ·
                        rfl

theorem cell23_133436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_133436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133436 prefixEnd_133436 := by exact prefixLift 133436
  have htrace : WordTrace (prefixWord ++ tailWord_133436) baseStart_133436 baseEnd_133436 := by
    simpa [prefixWord, tailWord_133436, baseEnd_133436] using wordTrace_append hprefix tailTrace_133436
  have hstable : (prefixWord ++ tailWord_133436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133436).length < 2 ^ (prefixWord ++ tailWord_133436).sum := by decide
  have hdescent : baseEnd_133436 < baseStart_133436 := by decide
  rcases family_descends (prefixWord ++ tailWord_133436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133456 : List Nat := [2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 3]
def baseStart_133456 : Nat := 118140960795 + 133456 * 2 ^ 59
def prefixEnd_133456 : Nat := 4983230072969 + 3 ^ 40 * 133456 * 2
def baseEnd_133456 : Nat := 68527074226535086486253

theorem tailTrace_133456 : CollatzResearch.WordTrace tailWord_133456 prefixEnd_133456 68527074226535086486253 := by
  unfold tailWord_133456
  simp only [CollatzResearch.WordTrace]
  refine ⟨2433770102259589657654111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3245026803012786210205481 2433770102259589657654111)
  ·
    refine ⟨3650655153389384486481167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2433770102259589657654111 3650655153389384486481167)
    ·
      refine ⟨5475982730084076729721751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3650655153389384486481167 5475982730084076729721751)
      ·
        refine ⟨8213974095126115094582627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5475982730084076729721751 8213974095126115094582627)
        ·
          refine ⟨12320961142689172641873941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8213974095126115094582627 12320961142689172641873941)
          ·
            refine ⟨577545053563554967587841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12320961142689172641873941 577545053563554967587841)
            ·
              refine ⟨433158790172666225690881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577545053563554967587841 433158790172666225690881)
              ·
                refine ⟨324869092629499669268161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433158790172666225690881 324869092629499669268161)
                ·
                  refine ⟨243651819472124751951121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324869092629499669268161 243651819472124751951121)
                  ·
                    refine ⟨182738864604093563963341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 243651819472124751951121 182738864604093563963341)
                    ·
                      refine ⟨68527074226535086486253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 182738864604093563963341 68527074226535086486253)
                      ·
                        rfl

theorem cell23_133456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 3].length) (baseStart_133456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133456 prefixEnd_133456 := by exact prefixLift 133456
  have htrace : WordTrace (prefixWord ++ tailWord_133456) baseStart_133456 baseEnd_133456 := by
    simpa [prefixWord, tailWord_133456, baseEnd_133456] using wordTrace_append hprefix tailTrace_133456
  have hstable : (prefixWord ++ tailWord_133456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133456).length < 2 ^ (prefixWord ++ tailWord_133456).sum := by decide
  have hdescent : baseEnd_133456 < baseStart_133456 := by decide
  rcases family_descends (prefixWord ++ tailWord_133456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133463 : List Nat := [1, 1, 3, 2, 3, 1, 3, 4, 1, 4]
def baseStart_133463 : Nat := 118140960795 + 133463 * 2 ^ 59
def prefixEnd_133463 : Nat := 4983230072969 + 3 ^ 40 * 133463 * 2
def baseEnd_133463 : Nat := 22843556197038853032907

theorem tailTrace_133463 : CollatzResearch.WordTrace tailWord_133463 prefixEnd_133463 22843556197038853032907 := by
  unfold tailWord_133463
  simp only [CollatzResearch.WordTrace]
  refine ⟨4867795515493819510813043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3245197010329213007208695 4867795515493819510813043)
  ·
    refine ⟨7301693273240729266219565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4867795515493819510813043 7301693273240729266219565)
    ·
      refine ⟨2738134977465273474832337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7301693273240729266219565 2738134977465273474832337)
      ·
        refine ⟨2053601233098955106124253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2738134977465273474832337 2053601233098955106124253)
        ·
          refine ⟨770100462412108164796595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2053601233098955106124253 770100462412108164796595)
          ·
            refine ⟨1155150693618162247194893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770100462412108164796595 1155150693618162247194893)
            ·
              refine ⟨433181510106810842698085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1155150693618162247194893 433181510106810842698085)
              ·
                refine ⟨81221533145027033005891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 433181510106810842698085 81221533145027033005891)
                ·
                  refine ⟨121832299717540549508837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81221533145027033005891 121832299717540549508837)
                  ·
                    refine ⟨22843556197038853032907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121832299717540549508837 22843556197038853032907)
                    ·
                      rfl

theorem cell23_133463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4, 1, 4].length) (baseStart_133463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133463 prefixEnd_133463 := by exact prefixLift 133463
  have htrace : WordTrace (prefixWord ++ tailWord_133463) baseStart_133463 baseEnd_133463 := by
    simpa [prefixWord, tailWord_133463, baseEnd_133463] using wordTrace_append hprefix tailTrace_133463
  have hstable : (prefixWord ++ tailWord_133463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133463).length < 2 ^ (prefixWord ++ tailWord_133463).sum := by decide
  have hdescent : baseEnd_133463 < baseStart_133463 := by decide
  rcases family_descends (prefixWord ++ tailWord_133463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133536 : List Nat := [2, 1, 1, 4, 1, 3, 3, 1, 1, 6]
def baseStart_133536 : Nat := 118140960795 + 133536 * 2 ^ 59
def prefixEnd_133536 : Nat := 4983230072969 + 3 ^ 40 * 133536 * 2
def baseEnd_133536 : Nat := 22856050892964924495295

theorem tailTrace_133536 : CollatzResearch.WordTrace tailWord_133536 prefixEnd_133536 22856050892964924495295 := by
  unfold tailWord_133536
  simp only [CollatzResearch.WordTrace]
  refine ⟨2435229022114676489110231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3246972029486235318813641 2435229022114676489110231)
  ·
    refine ⟨3652843533172014733665347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2435229022114676489110231 3652843533172014733665347)
    ·
      refine ⟨5479265299758022100498021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3652843533172014733665347 5479265299758022100498021)
      ·
        refine ⟨1027362243704629143843379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5479265299758022100498021 1027362243704629143843379)
        ·
          refine ⟨1541043365556943715765069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1027362243704629143843379 1541043365556943715765069)
          ·
            refine ⟨577891262083853893411901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1541043365556943715765069 577891262083853893411901)
            ·
              refine ⟨216709223281445210029463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 577891262083853893411901 216709223281445210029463)
              ·
                refine ⟨325063834922167815044195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216709223281445210029463 325063834922167815044195)
                ·
                  refine ⟨487595752383251722566293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 325063834922167815044195 487595752383251722566293)
                  ·
                    refine ⟨22856050892964924495295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 487595752383251722566293 22856050892964924495295)
                    ·
                      rfl

theorem cell23_133536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 1, 6].length) (baseStart_133536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133536 prefixEnd_133536 := by exact prefixLift 133536
  have htrace : WordTrace (prefixWord ++ tailWord_133536) baseStart_133536 baseEnd_133536 := by
    simpa [prefixWord, tailWord_133536, baseEnd_133536] using wordTrace_append hprefix tailTrace_133536
  have hstable : (prefixWord ++ tailWord_133536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133536).length < 2 ^ (prefixWord ++ tailWord_133536).sum := by decide
  have hdescent : baseEnd_133536 < baseStart_133536 := by decide
  rcases family_descends (prefixWord ++ tailWord_133536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133543 : List Nat := [1, 1, 6, 1, 1, 2, 1, 4, 1, 1, 4]
def baseStart_133543 : Nat := 118140960795 + 133543 * 2 ^ 59
def prefixEnd_133543 : Nat := 4983230072969 + 3 ^ 40 * 133543 * 2
def baseEnd_133543 : Nat := 68571747043476246098353

theorem tailTrace_133543 : CollatzResearch.WordTrace tailWord_133543 prefixEnd_133543 68571747043476246098353 := by
  unfold tailWord_133543
  simp only [CollatzResearch.WordTrace]
  refine ⟨4870713355203993173725283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3247142236802662115816855 4870713355203993173725283)
  ·
    refine ⟨7306070032805989760587925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4870713355203993173725283 7306070032805989760587925)
    ·
      refine ⟨342472032787780770027559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7306070032805989760587925 342472032787780770027559)
      ·
        refine ⟨513708049181671155041339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342472032787780770027559 513708049181671155041339)
        ·
          refine ⟨770562073772506732562009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513708049181671155041339 770562073772506732562009)
          ·
            refine ⟨577921555329380049421507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 770562073772506732562009 577921555329380049421507)
            ·
              refine ⟨866882332994070074132261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577921555329380049421507 866882332994070074132261)
              ·
                refine ⟨162540437436388138899799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 866882332994070074132261 162540437436388138899799)
                ·
                  refine ⟨243810656154582208349699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162540437436388138899799 243810656154582208349699)
                  ·
                    refine ⟨365715984231873312524549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 243810656154582208349699 365715984231873312524549)
                    ·
                      refine ⟨68571747043476246098353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 365715984231873312524549 68571747043476246098353)
                      ·
                        rfl

theorem cell23_133543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_133543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133543 prefixEnd_133543 := by exact prefixLift 133543
  have htrace : WordTrace (prefixWord ++ tailWord_133543) baseStart_133543 baseEnd_133543 := by
    simpa [prefixWord, tailWord_133543, baseEnd_133543] using wordTrace_append hprefix tailTrace_133543
  have hstable : (prefixWord ++ tailWord_133543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133543).length < 2 ^ (prefixWord ++ tailWord_133543).sum := by decide
  have hdescent : baseEnd_133543 < baseStart_133543 := by decide
  rcases family_descends (prefixWord ++ tailWord_133543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133579 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 2, 7]
def baseStart_133579 : Nat := 118140960795 + 133579 * 2 ^ 59
def prefixEnd_133579 : Nat := 4983230072969 + 3 ^ 40 * 133579 * 2
def baseEnd_133579 : Nat := 22863410782346035082729

theorem tailTrace_133579 : CollatzResearch.WordTrace tailWord_133579 prefixEnd_133579 22863410782346035082729 := by
  unfold tailWord_133579
  simp only [CollatzResearch.WordTrace]
  refine ⟨4872026383073571322035791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3248017588715714214690527 4872026383073571322035791)
  ·
    refine ⟨7308039574610356983053687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4872026383073571322035791 7308039574610356983053687)
    ·
      refine ⟨10962059361915535474580531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7308039574610356983053687 10962059361915535474580531)
      ·
        refine ⟨16443089042873303211870797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10962059361915535474580531 16443089042873303211870797)
        ·
          refine ⟨6166158391077488704451549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16443089042873303211870797 6166158391077488704451549)
          ·
            refine ⟨2312309396654058264169331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6166158391077488704451549 2312309396654058264169331)
            ·
              refine ⟨3468464094981087396253997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2312309396654058264169331 3468464094981087396253997)
              ·
                refine ⟨1300674035617907773595249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3468464094981087396253997 1300674035617907773595249)
                ·
                  refine ⟨975505526713430830196437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1300674035617907773595249 975505526713430830196437)
                  ·
                    refine ⟨22863410782346035082729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 975505526713430830196437 22863410782346035082729)
                    ·
                      rfl

theorem cell23_133579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 7].length) (baseStart_133579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133579 prefixEnd_133579 := by exact prefixLift 133579
  have htrace : WordTrace (prefixWord ++ tailWord_133579) baseStart_133579 baseEnd_133579 := by
    simpa [prefixWord, tailWord_133579, baseEnd_133579] using wordTrace_append hprefix tailTrace_133579
  have hstable : (prefixWord ++ tailWord_133579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133579).length < 2 ^ (prefixWord ++ tailWord_133579).sum := by decide
  have hdescent : baseEnd_133579 < baseStart_133579 := by decide
  rcases family_descends (prefixWord ++ tailWord_133579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133609 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 3, 8]
def baseStart_133609 : Nat := 118140960795 + 133609 * 2 ^ 59
def prefixEnd_133609 : Nat := 4983230072969 + 3 ^ 40 * 133609 * 2
def baseEnd_133609 : Nat := 22868545588890995957683

theorem tailTrace_133609 : CollatzResearch.WordTrace tailWord_133609 prefixEnd_133609 22868545588890995957683 := by
  unfold tailWord_133609
  simp only [CollatzResearch.WordTrace]
  refine ⟨4873120572964886445627881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3248747048643257630418587 4873120572964886445627881)
  ·
    refine ⟨3654840429723664834220911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4873120572964886445627881 3654840429723664834220911)
    ·
      refine ⟨5482260644585497251331367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3654840429723664834220911 5482260644585497251331367)
      ·
        refine ⟨8223390966878245876997051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5482260644585497251331367 8223390966878245876997051)
        ·
          refine ⟨12335086450317368815495577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8223390966878245876997051 12335086450317368815495577)
          ·
            refine ⟨9251314837738026611621683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12335086450317368815495577 9251314837738026611621683)
            ·
              refine ⟨13876972256607039917432525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9251314837738026611621683 13876972256607039917432525)
              ·
                refine ⟨5203864596227639969037197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13876972256607039917432525 5203864596227639969037197)
                ·
                  refine ⟨1951449223585364988388949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5203864596227639969037197 1951449223585364988388949)
                  ·
                    refine ⟨22868545588890995957683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1951449223585364988388949 22868545588890995957683)
                    ·
                      rfl

theorem cell23_133609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 8].length) (baseStart_133609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133609 prefixEnd_133609 := by exact prefixLift 133609
  have htrace : WordTrace (prefixWord ++ tailWord_133609) baseStart_133609 baseEnd_133609 := by
    simpa [prefixWord, tailWord_133609, baseEnd_133609] using wordTrace_append hprefix tailTrace_133609
  have hstable : (prefixWord ++ tailWord_133609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133609).length < 2 ^ (prefixWord ++ tailWord_133609).sum := by decide
  have hdescent : baseEnd_133609 < baseStart_133609 := by decide
  rcases family_descends (prefixWord ++ tailWord_133609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133656 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 9]
def baseStart_133656 : Nat := 118140960795 + 133656 * 2 ^ 59
def prefixEnd_133656 : Nat := 4983230072969 + 3 ^ 40 * 133656 * 2
def baseEnd_133656 : Nat := 7625530039714922665037

theorem tailTrace_133656 : CollatzResearch.WordTrace tailWord_133656 prefixEnd_133656 7625530039714922665037 := by
  unfold tailWord_133656
  simp only [CollatzResearch.WordTrace]
  refine ⟨2437417401897306736294411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3249889869196408981725881 2437417401897306736294411)
  ·
    refine ⟨3656126102845960104441617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2437417401897306736294411 3656126102845960104441617)
    ·
      refine ⟨2742094577134470078331213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3656126102845960104441617 2742094577134470078331213)
      ·
        refine ⟨1028285466425426279374205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2742094577134470078331213 1028285466425426279374205)
        ·
          refine ⟨385607049909534854765327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1028285466425426279374205 385607049909534854765327)
          ·
            refine ⟨578410574864302282147991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385607049909534854765327 578410574864302282147991)
            ·
              refine ⟨867615862296453423221987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578410574864302282147991 867615862296453423221987)
              ·
                refine ⟨1301423793444680134832981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 867615862296453423221987 1301423793444680134832981)
                ·
                  refine ⟨7625530039714922665037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1301423793444680134832981 7625530039714922665037)
                  ·
                    rfl

theorem cell23_133656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 9].length) (baseStart_133656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133656 prefixEnd_133656 := by exact prefixLift 133656
  have htrace : WordTrace (prefixWord ++ tailWord_133656) baseStart_133656 baseEnd_133656 := by
    simpa [prefixWord, tailWord_133656, baseEnd_133656] using wordTrace_append hprefix tailTrace_133656
  have hstable : (prefixWord ++ tailWord_133656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133656).length < 2 ^ (prefixWord ++ tailWord_133656).sum := by decide
  have hdescent : baseEnd_133656 < baseStart_133656 := by decide
  rcases family_descends (prefixWord ++ tailWord_133656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133666 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_133666 : Nat := 118140960795 + 133666 * 2 ^ 59
def prefixEnd_133666 : Nat := 4983230072969 + 3 ^ 40 * 133666 * 2
def baseEnd_133666 : Nat := 68634905163979264860287

theorem tailTrace_133666 : CollatzResearch.WordTrace tailWord_133666 prefixEnd_133666 68634905163979264860287 := by
  unfold tailWord_133666
  simp only [CollatzResearch.WordTrace]
  refine ⟨1218799883439596295113213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3250133022505590120301901 1218799883439596295113213)
  ·
    refine ⟨457049956289848610667455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1218799883439596295113213 457049956289848610667455)
    ·
      refine ⟨685574934434772916001183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457049956289848610667455 685574934434772916001183)
      ·
        refine ⟨1028362401652159374001775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685574934434772916001183 1028362401652159374001775)
        ·
          refine ⟨1542543602478239061002663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1028362401652159374001775 1542543602478239061002663)
          ·
            refine ⟨2313815403717358591503995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1542543602478239061002663 2313815403717358591503995)
            ·
              refine ⟨3470723105576037887255993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2313815403717358591503995 3470723105576037887255993)
              ·
                refine ⟨2603042329182028415441995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3470723105576037887255993 2603042329182028415441995)
                ·
                  refine ⟨3904563493773042623162993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2603042329182028415441995 3904563493773042623162993)
                  ·
                    refine ⟨2928422620329781967372245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3904563493773042623162993 2928422620329781967372245)
                    ·
                      refine ⟨68634905163979264860287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 2928422620329781967372245 68634905163979264860287)
                      ·
                        rfl

theorem cell23_133666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_133666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133666 prefixEnd_133666 := by exact prefixLift 133666
  have htrace : WordTrace (prefixWord ++ tailWord_133666) baseStart_133666 baseEnd_133666 := by
    simpa [prefixWord, tailWord_133666, baseEnd_133666] using wordTrace_append hprefix tailTrace_133666
  have hstable : (prefixWord ++ tailWord_133666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133666).length < 2 ^ (prefixWord ++ tailWord_133666).sum := by decide
  have hdescent : baseEnd_133666 < baseStart_133666 := by decide
  rcases family_descends (prefixWord ++ tailWord_133666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133696 : List Nat := [2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 5]
def baseStart_133696 : Nat := 118140960795 + 133696 * 2 ^ 59
def prefixEnd_133696 : Nat := 4983230072969 + 3 ^ 40 * 133696 * 2
def baseEnd_133696 : Nat := 68650309583614147485149

theorem tailTrace_133696 : CollatzResearch.WordTrace tailWord_133696 prefixEnd_133696 68650309583614147485149 := by
  unfold tailWord_133696
  simp only [CollatzResearch.WordTrace]
  refine ⟨2438146861824850152022471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3250862482433133536029961 2438146861824850152022471)
  ·
    refine ⟨3657220292737275228033707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2438146861824850152022471 3657220292737275228033707)
    ·
      refine ⟨5485830439105912842050561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3657220292737275228033707 5485830439105912842050561)
      ·
        refine ⟨4114372829329434631537921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5485830439105912842050561 4114372829329434631537921)
        ·
          refine ⟨3085779621997075973653441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4114372829329434631537921 3085779621997075973653441)
          ·
            refine ⟨2314334716497806980240081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3085779621997075973653441 2314334716497806980240081)
            ·
              refine ⟨1735751037373355235180061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2314334716497806980240081 1735751037373355235180061)
              ·
                refine ⟨650906639015008213192523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1735751037373355235180061 650906639015008213192523)
                ·
                  refine ⟨976359958522512319788785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 650906639015008213192523 976359958522512319788785)
                  ·
                    refine ⟨732269968891884239841589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 976359958522512319788785 732269968891884239841589)
                    ·
                      refine ⟨68650309583614147485149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 732269968891884239841589 68650309583614147485149)
                      ·
                        rfl

theorem cell23_133696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_133696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133696 prefixEnd_133696 := by exact prefixLift 133696
  have htrace : WordTrace (prefixWord ++ tailWord_133696) baseStart_133696 baseEnd_133696 := by
    simpa [prefixWord, tailWord_133696, baseEnd_133696] using wordTrace_append hprefix tailTrace_133696
  have hstable : (prefixWord ++ tailWord_133696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133696).length < 2 ^ (prefixWord ++ tailWord_133696).sum := by decide
  have hdescent : baseEnd_133696 < baseStart_133696 := by decide
  rcases family_descends (prefixWord ++ tailWord_133696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133724 : List Nat := [2, 2, 4, 1, 4, 1, 1, 3, 5]
def baseStart_133724 : Nat := 118140960795 + 133724 * 2 ^ 59
def prefixEnd_133724 : Nat := 4983230072969 + 3 ^ 40 * 133724 * 2
def baseEnd_133724 : Nat := 7629409671326670881669

theorem tailTrace_133724 : CollatzResearch.WordTrace tailWord_133724 prefixEnd_133724 7629409671326670881669 := by
  unfold tailWord_133724
  simp only [CollatzResearch.WordTrace]
  refine ⟨2438657483774130543032113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3251543311698840724042817 2438657483774130543032113)
  ·
    refine ⟨1828993112830597907274085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2438657483774130543032113 1828993112830597907274085)
    ·
      refine ⟨342936208655737107613891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1828993112830597907274085 342936208655737107613891)
      ·
        refine ⟨514404312983605661420837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342936208655737107613891 514404312983605661420837)
        ·
          refine ⟨96450808684426061516407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 514404312983605661420837 96450808684426061516407)
          ·
            refine ⟨144676213026639092274611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96450808684426061516407 144676213026639092274611)
            ·
              refine ⟨217014319539958638411917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144676213026639092274611 217014319539958638411917)
              ·
                refine ⟨81380369827484489404469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217014319539958638411917 81380369827484489404469)
                ·
                  refine ⟨7629409671326670881669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81380369827484489404469 7629409671326670881669)
                  ·
                    rfl

theorem cell23_133724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3, 5].length) (baseStart_133724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133724 prefixEnd_133724 := by exact prefixLift 133724
  have htrace : WordTrace (prefixWord ++ tailWord_133724) baseStart_133724 baseEnd_133724 := by
    simpa [prefixWord, tailWord_133724, baseEnd_133724] using wordTrace_append hprefix tailTrace_133724
  have hstable : (prefixWord ++ tailWord_133724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133724).length < 2 ^ (prefixWord ++ tailWord_133724).sum := by decide
  have hdescent : baseEnd_133724 < baseStart_133724 := by decide
  rcases family_descends (prefixWord ++ tailWord_133724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133743 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 4, 2, 3]
def baseStart_133743 : Nat := 118140960795 + 133743 * 2 ^ 59
def prefixEnd_133743 : Nat := 4983230072969 + 3 ^ 40 * 133743 * 2
def baseEnd_133743 : Nat := 68674443174375463597433

theorem tailTrace_133743 : CollatzResearch.WordTrace tailWord_133743 prefixEnd_133743 68674443174375463597433 := by
  unfold tailWord_133743
  simp only [CollatzResearch.WordTrace]
  refine ⟨4878007954479427331005883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3252005302986284887337255 4878007954479427331005883)
  ·
    refine ⟨7317011931719140996508825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4878007954479427331005883 7317011931719140996508825)
    ·
      refine ⟨5487758948789355747381619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7317011931719140996508825 5487758948789355747381619)
      ·
        refine ⟨8231638423184033621072429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5487758948789355747381619 8231638423184033621072429)
        ·
          refine ⟨3086864408694012607902161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8231638423184033621072429 3086864408694012607902161)
          ·
            refine ⟨2315148306520509455926621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3086864408694012607902161 2315148306520509455926621)
            ·
              refine ⟨868180614945191045972483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2315148306520509455926621 868180614945191045972483)
              ·
                refine ⟨1302270922417786568958725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 868180614945191045972483 1302270922417786568958725)
                ·
                  refine ⟨244175797953334981679761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1302270922417786568958725 244175797953334981679761)
                  ·
                    refine ⟨183131848465001236259821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 244175797953334981679761 183131848465001236259821)
                    ·
                      refine ⟨68674443174375463597433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 183131848465001236259821 68674443174375463597433)
                      ·
                        rfl

theorem cell23_133743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2, 3].length) (baseStart_133743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133743 prefixEnd_133743 := by exact prefixLift 133743
  have htrace : WordTrace (prefixWord ++ tailWord_133743) baseStart_133743 baseEnd_133743 := by
    simpa [prefixWord, tailWord_133743, baseEnd_133743] using wordTrace_append hprefix tailTrace_133743
  have hstable : (prefixWord ++ tailWord_133743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133743).length < 2 ^ (prefixWord ++ tailWord_133743).sum := by decide
  have hdescent : baseEnd_133743 < baseStart_133743 := by decide
  rcases family_descends (prefixWord ++ tailWord_133743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133823 : List Nat := [1, 1, 2, 2, 2, 4, 1, 3, 1, 6]
def baseStart_133823 : Nat := 118140960795 + 133823 * 2 ^ 59
def prefixEnd_133823 : Nat := 4983230072969 + 3 ^ 40 * 133823 * 2
def baseEnd_133823 : Nat := 22905173875578383532355

theorem tailTrace_133823 : CollatzResearch.WordTrace tailWord_133823 prefixEnd_133823 22905173875578383532355 := by
  unfold tailWord_133823
  simp only [CollatzResearch.WordTrace]
  refine ⟨4880925794189600993918123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3253950529459733995945415 4880925794189600993918123)
  ·
    refine ⟨7321388691284401490877185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4880925794189600993918123 7321388691284401490877185)
    ·
      refine ⟨5491041518463301118157889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7321388691284401490877185 5491041518463301118157889)
      ·
        refine ⟨4118281138847475838618417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5491041518463301118157889 4118281138847475838618417)
        ·
          refine ⟨3088710854135606878963813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4118281138847475838618417 3088710854135606878963813)
          ·
            refine ⟨579133285150426289805715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3088710854135606878963813 579133285150426289805715)
            ·
              refine ⟨868699927725639434708573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579133285150426289805715 868699927725639434708573)
              ·
                refine ⟨325762472897114788015715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 868699927725639434708573 325762472897114788015715)
                ·
                  refine ⟨488643709345672182023573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 325762472897114788015715 488643709345672182023573)
                  ·
                    refine ⟨22905173875578383532355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 488643709345672182023573 22905173875578383532355)
                    ·
                      rfl

theorem cell23_133823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 6].length) (baseStart_133823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133823 prefixEnd_133823 := by exact prefixLift 133823
  have htrace : WordTrace (prefixWord ++ tailWord_133823) baseStart_133823 baseEnd_133823 := by
    simpa [prefixWord, tailWord_133823, baseEnd_133823] using wordTrace_append hprefix tailTrace_133823
  have hstable : (prefixWord ++ tailWord_133823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133823).length < 2 ^ (prefixWord ++ tailWord_133823).sum := by decide
  have hdescent : baseEnd_133823 < baseStart_133823 := by decide
  rcases family_descends (prefixWord ++ tailWord_133823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133834 : List Nat := [3, 1, 2, 1, 4, 3, 1, 1, 2, 3, 2]
def baseStart_133834 : Nat := 118140960795 + 133834 * 2 ^ 59
def prefixEnd_133834 : Nat := 4983230072969 + 3 ^ 40 * 133834 * 2
def baseEnd_133834 : Nat := 68721169913934607559515

theorem tailTrace_133834 : CollatzResearch.WordTrace tailWord_133834 prefixEnd_133834 68721169913934607559515 := by
  unfold tailWord_133834
  simp only [CollatzResearch.WordTrace]
  refine ⟨1220331749287437468142139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3254217998099833248379037 1220331749287437468142139)
  ·
    refine ⟨1830497623931156202213209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1220331749287437468142139 1830497623931156202213209)
    ·
      refine ⟨1372873217948367151659907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1830497623931156202213209 1372873217948367151659907)
      ·
        refine ⟨2059309826922550727489861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1372873217948367151659907 2059309826922550727489861)
        ·
          refine ⟨386120592547978261404349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2059309826922550727489861 386120592547978261404349)
          ·
            refine ⟨144795222205491848026631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 386120592547978261404349 144795222205491848026631)
            ·
              refine ⟨217192833308237772039947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144795222205491848026631 217192833308237772039947)
              ·
                refine ⟨325789249962356658059921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217192833308237772039947 325789249962356658059921)
                ·
                  refine ⟨244341937471767493544941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 325789249962356658059921 244341937471767493544941)
                  ·
                    refine ⟨91628226551912810079353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 244341937471767493544941 91628226551912810079353)
                    ·
                      refine ⟨68721169913934607559515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 91628226551912810079353 68721169913934607559515)
                      ·
                        rfl

theorem cell23_133834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 2, 3, 2].length) (baseStart_133834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133834 prefixEnd_133834 := by exact prefixLift 133834
  have htrace : WordTrace (prefixWord ++ tailWord_133834) baseStart_133834 baseEnd_133834 := by
    simpa [prefixWord, tailWord_133834, baseEnd_133834] using wordTrace_append hprefix tailTrace_133834
  have hstable : (prefixWord ++ tailWord_133834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133834).length < 2 ^ (prefixWord ++ tailWord_133834).sum := by decide
  have hdescent : baseEnd_133834 < baseStart_133834 := by decide
  rcases family_descends (prefixWord ++ tailWord_133834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133847 : List Nat := [1, 1, 3, 2, 1, 4, 4, 1, 1, 1, 4]
def baseStart_133847 : Nat := 118140960795 + 133847 * 2 ^ 59
def prefixEnd_133847 : Nat := 4983230072969 + 3 ^ 40 * 133847 * 2
def baseEnd_133847 : Nat := 68727845162443056696955

theorem tailTrace_133847 : CollatzResearch.WordTrace tailWord_133847 prefixEnd_133847 68727845162443056696955 := by
  unfold tailWord_133847
  simp only [CollatzResearch.WordTrace]
  refine ⟨4881801146102653092791795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3254534097401768728527863 4881801146102653092791795)
  ·
    refine ⟨7322701719153979639187693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4881801146102653092791795 7322701719153979639187693)
    ·
      refine ⟨2746013144682742364695385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7322701719153979639187693 2746013144682742364695385)
      ·
        refine ⟨2059509858512056773521539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2746013144682742364695385 2059509858512056773521539)
        ·
          refine ⟨3089264787768085160282309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2059509858512056773521539 3089264787768085160282309)
          ·
            refine ⟨579237147706515967552933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3089264787768085160282309 579237147706515967552933)
            ·
              refine ⟨108606965194971743916175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 579237147706515967552933 108606965194971743916175)
              ·
                refine ⟨162910447792457615874263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108606965194971743916175 162910447792457615874263)
                ·
                  refine ⟨244365671688686423811395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162910447792457615874263 244365671688686423811395)
                  ·
                    refine ⟨366548507533029635717093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 244365671688686423811395 366548507533029635717093)
                    ·
                      refine ⟨68727845162443056696955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 366548507533029635717093 68727845162443056696955)
                      ·
                        rfl

theorem cell23_133847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 1, 1, 4].length) (baseStart_133847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133847 prefixEnd_133847 := by exact prefixLift 133847
  have htrace : WordTrace (prefixWord ++ tailWord_133847) baseStart_133847 baseEnd_133847 := by
    simpa [prefixWord, tailWord_133847, baseEnd_133847] using wordTrace_append hprefix tailTrace_133847
  have hstable : (prefixWord ++ tailWord_133847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133847).length < 2 ^ (prefixWord ++ tailWord_133847).sum := by decide
  have hdescent : baseEnd_133847 < baseStart_133847 := by decide
  rcases family_descends (prefixWord ++ tailWord_133847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133857 : List Nat := [1, 2, 3, 1, 4, 1, 3, 2, 2, 4]
def baseStart_133857 : Nat := 118140960795 + 133857 * 2 ^ 59
def prefixEnd_133857 : Nat := 4983230072969 + 3 ^ 40 * 133857 * 2
def baseEnd_133857 : Nat := 22910993322996005857303

theorem tailTrace_133857 : CollatzResearch.WordTrace tailWord_133857 prefixEnd_133857 22910993322996005857303 := by
  unfold tailWord_133857
  simp only [CollatzResearch.WordTrace]
  refine ⟨4882165876066424800655825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3254777250710949867103883 4882165876066424800655825)
  ·
    refine ⟨3661624407049818600491869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4882165876066424800655825 3661624407049818600491869)
    ·
      refine ⟨1373109152643681975184451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3661624407049818600491869 1373109152643681975184451)
      ·
        refine ⟨2059663728965522962776677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1373109152643681975184451 2059663728965522962776677)
        ·
          refine ⟨386186949181035555520627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2059663728965522962776677 386186949181035555520627)
          ·
            refine ⟨579280423771553333280941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386186949181035555520627 579280423771553333280941)
            ·
              refine ⟨217230158914332499980353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 579280423771553333280941 217230158914332499980353)
              ·
                refine ⟨162922619185749374985265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217230158914332499980353 162922619185749374985265)
                ·
                  refine ⟨122191964389312031238949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162922619185749374985265 122191964389312031238949)
                  ·
                    refine ⟨22910993322996005857303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 122191964389312031238949 22910993322996005857303)
                    ·
                      rfl

theorem cell23_133857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_133857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133857 prefixEnd_133857 := by exact prefixLift 133857
  have htrace : WordTrace (prefixWord ++ tailWord_133857) baseStart_133857 baseEnd_133857 := by
    simpa [prefixWord, tailWord_133857, baseEnd_133857] using wordTrace_append hprefix tailTrace_133857
  have hstable : (prefixWord ++ tailWord_133857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133857).length < 2 ^ (prefixWord ++ tailWord_133857).sum := by decide
  have hdescent : baseEnd_133857 < baseStart_133857 := by decide
  rcases family_descends (prefixWord ++ tailWord_133857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133874 : List Nat := [3, 2, 1, 3, 1, 3, 3, 1, 2, 4]
def baseStart_133874 : Nat := 118140960795 + 133874 * 2 ^ 59
def prefixEnd_133874 : Nat := 4983230072969 + 3 ^ 40 * 133874 * 2
def baseEnd_133874 : Nat := 22913903046704817019777

theorem tailTrace_133874 : CollatzResearch.WordTrace tailWord_133874 prefixEnd_133874 22913903046704817019777 := by
  unfold tailWord_133874
  simp only [CollatzResearch.WordTrace]
  refine ⟨1220696479251209176006169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3255190611336557802683117 1220696479251209176006169)
  ·
    refine ⟨915522359438406882004627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1220696479251209176006169 915522359438406882004627)
    ·
      refine ⟨1373283539157610323006941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 915522359438406882004627 1373283539157610323006941)
      ·
        refine ⟨514981327184103871127603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1373283539157610323006941 514981327184103871127603)
        ·
          refine ⟨772471990776155806691405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514981327184103871127603 772471990776155806691405)
          ·
            refine ⟨289676996541058427509277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 772471990776155806691405 289676996541058427509277)
            ·
              refine ⟨108628873702896910315979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289676996541058427509277 108628873702896910315979)
              ·
                refine ⟨162943310554345365473969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108628873702896910315979 162943310554345365473969)
                ·
                  refine ⟨122207482915759024105477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162943310554345365473969 122207482915759024105477)
                  ·
                    refine ⟨22913903046704817019777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 122207482915759024105477 22913903046704817019777)
                    ·
                      rfl

theorem cell23_133874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_133874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133874 prefixEnd_133874 := by exact prefixLift 133874
  have htrace : WordTrace (prefixWord ++ tailWord_133874) baseStart_133874 baseEnd_133874 := by
    simpa [prefixWord, tailWord_133874, baseEnd_133874] using wordTrace_append hprefix tailTrace_133874
  have hstable : (prefixWord ++ tailWord_133874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133874).length < 2 ^ (prefixWord ++ tailWord_133874).sum := by decide
  have hdescent : baseEnd_133874 < baseStart_133874 := by decide
  rcases family_descends (prefixWord ++ tailWord_133874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133907 : List Nat := [1, 1, 1, 2, 1, 3, 3, 5, 1, 3, 2]
def baseStart_133907 : Nat := 118140960795 + 133907 * 2 ^ 59
def prefixEnd_133907 : Nat := 4983230072969 + 3 ^ 40 * 133907 * 2
def baseEnd_133907 : Nat := 68758654001712821946679

theorem tailTrace_133907 : CollatzResearch.WordTrace tailWord_133907 prefixEnd_133907 68758654001712821946679 := by
  unfold tailWord_133907
  simp only [CollatzResearch.WordTrace]
  refine ⟨4883989525885283339975975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3255993017256855559983983 4883989525885283339975975)
  ·
    refine ⟨7325984288827925009963963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4883989525885283339975975 7325984288827925009963963)
    ·
      refine ⟨10988976433241887514945945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7325984288827925009963963 10988976433241887514945945)
      ·
        refine ⟨8241732324931415636209459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10988976433241887514945945 8241732324931415636209459)
        ·
          refine ⟨12362598487397123454314189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8241732324931415636209459 12362598487397123454314189)
          ·
            refine ⟨4635974432773921295367821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12362598487397123454314189 4635974432773921295367821)
            ·
              refine ⟨1738490412290220485762933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4635974432773921295367821 1738490412290220485762933)
              ·
                refine ⟨162983476152208170540275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1738490412290220485762933 162983476152208170540275)
                ·
                  refine ⟨244475214228312255810413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162983476152208170540275 244475214228312255810413)
                  ·
                    refine ⟨91678205335617095928905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 244475214228312255810413 91678205335617095928905)
                    ·
                      refine ⟨68758654001712821946679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 91678205335617095928905 68758654001712821946679)
                      ·
                        rfl

theorem cell23_133907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 3, 2].length) (baseStart_133907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133907 prefixEnd_133907 := by exact prefixLift 133907
  have htrace : WordTrace (prefixWord ++ tailWord_133907) baseStart_133907 baseEnd_133907 := by
    simpa [prefixWord, tailWord_133907, baseEnd_133907] using wordTrace_append hprefix tailTrace_133907
  have hstable : (prefixWord ++ tailWord_133907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133907).length < 2 ^ (prefixWord ++ tailWord_133907).sum := by decide
  have hdescent : baseEnd_133907 < baseStart_133907 := by decide
  rcases family_descends (prefixWord ++ tailWord_133907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133913 : List Nat := [1, 2, 1, 2, 1, 1, 1, 6, 2, 6]
def baseStart_133913 : Nat := 118140960795 + 133913 * 2 ^ 59
def prefixEnd_133913 : Nat := 4983230072969 + 3 ^ 40 * 133913 * 2
def baseEnd_133913 : Nat := 22920578295213266157217

theorem tailTrace_133913 : CollatzResearch.WordTrace tailWord_133913 prefixEnd_133913 22920578295213266157217 := by
  unfold tailWord_133913
  simp only [CollatzResearch.WordTrace]
  refine ⟨4884208363863546364694393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3256138909242364243129595 4884208363863546364694393)
  ·
    refine ⟨3663156272897659773520795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4884208363863546364694393 3663156272897659773520795)
    ·
      refine ⟨5494734409346489660281193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3663156272897659773520795 5494734409346489660281193)
      ·
        refine ⟨4121050807009867245210895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5494734409346489660281193 4121050807009867245210895)
        ·
          refine ⟨6181576210514800867816343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4121050807009867245210895 6181576210514800867816343)
          ·
            refine ⟨9272364315772201301724515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6181576210514800867816343 9272364315772201301724515)
            ·
              refine ⟨13908546473658301952586773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9272364315772201301724515 13908546473658301952586773)
              ·
                refine ⟨651963115952732904027505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13908546473658301952586773 651963115952732904027505)
                ·
                  refine ⟨488972336964549678020629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 651963115952732904027505 488972336964549678020629)
                  ·
                    refine ⟨22920578295213266157217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 488972336964549678020629 22920578295213266157217)
                    ·
                      rfl

theorem cell23_133913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 6].length) (baseStart_133913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133913 prefixEnd_133913 := by exact prefixLift 133913
  have htrace : WordTrace (prefixWord ++ tailWord_133913) baseStart_133913 baseEnd_133913 := by
    simpa [prefixWord, tailWord_133913, baseEnd_133913] using wordTrace_append hprefix tailTrace_133913
  have hstable : (prefixWord ++ tailWord_133913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133913).length < 2 ^ (prefixWord ++ tailWord_133913).sum := by decide
  have hdescent : baseEnd_133913 < baseStart_133913 := by decide
  rcases family_descends (prefixWord ++ tailWord_133913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133923 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 5]
def baseStart_133923 : Nat := 118140960795 + 133923 * 2 ^ 59
def prefixEnd_133923 : Nat := 4983230072969 + 3 ^ 40 * 133923 * 2
def baseEnd_133923 : Nat := 68766869692184759346605

theorem tailTrace_133923 : CollatzResearch.WordTrace tailWord_133923 prefixEnd_133923 68766869692184759346605 := by
  unfold tailWord_133923
  simp only [CollatzResearch.WordTrace]
  refine ⟨4884573093827318072558423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3256382062551545381705615 4884573093827318072558423)
  ·
    refine ⟨7326859640740977108837635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4884573093827318072558423 7326859640740977108837635)
    ·
      refine ⟨10990289461111465663256453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7326859640740977108837635 10990289461111465663256453)
      ·
        refine ⟨2060679273958399811860585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10990289461111465663256453 2060679273958399811860585)
        ·
          refine ⟨1545509455468799858895439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2060679273958399811860585 1545509455468799858895439)
          ·
            refine ⟨2318264183203199788343159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1545509455468799858895439 2318264183203199788343159)
            ·
              refine ⟨3477396274804799682514739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2318264183203199788343159 3477396274804799682514739)
              ·
                refine ⟨5216094412207199523772109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3477396274804799682514739 5216094412207199523772109)
                ·
                  refine ⟨1956035404577699821414541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5216094412207199523772109 1956035404577699821414541)
                  ·
                    refine ⟨733513276716637433030453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1956035404577699821414541 733513276716637433030453)
                    ·
                      refine ⟨68766869692184759346605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 733513276716637433030453 68766869692184759346605)
                      ·
                        rfl

theorem cell23_133923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_133923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133923 prefixEnd_133923 := by exact prefixLift 133923
  have htrace : WordTrace (prefixWord ++ tailWord_133923) baseStart_133923 baseEnd_133923 := by
    simpa [prefixWord, tailWord_133923, baseEnd_133923] using wordTrace_append hprefix tailTrace_133923
  have hstable : (prefixWord ++ tailWord_133923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133923).length < 2 ^ (prefixWord ++ tailWord_133923).sum := by decide
  have hdescent : baseEnd_133923 < baseStart_133923 := by decide
  rcases family_descends (prefixWord ++ tailWord_133923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133937 : List Nat := [1, 2, 2, 3, 2, 1, 2, 3, 1, 4, 2]
def baseStart_133937 : Nat := 118140960795 + 133937 * 2 ^ 59
def prefixEnd_133937 : Nat := 4983230072969 + 3 ^ 40 * 133937 * 2
def baseEnd_133937 : Nat := 68774058421347704571541

theorem tailTrace_133937 : CollatzResearch.WordTrace tailWord_133937 prefixEnd_133937 68774058421347704571541 := by
  unfold tailWord_133937
  simp only [CollatzResearch.WordTrace]
  refine ⟨4885083715776598463568065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3256722477184398975712043 4885083715776598463568065)
  ·
    refine ⟨3663812786832448847676049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4885083715776598463568065 3663812786832448847676049)
    ·
      refine ⟨2747859590124336635757037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3663812786832448847676049 2747859590124336635757037)
      ·
        refine ⟨1030447346296626238408889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2747859590124336635757037 1030447346296626238408889)
        ·
          refine ⟨772835509722469678806667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1030447346296626238408889 772835509722469678806667)
          ·
            refine ⟨1159253264583704518210001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772835509722469678806667 1159253264583704518210001)
            ·
              refine ⟨869439948437778388657501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1159253264583704518210001 869439948437778388657501)
              ·
                refine ⟨326039980664166895746563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 869439948437778388657501 326039980664166895746563)
                ·
                  refine ⟨489059970996250343619845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 326039980664166895746563 489059970996250343619845)
                  ·
                    refine ⟨91698744561796939428721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 489059970996250343619845 91698744561796939428721)
                    ·
                      refine ⟨68774058421347704571541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 91698744561796939428721 68774058421347704571541)
                      ·
                        rfl

theorem cell23_133937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_133937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133937 prefixEnd_133937 := by exact prefixLift 133937
  have htrace : WordTrace (prefixWord ++ tailWord_133937) baseStart_133937 baseEnd_133937 := by
    simpa [prefixWord, tailWord_133937, baseEnd_133937] using wordTrace_append hprefix tailTrace_133937
  have hstable : (prefixWord ++ tailWord_133937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133937).length < 2 ^ (prefixWord ++ tailWord_133937).sum := by decide
  have hdescent : baseEnd_133937 < baseStart_133937 := by decide
  rcases family_descends (prefixWord ++ tailWord_133937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133941 : List Nat := [1, 3, 3, 1, 3, 3, 1, 2, 1, 3, 2]
def baseStart_133941 : Nat := 118140960795 + 133941 * 2 ^ 59
def prefixEnd_133941 : Nat := 4983230072969 + 3 ^ 40 * 133941 * 2
def baseEnd_133941 : Nat := 68776112343965688921523

theorem tailTrace_133941 : CollatzResearch.WordTrace tailWord_133941 prefixEnd_133941 68776112343965688921523 := by
  unfold tailWord_133941
  simp only [CollatzResearch.WordTrace]
  refine ⟨4885229607762107146713677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3256819738508071431142451 4885229607762107146713677)
  ·
    refine ⟨1831961102910790180017629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4885229607762107146713677 1831961102910790180017629)
    ·
      refine ⟨686985413591546317506611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1831961102910790180017629 686985413591546317506611)
      ·
        refine ⟨1030478120387319476259917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686985413591546317506611 1030478120387319476259917)
        ·
          refine ⟨386429295145244803597469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1030478120387319476259917 386429295145244803597469)
          ·
            refine ⟨144910985679466801349051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 386429295145244803597469 144910985679466801349051)
            ·
              refine ⟨217366478519200202023577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144910985679466801349051 217366478519200202023577)
              ·
                refine ⟨163024858889400151517683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217366478519200202023577 163024858889400151517683)
                ·
                  refine ⟨244537288334100227276525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163024858889400151517683 244537288334100227276525)
                  ·
                    refine ⟨91701483125287585228697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 244537288334100227276525 91701483125287585228697)
                    ·
                      refine ⟨68776112343965688921523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 91701483125287585228697 68776112343965688921523)
                      ·
                        rfl

theorem cell23_133941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_133941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133941 prefixEnd_133941 := by exact prefixLift 133941
  have htrace : WordTrace (prefixWord ++ tailWord_133941) baseStart_133941 baseEnd_133941 := by
    simpa [prefixWord, tailWord_133941, baseEnd_133941] using wordTrace_append hprefix tailTrace_133941
  have hstable : (prefixWord ++ tailWord_133941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133941).length < 2 ^ (prefixWord ++ tailWord_133941).sum := by decide
  have hdescent : baseEnd_133941 < baseStart_133941 := by decide
  rcases family_descends (prefixWord ++ tailWord_133941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133943 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 9]
def baseStart_133943 : Nat := 118140960795 + 133943 * 2 ^ 59
def prefixEnd_133943 : Nat := 4983230072969 + 3 ^ 40 * 133943 * 2
def baseEnd_133943 : Nat := 7641904367252742344057

theorem tailTrace_133943 : CollatzResearch.WordTrace tailWord_133943 prefixEnd_133943 7641904367252742344057 := by
  unfold tailWord_133943
  simp only [CollatzResearch.WordTrace]
  refine ⟨4885302553754861488286483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3256868369169907658857655 4885302553754861488286483)
  ·
    refine ⟨7327953830632292232429725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4885302553754861488286483 7327953830632292232429725)
    ·
      refine ⟨2747982686487109587161147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7327953830632292232429725 2747982686487109587161147)
      ·
        refine ⟨4121974029730664380741721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2747982686487109587161147 4121974029730664380741721)
        ·
          refine ⟨3091480522297998285556291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4121974029730664380741721 3091480522297998285556291)
          ·
            refine ⟨4637220783446997428334437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3091480522297998285556291 4637220783446997428334437)
            ·
              refine ⟨869478896896312017812707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4637220783446997428334437 869478896896312017812707)
              ·
                refine ⟨1304218345344468026719061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 869478896896312017812707 1304218345344468026719061)
                ·
                  refine ⟨7641904367252742344057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1304218345344468026719061 7641904367252742344057)
                  ·
                    rfl

theorem cell23_133943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 9].length) (baseStart_133943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133943 prefixEnd_133943 := by exact prefixLift 133943
  have htrace : WordTrace (prefixWord ++ tailWord_133943) baseStart_133943 baseEnd_133943 := by
    simpa [prefixWord, tailWord_133943, baseEnd_133943] using wordTrace_append hprefix tailTrace_133943
  have hstable : (prefixWord ++ tailWord_133943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133943).length < 2 ^ (prefixWord ++ tailWord_133943).sum := by decide
  have hdescent : baseEnd_133943 < baseStart_133943 := by decide
  rcases family_descends (prefixWord ++ tailWord_133943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133977 : List Nat := [1, 2, 1, 2, 2, 5, 1, 4, 5]
def baseStart_133977 : Nat := 118140960795 + 133977 * 2 ^ 59
def prefixEnd_133977 : Nat := 4983230072969 + 3 ^ 40 * 133977 * 2
def baseEnd_133977 : Nat := 7643844183058616452373

theorem tailTrace_133977 : CollatzResearch.WordTrace tailWord_133977 prefixEnd_133977 7643844183058616452373 := by
  unfold tailWord_133977
  simp only [CollatzResearch.WordTrace]
  refine ⟨4886542635631685295024185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3257695090421123530016123 4886542635631685295024185)
  ·
    refine ⟨3664906976723763971268139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4886542635631685295024185 3664906976723763971268139)
    ·
      refine ⟨5497360465085645956902209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3664906976723763971268139 5497360465085645956902209)
      ·
        refine ⟨4123020348814234467676657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5497360465085645956902209 4123020348814234467676657)
        ·
          refine ⟨3092265261610675850757493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4123020348814234467676657 3092265261610675850757493)
          ·
            refine ⟨289899868276000861008515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3092265261610675850757493 289899868276000861008515)
            ·
              refine ⟨434849802414001291512773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289899868276000861008515 434849802414001291512773)
              ·
                refine ⟨81534337952625242158645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 434849802414001291512773 81534337952625242158645)
                ·
                  refine ⟨7643844183058616452373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81534337952625242158645 7643844183058616452373)
                  ·
                    rfl

theorem cell23_133977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4, 5].length) (baseStart_133977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133977 prefixEnd_133977 := by exact prefixLift 133977
  have htrace : WordTrace (prefixWord ++ tailWord_133977) baseStart_133977 baseEnd_133977 := by
    simpa [prefixWord, tailWord_133977, baseEnd_133977] using wordTrace_append hprefix tailTrace_133977
  have hstable : (prefixWord ++ tailWord_133977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133977).length < 2 ^ (prefixWord ++ tailWord_133977).sum := by decide
  have hdescent : baseEnd_133977 < baseStart_133977 := by decide
  rcases family_descends (prefixWord ++ tailWord_133977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133987 : List Nat := [1, 1, 1, 5, 3, 2, 1, 1, 2, 3, 3]
def baseStart_133987 : Nat := 118140960795 + 133987 * 2 ^ 59
def prefixEnd_133987 : Nat := 4983230072969 + 3 ^ 40 * 133987 * 2
def baseEnd_133987 : Nat := 68799732454072508946311

theorem tailTrace_133987 : CollatzResearch.WordTrace tailWord_133987 prefixEnd_133987 68799732454072508946311 := by
  unfold tailWord_133987
  simp only [CollatzResearch.WordTrace]
  refine ⟨4886907365595457002888215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3257938243730304668592143 4886907365595457002888215)
  ·
    refine ⟨7330361048393185504332323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4886907365595457002888215 7330361048393185504332323)
    ·
      refine ⟨10995541572589778256498485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7330361048393185504332323 10995541572589778256498485)
      ·
        refine ⟨1030832022430291711546733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10995541572589778256498485 1030832022430291711546733)
        ·
          refine ⟨386562008411359391830025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1030832022430291711546733 386562008411359391830025)
          ·
            refine ⟨289921506308519543872519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386562008411359391830025 289921506308519543872519)
            ·
              refine ⟨434882259462779315808779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289921506308519543872519 434882259462779315808779)
              ·
                refine ⟨652323389194168973713169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434882259462779315808779 652323389194168973713169)
                ·
                  refine ⟨489242541895626730284877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 652323389194168973713169 489242541895626730284877)
                  ·
                    refine ⟨183465953210860023856829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 489242541895626730284877 183465953210860023856829)
                    ·
                      refine ⟨68799732454072508946311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 183465953210860023856829 68799732454072508946311)
                      ·
                        rfl

theorem cell23_133987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_133987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133987 prefixEnd_133987 := by exact prefixLift 133987
  have htrace : WordTrace (prefixWord ++ tailWord_133987) baseStart_133987 baseEnd_133987 := by
    simpa [prefixWord, tailWord_133987, baseEnd_133987] using wordTrace_append hprefix tailTrace_133987
  have hstable : (prefixWord ++ tailWord_133987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133987).length < 2 ^ (prefixWord ++ tailWord_133987).sum := by decide
  have hdescent : baseEnd_133987 < baseStart_133987 := by decide
  rcases family_descends (prefixWord ++ tailWord_133987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133997 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 4, 5, 2]
def baseStart_133997 : Nat := 118140960795 + 133997 * 2 ^ 59
def prefixEnd_133997 : Nat := 4983230072969 + 3 ^ 40 * 133997 * 2
def baseEnd_133997 : Nat := 68804867260617469821265

theorem tailTrace_133997 : CollatzResearch.WordTrace tailWord_133997 prefixEnd_133997 68804867260617469821265 := by
  unfold tailWord_133997
  simp only [CollatzResearch.WordTrace]
  refine ⟨4887272095559228710752245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3258181397039485807168163 4887272095559228710752245)
  ·
    refine ⟨458181758958677691633023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4887272095559228710752245 458181758958677691633023)
    ·
      refine ⟨687272638438016537449535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458181758958677691633023 687272638438016537449535)
      ·
        refine ⟨1030908957657024806174303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687272638438016537449535 1030908957657024806174303)
        ·
          refine ⟨1546363436485537209261455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1030908957657024806174303 1546363436485537209261455)
          ·
            refine ⟨2319545154728305813892183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1546363436485537209261455 2319545154728305813892183)
            ·
              refine ⟨3479317732092458720838275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2319545154728305813892183 3479317732092458720838275)
              ·
                refine ⟨5218976598138688081257413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3479317732092458720838275 5218976598138688081257413)
                ·
                  refine ⟨978558112151004015235765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5218976598138688081257413 978558112151004015235765)
                  ·
                    refine ⟨91739823014156626428353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 978558112151004015235765 91739823014156626428353)
                    ·
                      refine ⟨68804867260617469821265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 91739823014156626428353 68804867260617469821265)
                      ·
                        rfl

theorem cell23_133997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_133997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_133997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_133997 prefixEnd_133997 := by exact prefixLift 133997
  have htrace : WordTrace (prefixWord ++ tailWord_133997) baseStart_133997 baseEnd_133997 := by
    simpa [prefixWord, tailWord_133997, baseEnd_133997] using wordTrace_append hprefix tailTrace_133997
  have hstable : (prefixWord ++ tailWord_133997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133997).length < 2 ^ (prefixWord ++ tailWord_133997).sum := by decide
  have hdescent : baseEnd_133997 < baseStart_133997 := by decide
  rcases family_descends (prefixWord ++ tailWord_133997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134027 : List Nat := [1, 1, 1, 1, 4, 2, 3, 2, 2, 4, 2]
def baseStart_134027 : Nat := 118140960795 + 134027 * 2 ^ 59
def prefixEnd_134027 : Nat := 4983230072969 + 3 ^ 40 * 134027 * 2
def baseEnd_134027 : Nat := 68820271680252352446127

theorem tailTrace_134027 : CollatzResearch.WordTrace tailWord_134027 prefixEnd_134027 68820271680252352446127 := by
  unfold tailWord_134027
  simp only [CollatzResearch.WordTrace]
  refine ⟨4888366285450543834344335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3258910856967029222896223 4888366285450543834344335)
  ·
    refine ⟨7332549428175815751516503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4888366285450543834344335 7332549428175815751516503)
    ·
      refine ⟨10998824142263723627274755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7332549428175815751516503 10998824142263723627274755)
      ·
        refine ⟨16498236213395585440912133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10998824142263723627274755 16498236213395585440912133)
        ·
          refine ⟨3093419290011672270171025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16498236213395585440912133 3093419290011672270171025)
          ·
            refine ⟨2320064467508754202628269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3093419290011672270171025 2320064467508754202628269)
            ·
              refine ⟨870024175315782825985601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2320064467508754202628269 870024175315782825985601)
              ·
                refine ⟨652518131486837119489201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 870024175315782825985601 652518131486837119489201)
                ·
                  refine ⟨489388598615127839616901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 652518131486837119489201 489388598615127839616901)
                  ·
                    refine ⟨91760362240336469928169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 489388598615127839616901 91760362240336469928169)
                    ·
                      refine ⟨68820271680252352446127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 91760362240336469928169 68820271680252352446127)
                      ·
                        rfl

theorem cell23_134027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 4, 2].length) (baseStart_134027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134027 prefixEnd_134027 := by exact prefixLift 134027
  have htrace : WordTrace (prefixWord ++ tailWord_134027) baseStart_134027 baseEnd_134027 := by
    simpa [prefixWord, tailWord_134027, baseEnd_134027] using wordTrace_append hprefix tailTrace_134027
  have hstable : (prefixWord ++ tailWord_134027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134027).length < 2 ^ (prefixWord ++ tailWord_134027).sum := by decide
  have hdescent : baseEnd_134027 < baseStart_134027 := by decide
  rcases family_descends (prefixWord ++ tailWord_134027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134037 : List Nat := [1, 3, 2, 1, 1, 4, 1, 3, 3, 4]
def baseStart_134037 : Nat := 118140960795 + 134037 * 2 ^ 59
def prefixEnd_134037 : Nat := 4983230072969 + 3 ^ 40 * 134037 * 2
def baseEnd_134037 : Nat := 22941802162265771107027

theorem tailTrace_134037 : CollatzResearch.WordTrace tailWord_134037 prefixEnd_134037 22941802162265771107027 := by
  unfold tailWord_134037
  simp only [CollatzResearch.WordTrace]
  refine ⟨4888731015414315542208365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3259154010276210361472243 4888731015414315542208365)
  ·
    refine ⟨1833274130780368328328137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4888731015414315542208365 1833274130780368328328137)
    ·
      refine ⟨1374955598085276246246103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1833274130780368328328137 1374955598085276246246103)
      ·
        refine ⟨2062433397127914369369155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1374955598085276246246103 2062433397127914369369155)
        ·
          refine ⟨3093650095691871554053733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2062433397127914369369155 3093650095691871554053733)
          ·
            refine ⟨580059392942225916385075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3093650095691871554053733 580059392942225916385075)
            ·
              refine ⟨870089089413338874577613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580059392942225916385075 870089089413338874577613)
              ·
                refine ⟨326283408530002077966605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 870089089413338874577613 326283408530002077966605)
                ·
                  refine ⟨122356278198750779237477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 326283408530002077966605 122356278198750779237477)
                  ·
                    refine ⟨22941802162265771107027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 122356278198750779237477 22941802162265771107027)
                    ·
                      rfl

theorem cell23_134037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_134037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134037 prefixEnd_134037 := by exact prefixLift 134037
  have htrace : WordTrace (prefixWord ++ tailWord_134037) baseStart_134037 baseEnd_134037 := by
    simpa [prefixWord, tailWord_134037, baseEnd_134037] using wordTrace_append hprefix tailTrace_134037
  have hstable : (prefixWord ++ tailWord_134037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134037).length < 2 ^ (prefixWord ++ tailWord_134037).sum := by decide
  have hdescent : baseEnd_134037 < baseStart_134037 := by decide
  rcases family_descends (prefixWord ++ tailWord_134037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134047 : List Nat := [1, 1, 2, 5, 2, 1, 1, 2, 1, 4, 3]
def baseStart_134047 : Nat := 118140960795 + 134047 * 2 ^ 59
def prefixEnd_134047 : Nat := 4983230072969 + 3 ^ 40 * 134047 * 2
def baseEnd_134047 : Nat := 68830541293342274196035

theorem tailTrace_134047 : CollatzResearch.WordTrace tailWord_134047 prefixEnd_134047 68830541293342274196035 := by
  unfold tailWord_134047
  simp only [CollatzResearch.WordTrace]
  refine ⟨4889095745378087250072395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3259397163585391500048263 4889095745378087250072395)
  ·
    refine ⟨7333643618067130875108593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4889095745378087250072395 7333643618067130875108593)
    ·
      refine ⟨5500232713550348156331445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7333643618067130875108593 5500232713550348156331445)
      ·
        refine ⟨515646816895345139656073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5500232713550348156331445 515646816895345139656073)
        ·
          refine ⟨386735112671508854742055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515646816895345139656073 386735112671508854742055)
          ·
            refine ⟨580102669007263282113083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386735112671508854742055 580102669007263282113083)
            ·
              refine ⟨870154003510894923169625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580102669007263282113083 870154003510894923169625)
              ·
                refine ⟨652615502633171192377219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 870154003510894923169625 652615502633171192377219)
                ·
                  refine ⟨978923253949756788565829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 652615502633171192377219 978923253949756788565829)
                  ·
                    refine ⟨183548110115579397856093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 978923253949756788565829 183548110115579397856093)
                    ·
                      refine ⟨68830541293342274196035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 183548110115579397856093 68830541293342274196035)
                      ·
                        rfl

theorem cell23_134047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_134047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134047 prefixEnd_134047 := by exact prefixLift 134047
  have htrace : WordTrace (prefixWord ++ tailWord_134047) baseStart_134047 baseEnd_134047 := by
    simpa [prefixWord, tailWord_134047, baseEnd_134047] using wordTrace_append hprefix tailTrace_134047
  have hstable : (prefixWord ++ tailWord_134047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134047).length < 2 ^ (prefixWord ++ tailWord_134047).sum := by decide
  have hdescent : baseEnd_134047 < baseStart_134047 := by decide
  rcases family_descends (prefixWord ++ tailWord_134047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134088 : List Nat := [2, 1, 3, 1, 5, 1, 3, 2, 1, 4]
def baseStart_134088 : Nat := 118140960795 + 134088 * 2 ^ 59
def prefixEnd_134088 : Nat := 4983230072969 + 3 ^ 40 * 134088 * 2
def baseEnd_134088 : Nat := 22950531333392204594449

theorem tailTrace_134088 : CollatzResearch.WordTrace tailWord_134088 prefixEnd_134088 22950531333392204594449 := by
  unfold tailWord_134088
  simp only [CollatzResearch.WordTrace]
  refine ⟨2445295569114775626157459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3260394092153034168209945 2445295569114775626157459)
  ·
    refine ⟨3667943353672163439236189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2445295569114775626157459 3667943353672163439236189)
    ·
      refine ⟨1375478757627061289713571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3667943353672163439236189 1375478757627061289713571)
      ·
        refine ⟨2063218136440591934570357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1375478757627061289713571 2063218136440591934570357)
        ·
          refine ⟨193426700291305493865971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2063218136440591934570357 193426700291305493865971)
          ·
            refine ⟨290140050436958240798957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193426700291305493865971 290140050436958240798957)
            ·
              refine ⟨108802518913859340299609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 290140050436958240798957 108802518913859340299609)
              ·
                refine ⟨81601889185394505224707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108802518913859340299609 81601889185394505224707)
                ·
                  refine ⟨122402833778091757837061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81601889185394505224707 122402833778091757837061)
                  ·
                    refine ⟨22950531333392204594449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 122402833778091757837061 22950531333392204594449)
                    ·
                      rfl

theorem cell23_134088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_134088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134088 prefixEnd_134088 := by exact prefixLift 134088
  have htrace : WordTrace (prefixWord ++ tailWord_134088) baseStart_134088 baseEnd_134088 := by
    simpa [prefixWord, tailWord_134088, baseEnd_134088] using wordTrace_append hprefix tailTrace_134088
  have hstable : (prefixWord ++ tailWord_134088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134088).length < 2 ^ (prefixWord ++ tailWord_134088).sum := by decide
  have hdescent : baseEnd_134088 < baseStart_134088 := by decide
  rcases family_descends (prefixWord ++ tailWord_134088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134090 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 2, 1, 7]
def baseStart_134090 : Nat := 118140960795 + 134090 * 2 ^ 59
def prefixEnd_134090 : Nat := 4983230072969 + 3 ^ 40 * 134090 * 2
def baseEnd_134090 : Nat := 68852620961485605958337

theorem tailTrace_134090 : CollatzResearch.WordTrace tailWord_134090 prefixEnd_134090 68852620961485605958337 := by
  unfold tailWord_134090
  simp only [CollatzResearch.WordTrace]
  refine ⟨1222666021055576398471931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3260442722814870395925149 1222666021055576398471931)
  ·
    refine ⟨1833999031583364597707897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1222666021055576398471931 1833999031583364597707897)
    ·
      refine ⟨1375499273687523448280923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1833999031583364597707897 1375499273687523448280923)
      ·
        refine ⟨2063248910531285172421385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1375499273687523448280923 2063248910531285172421385)
        ·
          refine ⟨1547436682898463879316039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2063248910531285172421385 1547436682898463879316039)
          ·
            refine ⟨2321155024347695818974059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1547436682898463879316039 2321155024347695818974059)
            ·
              refine ⟨3481732536521543728461089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2321155024347695818974059 3481732536521543728461089)
              ·
                refine ⟨2611299402391157796345817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3481732536521543728461089 2611299402391157796345817)
                ·
                  refine ⟨1958474551793368347259363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2611299402391157796345817 1958474551793368347259363)
                  ·
                    refine ⟨2937711827690052520889045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1958474551793368347259363 2937711827690052520889045)
                    ·
                      refine ⟨68852620961485605958337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 2937711827690052520889045 68852620961485605958337)
                      ·
                        rfl

theorem cell23_134090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_134090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134090 prefixEnd_134090 := by exact prefixLift 134090
  have htrace : WordTrace (prefixWord ++ tailWord_134090) baseStart_134090 baseEnd_134090 := by
    simpa [prefixWord, tailWord_134090, baseEnd_134090] using wordTrace_append hprefix tailTrace_134090
  have hstable : (prefixWord ++ tailWord_134090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134090).length < 2 ^ (prefixWord ++ tailWord_134090).sum := by decide
  have hdescent : baseEnd_134090 < baseStart_134090 := by decide
  rcases family_descends (prefixWord ++ tailWord_134090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134101 : List Nat := [1, 3, 2, 3, 3, 2, 2, 1, 6]
def baseStart_134101 : Nat := 118140960795 + 134101 * 2 ^ 59
def prefixEnd_134101 : Nat := 4983230072969 + 3 ^ 40 * 134101 * 2
def baseEnd_134101 : Nat := 7650918805409451435643

theorem tailTrace_134101 : CollatzResearch.WordTrace tailWord_134101 prefixEnd_134101 7650918805409451435643 := by
  unfold tailWord_134101
  simp only [CollatzResearch.WordTrace]
  refine ⟨4891065287182454472538157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3260710191454969648358771 4891065287182454472538157)
  ·
    refine ⟨1834149482693420427201809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4891065287182454472538157 1834149482693420427201809)
    ·
      refine ⟨1375612112020065320401357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1834149482693420427201809 1375612112020065320401357)
      ·
        refine ⟨515854542007524495150509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1375612112020065320401357 515854542007524495150509)
        ·
          refine ⟨193445453252821685681441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 515854542007524495150509 193445453252821685681441)
          ·
            refine ⟨145084089939616264261081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193445453252821685681441 145084089939616264261081)
            ·
              refine ⟨108813067454712198195811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145084089939616264261081 108813067454712198195811)
              ·
                refine ⟨163219601182068297293717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108813067454712198195811 163219601182068297293717)
                ·
                  refine ⟨7650918805409451435643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 163219601182068297293717 7650918805409451435643)
                  ·
                    rfl

theorem cell23_134101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 6].length) (baseStart_134101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134101 prefixEnd_134101 := by exact prefixLift 134101
  have htrace : WordTrace (prefixWord ++ tailWord_134101) baseStart_134101 baseEnd_134101 := by
    simpa [prefixWord, tailWord_134101, baseEnd_134101] using wordTrace_append hprefix tailTrace_134101
  have hstable : (prefixWord ++ tailWord_134101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134101).length < 2 ^ (prefixWord ++ tailWord_134101).sum := by decide
  have hdescent : baseEnd_134101 < baseStart_134101 := by decide
  rcases family_descends (prefixWord ++ tailWord_134101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134127 : List Nat := [1, 1, 2, 1, 4, 4, 1, 2, 1, 6]
def baseStart_134127 : Nat := 118140960795 + 134127 * 2 ^ 59
def prefixEnd_134127 : Nat := 4983230072969 + 3 ^ 40 * 134127 * 2
def baseEnd_134127 : Nat := 22957206581900653731889

theorem tailTrace_134127 : CollatzResearch.WordTrace tailWord_134127 prefixEnd_134127 22957206581900653731889 := by
  unfold tailWord_134127
  simp only [CollatzResearch.WordTrace]
  refine ⟨4892013585088260912984635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3261342390058840608656423 4892013585088260912984635)
  ·
    refine ⟨7338020377632391369476953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4892013585088260912984635 7338020377632391369476953)
    ·
      refine ⟨5503515283224293527107715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7338020377632391369476953 5503515283224293527107715)
      ·
        refine ⟨8255272924836440290661573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5503515283224293527107715 8255272924836440290661573)
        ·
          refine ⟨1547863673406832554499045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8255272924836440290661573 1547863673406832554499045)
          ·
            refine ⟨290224438763781103968571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1547863673406832554499045 290224438763781103968571)
            ·
              refine ⟨435336658145671655952857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290224438763781103968571 435336658145671655952857)
              ·
                refine ⟨326502493609253741964643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 435336658145671655952857 326502493609253741964643)
                ·
                  refine ⟨489753740413880612946965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 326502493609253741964643 489753740413880612946965)
                  ·
                    refine ⟨22957206581900653731889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 489753740413880612946965 22957206581900653731889)
                    ·
                      rfl

theorem cell23_134127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 6].length) (baseStart_134127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134127 prefixEnd_134127 := by exact prefixLift 134127
  have htrace : WordTrace (prefixWord ++ tailWord_134127) baseStart_134127 baseEnd_134127 := by
    simpa [prefixWord, tailWord_134127, baseEnd_134127] using wordTrace_append hprefix tailTrace_134127
  have hstable : (prefixWord ++ tailWord_134127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134127).length < 2 ^ (prefixWord ++ tailWord_134127).sum := by decide
  have hdescent : baseEnd_134127 < baseStart_134127 := by decide
  rcases family_descends (prefixWord ++ tailWord_134127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134140 : List Nat := [2, 2, 2, 1, 2, 14]
def baseStart_134140 : Nat := 118140960795 + 134140 * 2 ^ 59
def prefixEnd_134140 : Nat := 4983230072969 + 3 ^ 40 * 134140 * 2
def baseEnd_134140 : Nat := 283449773638725968449

theorem tailTrace_134140 : CollatzResearch.WordTrace tailWord_134140 prefixEnd_134140 283449773638725968449 := by
  unfold tailWord_134140
  simp only [CollatzResearch.WordTrace]
  refine ⟨2446243867020582066603937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3261658489360776088805249 2446243867020582066603937)
  ·
    refine ⟨1834682900265436549952953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2446243867020582066603937 1834682900265436549952953)
    ·
      refine ⟨1376012175199077412464715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1834682900265436549952953 1376012175199077412464715)
      ·
        refine ⟨2064018262798616118697073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1376012175199077412464715 2064018262798616118697073)
        ·
          refine ⟨1548013697098962089022805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2064018262798616118697073 1548013697098962089022805)
          ·
            refine ⟨283449773638725968449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 1548013697098962089022805 283449773638725968449)
            ·
              rfl

theorem cell23_134140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 14].length) (baseStart_134140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134140 prefixEnd_134140 := by exact prefixLift 134140
  have htrace : WordTrace (prefixWord ++ tailWord_134140) baseStart_134140 baseEnd_134140 := by
    simpa [prefixWord, tailWord_134140, baseEnd_134140] using wordTrace_append hprefix tailTrace_134140
  have hstable : (prefixWord ++ tailWord_134140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134140).length < 2 ^ (prefixWord ++ tailWord_134140).sum := by decide
  have hdescent : baseEnd_134140 < baseStart_134140 := by decide
  rcases family_descends (prefixWord ++ tailWord_134140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134145 : List Nat := [1, 2, 4, 1, 2, 4, 2, 2, 1, 1, 3]
def baseStart_134145 : Nat := 118140960795 + 134145 * 2 ^ 59
def prefixEnd_134145 : Nat := 4983230072969 + 3 ^ 40 * 134145 * 2
def baseEnd_134145 : Nat := 68880862397482890770585

theorem tailTrace_134145 : CollatzResearch.WordTrace tailWord_134145 prefixEnd_134145 68880862397482890770585 := by
  unfold tailWord_134145
  simp only [CollatzResearch.WordTrace]
  refine ⟨4892670099023049987139889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3261780066015366658093259 4892670099023049987139889)
  ·
    refine ⟨3669502574267287490354917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4892670099023049987139889 3669502574267287490354917)
    ·
      refine ⟨688031732675116404441547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3669502574267287490354917 688031732675116404441547)
      ·
        refine ⟨1032047599012674606662321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 688031732675116404441547 1032047599012674606662321)
        ·
          refine ⟨774035699259505954996741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1032047599012674606662321 774035699259505954996741)
          ·
            refine ⟨145131693611157366561889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 774035699259505954996741 145131693611157366561889)
            ·
              refine ⟨108848770208368024921417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145131693611157366561889 108848770208368024921417)
              ·
                refine ⟨81636577656276018691063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108848770208368024921417 81636577656276018691063)
                ·
                  refine ⟨122454866484414028036595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81636577656276018691063 122454866484414028036595)
                  ·
                    refine ⟨183682299726621042054893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 122454866484414028036595 183682299726621042054893)
                    ·
                      refine ⟨68880862397482890770585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 183682299726621042054893 68880862397482890770585)
                      ·
                        rfl

theorem cell23_134145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_134145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134145 prefixEnd_134145 := by exact prefixLift 134145
  have htrace : WordTrace (prefixWord ++ tailWord_134145) baseStart_134145 baseEnd_134145 := by
    simpa [prefixWord, tailWord_134145, baseEnd_134145] using wordTrace_append hprefix tailTrace_134145
  have hstable : (prefixWord ++ tailWord_134145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134145).length < 2 ^ (prefixWord ++ tailWord_134145).sum := by decide
  have hdescent : baseEnd_134145 < baseStart_134145 := by decide
  rcases family_descends (prefixWord ++ tailWord_134145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134151 : List Nat := [1, 1, 4, 3, 1, 1, 2, 3, 3, 2, 2]
def baseStart_134151 : Nat := 118140960795 + 134151 * 2 ^ 59
def prefixEnd_134151 : Nat := 4983230072969 + 3 ^ 40 * 134151 * 2
def baseEnd_134151 : Nat := 68883943281409867295557

theorem tailTrace_134151 : CollatzResearch.WordTrace tailWord_134151 prefixEnd_134151 68883943281409867295557 := by
  unfold tailWord_134151
  simp only [CollatzResearch.WordTrace]
  refine ⟨4892888937001313011858307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3261925958000875341238871 4892888937001313011858307)
  ·
    refine ⟨7339333405501969517787461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4892888937001313011858307 7339333405501969517787461)
    ·
      refine ⟨1376125013531619284585149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7339333405501969517787461 1376125013531619284585149)
      ·
        refine ⟨516046880074357231719431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1376125013531619284585149 516046880074357231719431)
        ·
          refine ⟨774070320111535847579147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516046880074357231719431 774070320111535847579147)
          ·
            refine ⟨1161105480167303771368721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 774070320111535847579147 1161105480167303771368721)
            ·
              refine ⟨870829110125477828526541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1161105480167303771368721 870829110125477828526541)
              ·
                refine ⟨326560916297054185697453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 870829110125477828526541 326560916297054185697453)
                ·
                  refine ⟨122460343611395319636545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 326560916297054185697453 122460343611395319636545)
                  ·
                    refine ⟨91845257708546489727409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 122460343611395319636545 91845257708546489727409)
                    ·
                      refine ⟨68883943281409867295557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 91845257708546489727409 68883943281409867295557)
                      ·
                        rfl

theorem cell23_134151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_134151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134151 prefixEnd_134151 := by exact prefixLift 134151
  have htrace : WordTrace (prefixWord ++ tailWord_134151) baseStart_134151 baseEnd_134151 := by
    simpa [prefixWord, tailWord_134151, baseEnd_134151] using wordTrace_append hprefix tailTrace_134151
  have hstable : (prefixWord ++ tailWord_134151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134151).length < 2 ^ (prefixWord ++ tailWord_134151).sum := by decide
  have hdescent : baseEnd_134151 < baseStart_134151 := by decide
  rcases family_descends (prefixWord ++ tailWord_134151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134154 : List Nat := [3, 1, 2, 2, 3, 1, 1, 2, 3, 2, 3]
def baseStart_134154 : Nat := 118140960795 + 134154 * 2 ^ 59
def prefixEnd_134154 : Nat := 4983230072969 + 3 ^ 40 * 134154 * 2
def baseEnd_134154 : Nat := 68885483723373355558043

theorem tailTrace_134154 : CollatzResearch.WordTrace tailWord_134154 prefixEnd_134154 68885483723373355558043 := by
  unfold tailWord_134154
  simp only [CollatzResearch.WordTrace]
  refine ⟨1223249588997611131054379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3261998903993629682811677 1223249588997611131054379)
  ·
    refine ⟨1834874383496416696581569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1223249588997611131054379 1834874383496416696581569)
    ·
      refine ⟨1376155787622312522436177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1834874383496416696581569 1376155787622312522436177)
      ·
        refine ⟨1032116840716734391827133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1376155787622312522436177 1032116840716734391827133)
        ·
          refine ⟨387043815268775396935175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1032116840716734391827133 387043815268775396935175)
          ·
            refine ⟨580565722903163095402763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387043815268775396935175 580565722903163095402763)
            ·
              refine ⟨870848584354744643104145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580565722903163095402763 870848584354744643104145)
              ·
                refine ⟨653136438266058482328109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 870848584354744643104145 653136438266058482328109)
                ·
                  refine ⟨244926164349771930873041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 653136438266058482328109 244926164349771930873041)
                  ·
                    refine ⟨183694623262328948154781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 244926164349771930873041 183694623262328948154781)
                    ·
                      refine ⟨68885483723373355558043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 183694623262328948154781 68885483723373355558043)
                      ·
                        rfl

theorem cell23_134154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_134154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134154 prefixEnd_134154 := by exact prefixLift 134154
  have htrace : WordTrace (prefixWord ++ tailWord_134154) baseStart_134154 baseEnd_134154 := by
    simpa [prefixWord, tailWord_134154, baseEnd_134154] using wordTrace_append hprefix tailTrace_134154
  have hstable : (prefixWord ++ tailWord_134154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134154).length < 2 ^ (prefixWord ++ tailWord_134154).sum := by decide
  have hdescent : baseEnd_134154 < baseStart_134154 := by decide
  rcases family_descends (prefixWord ++ tailWord_134154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134201 : List Nat := [1, 2, 1, 5, 2, 2, 1, 1, 4, 1, 3]
def baseStart_134201 : Nat := 118140960795 + 134201 * 2 ^ 59
def prefixEnd_134201 : Nat := 4983230072969 + 3 ^ 40 * 134201 * 2
def baseEnd_134201 : Nat := 68909617314134671670327

theorem tailTrace_134201 : CollatzResearch.WordTrace tailWord_134201 prefixEnd_134201 68909617314134671670327 := by
  unfold tailWord_134201
  simp only [CollatzResearch.WordTrace]
  refine ⟨4894712586820171551178457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3263141724546781034118971 4894712586820171551178457)
  ·
    refine ⟨3671034440115128663383843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4894712586820171551178457 3671034440115128663383843)
    ·
      refine ⟨5506551660172692995075765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3671034440115128663383843 5506551660172692995075765)
      ·
        refine ⟨516239218141189968288353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5506551660172692995075765 516239218141189968288353)
        ·
          refine ⟨387179413605892476216265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 516239218141189968288353 387179413605892476216265)
          ·
            refine ⟨290384560204419357162199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387179413605892476216265 290384560204419357162199)
            ·
              refine ⟨435576840306629035743299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290384560204419357162199 435576840306629035743299)
              ·
                refine ⟨653365260459943553614949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 435576840306629035743299 653365260459943553614949)
                ·
                  refine ⟨122505986336239416302803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 653365260459943553614949 122505986336239416302803)
                  ·
                    refine ⟨183758979504359124454205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 122505986336239416302803 183758979504359124454205)
                    ·
                      refine ⟨68909617314134671670327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 183758979504359124454205 68909617314134671670327)
                      ·
                        rfl

theorem cell23_134201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_134201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134201 prefixEnd_134201 := by exact prefixLift 134201
  have htrace : WordTrace (prefixWord ++ tailWord_134201) baseStart_134201 baseEnd_134201 := by
    simpa [prefixWord, tailWord_134201, baseEnd_134201] using wordTrace_append hprefix tailTrace_134201
  have hstable : (prefixWord ++ tailWord_134201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134201).length < 2 ^ (prefixWord ++ tailWord_134201).sum := by decide
  have hdescent : baseEnd_134201 < baseStart_134201 := by decide
  rcases family_descends (prefixWord ++ tailWord_134201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134227 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 4, 4, 3]
def baseStart_134227 : Nat := 118140960795 + 134227 * 2 ^ 59
def prefixEnd_134227 : Nat := 4983230072969 + 3 ^ 40 * 134227 * 2
def baseEnd_134227 : Nat := 68922967811151569945207

theorem tailTrace_134227 : CollatzResearch.WordTrace tailWord_134227 prefixEnd_134227 68922967811151569945207 := by
  unfold tailWord_134227
  simp only [CollatzResearch.WordTrace]
  refine ⟨4895660884725977991624935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3263773923150651994416623 4895660884725977991624935)
  ·
    refine ⟨7343491327088966987437403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4895660884725977991624935 7343491327088966987437403)
    ·
      refine ⟨11015236990633450481156105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7343491327088966987437403 11015236990633450481156105)
      ·
        refine ⟨8261427742975087860867079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11015236990633450481156105 8261427742975087860867079)
        ·
          refine ⟨12392141614462631791300619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8261427742975087860867079 12392141614462631791300619)
          ·
            refine ⟨18588212421693947686950929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12392141614462631791300619 18588212421693947686950929)
            ·
              refine ⟨13941159316270460765213197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18588212421693947686950929 13941159316270460765213197)
              ·
                refine ⟨5227934743601422786954949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13941159316270460765213197 5227934743601422786954949)
                ·
                  refine ⟨980237764425266772554053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5227934743601422786954949 980237764425266772554053)
                  ·
                    refine ⟨183794580829737519853885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 980237764425266772554053 183794580829737519853885)
                    ·
                      refine ⟨68922967811151569945207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 183794580829737519853885 68922967811151569945207)
                      ·
                        rfl

theorem cell23_134227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4, 3].length) (baseStart_134227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134227 prefixEnd_134227 := by exact prefixLift 134227
  have htrace : WordTrace (prefixWord ++ tailWord_134227) baseStart_134227 baseEnd_134227 := by
    simpa [prefixWord, tailWord_134227, baseEnd_134227] using wordTrace_append hprefix tailTrace_134227
  have hstable : (prefixWord ++ tailWord_134227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134227).length < 2 ^ (prefixWord ++ tailWord_134227).sum := by decide
  have hdescent : baseEnd_134227 < baseStart_134227 := by decide
  rcases family_descends (prefixWord ++ tailWord_134227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134241 : List Nat := [1, 2, 3, 1, 1, 2, 3, 2, 4, 2, 2]
def baseStart_134241 : Nat := 118140960795 + 134241 * 2 ^ 59
def prefixEnd_134241 : Nat := 4983230072969 + 3 ^ 40 * 134241 * 2
def baseEnd_134241 : Nat := 68930156540314515170143

theorem tailTrace_134241 : CollatzResearch.WordTrace tailWord_134241 prefixEnd_134241 68930156540314515170143 := by
  unfold tailWord_134241
  simp only [CollatzResearch.WordTrace]
  refine ⟨4896171506675258382634577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3264114337783505588423051 4896171506675258382634577)
  ·
    refine ⟨3672128630006443786975933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4896171506675258382634577 3672128630006443786975933)
    ·
      refine ⟨1377048236252416420115975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3672128630006443786975933 1377048236252416420115975)
      ·
        refine ⟨2065572354378624630173963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1377048236252416420115975 2065572354378624630173963)
        ·
          refine ⟨3098358531567936945260945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2065572354378624630173963 3098358531567936945260945)
          ·
            refine ⟨2323768898675952708945709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3098358531567936945260945 2323768898675952708945709)
            ·
              refine ⟨871413337003482265854641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2323768898675952708945709 871413337003482265854641)
              ·
                refine ⟨653560002752611699390981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 871413337003482265854641 653560002752611699390981)
                ·
                  refine ⟨122542500516114693635809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 653560002752611699390981 122542500516114693635809)
                  ·
                    refine ⟨91906875387086020226857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 122542500516114693635809 91906875387086020226857)
                    ·
                      refine ⟨68930156540314515170143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 91906875387086020226857 68930156540314515170143)
                      ·
                        rfl

theorem cell23_134241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4, 2, 2].length) (baseStart_134241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134241 prefixEnd_134241 := by exact prefixLift 134241
  have htrace : WordTrace (prefixWord ++ tailWord_134241) baseStart_134241 baseEnd_134241 := by
    simpa [prefixWord, tailWord_134241, baseEnd_134241] using wordTrace_append hprefix tailTrace_134241
  have hstable : (prefixWord ++ tailWord_134241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134241).length < 2 ^ (prefixWord ++ tailWord_134241).sum := by decide
  have hdescent : baseEnd_134241 < baseStart_134241 := by decide
  rcases family_descends (prefixWord ++ tailWord_134241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134258 : List Nat := [3, 2, 1, 2, 2, 1, 2, 4, 2, 2, 2]
def baseStart_134258 : Nat := 118140960795 + 134258 * 2 ^ 59
def prefixEnd_134258 : Nat := 4983230072969 + 3 ^ 40 * 134258 * 2
def baseEnd_134258 : Nat := 68938885711440948657565

theorem tailTrace_134258 : CollatzResearch.WordTrace tailWord_134258 prefixEnd_134258 68938885711440948657565 := by
  unfold tailWord_134258
  simp only [CollatzResearch.WordTrace]
  refine ⟨1224197886903417571500857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3264527698409113524002285 1224197886903417571500857)
  ·
    refine ⟨918148415177563178625643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1224197886903417571500857 918148415177563178625643)
    ·
      refine ⟨1377222622766344767938465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 918148415177563178625643 1377222622766344767938465)
      ·
        refine ⟨1032916967074758575953849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1377222622766344767938465 1032916967074758575953849)
        ·
          refine ⟨774687725306068931965387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1032916967074758575953849 774687725306068931965387)
          ·
            refine ⟨1162031587959103397948081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 774687725306068931965387 1162031587959103397948081)
            ·
              refine ⟨871523690969327548461061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1162031587959103397948081 871523690969327548461061)
              ·
                refine ⟨163410692056748915336449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 871523690969327548461061 163410692056748915336449)
                ·
                  refine ⟨122558019042561686502337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163410692056748915336449 122558019042561686502337)
                  ·
                    refine ⟨91918514281921264876753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 122558019042561686502337 91918514281921264876753)
                    ·
                      refine ⟨68938885711440948657565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 91918514281921264876753 68938885711440948657565)
                      ·
                        rfl

theorem cell23_134258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_134258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134258 prefixEnd_134258 := by exact prefixLift 134258
  have htrace : WordTrace (prefixWord ++ tailWord_134258) baseStart_134258 baseEnd_134258 := by
    simpa [prefixWord, tailWord_134258, baseEnd_134258] using wordTrace_append hprefix tailTrace_134258
  have hstable : (prefixWord ++ tailWord_134258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134258).length < 2 ^ (prefixWord ++ tailWord_134258).sum := by decide
  have hdescent : baseEnd_134258 < baseStart_134258 := by decide
  rcases family_descends (prefixWord ++ tailWord_134258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134264 : List Nat := [2, 1, 2, 1, 1, 1, 4, 6, 5]
def baseStart_134264 : Nat := 118140960795 + 134264 * 2 ^ 59
def prefixEnd_134264 : Nat := 4983230072969 + 3 ^ 40 * 134264 * 2
def baseEnd_134264 : Nat := 7660218510596436131393

theorem tailTrace_134264 : CollatzResearch.WordTrace tailWord_134264 prefixEnd_134264 7660218510596436131393 := by
  unfold tailWord_134264
  simp only [CollatzResearch.WordTrace]
  refine ⟨2448505192795966655360923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3264673590394622207147897 2448505192795966655360923)
  ·
    refine ⟨3672757789193949983041385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2448505192795966655360923 3672757789193949983041385)
    ·
      refine ⟨2754568341895462487281039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3672757789193949983041385 2754568341895462487281039)
      ·
        refine ⟨4131852512843193730921559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2754568341895462487281039 4131852512843193730921559)
        ·
          refine ⟨6197778769264790596382339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4131852512843193730921559 6197778769264790596382339)
          ·
            refine ⟨9296668153897185894573509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6197778769264790596382339 9296668153897185894573509)
            ·
              refine ⟨1743125278855722355232533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9296668153897185894573509 1743125278855722355232533)
              ·
                refine ⟨81708997446361985401525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1743125278855722355232533 81708997446361985401525)
                ·
                  refine ⟨7660218510596436131393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81708997446361985401525 7660218510596436131393)
                  ·
                    rfl

theorem cell23_134264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6, 5].length) (baseStart_134264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134264 prefixEnd_134264 := by exact prefixLift 134264
  have htrace : WordTrace (prefixWord ++ tailWord_134264) baseStart_134264 baseEnd_134264 := by
    simpa [prefixWord, tailWord_134264, baseEnd_134264] using wordTrace_append hprefix tailTrace_134264
  have hstable : (prefixWord ++ tailWord_134264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134264).length < 2 ^ (prefixWord ++ tailWord_134264).sum := by decide
  have hdescent : baseEnd_134264 < baseStart_134264 := by decide
  rcases family_descends (prefixWord ++ tailWord_134264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134311 : List Nat := [1, 1, 6, 2, 1, 1, 2, 2, 2, 5]
def baseStart_134311 : Nat := 118140960795 + 134311 * 2 ^ 59
def prefixEnd_134311 : Nat := 4983230072969 + 3 ^ 40 * 134311 * 2
def baseEnd_134311 : Nat := 22988700062043080431607

theorem tailTrace_134311 : CollatzResearch.WordTrace tailWord_134311 prefixEnd_134311 22988700062043080431607 := by
  unfold tailWord_134311
  simp only [CollatzResearch.WordTrace]
  refine ⟨4898724616421660337682787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3265816410947773558455191 4898724616421660337682787)
  ·
    refine ⟨7348086924632490506524181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4898724616421660337682787 7348086924632490506524181)
    ·
      refine ⟨344441574592147992493321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7348086924632490506524181 344441574592147992493321)
      ·
        refine ⟨258331180944110994369991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344441574592147992493321 258331180944110994369991)
        ·
          refine ⟨387496771416166491554987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258331180944110994369991 387496771416166491554987)
          ·
            refine ⟨581245157124249737332481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387496771416166491554987 581245157124249737332481)
            ·
              refine ⟨435933867843187302999361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 581245157124249737332481 435933867843187302999361)
              ·
                refine ⟨326950400882390477249521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 435933867843187302999361 326950400882390477249521)
                ·
                  refine ⟨245212800661792857937141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 326950400882390477249521 245212800661792857937141)
                  ·
                    refine ⟨22988700062043080431607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 245212800661792857937141 22988700062043080431607)
                    ·
                      rfl

theorem cell23_134311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_134311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134311 prefixEnd_134311 := by exact prefixLift 134311
  have htrace : WordTrace (prefixWord ++ tailWord_134311) baseStart_134311 baseEnd_134311 := by
    simpa [prefixWord, tailWord_134311, baseEnd_134311] using wordTrace_append hprefix tailTrace_134311
  have hstable : (prefixWord ++ tailWord_134311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134311).length < 2 ^ (prefixWord ++ tailWord_134311).sum := by decide
  have hdescent : baseEnd_134311 < baseStart_134311 := by decide
  rcases family_descends (prefixWord ++ tailWord_134311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134354 : List Nat := [3, 2, 2, 2, 1, 1, 2, 2, 8]
def baseStart_134354 : Nat := 118140960795 + 134354 * 2 ^ 59
def prefixEnd_134354 : Nat := 4983230072969 + 3 ^ 40 * 134354 * 2
def baseEnd_134354 : Nat := 7665353317141397006347

theorem tailTrace_134354 : CollatzResearch.WordTrace tailWord_134354 prefixEnd_134354 7665353317141397006347 := by
  unfold tailWord_134354
  simp only [CollatzResearch.WordTrace]
  refine ⟨1225073238816469670374529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3266861970177252454332077 1225073238816469670374529)
  ·
    refine ⟨918804929112352252780897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1225073238816469670374529 918804929112352252780897)
    ·
      refine ⟨689103696834264189585673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 918804929112352252780897 689103696834264189585673)
      ·
        refine ⟨516827772625698142189255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 689103696834264189585673 516827772625698142189255)
        ·
          refine ⟨775241658938547213283883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516827772625698142189255 775241658938547213283883)
          ·
            refine ⟨1162862488407820819925825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 775241658938547213283883 1162862488407820819925825)
            ·
              refine ⟨872146866305865614944369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1162862488407820819925825 872146866305865614944369)
              ·
                refine ⟨654110149729399211208277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 872146866305865614944369 654110149729399211208277)
                ·
                  refine ⟨7665353317141397006347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 654110149729399211208277 7665353317141397006347)
                  ·
                    rfl

theorem cell23_134354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_134354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134354 prefixEnd_134354 := by exact prefixLift 134354
  have htrace : WordTrace (prefixWord ++ tailWord_134354) baseStart_134354 baseEnd_134354 := by
    simpa [prefixWord, tailWord_134354, baseEnd_134354] using wordTrace_append hprefix tailTrace_134354
  have hstable : (prefixWord ++ tailWord_134354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134354).length < 2 ^ (prefixWord ++ tailWord_134354).sum := by decide
  have hdescent : baseEnd_134354 < baseStart_134354 := by decide
  rcases family_descends (prefixWord ++ tailWord_134354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134391 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 4, 3, 2]
def baseStart_134391 : Nat := 118140960795 + 134391 * 2 ^ 59
def prefixEnd_134391 : Nat := 4983230072969 + 3 ^ 40 * 134391 * 2
def baseEnd_134391 : Nat := 69007178638488928294453

theorem tailTrace_134391 : CollatzResearch.WordTrace tailWord_134391 prefixEnd_134391 69007178638488928294453 := by
  unfold tailWord_134391
  simp only [CollatzResearch.WordTrace]
  refine ⟨4901642456131834000595027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3267761637421222667063351 4901642456131834000595027)
  ·
    refine ⟨7352463684197751000892541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4901642456131834000595027 7352463684197751000892541)
    ·
      refine ⟨2757173881574156625334703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7352463684197751000892541 2757173881574156625334703)
      ·
        refine ⟨4135760822361234938002055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2757173881574156625334703 4135760822361234938002055)
        ·
          refine ⟨6203641233541852407003083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4135760822361234938002055 6203641233541852407003083)
          ·
            refine ⟨9305461850312778610504625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6203641233541852407003083 9305461850312778610504625)
            ·
              refine ⟨6979096387734583957878469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9305461850312778610504625 6979096387734583957878469)
              ·
                refine ⟨1308580572700234492102213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6979096387734583957878469 1308580572700234492102213)
                ·
                  refine ⟨245358857381293967269165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1308580572700234492102213 245358857381293967269165)
                  ·
                    refine ⟨92009571517985237725937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 245358857381293967269165 92009571517985237725937)
                    ·
                      refine ⟨69007178638488928294453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 92009571517985237725937 69007178638488928294453)
                      ·
                        rfl

theorem cell23_134391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 3, 2].length) (baseStart_134391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134391 prefixEnd_134391 := by exact prefixLift 134391
  have htrace : WordTrace (prefixWord ++ tailWord_134391) baseStart_134391 baseEnd_134391 := by
    simpa [prefixWord, tailWord_134391, baseEnd_134391] using wordTrace_append hprefix tailTrace_134391
  have hstable : (prefixWord ++ tailWord_134391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134391).length < 2 ^ (prefixWord ++ tailWord_134391).sum := by decide
  have hdescent : baseEnd_134391 < baseStart_134391 := by decide
  rcases family_descends (prefixWord ++ tailWord_134391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134401 : List Nat := [1, 2, 4, 1, 1, 3, 1, 4, 1, 5]
def baseStart_134401 : Nat := 118140960795 + 134401 * 2 ^ 59
def prefixEnd_134401 : Nat := 4983230072969 + 3 ^ 40 * 134401 * 2
def baseEnd_134401 : Nat := 23004104481677963056469

theorem tailTrace_134401 : CollatzResearch.WordTrace tailWord_134401 prefixEnd_134401 23004104481677963056469 := by
  unfold tailWord_134401
  simp only [CollatzResearch.WordTrace]
  refine ⟨4902007186095605708459057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3268004790730403805639371 4902007186095605708459057)
  ·
    refine ⟨3676505389571704281344293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4902007186095605708459057 3676505389571704281344293)
    ·
      refine ⟨689344760544694552752055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3676505389571704281344293 689344760544694552752055)
      ·
        refine ⟨1034017140817041829128083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 689344760544694552752055 1034017140817041829128083)
        ·
          refine ⟨1551025711225562743692125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1034017140817041829128083 1551025711225562743692125)
          ·
            refine ⟨581634641709586028884547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1551025711225562743692125 581634641709586028884547)
            ·
              refine ⟨872451962564379043326821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581634641709586028884547 872451962564379043326821)
              ·
                refine ⟨163584742980821070623779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 872451962564379043326821 163584742980821070623779)
                ·
                  refine ⟨245377114471231605935669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163584742980821070623779 245377114471231605935669)
                  ·
                    refine ⟨23004104481677963056469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 245377114471231605935669 23004104481677963056469)
                    ·
                      rfl

theorem cell23_134401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_134401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134401 prefixEnd_134401 := by exact prefixLift 134401
  have htrace : WordTrace (prefixWord ++ tailWord_134401) baseStart_134401 baseEnd_134401 := by
    simpa [prefixWord, tailWord_134401, baseEnd_134401] using wordTrace_append hprefix tailTrace_134401
  have hstable : (prefixWord ++ tailWord_134401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134401).length < 2 ^ (prefixWord ++ tailWord_134401).sum := by decide
  have hdescent : baseEnd_134401 < baseStart_134401 := by decide
  rcases family_descends (prefixWord ++ tailWord_134401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134432 : List Nat := [2, 1, 1, 5, 4, 1, 1, 1, 3, 1, 3]
def baseStart_134432 : Nat := 118140960795 + 134432 * 2 ^ 59
def prefixEnd_134432 : Nat := 4983230072969 + 3 ^ 40 * 134432 * 2
def baseEnd_134432 : Nat := 69028231345323267881765

theorem tailTrace_134432 : CollatzResearch.WordTrace tailWord_134432 prefixEnd_134432 69028231345323267881765 := by
  unfold tailWord_134432
  simp only [CollatzResearch.WordTrace]
  refine ⟨2451568924491649001418775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3268758565988865335225033 2451568924491649001418775)
  ·
    refine ⟨3677353386737473502128163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2451568924491649001418775 3677353386737473502128163)
    ·
      refine ⟨5516030080106210253192245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3677353386737473502128163 5516030080106210253192245)
      ·
        refine ⟨517127820009957211236773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5516030080106210253192245 517127820009957211236773)
        ·
          refine ⟨96961466251866977106895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 517127820009957211236773 96961466251866977106895)
          ·
            refine ⟨145442199377800465660343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96961466251866977106895 145442199377800465660343)
            ·
              refine ⟨218163299066700698490515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145442199377800465660343 218163299066700698490515)
              ·
                refine ⟨327244948600051047735773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218163299066700698490515 327244948600051047735773)
                ·
                  refine ⟨122716855725019142900915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 327244948600051047735773 122716855725019142900915)
                  ·
                    refine ⟨184075283587528714351373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 122716855725019142900915 184075283587528714351373)
                    ·
                      refine ⟨69028231345323267881765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 184075283587528714351373 69028231345323267881765)
                      ·
                        rfl

theorem cell23_134432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_134432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134432 prefixEnd_134432 := by exact prefixLift 134432
  have htrace : WordTrace (prefixWord ++ tailWord_134432) baseStart_134432 baseEnd_134432 := by
    simpa [prefixWord, tailWord_134432, baseEnd_134432] using wordTrace_append hprefix tailTrace_134432
  have hstable : (prefixWord ++ tailWord_134432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134432).length < 2 ^ (prefixWord ++ tailWord_134432).sum := by decide
  have hdescent : baseEnd_134432 < baseStart_134432 := by decide
  rcases family_descends (prefixWord ++ tailWord_134432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134468 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_134468 : Nat := 118140960795 + 134468 * 2 ^ 59
def prefixEnd_134468 : Nat := 4983230072969 + 3 ^ 40 * 134468 * 2
def baseEnd_134468 : Nat := 69046716648885127031599

theorem tailTrace_134468 : CollatzResearch.WordTrace tailWord_134468 prefixEnd_134468 69046716648885127031599 := by
  unfold tailWord_134468
  simp only [CollatzResearch.WordTrace]
  refine ⟨2452225438426438075574029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3269633917901917434098705 2452225438426438075574029)
  ·
    refine ⟨919584539409914278340261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2452225438426438075574029 919584539409914278340261)
    ·
      refine ⟨172422101139358927188799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 919584539409914278340261 172422101139358927188799)
      ·
        refine ⟨258633151709038390783199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172422101139358927188799 258633151709038390783199)
        ·
          refine ⟨387949727563557586174799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258633151709038390783199 387949727563557586174799)
          ·
            refine ⟨581924591345336379262199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387949727563557586174799 581924591345336379262199)
            ·
              refine ⟨872886887018004568893299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581924591345336379262199 872886887018004568893299)
              ·
                refine ⟨1309330330527006853339949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 872886887018004568893299 1309330330527006853339949)
                ·
                  refine ⟨490998873947627570002481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1309330330527006853339949 490998873947627570002481)
                  ·
                    refine ⟨368249155460720677501861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 490998873947627570002481 368249155460720677501861)
                    ·
                      refine ⟨69046716648885127031599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 368249155460720677501861 69046716648885127031599)
                      ·
                        rfl

theorem cell23_134468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_134468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134468 prefixEnd_134468 := by exact prefixLift 134468
  have htrace : WordTrace (prefixWord ++ tailWord_134468) baseStart_134468 baseEnd_134468 := by
    simpa [prefixWord, tailWord_134468, baseEnd_134468] using wordTrace_append hprefix tailTrace_134468
  have hstable : (prefixWord ++ tailWord_134468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134468).length < 2 ^ (prefixWord ++ tailWord_134468).sum := by decide
  have hdescent : baseEnd_134468 < baseStart_134468 := by decide
  rcases family_descends (prefixWord ++ tailWord_134468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134471 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 3, 3, 3]
def baseStart_134471 : Nat := 118140960795 + 134471 * 2 ^ 59
def prefixEnd_134471 : Nat := 4983230072969 + 3 ^ 40 * 134471 * 2
def baseEnd_134471 : Nat := 69048257090848615294085

theorem tailTrace_134471 : CollatzResearch.WordTrace tailWord_134471 prefixEnd_134471 69048257090848615294085 := by
  unfold tailWord_134471
  simp only [CollatzResearch.WordTrace]
  refine ⟨4904560295842007663507267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3269706863894671775671511 4904560295842007663507267)
  ·
    refine ⟨7356840443763011495260901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4904560295842007663507267 7356840443763011495260901)
    ·
      refine ⟨1379407583205564655361419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7356840443763011495260901 1379407583205564655361419)
      ·
        refine ⟨2069111374808346983042129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1379407583205564655361419 2069111374808346983042129)
        ·
          refine ⟨1551833531106260237281597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2069111374808346983042129 1551833531106260237281597)
          ·
            refine ⟨581937574164847588980599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1551833531106260237281597 581937574164847588980599)
            ·
              refine ⟨872906361247271383470899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581937574164847588980599 872906361247271383470899)
              ·
                refine ⟨1309359541870907075206349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 872906361247271383470899 1309359541870907075206349)
                ·
                  refine ⟨491009828201590153202381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1309359541870907075206349 491009828201590153202381)
                  ·
                    refine ⟨184128685575596307450893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 491009828201590153202381 184128685575596307450893)
                    ·
                      refine ⟨69048257090848615294085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 184128685575596307450893 69048257090848615294085)
                      ·
                        rfl

theorem cell23_134471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_134471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134471 prefixEnd_134471 := by exact prefixLift 134471
  have htrace : WordTrace (prefixWord ++ tailWord_134471) baseStart_134471 baseEnd_134471 := by
    simpa [prefixWord, tailWord_134471, baseEnd_134471] using wordTrace_append hprefix tailTrace_134471
  have hstable : (prefixWord ++ tailWord_134471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134471).length < 2 ^ (prefixWord ++ tailWord_134471).sum := by decide
  have hdescent : baseEnd_134471 < baseStart_134471 := by decide
  rcases family_descends (prefixWord ++ tailWord_134471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134474 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 4, 7]
def baseStart_134474 : Nat := 118140960795 + 134474 * 2 ^ 59
def prefixEnd_134474 : Nat := 4983230072969 + 3 ^ 40 * 134474 * 2
def baseEnd_134474 : Nat := 23016599177604034518857

theorem tailTrace_134474 : CollatzResearch.WordTrace tailWord_134474 prefixEnd_134474 23016599177604034518857 := by
  unfold tailWord_134474
  simp only [CollatzResearch.WordTrace]
  refine ⟨1226167428707784793966619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3269779809887426117244317 1226167428707784793966619)
  ·
    refine ⟨1839251143061677190949929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1226167428707784793966619 1839251143061677190949929)
    ·
      refine ⟨1379438357296257893212447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1839251143061677190949929 1379438357296257893212447)
      ·
        refine ⟨2069157535944386839818671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1379438357296257893212447 2069157535944386839818671)
        ·
          refine ⟨3103736303916580259728007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2069157535944386839818671 3103736303916580259728007)
          ·
            refine ⟨4655604455874870389592011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3103736303916580259728007 4655604455874870389592011)
            ·
              refine ⟨6983406683812305584388017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4655604455874870389592011 6983406683812305584388017)
              ·
                refine ⟨5237555012859229188291013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6983406683812305584388017 5237555012859229188291013)
                ·
                  refine ⟨982041564911105472804565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5237555012859229188291013 982041564911105472804565)
                  ·
                    refine ⟨23016599177604034518857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 982041564911105472804565 23016599177604034518857)
                    ·
                      rfl

theorem cell23_134474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_134474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134474 prefixEnd_134474 := by exact prefixLift 134474
  have htrace : WordTrace (prefixWord ++ tailWord_134474) baseStart_134474 baseEnd_134474 := by
    simpa [prefixWord, tailWord_134474, baseEnd_134474] using wordTrace_append hprefix tailTrace_134474
  have hstable : (prefixWord ++ tailWord_134474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134474).length < 2 ^ (prefixWord ++ tailWord_134474).sum := by decide
  have hdescent : baseEnd_134474 < baseStart_134474 := by decide
  rcases family_descends (prefixWord ++ tailWord_134474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134526 : List Nat := [4, 2, 3, 2, 1, 2, 2, 1, 1, 2, 3]
def baseStart_134526 : Nat := 118140960795 + 134526 * 2 ^ 59
def prefixEnd_134526 : Nat := 4983230072969 + 3 ^ 40 * 134526 * 2
def baseEnd_134526 : Nat := 69076498526845900106333

theorem tailTrace_134526 : CollatzResearch.WordTrace tailWord_134526 prefixEnd_134526 69076498526845900106333 := by
  unfold tailWord_134526
  simp only [CollatzResearch.WordTrace]
  refine ⟨613320788830344007094929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3271044207095168037839621 613320788830344007094929)
  ·
    refine ⟨459990591622758005321197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 613320788830344007094929 459990591622758005321197)
    ·
      refine ⟨172496471858534251995449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 459990591622758005321197 172496471858534251995449)
      ·
        refine ⟨129372353893900688996587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172496471858534251995449 129372353893900688996587)
        ·
          refine ⟨194058530840851033494881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129372353893900688996587 194058530840851033494881)
          ·
            refine ⟨145543898130638275121161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194058530840851033494881 145543898130638275121161)
            ·
              refine ⟨109157923597978706340871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145543898130638275121161 109157923597978706340871)
              ·
                refine ⟨163736885396968059511307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109157923597978706340871 163736885396968059511307)
                ·
                  refine ⟨245605328095452089266961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163736885396968059511307 245605328095452089266961)
                  ·
                    refine ⟨184203996071589066950221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 245605328095452089266961 184203996071589066950221)
                    ·
                      refine ⟨69076498526845900106333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 184203996071589066950221 69076498526845900106333)
                      ·
                        rfl

theorem cell23_134526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_134526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134526 prefixEnd_134526 := by exact prefixLift 134526
  have htrace : WordTrace (prefixWord ++ tailWord_134526) baseStart_134526 baseEnd_134526 := by
    simpa [prefixWord, tailWord_134526, baseEnd_134526] using wordTrace_append hprefix tailTrace_134526
  have hstable : (prefixWord ++ tailWord_134526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134526).length < 2 ^ (prefixWord ++ tailWord_134526).sum := by decide
  have hdescent : baseEnd_134526 < baseStart_134526 := by decide
  rcases family_descends (prefixWord ++ tailWord_134526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134532 : List Nat := [2, 3, 2, 1, 1, 3, 4, 1, 1, 3, 2]
def baseStart_134532 : Nat := 118140960795 + 134532 * 2 ^ 59
def prefixEnd_134532 : Nat := 4983230072969 + 3 ^ 40 * 134532 * 2
def baseEnd_134532 : Nat := 69079579410772876631305

theorem tailTrace_134532 : CollatzResearch.WordTrace tailWord_134532 prefixEnd_134532 69079579410772876631305 := by
  unfold tailWord_134532
  simp only [CollatzResearch.WordTrace]
  refine ⟨2453392574310507540738925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3271190099080676720985233 2453392574310507540738925)
  ·
    refine ⟨920022215366440327777097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2453392574310507540738925 920022215366440327777097)
    ·
      refine ⟨690016661524830245832823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 920022215366440327777097 690016661524830245832823)
      ·
        refine ⟨1035024992287245368749235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 690016661524830245832823 1035024992287245368749235)
        ·
          refine ⟨1552537488430868053123853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1035024992287245368749235 1552537488430868053123853)
          ·
            refine ⟨582201558161575519921445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1552537488430868053123853 582201558161575519921445)
            ·
              refine ⟨109162792155295409985271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 582201558161575519921445 109162792155295409985271)
              ·
                refine ⟨163744188232943114977907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109162792155295409985271 163744188232943114977907)
                ·
                  refine ⟨245616282349414672466861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163744188232943114977907 245616282349414672466861)
                  ·
                    refine ⟨92106105881030502175073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 245616282349414672466861 92106105881030502175073)
                    ·
                      refine ⟨69079579410772876631305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 92106105881030502175073 69079579410772876631305)
                      ·
                        rfl

theorem cell23_134532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_134532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134532 prefixEnd_134532 := by exact prefixLift 134532
  have htrace : WordTrace (prefixWord ++ tailWord_134532) baseStart_134532 baseEnd_134532 := by
    simpa [prefixWord, tailWord_134532, baseEnd_134532] using wordTrace_append hprefix tailTrace_134532
  have hstable : (prefixWord ++ tailWord_134532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134532).length < 2 ^ (prefixWord ++ tailWord_134532).sum := by decide
  have hdescent : baseEnd_134532 < baseStart_134532 := by decide
  rcases family_descends (prefixWord ++ tailWord_134532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134562 : List Nat := [3, 3, 1, 2, 1, 4, 1, 1, 1, 4, 2]
def baseStart_134562 : Nat := 118140960795 + 134562 * 2 ^ 59
def prefixEnd_134562 : Nat := 4983230072969 + 3 ^ 40 * 134562 * 2
def baseEnd_134562 : Nat := 69094983830407759256167

theorem tailTrace_134562 : CollatzResearch.WordTrace tailWord_134562 prefixEnd_134562 69094983830407759256167 := by
  unfold tailWord_134562
  simp only [CollatzResearch.WordTrace]
  refine ⟨1226969834628082551267485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3271919559008220136713293 1226969834628082551267485)
  ·
    refine ⟨460113687985530956725307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1226969834628082551267485 460113687985530956725307)
    ·
      refine ⟨690170531978296435087961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 460113687985530956725307 690170531978296435087961)
      ·
        refine ⟨517627898983722326315971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 690170531978296435087961 517627898983722326315971)
        ·
          refine ⟨776441848475583489473957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 517627898983722326315971 776441848475583489473957)
          ·
            refine ⟨145582846589171904276367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 776441848475583489473957 145582846589171904276367)
            ·
              refine ⟨218374269883757856414551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145582846589171904276367 218374269883757856414551)
              ·
                refine ⟨327561404825636784621827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218374269883757856414551 327561404825636784621827)
                ·
                  refine ⟨491342107238455176932741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 327561404825636784621827 491342107238455176932741)
                  ·
                    refine ⟨92126645107210345674889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 491342107238455176932741 92126645107210345674889)
                    ·
                      refine ⟨69094983830407759256167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 92126645107210345674889 69094983830407759256167)
                      ·
                        rfl

theorem cell23_134562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_134562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134562 prefixEnd_134562 := by exact prefixLift 134562
  have htrace : WordTrace (prefixWord ++ tailWord_134562) baseStart_134562 baseEnd_134562 := by
    simpa [prefixWord, tailWord_134562, baseEnd_134562] using wordTrace_append hprefix tailTrace_134562
  have hstable : (prefixWord ++ tailWord_134562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134562).length < 2 ^ (prefixWord ++ tailWord_134562).sum := by decide
  have hdescent : baseEnd_134562 < baseStart_134562 := by decide
  rcases family_descends (prefixWord ++ tailWord_134562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134628 : List Nat := [2, 3, 1, 1, 1, 1, 1, 6, 3, 4]
def baseStart_134628 : Nat := 118140960795 + 134628 * 2 ^ 59
def prefixEnd_134628 : Nat := 4983230072969 + 3 ^ 40 * 134628 * 2
def baseEnd_134628 : Nat := 23042957851201500343621

theorem tailTrace_134628 : CollatzResearch.WordTrace tailWord_134628 prefixEnd_134628 23042957851201500343621 := by
  unfold tailWord_134628
  simp only [CollatzResearch.WordTrace]
  refine ⟨2455143278136611738486269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3273524370848815651315025 2455143278136611738486269)
  ·
    refine ⟨920678729301229401932351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2455143278136611738486269 920678729301229401932351)
    ·
      refine ⟨1381018093951844102898527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 920678729301229401932351 1381018093951844102898527)
      ·
        refine ⟨2071527140927766154347791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1381018093951844102898527 2071527140927766154347791)
        ·
          refine ⟨3107290711391649231521687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2071527140927766154347791 3107290711391649231521687)
          ·
            refine ⟨4660936067087473847282531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3107290711391649231521687 4660936067087473847282531)
            ·
              refine ⟨6991404100631210770923797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4660936067087473847282531 6991404100631210770923797)
              ·
                refine ⟨327722067217088004887053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6991404100631210770923797 327722067217088004887053)
                ·
                  refine ⟨122895775206408001832645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 327722067217088004887053 122895775206408001832645)
                  ·
                    refine ⟨23042957851201500343621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 122895775206408001832645 23042957851201500343621)
                    ·
                      rfl

theorem cell23_134628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_134628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134628 prefixEnd_134628 := by exact prefixLift 134628
  have htrace : WordTrace (prefixWord ++ tailWord_134628) baseStart_134628 baseEnd_134628 := by
    simpa [prefixWord, tailWord_134628, baseEnd_134628] using wordTrace_append hprefix tailTrace_134628
  have hstable : (prefixWord ++ tailWord_134628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134628).length < 2 ^ (prefixWord ++ tailWord_134628).sum := by decide
  have hdescent : baseEnd_134628 < baseStart_134628 := by decide
  rcases family_descends (prefixWord ++ tailWord_134628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134661 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 1, 2, 6]
def baseStart_134661 : Nat := 118140960795 + 134661 * 2 ^ 59
def prefixEnd_134661 : Nat := 4983230072969 + 3 ^ 40 * 134661 * 2
def baseEnd_134661 : Nat := 69145818415202871918211

theorem tailTrace_134661 : CollatzResearch.WordTrace tailWord_134661 prefixEnd_134661 69145818415202871918211 := by
  unfold tailWord_134661
  simp only [CollatzResearch.WordTrace]
  refine ⟨4911490165153670112923837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3274326776769113408615891 4911490165153670112923837)
  ·
    refine ⟨1841808811932626292346439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4911490165153670112923837 1841808811932626292346439)
    ·
      refine ⟨2762713217898939438519659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1841808811932626292346439 2762713217898939438519659)
      ·
        refine ⟨4144069826848409157779489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2762713217898939438519659 4144069826848409157779489)
        ·
          refine ⟨3108052370136306868334617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4144069826848409157779489 3108052370136306868334617)
          ·
            refine ⟨2331039277602230151250963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3108052370136306868334617 2331039277602230151250963)
            ·
              refine ⟨3496558916403345226876445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2331039277602230151250963 3496558916403345226876445)
              ·
                refine ⟨1311209593651254460078667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3496558916403345226876445 1311209593651254460078667)
                ·
                  refine ⟨1966814390476881690118001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1311209593651254460078667 1966814390476881690118001)
                  ·
                    refine ⟨1475110792857661267588501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1966814390476881690118001 1475110792857661267588501)
                    ·
                      refine ⟨69145818415202871918211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1475110792857661267588501 69145818415202871918211)
                      ·
                        rfl

theorem cell23_134661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_134661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134661 prefixEnd_134661 := by exact prefixLift 134661
  have htrace : WordTrace (prefixWord ++ tailWord_134661) baseStart_134661 baseEnd_134661 := by
    simpa [prefixWord, tailWord_134661, baseEnd_134661] using wordTrace_append hprefix tailTrace_134661
  have hstable : (prefixWord ++ tailWord_134661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134661).length < 2 ^ (prefixWord ++ tailWord_134661).sum := by decide
  have hdescent : baseEnd_134661 < baseStart_134661 := by decide
  rcases family_descends (prefixWord ++ tailWord_134661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134731 : List Nat := [1, 1, 1, 1, 3, 1, 3, 12]
def baseStart_134731 : Nat := 118140960795 + 134731 * 2 ^ 59
def prefixEnd_134731 : Nat := 4983230072969 + 3 ^ 40 * 134731 * 2
def baseEnd_134731 : Nat := 2562287483741392520107

theorem tailTrace_134731 : CollatzResearch.WordTrace tailWord_134731 prefixEnd_134731 2562287483741392520107 := by
  unfold tailWord_134731
  simp only [CollatzResearch.WordTrace]
  refine ⟨4914043274900072067972047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3276028849933381378648031 4914043274900072067972047)
  ·
    refine ⟨7371064912350108101958071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4914043274900072067972047 7371064912350108101958071)
    ·
      refine ⟨11056597368525162152937107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7371064912350108101958071 11056597368525162152937107)
      ·
        refine ⟨16584896052787743229405661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11056597368525162152937107 16584896052787743229405661)
        ·
          refine ⟨6219336019795403711027123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16584896052787743229405661 6219336019795403711027123)
          ·
            refine ⟨9329004029693105566540685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6219336019795403711027123 9329004029693105566540685)
            ·
              refine ⟨3498376511134914587452757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9329004029693105566540685 3498376511134914587452757)
              ·
                refine ⟨2562287483741392520107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 3498376511134914587452757 2562287483741392520107)
                ·
                  rfl

theorem cell23_134731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 12].length) (baseStart_134731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134731 prefixEnd_134731 := by exact prefixLift 134731
  have htrace : WordTrace (prefixWord ++ tailWord_134731) baseStart_134731 baseEnd_134731 := by
    simpa [prefixWord, tailWord_134731, baseEnd_134731] using wordTrace_append hprefix tailTrace_134731
  have hstable : (prefixWord ++ tailWord_134731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134731).length < 2 ^ (prefixWord ++ tailWord_134731).sum := by decide
  have hdescent : baseEnd_134731 < baseStart_134731 := by decide
  rcases family_descends (prefixWord ++ tailWord_134731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134762 : List Nat := [3, 1, 3, 2, 1, 2, 2, 3, 1, 2, 3]
def baseStart_134762 : Nat := 118140960795 + 134762 * 2 ^ 59
def prefixEnd_134762 : Nat := 4983230072969 + 3 ^ 40 * 134762 * 2
def baseEnd_134762 : Nat := 69197679961306976755247

theorem tailTrace_134762 : CollatzResearch.WordTrace tailWord_134762 prefixEnd_134762 69197679961306976755247 := by
  unfold tailWord_134762
  simp only [CollatzResearch.WordTrace]
  refine ⟨1228793484446941090587635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3276782625191842908233693 1228793484446941090587635)
  ·
    refine ⟨1843190226670411635881453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1228793484446941090587635 1843190226670411635881453)
    ·
      refine ⟨691196335001404363455545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1843190226670411635881453 691196335001404363455545)
      ·
        refine ⟨518397251251053272591659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 691196335001404363455545 518397251251053272591659)
        ·
          refine ⟨777595876876579908887489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518397251251053272591659 777595876876579908887489)
          ·
            refine ⟨583196907657434931665617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 777595876876579908887489 583196907657434931665617)
            ·
              refine ⟨437397680743076198749213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 583196907657434931665617 437397680743076198749213)
              ·
                refine ⟨164024130278653574530955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 437397680743076198749213 164024130278653574530955)
                ·
                  refine ⟨246036195417980361796433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164024130278653574530955 246036195417980361796433)
                  ·
                    refine ⟨184527146563485271347325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 246036195417980361796433 184527146563485271347325)
                    ·
                      refine ⟨69197679961306976755247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 184527146563485271347325 69197679961306976755247)
                      ·
                        rfl

theorem cell23_134762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_134762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134762 prefixEnd_134762 := by exact prefixLift 134762
  have htrace : WordTrace (prefixWord ++ tailWord_134762) baseStart_134762 baseEnd_134762 := by
    simpa [prefixWord, tailWord_134762, baseEnd_134762] using wordTrace_append hprefix tailTrace_134762
  have hstable : (prefixWord ++ tailWord_134762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134762).length < 2 ^ (prefixWord ++ tailWord_134762).sum := by decide
  have hdescent : baseEnd_134762 < baseStart_134762 := by decide
  rcases family_descends (prefixWord ++ tailWord_134762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134765 : List Nat := [1, 5, 1, 1, 4, 2, 9]
def baseStart_134765 : Nat := 118140960795 + 134765 * 2 ^ 59
def prefixEnd_134765 : Nat := 4983230072969 + 3 ^ 40 * 134765 * 2
def baseEnd_134765 : Nat := 854311363003339074293

theorem tailTrace_134765 : CollatzResearch.WordTrace tailWord_134765 prefixEnd_134765 854311363003339074293 := by
  unfold tailWord_134765
  simp only [CollatzResearch.WordTrace]
  refine ⟨4915283356776895874709749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3276855571184597249806499 4915283356776895874709749)
  ·
    refine ⟨460807814697833988254039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4915283356776895874709749 460807814697833988254039)
    ·
      refine ⟨691211722046750982381059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 460807814697833988254039 691211722046750982381059)
      ·
        refine ⟨1036817583070126473571589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 691211722046750982381059 1036817583070126473571589)
        ·
          refine ⟨194403296825648713794673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1036817583070126473571589 194403296825648713794673)
          ·
            refine ⟨145802472619236535346005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194403296825648713794673 145802472619236535346005)
            ·
              refine ⟨854311363003339074293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 145802472619236535346005 854311363003339074293)
              ·
                rfl

theorem cell23_134765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 9].length) (baseStart_134765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134765 prefixEnd_134765 := by exact prefixLift 134765
  have htrace : WordTrace (prefixWord ++ tailWord_134765) baseStart_134765 baseEnd_134765 := by
    simpa [prefixWord, tailWord_134765, baseEnd_134765] using wordTrace_append hprefix tailTrace_134765
  have hstable : (prefixWord ++ tailWord_134765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134765).length < 2 ^ (prefixWord ++ tailWord_134765).sum := by decide
  have hdescent : baseEnd_134765 < baseStart_134765 := by decide
  rcases family_descends (prefixWord ++ tailWord_134765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134819 : List Nat := [1, 1, 1, 4, 1, 1, 7, 1, 1, 3, 2]
def baseStart_134819 : Nat := 118140960795 + 134819 * 2 ^ 59
def prefixEnd_134819 : Nat := 4983230072969 + 3 ^ 40 * 134819 * 2
def baseEnd_134819 : Nat := 69226948358613253742485

theorem tailTrace_134819 : CollatzResearch.WordTrace tailWord_134819 prefixEnd_134819 69226948358613253742485 := by
  unfold tailWord_134819
  simp only [CollatzResearch.WordTrace]
  refine ⟨4917252898581263097175511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3278168599054175398117007 4917252898581263097175511)
  ·
    refine ⟨7375879347871894645763267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4917252898581263097175511 7375879347871894645763267)
    ·
      refine ⟨11063819021807841968644901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7375879347871894645763267 11063819021807841968644901)
      ·
        refine ⟨2074466066588970369120919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11063819021807841968644901 2074466066588970369120919)
        ·
          refine ⟨3111699099883455553681379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2074466066588970369120919 3111699099883455553681379)
          ·
            refine ⟨4667548649825183330522069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3111699099883455553681379 4667548649825183330522069)
            ·
              refine ⟨109395671480277734309111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 4667548649825183330522069 109395671480277734309111)
              ·
                refine ⟨164093507220416601463667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109395671480277734309111 164093507220416601463667)
                ·
                  refine ⟨246140260830624902195501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164093507220416601463667 246140260830624902195501)
                  ·
                    refine ⟨92302597811484338323313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 246140260830624902195501 92302597811484338323313)
                    ·
                      refine ⟨69226948358613253742485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 92302597811484338323313 69226948358613253742485)
                      ·
                        rfl

theorem cell23_134819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 1, 3, 2].length) (baseStart_134819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134819 prefixEnd_134819 := by exact prefixLift 134819
  have htrace : WordTrace (prefixWord ++ tailWord_134819) baseStart_134819 baseEnd_134819 := by
    simpa [prefixWord, tailWord_134819, baseEnd_134819] using wordTrace_append hprefix tailTrace_134819
  have hstable : (prefixWord ++ tailWord_134819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134819).length < 2 ^ (prefixWord ++ tailWord_134819).sum := by decide
  have hdescent : baseEnd_134819 < baseStart_134819 := by decide
  rcases family_descends (prefixWord ++ tailWord_134819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134828 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 4]
def baseStart_134828 : Nat := 118140960795 + 134828 * 2 ^ 59
def prefixEnd_134828 : Nat := 4983230072969 + 3 ^ 40 * 134828 * 2
def baseEnd_134828 : Nat := 69231569684503718529943

theorem tailTrace_134828 : CollatzResearch.WordTrace tailWord_134828 prefixEnd_134828 69231569684503718529943 := by
  unfold tailWord_134828
  simp only [CollatzResearch.WordTrace]
  refine ⟨2458790577774328817126569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3278387437032438422835425 2458790577774328817126569)
  ·
    refine ⟨1844092933330746612844927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2458790577774328817126569 1844092933330746612844927)
    ·
      refine ⟨2766139399996119919267391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1844092933330746612844927 2766139399996119919267391)
      ·
        refine ⟨4149209099994179878901087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2766139399996119919267391 4149209099994179878901087)
        ·
          refine ⟨6223813649991269818351631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4149209099994179878901087 6223813649991269818351631)
          ·
            refine ⟨9335720474986904727527447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6223813649991269818351631 9335720474986904727527447)
            ·
              refine ⟨14003580712480357091291171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9335720474986904727527447 14003580712480357091291171)
              ·
                refine ⟨21005371068720535636936757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14003580712480357091291171 21005371068720535636936757)
                ·
                  refine ⟨1969253537692550215962821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21005371068720535636936757 1969253537692550215962821)
                  ·
                    refine ⟨369235038317353165493029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1969253537692550215962821 369235038317353165493029)
                    ·
                      refine ⟨69231569684503718529943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 369235038317353165493029 69231569684503718529943)
                      ·
                        rfl

theorem cell23_134828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_134828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134828 prefixEnd_134828 := by exact prefixLift 134828
  have htrace : WordTrace (prefixWord ++ tailWord_134828) baseStart_134828 baseEnd_134828 := by
    simpa [prefixWord, tailWord_134828, baseEnd_134828] using wordTrace_append hprefix tailTrace_134828
  have hstable : (prefixWord ++ tailWord_134828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134828).length < 2 ^ (prefixWord ++ tailWord_134828).sum := by decide
  have hdescent : baseEnd_134828 < baseStart_134828 := by decide
  rcases family_descends (prefixWord ++ tailWord_134828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134832 : List Nat := [2, 1, 1, 1, 2, 1, 4, 3, 4, 2, 2]
def baseStart_134832 : Nat := 118140960795 + 134832 * 2 ^ 59
def prefixEnd_134832 : Nat := 4983230072969 + 3 ^ 40 * 134832 * 2
def baseEnd_134832 : Nat := 69233623607121702879925

theorem tailTrace_134832 : CollatzResearch.WordTrace tailWord_134832 prefixEnd_134832 69233623607121702879925 := by
  unfold tailWord_134832
  simp only [CollatzResearch.WordTrace]
  refine ⟨2458863523767083158699375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3278484698356110878265833 2458863523767083158699375)
  ·
    refine ⟨3688295285650624738049063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2458863523767083158699375 3688295285650624738049063)
    ·
      refine ⟨5532442928475937107073595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3688295285650624738049063 5532442928475937107073595)
      ·
        refine ⟨8298664392713905660610393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5532442928475937107073595 8298664392713905660610393)
        ·
          refine ⟨6223998294535429245457795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8298664392713905660610393 6223998294535429245457795)
          ·
            refine ⟨9335997441803143868186693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6223998294535429245457795 9335997441803143868186693)
            ·
              refine ⟨1750499520338089475285005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9335997441803143868186693 1750499520338089475285005)
              ·
                refine ⟨656437320126783553231877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1750499520338089475285005 656437320126783553231877)
                ·
                  refine ⟨123081997523771916230977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 656437320126783553231877 123081997523771916230977)
                  ·
                    refine ⟨92311498142828937173233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 123081997523771916230977 92311498142828937173233)
                    ·
                      refine ⟨69233623607121702879925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 92311498142828937173233 69233623607121702879925)
                      ·
                        rfl

theorem cell23_134832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 4, 2, 2].length) (baseStart_134832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134832 prefixEnd_134832 := by exact prefixLift 134832
  have htrace : WordTrace (prefixWord ++ tailWord_134832) baseStart_134832 baseEnd_134832 := by
    simpa [prefixWord, tailWord_134832, baseEnd_134832] using wordTrace_append hprefix tailTrace_134832
  have hstable : (prefixWord ++ tailWord_134832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134832).length < 2 ^ (prefixWord ++ tailWord_134832).sum := by decide
  have hdescent : baseEnd_134832 < baseStart_134832 := by decide
  rcases family_descends (prefixWord ++ tailWord_134832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134845 : List Nat := [1, 4, 1, 2, 1, 2, 3, 1, 2, 2, 4]
def baseStart_134845 : Nat := 118140960795 + 134845 * 2 ^ 59
def prefixEnd_134845 : Nat := 4983230072969 + 3 ^ 40 * 134845 * 2
def baseEnd_134845 : Nat := 69240298855630152017365

theorem tailTrace_134845 : CollatzResearch.WordTrace tailWord_134845 prefixEnd_134845 69240298855630152017365 := by
  unfold tailWord_134845
  simp only [CollatzResearch.WordTrace]
  refine ⟨4918201196487069537621989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3278800797658046358414659 4918201196487069537621989)
  ·
    refine ⟨922162724341325538304123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4918201196487069537621989 922162724341325538304123)
    ·
      refine ⟨1383244086511988307456185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 922162724341325538304123 1383244086511988307456185)
      ·
        refine ⟨1037433064883991230592139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1383244086511988307456185 1037433064883991230592139)
        ·
          refine ⟨1556149597325986845888209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1037433064883991230592139 1556149597325986845888209)
          ·
            refine ⟨1167112197994490134416157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1556149597325986845888209 1167112197994490134416157)
            ·
              refine ⟨437667074247933800406059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1167112197994490134416157 437667074247933800406059)
              ·
                refine ⟨656500611371900700609089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 437667074247933800406059 656500611371900700609089)
                ·
                  refine ⟨492375458528925525456817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 656500611371900700609089 492375458528925525456817)
                  ·
                    refine ⟨369281593896694144092613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 492375458528925525456817 369281593896694144092613)
                    ·
                      refine ⟨69240298855630152017365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 369281593896694144092613 69240298855630152017365)
                      ·
                        rfl

theorem cell23_134845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_134845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134845 prefixEnd_134845 := by exact prefixLift 134845
  have htrace : WordTrace (prefixWord ++ tailWord_134845) baseStart_134845 baseEnd_134845 := by
    simpa [prefixWord, tailWord_134845, baseEnd_134845] using wordTrace_append hprefix tailTrace_134845
  have hstable : (prefixWord ++ tailWord_134845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134845).length < 2 ^ (prefixWord ++ tailWord_134845).sum := by decide
  have hdescent : baseEnd_134845 < baseStart_134845 := by decide
  rcases family_descends (prefixWord ++ tailWord_134845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134872 : List Nat := [2, 1, 2, 2, 3, 1, 4, 3, 5]
def baseStart_134872 : Nat := 118140960795 + 134872 * 2 ^ 59
def prefixEnd_134872 : Nat := 4983230072969 + 3 ^ 40 * 134872 * 2
def baseEnd_134872 : Nat := 7694906981477949597749

theorem tailTrace_134872 : CollatzResearch.WordTrace tailWord_134872 prefixEnd_134872 7694906981477949597749 := by
  unfold tailWord_134872
  simp only [CollatzResearch.WordTrace]
  refine ⟨2459592983694626574427435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3279457311592835432569913 2459592983694626574427435)
  ·
    refine ⟨3689389475541939861641153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2459592983694626574427435 3689389475541939861641153)
    ·
      refine ⟨2767042106656454896230865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3689389475541939861641153 2767042106656454896230865)
      ·
        refine ⟨2075281579992341172173149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2767042106656454896230865 2075281579992341172173149)
        ·
          refine ⟨778230592497127939564931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2075281579992341172173149 778230592497127939564931)
          ·
            refine ⟨1167345888745691909347397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 778230592497127939564931 1167345888745691909347397)
            ·
              refine ⟨218877354139817233002637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1167345888745691909347397 218877354139817233002637)
              ·
                refine ⟨82079007802431462375989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 218877354139817233002637 82079007802431462375989)
                ·
                  refine ⟨7694906981477949597749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82079007802431462375989 7694906981477949597749)
                  ·
                    rfl

theorem cell23_134872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3, 5].length) (baseStart_134872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134872 prefixEnd_134872 := by exact prefixLift 134872
  have htrace : WordTrace (prefixWord ++ tailWord_134872) baseStart_134872 baseEnd_134872 := by
    simpa [prefixWord, tailWord_134872, baseEnd_134872] using wordTrace_append hprefix tailTrace_134872
  have hstable : (prefixWord ++ tailWord_134872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134872).length < 2 ^ (prefixWord ++ tailWord_134872).sum := by decide
  have hdescent : baseEnd_134872 < baseStart_134872 := by decide
  rcases family_descends (prefixWord ++ tailWord_134872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134883 : List Nat := [1, 1, 1, 7, 2, 2, 1, 2, 2, 2, 2]
def baseStart_134883 : Nat := 118140960795 + 134883 * 2 ^ 59
def prefixEnd_134883 : Nat := 4983230072969 + 3 ^ 40 * 134883 * 2
def baseEnd_134883 : Nat := 69259811120501003342191

theorem tailTrace_134883 : CollatzResearch.WordTrace tailWord_134883 prefixEnd_134883 69259811120501003342191 := by
  unfold tailWord_134883
  simp only [CollatzResearch.WordTrace]
  refine ⟨4919587170349402027505303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3279724780232934685003535 4919587170349402027505303)
  ·
    refine ⟨7379380755524103041257955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4919587170349402027505303 7379380755524103041257955)
    ·
      refine ⟨11069071133286154561886933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7379380755524103041257955 11069071133286154561886933)
      ·
        refine ⟨259431354686394247544225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 11069071133286154561886933 259431354686394247544225)
        ·
          refine ⟨194573516014795685658169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259431354686394247544225 194573516014795685658169)
          ·
            refine ⟨145930137011096764243627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194573516014795685658169 145930137011096764243627)
            ·
              refine ⟨218895205516645146365441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145930137011096764243627 218895205516645146365441)
              ·
                refine ⟨164171404137483859774081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218895205516645146365441 164171404137483859774081)
                ·
                  refine ⟨123128553103112894830561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164171404137483859774081 123128553103112894830561)
                  ·
                    refine ⟨92346414827334671122921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 123128553103112894830561 92346414827334671122921)
                    ·
                      refine ⟨69259811120501003342191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 92346414827334671122921 69259811120501003342191)
                      ·
                        rfl

theorem cell23_134883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_134883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134883 prefixEnd_134883 := by exact prefixLift 134883
  have htrace : WordTrace (prefixWord ++ tailWord_134883) baseStart_134883 baseEnd_134883 := by
    simpa [prefixWord, tailWord_134883, baseEnd_134883] using wordTrace_append hprefix tailTrace_134883
  have hstable : (prefixWord ++ tailWord_134883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134883).length < 2 ^ (prefixWord ++ tailWord_134883).sum := by decide
  have hdescent : baseEnd_134883 < baseStart_134883 := by decide
  rcases family_descends (prefixWord ++ tailWord_134883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134885 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 4, 5]
def baseStart_134885 : Nat := 118140960795 + 134885 * 2 ^ 59
def prefixEnd_134885 : Nat := 4983230072969 + 3 ^ 40 * 134885 * 2
def baseEnd_134885 : Nat := 23086946027269998505727

theorem tailTrace_134885 : CollatzResearch.WordTrace tailWord_134885 prefixEnd_134885 23086946027269998505727 := by
  unfold tailWord_134885
  simp only [CollatzResearch.WordTrace]
  refine ⟨4919660116342156369078109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3279773410894770912718739 4919660116342156369078109)
  ·
    refine ⟨1844872543628308638404291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4919660116342156369078109 1844872543628308638404291)
    ·
      refine ⟨2767308815442462957606437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1844872543628308638404291 2767308815442462957606437)
      ·
        refine ⟨518870402895461804551207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2767308815442462957606437 518870402895461804551207)
        ·
          refine ⟨778305604343192706826811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518870402895461804551207 778305604343192706826811)
          ·
            refine ⟨1167458406514789060240217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 778305604343192706826811 1167458406514789060240217)
            ·
              refine ⟨875593804886091795180163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1167458406514789060240217 875593804886091795180163)
              ·
                refine ⟨1313390707329137692770245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 875593804886091795180163 1313390707329137692770245)
                ·
                  refine ⟨246260757624213317394421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1313390707329137692770245 246260757624213317394421)
                  ·
                    refine ⟨23086946027269998505727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 246260757624213317394421 23086946027269998505727)
                    ·
                      rfl

theorem cell23_134885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 5].length) (baseStart_134885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134885 prefixEnd_134885 := by exact prefixLift 134885
  have htrace : WordTrace (prefixWord ++ tailWord_134885) baseStart_134885 baseEnd_134885 := by
    simpa [prefixWord, tailWord_134885, baseEnd_134885] using wordTrace_append hprefix tailTrace_134885
  have hstable : (prefixWord ++ tailWord_134885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134885).length < 2 ^ (prefixWord ++ tailWord_134885).sum := by decide
  have hdescent : baseEnd_134885 < baseStart_134885 := by decide
  rcases family_descends (prefixWord ++ tailWord_134885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134945 : List Nat := [1, 2, 3, 2, 1, 3, 2, 1, 8]
def baseStart_134945 : Nat := 118140960795 + 134945 * 2 ^ 59
def prefixEnd_134945 : Nat := 4983230072969 + 3 ^ 40 * 134945 * 2
def baseEnd_134945 : Nat := 7699071880119973418545

theorem tailTrace_134945 : CollatzResearch.WordTrace tailWord_134945 prefixEnd_134945 7699071880119973418545 := by
  unfold tailWord_134945
  simp only [CollatzResearch.WordTrace]
  refine ⟨4921848496124786616262289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3281232330749857744174859 4921848496124786616262289)
  ·
    refine ⟨3691386372093589962196717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4921848496124786616262289 3691386372093589962196717)
    ·
      refine ⟨1384269889535096235823769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3691386372093589962196717 1384269889535096235823769)
      ·
        refine ⟨1038202417151322176867827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1384269889535096235823769 1038202417151322176867827)
        ·
          refine ⟨1557303625726983265301741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1038202417151322176867827 1557303625726983265301741)
          ·
            refine ⟨583988859647618724488153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1557303625726983265301741 583988859647618724488153)
            ·
              refine ⟨437991644735714043366115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 583988859647618724488153 437991644735714043366115)
              ·
                refine ⟨656987467103571065049173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 437991644735714043366115 656987467103571065049173)
                ·
                  refine ⟨7699071880119973418545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 656987467103571065049173 7699071880119973418545)
                  ·
                    rfl

theorem cell23_134945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 8].length) (baseStart_134945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134945 prefixEnd_134945 := by exact prefixLift 134945
  have htrace : WordTrace (prefixWord ++ tailWord_134945) baseStart_134945 baseEnd_134945 := by
    simpa [prefixWord, tailWord_134945, baseEnd_134945] using wordTrace_append hprefix tailTrace_134945
  have hstable : (prefixWord ++ tailWord_134945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134945).length < 2 ^ (prefixWord ++ tailWord_134945).sum := by decide
  have hdescent : baseEnd_134945 < baseStart_134945 := by decide
  rcases family_descends (prefixWord ++ tailWord_134945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134949 : List Nat := [1, 3, 1, 2, 3, 4, 1, 1, 3, 4]
def baseStart_134949 : Nat := 118140960795 + 134949 * 2 ^ 59
def prefixEnd_134949 : Nat := 4983230072969 + 3 ^ 40 * 134949 * 2
def baseEnd_134949 : Nat := 23097900281232581705629

theorem tailTrace_134949 : CollatzResearch.WordTrace tailWord_134949 prefixEnd_134949 23097900281232581705629 := by
  unfold tailWord_134949
  simp only [CollatzResearch.WordTrace]
  refine ⟨4921994388110295299407901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3281329592073530199605267 4921994388110295299407901)
  ·
    refine ⟨1845747895541360737277963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4921994388110295299407901 1845747895541360737277963)
    ·
      refine ⟨2768621843312041105916945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1845747895541360737277963 2768621843312041105916945)
      ·
        refine ⟨2076466382484030829437709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2768621843312041105916945 2076466382484030829437709)
        ·
          refine ⟨778674893431511561039141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2076466382484030829437709 778674893431511561039141)
          ·
            refine ⟨146001542518408417694839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 778674893431511561039141 146001542518408417694839)
            ·
              refine ⟨219002313777612626542259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146001542518408417694839 219002313777612626542259)
              ·
                refine ⟨328503470666418939813389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219002313777612626542259 328503470666418939813389)
                ·
                  refine ⟨123188801499907102430021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 328503470666418939813389 123188801499907102430021)
                  ·
                    refine ⟨23097900281232581705629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 123188801499907102430021 23097900281232581705629)
                    ·
                      rfl

theorem cell23_134949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3, 4].length) (baseStart_134949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134949 prefixEnd_134949 := by exact prefixLift 134949
  have htrace : WordTrace (prefixWord ++ tailWord_134949) baseStart_134949 baseEnd_134949 := by
    simpa [prefixWord, tailWord_134949, baseEnd_134949] using wordTrace_append hprefix tailTrace_134949
  have hstable : (prefixWord ++ tailWord_134949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134949).length < 2 ^ (prefixWord ++ tailWord_134949).sum := by decide
  have hdescent : baseEnd_134949 < baseStart_134949 := by decide
  rcases family_descends (prefixWord ++ tailWord_134949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134962 : List Nat := [3, 2, 1, 1, 3, 3, 1, 3, 6]
def baseStart_134962 : Nat := 118140960795 + 134962 * 2 ^ 59
def prefixEnd_134962 : Nat := 4983230072969 + 3 ^ 40 * 134962 * 2
def baseEnd_134962 : Nat := 7700041788022910472703

theorem tailTrace_134962 : CollatzResearch.WordTrace tailWord_134962 prefixEnd_134962 7700041788022910472703 := by
  unfold tailWord_134962
  simp only [CollatzResearch.WordTrace]
  refine ⟨1230617134265799629907785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3281645691375465679754093 1230617134265799629907785)
  ·
    refine ⟨922962850699349722430839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1230617134265799629907785 922962850699349722430839)
    ·
      refine ⟨1384444276049024583646259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 922962850699349722430839 1384444276049024583646259)
      ·
        refine ⟨2076666414073536875469389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1384444276049024583646259 2076666414073536875469389)
        ·
          refine ⟨778749905277576328301021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2076666414073536875469389 778749905277576328301021)
          ·
            refine ⟨292031214479091123112883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 778749905277576328301021 292031214479091123112883)
            ·
              refine ⟨438046821718636684669325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292031214479091123112883 438046821718636684669325)
              ·
                refine ⟨164267558144488756750997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 438046821718636684669325 164267558144488756750997)
                ·
                  refine ⟨7700041788022910472703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 164267558144488756750997 7700041788022910472703)
                  ·
                    rfl

theorem cell23_134962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 6].length) (baseStart_134962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_134962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_134962 prefixEnd_134962 := by exact prefixLift 134962
  have htrace : WordTrace (prefixWord ++ tailWord_134962) baseStart_134962 baseEnd_134962 := by
    simpa [prefixWord, tailWord_134962, baseEnd_134962] using wordTrace_append hprefix tailTrace_134962
  have hstable : (prefixWord ++ tailWord_134962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134962).length < 2 ^ (prefixWord ++ tailWord_134962).sum := by decide
  have hdescent : baseEnd_134962 < baseStart_134962 := by decide
  rcases family_descends (prefixWord ++ tailWord_134962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135029 : List Nat := [1, 3, 4, 1, 1, 1, 2, 4, 1, 1, 4]
def baseStart_135029 : Nat := 118140960795 + 135029 * 2 ^ 59
def prefixEnd_135029 : Nat := 4983230072969 + 3 ^ 40 * 135029 * 2
def baseEnd_135029 : Nat := 69334779296057432116519

theorem tailTrace_135029 : CollatzResearch.WordTrace tailWord_135029 prefixEnd_135029 69334779296057432116519 := by
  unfold tailWord_135029
  simp only [CollatzResearch.WordTrace]
  refine ⟨4924912227820468962320141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3283274818546979308213427 4924912227820468962320141)
  ·
    refine ⟨1846842085432675860870053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4924912227820468962320141 1846842085432675860870053)
    ·
      refine ⟨346282891018626723913135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1846842085432675860870053 346282891018626723913135)
      ·
        refine ⟨519424336527940085869703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346282891018626723913135 519424336527940085869703)
        ·
          refine ⟨779136504791910128804555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 519424336527940085869703 779136504791910128804555)
          ·
            refine ⟨1168704757187865193206833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 779136504791910128804555 1168704757187865193206833)
            ·
              refine ⟨876528567890898894905125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1168704757187865193206833 876528567890898894905125)
              ·
                refine ⟨164349106479543542794711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 876528567890898894905125 164349106479543542794711)
                ·
                  refine ⟨246523659719315314192067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164349106479543542794711 246523659719315314192067)
                  ·
                    refine ⟨369785489578972971288101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 246523659719315314192067 369785489578972971288101)
                    ·
                      refine ⟨69334779296057432116519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 369785489578972971288101 69334779296057432116519)
                      ·
                        rfl

theorem cell23_135029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_135029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135029 prefixEnd_135029 := by exact prefixLift 135029
  have htrace : WordTrace (prefixWord ++ tailWord_135029) baseStart_135029 baseEnd_135029 := by
    simpa [prefixWord, tailWord_135029, baseEnd_135029] using wordTrace_append hprefix tailTrace_135029
  have hstable : (prefixWord ++ tailWord_135029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135029).length < 2 ^ (prefixWord ++ tailWord_135029).sum := by decide
  have hdescent : baseEnd_135029 < baseStart_135029 := by decide
  rcases family_descends (prefixWord ++ tailWord_135029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135049 : List Nat := [1, 2, 1, 1, 5, 1, 3, 3, 1, 2, 3]
def baseStart_135049 : Nat := 118140960795 + 135049 * 2 ^ 59
def prefixEnd_135049 : Nat := 4983230072969 + 3 ^ 40 * 135049 * 2
def baseEnd_135049 : Nat := 69345048909147353866427

theorem tailTrace_135049 : CollatzResearch.WordTrace tailWord_135049 prefixEnd_135049 69345048909147353866427 := by
  unfold tailWord_135049
  simp only [CollatzResearch.WordTrace]
  refine ⟨4925641687748012378048201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3283761125165341585365467 4925641687748012378048201)
  ·
    refine ⟨3694231265811009283536151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4925641687748012378048201 3694231265811009283536151)
    ·
      refine ⟨5541346898716513925304227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3694231265811009283536151 5541346898716513925304227)
      ·
        refine ⟨8312020348074770887956341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5541346898716513925304227 8312020348074770887956341)
        ·
          refine ⟨779251907632009770745907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8312020348074770887956341 779251907632009770745907)
          ·
            refine ⟨1168877861448014656118861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 779251907632009770745907 1168877861448014656118861)
            ·
              refine ⟨438329198043005496044573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1168877861448014656118861 438329198043005496044573)
              ·
                refine ⟨164373449266127061016715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 438329198043005496044573 164373449266127061016715)
                ·
                  refine ⟨246560173899190591525073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164373449266127061016715 246560173899190591525073)
                  ·
                    refine ⟨184920130424392943643805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 246560173899190591525073 184920130424392943643805)
                    ·
                      refine ⟨69345048909147353866427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 184920130424392943643805 69345048909147353866427)
                      ·
                        rfl

theorem cell23_135049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 2, 3].length) (baseStart_135049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135049 prefixEnd_135049 := by exact prefixLift 135049
  have htrace : WordTrace (prefixWord ++ tailWord_135049) baseStart_135049 baseEnd_135049 := by
    simpa [prefixWord, tailWord_135049, baseEnd_135049] using wordTrace_append hprefix tailTrace_135049
  have hstable : (prefixWord ++ tailWord_135049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135049).length < 2 ^ (prefixWord ++ tailWord_135049).sum := by decide
  have hdescent : baseEnd_135049 < baseStart_135049 := by decide
  rcases family_descends (prefixWord ++ tailWord_135049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135063 : List Nat := [1, 1, 3, 3, 1, 3, 2, 4, 1, 2, 2]
def baseStart_135063 : Nat := 118140960795 + 135063 * 2 ^ 59
def prefixEnd_135063 : Nat := 4983230072969 + 3 ^ 40 * 135063 * 2
def baseEnd_135063 : Nat := 69352237638310299091363

theorem tailTrace_135063 : CollatzResearch.WordTrace tailWord_135063 prefixEnd_135063 69352237638310299091363 := by
  unfold tailWord_135063
  simp only [CollatzResearch.WordTrace]
  refine ⟨4926152309697292769057843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3284101539798195179371895 4926152309697292769057843)
  ·
    refine ⟨7389228464545939153586765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4926152309697292769057843 7389228464545939153586765)
    ·
      refine ⟨2770960674204727182595037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7389228464545939153586765 2770960674204727182595037)
      ·
        refine ⟨1039110252826772693473139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2770960674204727182595037 1039110252826772693473139)
        ·
          refine ⟨1558665379240159040209709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1039110252826772693473139 1558665379240159040209709)
          ·
            refine ⟨584499517215059640078641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1558665379240159040209709 584499517215059640078641)
            ·
              refine ⟨438374637911294730058981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 584499517215059640078641 438374637911294730058981)
              ·
                refine ⟨82195244608367761886059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 438374637911294730058981 82195244608367761886059)
                ·
                  refine ⟨123292866912551642829089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82195244608367761886059 123292866912551642829089)
                  ·
                    refine ⟨92469650184413732121817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 123292866912551642829089 92469650184413732121817)
                    ·
                      refine ⟨69352237638310299091363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 92469650184413732121817 69352237638310299091363)
                      ·
                        rfl

theorem cell23_135063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_135063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135063 prefixEnd_135063 := by exact prefixLift 135063
  have htrace : WordTrace (prefixWord ++ tailWord_135063) baseStart_135063 baseEnd_135063 := by
    simpa [prefixWord, tailWord_135063, baseEnd_135063] using wordTrace_append hprefix tailTrace_135063
  have hstable : (prefixWord ++ tailWord_135063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135063).length < 2 ^ (prefixWord ++ tailWord_135063).sum := by decide
  have hdescent : baseEnd_135063 < baseStart_135063 := by decide
  rcases family_descends (prefixWord ++ tailWord_135063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135065 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 1, 9]
def baseStart_135065 : Nat := 118140960795 + 135065 * 2 ^ 59
def prefixEnd_135065 : Nat := 4983230072969 + 3 ^ 40 * 135065 * 2
def baseEnd_135065 : Nat := 23117754866539763755451

theorem tailTrace_135065 : CollatzResearch.WordTrace tailWord_135065 prefixEnd_135065 23117754866539763755451 := by
  unfold tailWord_135065
  simp only [CollatzResearch.WordTrace]
  refine ⟨4926225255690047110630649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3284150170460031407087099 4926225255690047110630649)
  ·
    refine ⟨3694668941767535332972987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4926225255690047110630649 3694668941767535332972987)
    ·
      refine ⟨5542003412651302999459481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3694668941767535332972987 5542003412651302999459481)
      ·
        refine ⟨4156502559488477249594611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5542003412651302999459481 4156502559488477249594611)
        ·
          refine ⟨6234753839232715874391917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4156502559488477249594611 6234753839232715874391917)
          ·
            refine ⟨2338032689712268452896969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6234753839232715874391917 2338032689712268452896969)
            ·
              refine ⟨1753524517284201339672727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2338032689712268452896969 1753524517284201339672727)
              ·
                refine ⟨2630286775926302009509091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1753524517284201339672727 2630286775926302009509091)
                ·
                  refine ⟨3945430163889453014263637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2630286775926302009509091 3945430163889453014263637)
                  ·
                    refine ⟨23117754866539763755451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 3945430163889453014263637 23117754866539763755451)
                    ·
                      rfl

theorem cell23_135065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 9].length) (baseStart_135065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135065 prefixEnd_135065 := by exact prefixLift 135065
  have htrace : WordTrace (prefixWord ++ tailWord_135065) baseStart_135065 baseEnd_135065 := by
    simpa [prefixWord, tailWord_135065, baseEnd_135065] using wordTrace_append hprefix tailTrace_135065
  have hstable : (prefixWord ++ tailWord_135065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135065).length < 2 ^ (prefixWord ++ tailWord_135065).sum := by decide
  have hdescent : baseEnd_135065 < baseStart_135065 := by decide
  rcases family_descends (prefixWord ++ tailWord_135065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135073 : List Nat := [1, 2, 3, 4, 2, 1, 3, 1, 2, 4]
def baseStart_135073 : Nat := 118140960795 + 135073 * 2 ^ 59
def prefixEnd_135073 : Nat := 4983230072969 + 3 ^ 40 * 135073 * 2
def baseEnd_135073 : Nat := 23119124148285086655439

theorem tailTrace_135073 : CollatzResearch.WordTrace tailWord_135073 prefixEnd_135073 23119124148285086655439 := by
  unfold tailWord_135073
  simp only [CollatzResearch.WordTrace]
  refine ⟨4926517039661064476921873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3284344693107376317947915 4926517039661064476921873)
  ·
    refine ⟨3694887779745798357691405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4926517039661064476921873 3694887779745798357691405)
    ·
      refine ⟨1385582917404674384134277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3694887779745798357691405 1385582917404674384134277)
      ·
        refine ⟨259796797013376447025177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1385582917404674384134277 259796797013376447025177)
        ·
          refine ⟨194847597760032335268883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259796797013376447025177 194847597760032335268883)
          ·
            refine ⟨292271396640048502903325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194847597760032335268883 292271396640048502903325)
            ·
              refine ⟨109601773740018188588747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 292271396640048502903325 109601773740018188588747)
              ·
                refine ⟨164402660610027282883121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109601773740018188588747 164402660610027282883121)
                ·
                  refine ⟨123301995457520462162341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164402660610027282883121 123301995457520462162341)
                  ·
                    refine ⟨23119124148285086655439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 123301995457520462162341 23119124148285086655439)
                    ·
                      rfl

theorem cell23_135073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_135073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135073 prefixEnd_135073 := by exact prefixLift 135073
  have htrace : WordTrace (prefixWord ++ tailWord_135073) baseStart_135073 baseEnd_135073 := by
    simpa [prefixWord, tailWord_135073, baseEnd_135073] using wordTrace_append hprefix tailTrace_135073
  have hstable : (prefixWord ++ tailWord_135073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135073).length < 2 ^ (prefixWord ++ tailWord_135073).sum := by decide
  have hdescent : baseEnd_135073 < baseStart_135073 := by decide
  rcases family_descends (prefixWord ++ tailWord_135073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135130 : List Nat := [3, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3]
def baseStart_135130 : Nat := 118140960795 + 135130 * 2 ^ 59
def prefixEnd_135130 : Nat := 4983230072969 + 3 ^ 40 * 135130 * 2
def baseEnd_135130 : Nat := 69386640842161536953555

theorem tailTrace_135130 : CollatzResearch.WordTrace tailWord_135130 prefixEnd_135130 69386640842161536953555 := by
  unfold tailWord_135130
  simp only [CollatzResearch.WordTrace]
  refine ⟨1232149000113640802936711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3285730666969708807831229 1232149000113640802936711)
  ·
    refine ⟨1848223500170461204405067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1232149000113640802936711 1848223500170461204405067)
    ·
      refine ⟨2772335250255691806607601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1848223500170461204405067 2772335250255691806607601)
      ·
        refine ⟨2079251437691768854955701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2772335250255691806607601 2079251437691768854955701)
        ·
          refine ⟨194929822283603330152097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2079251437691768854955701 194929822283603330152097)
          ·
            refine ⟨146197366712702497614073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194929822283603330152097 146197366712702497614073)
            ·
              refine ⟨109648025034526873210555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146197366712702497614073 109648025034526873210555)
              ·
                refine ⟨164472037551790309815833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109648025034526873210555 164472037551790309815833)
                ·
                  refine ⟨123354028163842732361875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164472037551790309815833 123354028163842732361875)
                  ·
                    refine ⟨185031042245764098542813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 123354028163842732361875 185031042245764098542813)
                    ·
                      refine ⟨69386640842161536953555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 185031042245764098542813 69386640842161536953555)
                      ·
                        rfl

theorem cell23_135130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3].length) (baseStart_135130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135130 prefixEnd_135130 := by exact prefixLift 135130
  have htrace : WordTrace (prefixWord ++ tailWord_135130) baseStart_135130 baseEnd_135130 := by
    simpa [prefixWord, tailWord_135130, baseEnd_135130] using wordTrace_append hprefix tailTrace_135130
  have hstable : (prefixWord ++ tailWord_135130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135130).length < 2 ^ (prefixWord ++ tailWord_135130).sum := by decide
  have hdescent : baseEnd_135130 < baseStart_135130 := by decide
  rcases family_descends (prefixWord ++ tailWord_135130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135169 : List Nat := [1, 2, 4, 1, 2, 1, 2, 2, 2, 3, 3]
def baseStart_135169 : Nat := 118140960795 + 135169 * 2 ^ 59
def prefixEnd_135169 : Nat := 4983230072969 + 3 ^ 40 * 135169 * 2
def baseEnd_135169 : Nat := 69406666587686884365875

theorem tailTrace_135169 : CollatzResearch.WordTrace tailWord_135169 prefixEnd_135169 69406666587686884365875 := by
  unfold tailWord_135169
  simp only [CollatzResearch.WordTrace]
  refine ⟨4930018447313272872416561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3286678964875515248277707 4930018447313272872416561)
  ·
    refine ⟨3697513835484954654312421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4930018447313272872416561 3697513835484954654312421)
    ·
      refine ⟨693283844153428997683579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3697513835484954654312421 693283844153428997683579)
      ·
        refine ⟨1039925766230143496525369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 693283844153428997683579 1039925766230143496525369)
        ·
          refine ⟨779944324672607622394027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1039925766230143496525369 779944324672607622394027)
          ·
            refine ⟨1169916487008911433591041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 779944324672607622394027 1169916487008911433591041)
            ·
              refine ⟨877437365256683575193281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1169916487008911433591041 877437365256683575193281)
              ·
                refine ⟨658078023942512681394961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 877437365256683575193281 658078023942512681394961)
                ·
                  refine ⟨493558517956884511046221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 658078023942512681394961 493558517956884511046221)
                  ·
                    refine ⟨185084444233831691642333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 493558517956884511046221 185084444233831691642333)
                    ·
                      refine ⟨69406666587686884365875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 185084444233831691642333 69406666587686884365875)
                      ·
                        rfl

theorem cell23_135169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_135169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135169 prefixEnd_135169 := by exact prefixLift 135169
  have htrace : WordTrace (prefixWord ++ tailWord_135169) baseStart_135169 baseEnd_135169 := by
    simpa [prefixWord, tailWord_135169, baseEnd_135169] using wordTrace_append hprefix tailTrace_135169
  have hstable : (prefixWord ++ tailWord_135169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135169).length < 2 ^ (prefixWord ++ tailWord_135169).sum := by decide
  have hdescent : baseEnd_135169 < baseStart_135169 := by decide
  rcases family_descends (prefixWord ++ tailWord_135169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135179 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 1, 7, 2]
def baseStart_135179 : Nat := 118140960795 + 135179 * 2 ^ 59
def prefixEnd_135179 : Nat := 4983230072969 + 3 ^ 40 * 135179 * 2
def baseEnd_135179 : Nat := 69411801394231845240829

theorem tailTrace_135179 : CollatzResearch.WordTrace tailWord_135179 prefixEnd_135179 69411801394231845240829 := by
  unfold tailWord_135179
  simp only [CollatzResearch.WordTrace]
  refine ⟨4930383177277044580280591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3286922118184696386853727 4930383177277044580280591)
  ·
    refine ⟨7395574765915566870420887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4930383177277044580280591 7395574765915566870420887)
    ·
      refine ⟨11093362148873350305631331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7395574765915566870420887 11093362148873350305631331)
      ·
        refine ⟨16640043223310025458446997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11093362148873350305631331 16640043223310025458446997)
        ·
          refine ⟨780002026092657443364703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16640043223310025458446997 780002026092657443364703)
          ·
            refine ⟨1170003039138986165047055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 780002026092657443364703 1170003039138986165047055)
            ·
              refine ⟨1755004558708479247570583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1170003039138986165047055 1755004558708479247570583)
              ·
                refine ⟨2632506838062718871355875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1755004558708479247570583 2632506838062718871355875)
                ·
                  refine ⟨3948760257094078307033813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2632506838062718871355875 3948760257094078307033813)
                  ·
                    refine ⟨92549068525642460321105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3948760257094078307033813 92549068525642460321105)
                    ·
                      refine ⟨69411801394231845240829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 92549068525642460321105 69411801394231845240829)
                      ·
                        rfl

theorem cell23_135179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 7, 2].length) (baseStart_135179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135179 prefixEnd_135179 := by exact prefixLift 135179
  have htrace : WordTrace (prefixWord ++ tailWord_135179) baseStart_135179 baseEnd_135179 := by
    simpa [prefixWord, tailWord_135179, baseEnd_135179] using wordTrace_append hprefix tailTrace_135179
  have hstable : (prefixWord ++ tailWord_135179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135179).length < 2 ^ (prefixWord ++ tailWord_135179).sum := by decide
  have hdescent : baseEnd_135179 < baseStart_135179 := by decide
  rcases family_descends (prefixWord ++ tailWord_135179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135212 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 5]
def baseStart_135212 : Nat := 118140960795 + 135212 * 2 ^ 59
def prefixEnd_135212 : Nat := 4983230072969 + 3 ^ 40 * 135212 * 2
def baseEnd_135212 : Nat := 69428746255830216128177

theorem tailTrace_135212 : CollatzResearch.WordTrace tailWord_135212 prefixEnd_135212 69428746255830216128177 := by
  unfold tailWord_135212
  simp only [CollatzResearch.WordTrace]
  refine ⟨2465793393078745608115945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3287724524104994144154593 2465793393078745608115945)
  ·
    refine ⟨1849345044809059206086959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2465793393078745608115945 1849345044809059206086959)
    ·
      refine ⟨2774017567213588809130439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1849345044809059206086959 2774017567213588809130439)
      ·
        refine ⟨4161026350820383213695659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2774017567213588809130439 4161026350820383213695659)
        ·
          refine ⟨6241539526230574820543489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4161026350820383213695659 6241539526230574820543489)
          ·
            refine ⟨4681154644672931115407617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6241539526230574820543489 4681154644672931115407617)
            ·
              refine ⟨3510865983504698336555713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4681154644672931115407617 3510865983504698336555713)
              ·
                refine ⟨2633149487628523752416785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3510865983504698336555713 2633149487628523752416785)
                ·
                  refine ⟨1974862115721392814312589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2633149487628523752416785 1974862115721392814312589)
                  ·
                    refine ⟨740573293395522305367221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1974862115721392814312589 740573293395522305367221)
                    ·
                      refine ⟨69428746255830216128177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 740573293395522305367221 69428746255830216128177)
                      ·
                        rfl

theorem cell23_135212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_135212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135212 prefixEnd_135212 := by exact prefixLift 135212
  have htrace : WordTrace (prefixWord ++ tailWord_135212) baseStart_135212 baseEnd_135212 := by
    simpa [prefixWord, tailWord_135212, baseEnd_135212] using wordTrace_append hprefix tailTrace_135212
  have hstable : (prefixWord ++ tailWord_135212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135212).length < 2 ^ (prefixWord ++ tailWord_135212).sum := by decide
  have hdescent : baseEnd_135212 < baseStart_135212 := by decide
  rcases family_descends (prefixWord ++ tailWord_135212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135293 : List Nat := [1, 4, 1, 1, 3, 2, 3, 1, 3, 1, 3]
def baseStart_135293 : Nat := 118140960795 + 135293 * 2 ^ 59
def prefixEnd_135293 : Nat := 4983230072969 + 3 ^ 40 * 135293 * 2
def baseEnd_135293 : Nat := 69470338188844399215305

theorem tailTrace_135293 : CollatzResearch.WordTrace tailWord_135293 prefixEnd_135293 69470338188844399215305 := by
  unfold tailWord_135293
  simp only [CollatzResearch.WordTrace]
  refine ⟨4934541098864042049930533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3289694065909361366620355 4934541098864042049930533)
  ·
    refine ⟨925226456037007884361975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4934541098864042049930533 925226456037007884361975)
    ·
      refine ⟨1387839684055511826542963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 925226456037007884361975 1387839684055511826542963)
      ·
        refine ⟨2081759526083267739814445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1387839684055511826542963 2081759526083267739814445)
        ·
          refine ⟨780659822281225402430417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2081759526083267739814445 780659822281225402430417)
          ·
            refine ⟨585494866710919051822813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 780659822281225402430417 585494866710919051822813)
            ·
              refine ⟨219560575016594644433555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 585494866710919051822813 219560575016594644433555)
              ·
                refine ⟨329340862524891966650333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219560575016594644433555 329340862524891966650333)
                ·
                  refine ⟨123502823446834487493875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 329340862524891966650333 123502823446834487493875)
                  ·
                    refine ⟨185254235170251731240813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 123502823446834487493875 185254235170251731240813)
                    ·
                      refine ⟨69470338188844399215305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 185254235170251731240813 69470338188844399215305)
                      ·
                        rfl

theorem cell23_135293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_135293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135293 prefixEnd_135293 := by exact prefixLift 135293
  have htrace : WordTrace (prefixWord ++ tailWord_135293) baseStart_135293 baseEnd_135293 := by
    simpa [prefixWord, tailWord_135293, baseEnd_135293] using wordTrace_append hprefix tailTrace_135293
  have hstable : (prefixWord ++ tailWord_135293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135293).length < 2 ^ (prefixWord ++ tailWord_135293).sum := by decide
  have hdescent : baseEnd_135293 < baseStart_135293 := by decide
  rcases family_descends (prefixWord ++ tailWord_135293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135320 : List Nat := [2, 1, 2, 4, 3, 1, 2, 1, 2, 3, 2]
def baseStart_135320 : Nat := 118140960795 + 135320 * 2 ^ 59
def prefixEnd_135320 : Nat := 4983230072969 + 3 ^ 40 * 135320 * 2
def baseEnd_135320 : Nat := 69484202166515793577681

theorem tailTrace_135320 : CollatzResearch.WordTrace tailWord_135320 prefixEnd_135320 69484202166515793577681 := by
  unfold tailWord_135320
  simp only [CollatzResearch.WordTrace]
  refine ⟨2467762934883112830581707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3290350579844150440775609 2467762934883112830581707)
  ·
    refine ⟨3701644402324669245872561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2467762934883112830581707 3701644402324669245872561)
    ·
      refine ⟨2776233301743501934404421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3701644402324669245872561 2776233301743501934404421)
      ·
        refine ⟨520543744076906612700829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2776233301743501934404421 520543744076906612700829)
        ·
          refine ⟨195203904028839979762811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 520543744076906612700829 195203904028839979762811)
          ·
            refine ⟨292805856043259969644217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195203904028839979762811 292805856043259969644217)
            ·
              refine ⟨219604392032444977233163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 292805856043259969644217 219604392032444977233163)
              ·
                refine ⟨329406588048667465849745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219604392032444977233163 329406588048667465849745)
                ·
                  refine ⟨247054941036500599387309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 329406588048667465849745 247054941036500599387309)
                  ·
                    refine ⟨92645602888687724770241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 247054941036500599387309 92645602888687724770241)
                    ·
                      refine ⟨69484202166515793577681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 92645602888687724770241 69484202166515793577681)
                      ·
                        rfl

theorem cell23_135320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_135320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135320 prefixEnd_135320 := by exact prefixLift 135320
  have htrace : WordTrace (prefixWord ++ tailWord_135320) baseStart_135320 baseEnd_135320 := by
    simpa [prefixWord, tailWord_135320, baseEnd_135320] using wordTrace_append hprefix tailTrace_135320
  have hstable : (prefixWord ++ tailWord_135320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135320).length < 2 ^ (prefixWord ++ tailWord_135320).sum := by decide
  have hdescent : baseEnd_135320 < baseStart_135320 := by decide
  rcases family_descends (prefixWord ++ tailWord_135320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135330 : List Nat := [3, 3, 1, 3, 1, 2, 3, 1, 1, 5]
def baseStart_135330 : Nat := 118140960795 + 135330 * 2 ^ 59
def prefixEnd_135330 : Nat := 4983230072969 + 3 ^ 40 * 135330 * 2
def baseEnd_135330 : Nat := 23163112324353584817545

theorem tailTrace_135330 : CollatzResearch.WordTrace tailWord_135330 prefixEnd_135330 23163112324353584817545 := by
  unfold tailWord_135330
  simp only [CollatzResearch.WordTrace]
  refine ⟨1233972649932499342256861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3290593733153331579351629 1233972649932499342256861)
  ·
    refine ⟨462739743724687253346323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1233972649932499342256861 462739743724687253346323)
    ·
      refine ⟨694109615587030880019485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 462739743724687253346323 694109615587030880019485)
      ·
        refine ⟨260291105845136580007307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 694109615587030880019485 260291105845136580007307)
        ·
          refine ⟨390436658767704870010961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260291105845136580007307 390436658767704870010961)
          ·
            refine ⟨292827494075778652508221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 390436658767704870010961 292827494075778652508221)
            ·
              refine ⟨109810310278416994690583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 292827494075778652508221 109810310278416994690583)
              ·
                refine ⟨164715465417625492035875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109810310278416994690583 164715465417625492035875)
                ·
                  refine ⟨247073198126438238053813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164715465417625492035875 247073198126438238053813)
                  ·
                    refine ⟨23163112324353584817545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 247073198126438238053813 23163112324353584817545)
                    ·
                      rfl

theorem cell23_135330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_135330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135330 prefixEnd_135330 := by exact prefixLift 135330
  have htrace : WordTrace (prefixWord ++ tailWord_135330) baseStart_135330 baseEnd_135330 := by
    simpa [prefixWord, tailWord_135330, baseEnd_135330] using wordTrace_append hprefix tailTrace_135330
  have hstable : (prefixWord ++ tailWord_135330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135330).length < 2 ^ (prefixWord ++ tailWord_135330).sum := by decide
  have hdescent : baseEnd_135330 < baseStart_135330 := by decide
  rcases family_descends (prefixWord ++ tailWord_135330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135333 : List Nat := [1, 3, 1, 2, 1, 3, 5, 1, 1, 1, 4]
def baseStart_135333 : Nat := 118140960795 + 135333 * 2 ^ 59
def prefixEnd_135333 : Nat := 4983230072969 + 3 ^ 40 * 135333 * 2
def baseEnd_135333 : Nat := 69490877415024242715121

theorem tailTrace_135333 : CollatzResearch.WordTrace tailWord_135333 prefixEnd_135333 69490877415024242715121 := by
  unfold tailWord_135333
  simp only [CollatzResearch.WordTrace]
  refine ⟨4936000018719128881386653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3290666679146085920924435 4936000018719128881386653)
  ·
    refine ⟨1851000007019673330519995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4936000018719128881386653 1851000007019673330519995)
    ·
      refine ⟨2776500010529509995779993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1851000007019673330519995 2776500010529509995779993)
      ·
        refine ⟨2082375007897132496834995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2776500010529509995779993 2082375007897132496834995)
        ·
          refine ⟨3123562511845698745252493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2082375007897132496834995 3123562511845698745252493)
          ·
            refine ⟨1171335941942137029469685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3123562511845698745252493 1171335941942137029469685)
            ·
              refine ⟨109812744557075346512783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1171335941942137029469685 109812744557075346512783)
              ·
                refine ⟨164719116835613019769175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109812744557075346512783 164719116835613019769175)
                ·
                  refine ⟨247078675253419529653763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164719116835613019769175 247078675253419529653763)
                  ·
                    refine ⟨370618012880129294480645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 247078675253419529653763 370618012880129294480645)
                    ·
                      refine ⟨69490877415024242715121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 370618012880129294480645 69490877415024242715121)
                      ·
                        rfl

theorem cell23_135333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 1, 1, 4].length) (baseStart_135333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135333 prefixEnd_135333 := by exact prefixLift 135333
  have htrace : WordTrace (prefixWord ++ tailWord_135333) baseStart_135333 baseEnd_135333 := by
    simpa [prefixWord, tailWord_135333, baseEnd_135333] using wordTrace_append hprefix tailTrace_135333
  have hstable : (prefixWord ++ tailWord_135333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135333).length < 2 ^ (prefixWord ++ tailWord_135333).sum := by decide
  have hdescent : baseEnd_135333 < baseStart_135333 := by decide
  rcases family_descends (prefixWord ++ tailWord_135333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135400 : List Nat := [2, 1, 4, 1, 2, 2, 3, 2, 2, 1, 3]
def baseStart_135400 : Nat := 118140960795 + 135400 * 2 ^ 59
def prefixEnd_135400 : Nat := 4983230072969 + 3 ^ 40 * 135400 * 2
def baseEnd_135400 : Nat := 69525280618875480577313

theorem tailTrace_135400 : CollatzResearch.WordTrace tailWord_135400 prefixEnd_135400 69525280618875480577313 := by
  unfold tailWord_135400
  simp only [CollatzResearch.WordTrace]
  refine ⟨2469221854738199662037827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3292295806317599549383769 2469221854738199662037827)
  ·
    refine ⟨3703832782107299493056741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2469221854738199662037827 3703832782107299493056741)
    ·
      refine ⟨694468646645118654948139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3703832782107299493056741 694468646645118654948139)
      ·
        refine ⟨1041702969967677982422209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 694468646645118654948139 1041702969967677982422209)
        ·
          refine ⟨781277227475758486816657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1041702969967677982422209 781277227475758486816657)
          ·
            refine ⟨585957920606818865112493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 781277227475758486816657 585957920606818865112493)
            ·
              refine ⟨219734220227557074417185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 585957920606818865112493 219734220227557074417185)
              ·
                refine ⟨164800665170667805812889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 219734220227557074417185 164800665170667805812889)
                ·
                  refine ⟨123600498878000854359667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164800665170667805812889 123600498878000854359667)
                  ·
                    refine ⟨185400748317001281539501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 123600498878000854359667 185400748317001281539501)
                    ·
                      refine ⟨69525280618875480577313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 185400748317001281539501 69525280618875480577313)
                      ·
                        rfl

theorem cell23_135400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_135400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135400 prefixEnd_135400 := by exact prefixLift 135400
  have htrace : WordTrace (prefixWord ++ tailWord_135400) baseStart_135400 baseEnd_135400 := by
    simpa [prefixWord, tailWord_135400, baseEnd_135400] using wordTrace_append hprefix tailTrace_135400
  have hstable : (prefixWord ++ tailWord_135400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135400).length < 2 ^ (prefixWord ++ tailWord_135400).sum := by decide
  have hdescent : baseEnd_135400 < baseStart_135400 := by decide
  rcases family_descends (prefixWord ++ tailWord_135400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135429 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 9]
def baseStart_135429 : Nat := 118140960795 + 135429 * 2 ^ 59
def prefixEnd_135429 : Nat := 4983230072969 + 3 ^ 40 * 135429 * 2
def baseEnd_135429 : Nat := 7726685728650651901631

theorem tailTrace_135429 : CollatzResearch.WordTrace tailWord_135429 prefixEnd_135429 7726685728650651901631 := by
  unfold tailWord_135429
  simp only [CollatzResearch.WordTrace]
  refine ⟨4939501426371337276881341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3293000950914224851254227 4939501426371337276881341)
  ·
    refine ⟨1852313034889251478830503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4939501426371337276881341 1852313034889251478830503)
    ·
      refine ⟨2778469552333877218245755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1852313034889251478830503 2778469552333877218245755)
      ·
        refine ⟨4167704328500815827368633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2778469552333877218245755 4167704328500815827368633)
        ·
          refine ⟨3125778246375611870526475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4167704328500815827368633 3125778246375611870526475)
          ·
            refine ⟨4688667369563417805789713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3125778246375611870526475 4688667369563417805789713)
            ·
              refine ⟨3516500527172563354342285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4688667369563417805789713 3516500527172563354342285)
              ·
                refine ⟨1318687697689711257878357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3516500527172563354342285 1318687697689711257878357)
                ·
                  refine ⟨7726685728650651901631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1318687697689711257878357 7726685728650651901631)
                  ·
                    rfl

theorem cell23_135429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 9].length) (baseStart_135429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135429 prefixEnd_135429 := by exact prefixLift 135429
  have htrace : WordTrace (prefixWord ++ tailWord_135429) baseStart_135429 baseEnd_135429 := by
    simpa [prefixWord, tailWord_135429, baseEnd_135429] using wordTrace_append hprefix tailTrace_135429
  have hstable : (prefixWord ++ tailWord_135429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135429).length < 2 ^ (prefixWord ++ tailWord_135429).sum := by decide
  have hdescent : baseEnd_135429 < baseStart_135429 := by decide
  rcases family_descends (prefixWord ++ tailWord_135429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135449 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 1, 6, 6]
def baseStart_135449 : Nat := 118140960795 + 135449 * 2 ^ 59
def prefixEnd_135449 : Nat := 4983230072969 + 3 ^ 40 * 135449 * 2
def baseEnd_135449 : Nat := 69550441170945788864587

theorem tailTrace_135449 : CollatzResearch.WordTrace tailWord_135449 prefixEnd_135449 69550441170945788864587 := by
  unfold tailWord_135449
  simp only [CollatzResearch.WordTrace]
  refine ⟨4940230886298880692609401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3293487257532587128406267 4940230886298880692609401)
  ·
    refine ⟨3705173164724160519457051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4940230886298880692609401 3705173164724160519457051)
    ·
      refine ⟨5557759747086240779185577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3705173164724160519457051 5557759747086240779185577)
      ·
        refine ⟨4168319810314680584389183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5557759747086240779185577 4168319810314680584389183)
        ·
          refine ⟨6252479715472020876583775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4168319810314680584389183 6252479715472020876583775)
          ·
            refine ⟨9378719573208031314875663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6252479715472020876583775 9378719573208031314875663)
            ·
              refine ⟨14068079359812046972313495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9378719573208031314875663 14068079359812046972313495)
              ·
                refine ⟨21102119039718070458470243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14068079359812046972313495 21102119039718070458470243)
                ·
                  refine ⟨31653178559577105687705365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21102119039718070458470243 31653178559577105687705365)
                  ·
                    refine ⟨1483742744980176829111189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31653178559577105687705365 1483742744980176829111189)
                    ·
                      refine ⟨69550441170945788864587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1483742744980176829111189 69550441170945788864587)
                      ·
                        rfl

theorem cell23_135449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_135449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135449 prefixEnd_135449 := by exact prefixLift 135449
  have htrace : WordTrace (prefixWord ++ tailWord_135449) baseStart_135449 baseEnd_135449 := by
    simpa [prefixWord, tailWord_135449, baseEnd_135449] using wordTrace_append hprefix tailTrace_135449
  have hstable : (prefixWord ++ tailWord_135449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135449).length < 2 ^ (prefixWord ++ tailWord_135449).sum := by decide
  have hdescent : baseEnd_135449 < baseStart_135449 := by decide
  rcases family_descends (prefixWord ++ tailWord_135449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135496 : List Nat := [2, 1, 3, 1, 1, 2, 2, 3, 1, 3, 4]
def baseStart_135496 : Nat := 118140960795 + 135496 * 2 ^ 59
def prefixEnd_135496 : Nat := 4983230072969 + 3 ^ 40 * 135496 * 2
def baseEnd_135496 : Nat := 69574574761707104976871

theorem tailTrace_135496 : CollatzResearch.WordTrace tailWord_135496 prefixEnd_135496 69574574761707104976871 := by
  unfold tailWord_135496
  simp only [CollatzResearch.WordTrace]
  refine ⟨2470972558564303859785171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3294630078085738479713561 2470972558564303859785171)
  ·
    refine ⟨3706458837846455789677757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2470972558564303859785171 3706458837846455789677757)
    ·
      refine ⟨1389922064192420921129159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3706458837846455789677757 1389922064192420921129159)
      ·
        refine ⟨2084883096288631381693739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1389922064192420921129159 2084883096288631381693739)
        ·
          refine ⟨3127324644432947072540609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2084883096288631381693739 3127324644432947072540609)
          ·
            refine ⟨2345493483324710304405457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3127324644432947072540609 2345493483324710304405457)
            ·
              refine ⟨1759120112493532728304093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2345493483324710304405457 1759120112493532728304093)
              ·
                refine ⟨659670042185074773114035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1759120112493532728304093 659670042185074773114035)
                ·
                  refine ⟨989505063277612159671053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 659670042185074773114035 989505063277612159671053)
                  ·
                    refine ⟨371064398729104559876645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 989505063277612159671053 371064398729104559876645)
                    ·
                      refine ⟨69574574761707104976871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 371064398729104559876645 69574574761707104976871)
                      ·
                        rfl

theorem cell23_135496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_135496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135496 prefixEnd_135496 := by exact prefixLift 135496
  have htrace : WordTrace (prefixWord ++ tailWord_135496) baseStart_135496 baseEnd_135496 := by
    simpa [prefixWord, tailWord_135496, baseEnd_135496] using wordTrace_append hprefix tailTrace_135496
  have hstable : (prefixWord ++ tailWord_135496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135496).length < 2 ^ (prefixWord ++ tailWord_135496).sum := by decide
  have hdescent : baseEnd_135496 < baseStart_135496 := by decide
  rcases family_descends (prefixWord ++ tailWord_135496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135513 : List Nat := [1, 2, 1, 2, 2, 2, 1, 4, 2, 4, 2]
def baseStart_135513 : Nat := 118140960795 + 135513 * 2 ^ 59
def prefixEnd_135513 : Nat := 4983230072969 + 3 ^ 40 * 135513 * 2
def baseEnd_135513 : Nat := 69583303932833538464293

theorem tailTrace_135513 : CollatzResearch.WordTrace tailWord_135513 prefixEnd_135513 69583303932833538464293 := by
  unfold tailWord_135513
  simp only [CollatzResearch.WordTrace]
  refine ⟨4942565158067019622939193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3295043438711346415292795 4942565158067019622939193)
  ·
    refine ⟨3706923868550264717204395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4942565158067019622939193 3706923868550264717204395)
    ·
      refine ⟨5560385802825397075806593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3706923868550264717204395 5560385802825397075806593)
      ·
        refine ⟨4170289352119047806854945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5560385802825397075806593 4170289352119047806854945)
        ·
          refine ⟨3127717014089285855141209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4170289352119047806854945 3127717014089285855141209)
          ·
            refine ⟨2345787760566964391355907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3127717014089285855141209 2345787760566964391355907)
            ·
              refine ⟨3518681640850446587033861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2345787760566964391355907 3518681640850446587033861)
              ·
                refine ⟨659752807659458735068849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3518681640850446587033861 659752807659458735068849)
                ·
                  refine ⟨494814605744594051301637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 659752807659458735068849 494814605744594051301637)
                  ·
                    refine ⟨92777738577111384619057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 494814605744594051301637 92777738577111384619057)
                    ·
                      refine ⟨69583303932833538464293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 92777738577111384619057 69583303932833538464293)
                      ·
                        rfl

theorem cell23_135513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 4, 2].length) (baseStart_135513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135513 prefixEnd_135513 := by exact prefixLift 135513
  have htrace : WordTrace (prefixWord ++ tailWord_135513) baseStart_135513 baseEnd_135513 := by
    simpa [prefixWord, tailWord_135513, baseEnd_135513] using wordTrace_append hprefix tailTrace_135513
  have hstable : (prefixWord ++ tailWord_135513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135513).length < 2 ^ (prefixWord ++ tailWord_135513).sum := by decide
  have hdescent : baseEnd_135513 < baseStart_135513 := by decide
  rcases family_descends (prefixWord ++ tailWord_135513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135523 : List Nat := [1, 1, 1, 5, 2, 1, 2, 3, 3, 4]
def baseStart_135523 : Nat := 118140960795 + 135523 * 2 ^ 59
def prefixEnd_135523 : Nat := 4983230072969 + 3 ^ 40 * 135523 * 2
def baseEnd_135523 : Nat := 23196146246459499779749

theorem tailTrace_135523 : CollatzResearch.WordTrace tailWord_135523 prefixEnd_135523 23196146246459499779749 := by
  unfold tailWord_135523
  simp only [CollatzResearch.WordTrace]
  refine ⟨4942929888030791330803223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3295286592020527553868815 4942929888030791330803223)
  ·
    refine ⟨7414394832046186996204835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4942929888030791330803223 7414394832046186996204835)
    ·
      refine ⟨11121592248069280494307253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7414394832046186996204835 11121592248069280494307253)
      ·
        refine ⟨1042649273256495046341305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11121592248069280494307253 1042649273256495046341305)
        ·
          refine ⟨781986954942371284755979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1042649273256495046341305 781986954942371284755979)
          ·
            refine ⟨1172980432413556927133969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 781986954942371284755979 1172980432413556927133969)
            ·
              refine ⟨879735324310167695350477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1172980432413556927133969 879735324310167695350477)
              ·
                refine ⟨329900746616312885756429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 879735324310167695350477 329900746616312885756429)
                ·
                  refine ⟨123712779981117332158661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 329900746616312885756429 123712779981117332158661)
                  ·
                    refine ⟨23196146246459499779749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 123712779981117332158661 23196146246459499779749)
                    ·
                      rfl

theorem cell23_135523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3, 4].length) (baseStart_135523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135523 prefixEnd_135523 := by exact prefixLift 135523
  have htrace : WordTrace (prefixWord ++ tailWord_135523) baseStart_135523 baseEnd_135523 := by
    simpa [prefixWord, tailWord_135523, baseEnd_135523] using wordTrace_append hprefix tailTrace_135523
  have hstable : (prefixWord ++ tailWord_135523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135523).length < 2 ^ (prefixWord ++ tailWord_135523).sum := by decide
  have hdescent : baseEnd_135523 < baseStart_135523 := by decide
  rcases family_descends (prefixWord ++ tailWord_135523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135530 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 1, 6, 2]
def baseStart_135530 : Nat := 118140960795 + 135530 * 2 ^ 59
def prefixEnd_135530 : Nat := 4983230072969 + 3 ^ 40 * 135530 * 2
def baseEnd_135530 : Nat := 69592033103959971951715

theorem tailTrace_135530 : CollatzResearch.WordTrace tailWord_135530 prefixEnd_135530 69592033103959971951715 := by
  unfold tailWord_135530
  simp only [CollatzResearch.WordTrace]
  refine ⟨1235796299751357881577011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3295456799336954350872029 1235796299751357881577011)
  ·
    refine ⟨1853694449627036822365517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1235796299751357881577011 1853694449627036822365517)
    ·
      refine ⟨695135418610138808387069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1853694449627036822365517 695135418610138808387069)
      ·
        refine ⟨260675781978802053145151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 695135418610138808387069 260675781978802053145151)
        ·
          refine ⟨391013672968203079717727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260675781978802053145151 391013672968203079717727)
          ·
            refine ⟨586520509452304619576591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391013672968203079717727 586520509452304619576591)
            ·
              refine ⟨879780764178456929364887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 586520509452304619576591 879780764178456929364887)
              ·
                refine ⟨1319671146267685394047331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 879780764178456929364887 1319671146267685394047331)
                ·
                  refine ⟨1979506719401528091070997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1319671146267685394047331 1979506719401528091070997)
                  ·
                    refine ⟨92789377471946629268953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1979506719401528091070997 92789377471946629268953)
                    ·
                      refine ⟨69592033103959971951715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 92789377471946629268953 69592033103959971951715)
                      ·
                        rfl

theorem cell23_135530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_135530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135530 prefixEnd_135530 := by exact prefixLift 135530
  have htrace : WordTrace (prefixWord ++ tailWord_135530) baseStart_135530 baseEnd_135530 := by
    simpa [prefixWord, tailWord_135530, baseEnd_135530] using wordTrace_append hprefix tailTrace_135530
  have hstable : (prefixWord ++ tailWord_135530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135530).length < 2 ^ (prefixWord ++ tailWord_135530).sum := by decide
  have hdescent : baseEnd_135530 < baseStart_135530 := by decide
  rcases family_descends (prefixWord ++ tailWord_135530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135533 : List Nat := [1, 5, 1, 1, 1, 2, 2, 2, 1, 4, 3]
def baseStart_135533 : Nat := 118140960795 + 135533 * 2 ^ 59
def prefixEnd_135533 : Nat := 4983230072969 + 3 ^ 40 * 135533 * 2
def baseEnd_135533 : Nat := 69593573545923460214201

theorem tailTrace_135533 : CollatzResearch.WordTrace tailWord_135533 prefixEnd_135533 69593573545923460214201 := by
  unfold tailWord_135533
  simp only [CollatzResearch.WordTrace]
  refine ⟨4943294617994563038667253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3295529745329708692444835 4943294617994563038667253)
  ·
    refine ⟨463433870436990284875055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4943294617994563038667253 463433870436990284875055)
    ·
      refine ⟨695150805655485427312583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 463433870436990284875055 695150805655485427312583)
      ·
        refine ⟨1042726208483228140968875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 695150805655485427312583 1042726208483228140968875)
        ·
          refine ⟨1564089312724842211453313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1042726208483228140968875 1564089312724842211453313)
          ·
            refine ⟨1173066984543631658589985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1564089312724842211453313 1173066984543631658589985)
            ·
              refine ⟨879800238407723743942489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1173066984543631658589985 879800238407723743942489)
              ·
                refine ⟨659850178805792807956867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 879800238407723743942489 659850178805792807956867)
                ·
                  refine ⟨989775268208689211935301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 659850178805792807956867 989775268208689211935301)
                  ·
                    refine ⟨185582862789129227237869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 989775268208689211935301 185582862789129227237869)
                    ·
                      refine ⟨69593573545923460214201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 185582862789129227237869 69593573545923460214201)
                      ·
                        rfl

theorem cell23_135533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_135533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135533 prefixEnd_135533 := by exact prefixLift 135533
  have htrace : WordTrace (prefixWord ++ tailWord_135533) baseStart_135533 baseEnd_135533 := by
    simpa [prefixWord, tailWord_135533, baseEnd_135533] using wordTrace_append hprefix tailTrace_135533
  have hstable : (prefixWord ++ tailWord_135533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135533).length < 2 ^ (prefixWord ++ tailWord_135533).sum := by decide
  have hdescent : baseEnd_135533 < baseStart_135533 := by decide
  rcases family_descends (prefixWord ++ tailWord_135533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135614 : List Nat := [4, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3]
def baseStart_135614 : Nat := 118140960795 + 135614 * 2 ^ 59
def prefixEnd_135614 : Nat := 4983230072969 + 3 ^ 40 * 135614 * 2
def baseEnd_135614 : Nat := 69635165478937643301329

theorem tailTrace_135614 : CollatzResearch.WordTrace tailWord_135614 prefixEnd_135614 69635165478937643301329 := by
  unfold tailWord_135614
  simp only [CollatzResearch.WordTrace]
  refine ⟨618281116337639234045737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3297499287134075914910597 618281116337639234045737)
  ·
    refine ⟨463710837253229425534303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 618281116337639234045737 463710837253229425534303)
    ·
      refine ⟨695566255879844138301455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 463710837253229425534303 695566255879844138301455)
      ·
        refine ⟨1043349383819766207452183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 695566255879844138301455 1043349383819766207452183)
        ·
          refine ⟨1565024075729649311178275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1043349383819766207452183 1565024075729649311178275)
          ·
            refine ⟨2347536113594473966767413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1565024075729649311178275 2347536113594473966767413)
            ·
              refine ⟨220081510649481934384445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2347536113594473966767413 220081510649481934384445)
              ·
                refine ⟨82530566493555725394167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 220081510649481934384445 82530566493555725394167)
                ·
                  refine ⟨123795849740333588091251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82530566493555725394167 123795849740333588091251)
                  ·
                    refine ⟨185693774610500382136877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 123795849740333588091251 185693774610500382136877)
                    ·
                      refine ⟨69635165478937643301329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 185693774610500382136877 69635165478937643301329)
                      ·
                        rfl

theorem cell23_135614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_135614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135614 prefixEnd_135614 := by exact prefixLift 135614
  have htrace : WordTrace (prefixWord ++ tailWord_135614) baseStart_135614 baseEnd_135614 := by
    simpa [prefixWord, tailWord_135614, baseEnd_135614] using wordTrace_append hprefix tailTrace_135614
  have hstable : (prefixWord ++ tailWord_135614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135614).length < 2 ^ (prefixWord ++ tailWord_135614).sum := by decide
  have hdescent : baseEnd_135614 < baseStart_135614 := by decide
  rcases family_descends (prefixWord ++ tailWord_135614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135623 : List Nat := [1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 5]
def baseStart_135623 : Nat := 118140960795 + 135623 * 2 ^ 59
def prefixEnd_135623 : Nat := 4983230072969 + 3 ^ 40 * 135623 * 2
def baseEnd_135623 : Nat := 69639786804828108088787

theorem tailTrace_135623 : CollatzResearch.WordTrace tailWord_135623 prefixEnd_135623 69639786804828108088787 := by
  unfold tailWord_135623
  simp only [CollatzResearch.WordTrace]
  refine ⟨4946577187668508409443523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3297718125112338939629015 4946577187668508409443523)
  ·
    refine ⟨7419865781502762614165285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4946577187668508409443523 7419865781502762614165285)
    ·
      refine ⟨1391224834031767990155991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7419865781502762614165285 1391224834031767990155991)
      ·
        refine ⟨2086837251047651985233987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1391224834031767990155991 2086837251047651985233987)
        ·
          refine ⟨3130255876571477977850981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2086837251047651985233987 3130255876571477977850981)
          ·
            refine ⟨586922976857152120847059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3130255876571477977850981 586922976857152120847059)
            ·
              refine ⟨880384465285728181270589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 586922976857152120847059 880384465285728181270589)
              ·
                refine ⟨330144174482148067976471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 880384465285728181270589 330144174482148067976471)
                ·
                  refine ⟨495216261723222101964707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 330144174482148067976471 495216261723222101964707)
                  ·
                    refine ⟨742824392584833152947061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 495216261723222101964707 742824392584833152947061)
                    ·
                      refine ⟨69639786804828108088787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 742824392584833152947061 69639786804828108088787)
                      ·
                        rfl

theorem cell23_135623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_135623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135623 prefixEnd_135623 := by exact prefixLift 135623
  have htrace : WordTrace (prefixWord ++ tailWord_135623) baseStart_135623 baseEnd_135623 := by
    simpa [prefixWord, tailWord_135623, baseEnd_135623] using wordTrace_append hprefix tailTrace_135623
  have hstable : (prefixWord ++ tailWord_135623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135623).length < 2 ^ (prefixWord ++ tailWord_135623).sum := by decide
  have hdescent : baseEnd_135623 < baseStart_135623 := by decide
  rcases family_descends (prefixWord ++ tailWord_135623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135630 : List Nat := [4, 1, 1, 1, 2, 1, 1, 6, 2, 4]
def baseStart_135630 : Nat := 118140960795 + 135630 * 2 ^ 59
def prefixEnd_135630 : Nat := 4983230072969 + 3 ^ 40 * 135630 * 2
def baseEnd_135630 : Nat := 23214460389803193567085

theorem tailTrace_135630 : CollatzResearch.WordTrace tailWord_135630 prefixEnd_135630 23214460389803193567085 := by
  unfold tailWord_135630
  simp only [CollatzResearch.WordTrace]
  refine ⟨618354062330393575618543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3297888332428765736632229 618354062330393575618543)
  ·
    refine ⟨927531093495590363427815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 618354062330393575618543 927531093495590363427815)
    ·
      refine ⟨1391296640243385545141723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 927531093495590363427815 1391296640243385545141723)
      ·
        refine ⟨2086944960365078317712585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1391296640243385545141723 2086944960365078317712585)
        ·
          refine ⟨1565208720273808738284439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2086944960365078317712585 1565208720273808738284439)
          ·
            refine ⟨2347813080410713107426659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1565208720273808738284439 2347813080410713107426659)
            ·
              refine ⟨3521719620616069661139989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2347813080410713107426659 3521719620616069661139989)
              ·
                refine ⟨165080607216378265365937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3521719620616069661139989 165080607216378265365937)
                ·
                  refine ⟨123810455412283699024453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165080607216378265365937 123810455412283699024453)
                  ·
                    refine ⟨23214460389803193567085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 123810455412283699024453 23214460389803193567085)
                    ·
                      rfl

theorem cell23_135630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_135630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135630 prefixEnd_135630 := by exact prefixLift 135630
  have htrace : WordTrace (prefixWord ++ tailWord_135630) baseStart_135630 baseEnd_135630 := by
    simpa [prefixWord, tailWord_135630, baseEnd_135630] using wordTrace_append hprefix tailTrace_135630
  have hstable : (prefixWord ++ tailWord_135630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135630).length < 2 ^ (prefixWord ++ tailWord_135630).sum := by decide
  have hdescent : baseEnd_135630 < baseStart_135630 := by decide
  rcases family_descends (prefixWord ++ tailWord_135630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135647 : List Nat := [1, 1, 2, 3, 3, 2, 4, 1, 2, 4]
def baseStart_135647 : Nat := 118140960795 + 135647 * 2 ^ 59
def prefixEnd_135647 : Nat := 4983230072969 + 3 ^ 40 * 135647 * 2
def baseEnd_135647 : Nat := 23217370113512004729559

theorem tailTrace_135647 : CollatzResearch.WordTrace tailWord_135647 prefixEnd_135647 23217370113512004729559 := by
  unfold tailWord_135647
  simp only [CollatzResearch.WordTrace]
  refine ⟨4947452539581560508317195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3298301693054373672211463 4947452539581560508317195)
  ·
    refine ⟨7421178809372340762475793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4947452539581560508317195 7421178809372340762475793)
    ·
      refine ⟨5565884107029255571856845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7421178809372340762475793 5565884107029255571856845)
      ·
        refine ⟨2087206540135970839446317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5565884107029255571856845 2087206540135970839446317)
        ·
          refine ⟨782702452550989064792369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2087206540135970839446317 782702452550989064792369)
          ·
            refine ⟨587026839413241798594277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 782702452550989064792369 587026839413241798594277)
            ·
              refine ⟨110067532389982837236427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 587026839413241798594277 110067532389982837236427)
              ·
                refine ⟨165101298584974255854641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110067532389982837236427 165101298584974255854641)
                ·
                  refine ⟨123825973938730691890981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165101298584974255854641 123825973938730691890981)
                  ·
                    refine ⟨23217370113512004729559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 123825973938730691890981 23217370113512004729559)
                    ·
                      rfl

theorem cell23_135647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 2, 4].length) (baseStart_135647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135647 prefixEnd_135647 := by exact prefixLift 135647
  have htrace : WordTrace (prefixWord ++ tailWord_135647) baseStart_135647 baseEnd_135647 := by
    simpa [prefixWord, tailWord_135647, baseEnd_135647] using wordTrace_append hprefix tailTrace_135647
  have hstable : (prefixWord ++ tailWord_135647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135647).length < 2 ^ (prefixWord ++ tailWord_135647).sum := by decide
  have hdescent : baseEnd_135647 < baseStart_135647 := by decide
  rcases family_descends (prefixWord ++ tailWord_135647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135725 : List Nat := [1, 5, 4, 1, 1, 2, 2, 1, 1, 2, 3]
def baseStart_135725 : Nat := 118140960795 + 135725 * 2 ^ 59
def prefixEnd_135725 : Nat := 4983230072969 + 3 ^ 40 * 135725 * 2
def baseEnd_135725 : Nat := 69692161831586709013319

theorem tailTrace_135725 : CollatzResearch.WordTrace tailWord_135725 prefixEnd_135725 69692161831586709013319 := by
  unfold tailWord_135725
  simp only [CollatzResearch.WordTrace]
  refine ⟨4950297433298979829656629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3300198288865986553104419 4950297433298979829656629)
  ·
    refine ⟨464090384371779359030309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4950297433298979829656629 464090384371779359030309)
    ·
      refine ⟨87016947069708629818183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 464090384371779359030309 87016947069708629818183)
      ·
        refine ⟨130525420604562944727275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87016947069708629818183 130525420604562944727275)
        ·
          refine ⟨195788130906844417090913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130525420604562944727275 195788130906844417090913)
          ·
            refine ⟨146841098180133312818185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195788130906844417090913 146841098180133312818185)
            ·
              refine ⟨110130823635099984613639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146841098180133312818185 110130823635099984613639)
              ·
                refine ⟨165196235452649976920459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110130823635099984613639 165196235452649976920459)
                ·
                  refine ⟨247794353178974965380689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165196235452649976920459 247794353178974965380689)
                  ·
                    refine ⟨185845764884231224035517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 247794353178974965380689 185845764884231224035517)
                    ·
                      refine ⟨69692161831586709013319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 185845764884231224035517 69692161831586709013319)
                      ·
                        rfl

theorem cell23_135725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_135725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135725 prefixEnd_135725 := by exact prefixLift 135725
  have htrace : WordTrace (prefixWord ++ tailWord_135725) baseStart_135725 baseEnd_135725 := by
    simpa [prefixWord, tailWord_135725, baseEnd_135725] using wordTrace_append hprefix tailTrace_135725
  have hstable : (prefixWord ++ tailWord_135725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135725).length < 2 ^ (prefixWord ++ tailWord_135725).sum := by decide
  have hdescent : baseEnd_135725 < baseStart_135725 := by decide
  rcases family_descends (prefixWord ++ tailWord_135725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135733 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 9]
def baseStart_135733 : Nat := 118140960795 + 135733 * 2 ^ 59
def prefixEnd_135733 : Nat := 4983230072969 + 3 ^ 40 * 135733 * 2
def baseEnd_135733 : Nat := 7744029964091408634809

theorem tailTrace_135733 : CollatzResearch.WordTrace tailWord_135733 prefixEnd_135733 7744029964091408634809 := by
  unfold tailWord_135733
  simp only [CollatzResearch.WordTrace]
  refine ⟨4950589217269997195947853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3300392811513331463965235 4950589217269997195947853)
  ·
    refine ⟨1856470956476248948480445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4950589217269997195947853 1856470956476248948480445)
    ·
      refine ⟨696176608678593355680167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1856470956476248948480445 696176608678593355680167)
      ·
        refine ⟨1044264913017890033520251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 696176608678593355680167 1044264913017890033520251)
        ·
          refine ⟨1566397369526835050280377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1044264913017890033520251 1566397369526835050280377)
          ·
            refine ⟨1174798027145126287710283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1566397369526835050280377 1174798027145126287710283)
            ·
              refine ⟨1762197040717689431565425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1174798027145126287710283 1762197040717689431565425)
              ·
                refine ⟨1321647780538267073674069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1762197040717689431565425 1321647780538267073674069)
                ·
                  refine ⟨7744029964091408634809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1321647780538267073674069 7744029964091408634809)
                  ·
                    rfl

theorem cell23_135733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 9].length) (baseStart_135733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135733 prefixEnd_135733 := by exact prefixLift 135733
  have htrace : WordTrace (prefixWord ++ tailWord_135733) baseStart_135733 baseEnd_135733 := by
    simpa [prefixWord, tailWord_135733, baseEnd_135733] using wordTrace_append hprefix tailTrace_135733
  have hstable : (prefixWord ++ tailWord_135733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135733).length < 2 ^ (prefixWord ++ tailWord_135733).sum := by decide
  have hdescent : baseEnd_135733 < baseStart_135733 := by decide
  rcases family_descends (prefixWord ++ tailWord_135733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135740 : List Nat := [2, 2, 2, 2, 3, 1, 1, 2, 2, 2, 4]
def baseStart_135740 : Nat := 118140960795 + 135740 * 2 ^ 59
def prefixEnd_135740 : Nat := 4983230072969 + 3 ^ 40 * 135740 * 2
def baseEnd_135740 : Nat := 69699864041404150325749

theorem tailTrace_135740 : CollatzResearch.WordTrace tailWord_135740 prefixEnd_135740 69699864041404150325749 := by
  unfold tailWord_135740
  simp only [CollatzResearch.WordTrace]
  refine ⟨2475422264122318695726337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3300563018829758260968449 2475422264122318695726337)
  ·
    refine ⟨1856566698091739021794753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2475422264122318695726337 1856566698091739021794753)
    ·
      refine ⟨1392425023568804266346065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1856566698091739021794753 1392425023568804266346065)
      ·
        refine ⟨1044318767676603199759549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1392425023568804266346065 1044318767676603199759549)
        ·
          refine ⟨391619537878726199909831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1044318767676603199759549 391619537878726199909831)
          ·
            refine ⟨587429306818089299864747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391619537878726199909831 587429306818089299864747)
            ·
              refine ⟨881143960227133949797121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 587429306818089299864747 881143960227133949797121)
              ·
                refine ⟨660857970170350462347841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 881143960227133949797121 660857970170350462347841)
                ·
                  refine ⟨495643477627762846760881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 660857970170350462347841 495643477627762846760881)
                  ·
                    refine ⟨371732608220822135070661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 495643477627762846760881 371732608220822135070661)
                    ·
                      refine ⟨69699864041404150325749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 371732608220822135070661 69699864041404150325749)
                      ·
                        rfl

theorem cell23_135740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_135740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135740 prefixEnd_135740 := by exact prefixLift 135740
  have htrace : WordTrace (prefixWord ++ tailWord_135740) baseStart_135740 baseEnd_135740 := by
    simpa [prefixWord, tailWord_135740, baseEnd_135740] using wordTrace_append hprefix tailTrace_135740
  have hstable : (prefixWord ++ tailWord_135740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135740).length < 2 ^ (prefixWord ++ tailWord_135740).sum := by decide
  have hdescent : baseEnd_135740 < baseStart_135740 := by decide
  rcases family_descends (prefixWord ++ tailWord_135740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135744 : List Nat := [2, 1, 1, 2, 2, 2, 5, 2, 2, 2, 2]
def baseStart_135744 : Nat := 118140960795 + 135744 * 2 ^ 59
def prefixEnd_135744 : Nat := 4983230072969 + 3 ^ 40 * 135744 * 2
def baseEnd_135744 : Nat := 69701917964022134675731

theorem tailTrace_135744 : CollatzResearch.WordTrace tailWord_135744 prefixEnd_135744 69701917964022134675731 := by
  unfold tailWord_135744
  simp only [CollatzResearch.WordTrace]
  refine ⟨2475495210115073037299143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3300660280153430716398857 2475495210115073037299143)
  ·
    refine ⟨3713242815172609555948715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2475495210115073037299143 3713242815172609555948715)
    ·
      refine ⟨5569864222758914333923073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3713242815172609555948715 5569864222758914333923073)
      ·
        refine ⟨4177398167069185750442305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5569864222758914333923073 4177398167069185750442305)
        ·
          refine ⟨3133048625301889312831729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4177398167069185750442305 3133048625301889312831729)
          ·
            refine ⟨2349786468976416984623797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3133048625301889312831729 2349786468976416984623797)
            ·
              refine ⟨220292481466539092308481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2349786468976416984623797 220292481466539092308481)
              ·
                refine ⟨165219361099904319231361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220292481466539092308481 165219361099904319231361)
                ·
                  refine ⟨123914520824928239423521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165219361099904319231361 123914520824928239423521)
                  ·
                    refine ⟨92935890618696179567641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 123914520824928239423521 92935890618696179567641)
                    ·
                      refine ⟨69701917964022134675731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 92935890618696179567641 69701917964022134675731)
                      ·
                        rfl

theorem cell23_135744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 2, 2, 2].length) (baseStart_135744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135744 prefixEnd_135744 := by exact prefixLift 135744
  have htrace : WordTrace (prefixWord ++ tailWord_135744) baseStart_135744 baseEnd_135744 := by
    simpa [prefixWord, tailWord_135744, baseEnd_135744] using wordTrace_append hprefix tailTrace_135744
  have hstable : (prefixWord ++ tailWord_135744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135744).length < 2 ^ (prefixWord ++ tailWord_135744).sum := by decide
  have hdescent : baseEnd_135744 < baseStart_135744 := by decide
  rcases family_descends (prefixWord ++ tailWord_135744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135757 : List Nat := [1, 6, 1, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_135757 : Nat := 118140960795 + 135757 * 2 ^ 59
def prefixEnd_135757 : Nat := 4983230072969 + 3 ^ 40 * 135757 * 2
def baseEnd_135757 : Nat := 69708593212530583813171

theorem tailTrace_135757 : CollatzResearch.WordTrace tailWord_135757 prefixEnd_135757 69708593212530583813171 := by
  unfold tailWord_135757
  simp only [CollatzResearch.WordTrace]
  refine ⟨4951464569183049294821525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3300976379455366196547683 4951464569183049294821525)
  ·
    refine ⟨232099901680455435694759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4951464569183049294821525 232099901680455435694759)
    ·
      refine ⟨348149852520683153542139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232099901680455435694759 348149852520683153542139)
      ·
        refine ⟨522224778781024730313209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348149852520683153542139 522224778781024730313209)
        ·
          refine ⟨391668584085768547734907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 522224778781024730313209 391668584085768547734907)
          ·
            refine ⟨587502876128652821602361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391668584085768547734907 587502876128652821602361)
            ·
              refine ⟨440627157096489616201771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 587502876128652821602361 440627157096489616201771)
              ·
                refine ⟨660940735644734424302657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 440627157096489616201771 660940735644734424302657)
                ·
                  refine ⟨495705551733550818226993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 660940735644734424302657 495705551733550818226993)
                  ·
                    refine ⟨371779163800163113670245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 495705551733550818226993 371779163800163113670245)
                    ·
                      refine ⟨69708593212530583813171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 371779163800163113670245 69708593212530583813171)
                      ·
                        rfl

theorem cell23_135757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_135757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135757 prefixEnd_135757 := by exact prefixLift 135757
  have htrace : WordTrace (prefixWord ++ tailWord_135757) baseStart_135757 baseEnd_135757 := by
    simpa [prefixWord, tailWord_135757, baseEnd_135757] using wordTrace_append hprefix tailTrace_135757
  have hstable : (prefixWord ++ tailWord_135757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135757).length < 2 ^ (prefixWord ++ tailWord_135757).sum := by decide
  have hdescent : baseEnd_135757 < baseStart_135757 := by decide
  rcases family_descends (prefixWord ++ tailWord_135757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135761 : List Nat := [1, 2, 2, 1, 3, 4, 3, 1, 2, 2, 2]
def baseStart_135761 : Nat := 118140960795 + 135761 * 2 ^ 59
def prefixEnd_135761 : Nat := 4983230072969 + 3 ^ 40 * 135761 * 2
def baseEnd_135761 : Nat := 69710647135148568163153

theorem tailTrace_135761 : CollatzResearch.WordTrace tailWord_135761 prefixEnd_135761 69710647135148568163153 := by
  unfold tailWord_135761
  simp only [CollatzResearch.WordTrace]
  refine ⟨4951610461168557977967137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3301073640779038651978091 4951610461168557977967137)
  ·
    refine ⟨3713707845876418483475353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4951610461168557977967137 3713707845876418483475353)
    ·
      refine ⟨2785280884407313862606515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3713707845876418483475353 2785280884407313862606515)
      ·
        refine ⟨4177921326610970793909773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2785280884407313862606515 4177921326610970793909773)
        ·
          refine ⟨1566720497479114047716165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4177921326610970793909773 1566720497479114047716165)
          ·
            refine ⟨293760093277333883946781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1566720497479114047716165 293760093277333883946781)
            ·
              refine ⟨110160034979000206480043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 293760093277333883946781 110160034979000206480043)
              ·
                refine ⟨165240052468500309720065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110160034979000206480043 165240052468500309720065)
                ·
                  refine ⟨123930039351375232290049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165240052468500309720065 123930039351375232290049)
                  ·
                    refine ⟨92947529513531424217537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 123930039351375232290049 92947529513531424217537)
                    ·
                      refine ⟨69710647135148568163153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 92947529513531424217537 69710647135148568163153)
                      ·
                        rfl

theorem cell23_135761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 2, 2, 2].length) (baseStart_135761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135761 prefixEnd_135761 := by exact prefixLift 135761
  have htrace : WordTrace (prefixWord ++ tailWord_135761) baseStart_135761 baseEnd_135761 := by
    simpa [prefixWord, tailWord_135761, baseEnd_135761] using wordTrace_append hprefix tailTrace_135761
  have hstable : (prefixWord ++ tailWord_135761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135761).length < 2 ^ (prefixWord ++ tailWord_135761).sum := by decide
  have hdescent : baseEnd_135761 < baseStart_135761 := by decide
  rcases family_descends (prefixWord ++ tailWord_135761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135780 : List Nat := [2, 3, 1, 1, 2, 2, 2, 3, 2, 5]
def baseStart_135780 : Nat := 118140960795 + 135780 * 2 ^ 59
def prefixEnd_135780 : Nat := 4983230072969 + 3 ^ 40 * 135780 * 2
def baseEnd_135780 : Nat := 23240134422527997941855

theorem tailTrace_135780 : CollatzResearch.WordTrace tailWord_135780 prefixEnd_135780 23240134422527997941855 := by
  unfold tailWord_135780
  simp only [CollatzResearch.WordTrace]
  refine ⟨2476151724049862111454397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3301535632066482815272529 2476151724049862111454397)
  ·
    refine ⟨928556896518698291795399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2476151724049862111454397 928556896518698291795399)
    ·
      refine ⟨1392835344778047437693099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 928556896518698291795399 1392835344778047437693099)
      ·
        refine ⟨2089253017167071156539649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1392835344778047437693099 2089253017167071156539649)
        ·
          refine ⟨1566939762875303367404737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2089253017167071156539649 1566939762875303367404737)
          ·
            refine ⟨1175204822156477525553553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1566939762875303367404737 1175204822156477525553553)
            ·
              refine ⟨881403616617358144165165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1175204822156477525553553 881403616617358144165165)
              ·
                refine ⟨330526356231509304061937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 881403616617358144165165 330526356231509304061937)
                ·
                  refine ⟨247894767173631978046453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 330526356231509304061937 247894767173631978046453)
                  ·
                    refine ⟨23240134422527997941855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 247894767173631978046453 23240134422527997941855)
                    ·
                      rfl

theorem cell23_135780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_135780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135780 prefixEnd_135780 := by exact prefixLift 135780
  have htrace : WordTrace (prefixWord ++ tailWord_135780) baseStart_135780 baseEnd_135780 := by
    simpa [prefixWord, tailWord_135780, baseEnd_135780] using wordTrace_append hprefix tailTrace_135780
  have hstable : (prefixWord ++ tailWord_135780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135780).length < 2 ^ (prefixWord ++ tailWord_135780).sum := by decide
  have hdescent : baseEnd_135780 < baseStart_135780 := by decide
  rcases family_descends (prefixWord ++ tailWord_135780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135800 : List Nat := [2, 1, 2, 1, 1, 1, 2, 6, 2, 1, 4]
def baseStart_135800 : Nat := 118140960795 + 135800 * 2 ^ 59
def prefixEnd_135800 : Nat := 4983230072969 + 3 ^ 40 * 135800 * 2
def baseEnd_135800 : Nat := 69730672880673915575473

theorem tailTrace_135800 : CollatzResearch.WordTrace tailWord_135800 prefixEnd_135800 69730672880673915575473 := by
  unfold tailWord_135800
  simp only [CollatzResearch.WordTrace]
  refine ⟨2476516454013633819318427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3302021938684845092424569 2476516454013633819318427)
  ·
    refine ⟨3714774681020450728977641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2476516454013633819318427 3714774681020450728977641)
    ·
      refine ⟨2786081010765338046733231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3714774681020450728977641 2786081010765338046733231)
      ·
        refine ⟨4179121516148007070099847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2786081010765338046733231 4179121516148007070099847)
        ·
          refine ⟨6268682274222010605149771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4179121516148007070099847 6268682274222010605149771)
          ·
            refine ⟨9403023411333015907724657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6268682274222010605149771 9403023411333015907724657)
            ·
              refine ⟨7052267558499761930793493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9403023411333015907724657 7052267558499761930793493)
              ·
                refine ⟨330575041804676340505945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7052267558499761930793493 330575041804676340505945)
                ·
                  refine ⟨247931281353507255379459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 330575041804676340505945 247931281353507255379459)
                  ·
                    refine ⟨371896922030260883069189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 247931281353507255379459 371896922030260883069189)
                    ·
                      refine ⟨69730672880673915575473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 371896922030260883069189 69730672880673915575473)
                      ·
                        rfl

theorem cell23_135800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_135800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135800 prefixEnd_135800 := by exact prefixLift 135800
  have htrace : WordTrace (prefixWord ++ tailWord_135800) baseStart_135800 baseEnd_135800 := by
    simpa [prefixWord, tailWord_135800, baseEnd_135800] using wordTrace_append hprefix tailTrace_135800
  have hstable : (prefixWord ++ tailWord_135800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135800).length < 2 ^ (prefixWord ++ tailWord_135800).sum := by decide
  have hdescent : baseEnd_135800 < baseStart_135800 := by decide
  rcases family_descends (prefixWord ++ tailWord_135800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135803 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 5]
def baseStart_135803 : Nat := 118140960795 + 135803 * 2 ^ 59
def prefixEnd_135803 : Nat := 4983230072969 + 3 ^ 40 * 135803 * 2
def baseEnd_135803 : Nat := 69732213322637403837959

theorem tailTrace_135803 : CollatzResearch.WordTrace tailWord_135803 prefixEnd_135803 69732213322637403837959 := by
  unfold tailWord_135803
  simp only [CollatzResearch.WordTrace]
  refine ⟨4953142327016399150996063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3302094884677599433997375 4953142327016399150996063)
  ·
    refine ⟨7429713490524598726494095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4953142327016399150996063 7429713490524598726494095)
    ·
      refine ⟨11144570235786898089741143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7429713490524598726494095 11144570235786898089741143)
      ·
        refine ⟨16716855353680347134611715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11144570235786898089741143 16716855353680347134611715)
        ·
          refine ⟨25075283030520520701917573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16716855353680347134611715 25075283030520520701917573)
          ·
            refine ⟨4701615568222597631609545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25075283030520520701917573 4701615568222597631609545)
            ·
              refine ⟨3526211676166948223707159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4701615568222597631609545 3526211676166948223707159)
              ·
                refine ⟨5289317514250422335560739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3526211676166948223707159 5289317514250422335560739)
                ·
                  refine ⟨7933976271375633503341109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5289317514250422335560739 7933976271375633503341109)
                  ·
                    refine ⟨743810275441465640938229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7933976271375633503341109 743810275441465640938229)
                    ·
                      refine ⟨69732213322637403837959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 743810275441465640938229 69732213322637403837959)
                      ·
                        rfl

theorem cell23_135803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 5].length) (baseStart_135803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135803 prefixEnd_135803 := by exact prefixLift 135803
  have htrace : WordTrace (prefixWord ++ tailWord_135803) baseStart_135803 baseEnd_135803 := by
    simpa [prefixWord, tailWord_135803, baseEnd_135803] using wordTrace_append hprefix tailTrace_135803
  have hstable : (prefixWord ++ tailWord_135803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135803).length < 2 ^ (prefixWord ++ tailWord_135803).sum := by decide
  have hdescent : baseEnd_135803 < baseStart_135803 := by decide
  rcases family_descends (prefixWord ++ tailWord_135803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135820 : List Nat := [2, 2, 1, 2, 1, 1, 2, 4, 1, 4, 3]
def baseStart_135820 : Nat := 118140960795 + 135820 * 2 ^ 59
def prefixEnd_135820 : Nat := 4983230072969 + 3 ^ 40 * 135820 * 2
def baseEnd_135820 : Nat := 69740942493763837325381

theorem tailTrace_135820 : CollatzResearch.WordTrace tailWord_135820 prefixEnd_135820 69740942493763837325381 := by
  unfold tailWord_135820
  simp only [CollatzResearch.WordTrace]
  refine ⟨2476881183977405527182457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3302508245303207369576609 2476881183977405527182457)
  ·
    refine ⟨1857660887983054145386843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2476881183977405527182457 1857660887983054145386843)
    ·
      refine ⟨2786491331974581218080265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1857660887983054145386843 2786491331974581218080265)
      ·
        refine ⟨2089868498980935913560199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2786491331974581218080265 2089868498980935913560199)
        ·
          refine ⟨3134802748471403870340299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2089868498980935913560199 3134802748471403870340299)
          ·
            refine ⟨4702204122707105805510449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3134802748471403870340299 4702204122707105805510449)
            ·
              refine ⟨3526653092030329354132837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4702204122707105805510449 3526653092030329354132837)
              ·
                refine ⟨661247454755686753899907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3526653092030329354132837 661247454755686753899907)
                ·
                  refine ⟨991871182133530130849861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 661247454755686753899907 991871182133530130849861)
                  ·
                    refine ⟨185975846650036899534349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 991871182133530130849861 185975846650036899534349)
                    ·
                      refine ⟨69740942493763837325381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 185975846650036899534349 69740942493763837325381)
                      ·
                        rfl

theorem cell23_135820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_135820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135820 prefixEnd_135820 := by exact prefixLift 135820
  have htrace : WordTrace (prefixWord ++ tailWord_135820) baseStart_135820 baseEnd_135820 := by
    simpa [prefixWord, tailWord_135820, baseEnd_135820] using wordTrace_append hprefix tailTrace_135820
  have hstable : (prefixWord ++ tailWord_135820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135820).length < 2 ^ (prefixWord ++ tailWord_135820).sum := by decide
  have hdescent : baseEnd_135820 < baseStart_135820 := by decide
  rcases family_descends (prefixWord ++ tailWord_135820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135837 : List Nat := [1, 4, 2, 1, 1, 1, 3, 3, 2, 2, 3]
def baseStart_135837 : Nat := 118140960795 + 135837 * 2 ^ 59
def prefixEnd_135837 : Nat := 4983230072969 + 3 ^ 40 * 135837 * 2
def baseEnd_135837 : Nat := 69749671664890270812803

theorem tailTrace_135837 : CollatzResearch.WordTrace tailWord_135837 prefixEnd_135837 69749671664890270812803 := by
  unfold tailWord_135837
  simp only [CollatzResearch.WordTrace]
  refine ⟨4954382408893222957733765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3302921605928815305155843 4954382408893222957733765)
  ·
    refine ⟨928946701667479304575081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4954382408893222957733765 928946701667479304575081)
    ·
      refine ⟨696710026250609478431311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 928946701667479304575081 696710026250609478431311)
      ·
        refine ⟨1045065039375914217646967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 696710026250609478431311 1045065039375914217646967)
        ·
          refine ⟨1567597559063871326470451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1045065039375914217646967 1567597559063871326470451)
          ·
            refine ⟨2351396338595806989705677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1567597559063871326470451 2351396338595806989705677)
            ·
              refine ⟨881773626973427621139629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2351396338595806989705677 881773626973427621139629)
              ·
                refine ⟨330665110115035357927361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 881773626973427621139629 330665110115035357927361)
                ·
                  refine ⟨247998832586276518445521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 330665110115035357927361 247998832586276518445521)
                  ·
                    refine ⟨185999124439707388834141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 247998832586276518445521 185999124439707388834141)
                    ·
                      refine ⟨69749671664890270812803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 185999124439707388834141 69749671664890270812803)
                      ·
                        rfl

theorem cell23_135837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_135837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135837 prefixEnd_135837 := by exact prefixLift 135837
  have htrace : WordTrace (prefixWord ++ tailWord_135837) baseStart_135837 baseEnd_135837 := by
    simpa [prefixWord, tailWord_135837, baseEnd_135837] using wordTrace_append hprefix tailTrace_135837
  have hstable : (prefixWord ++ tailWord_135837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135837).length < 2 ^ (prefixWord ++ tailWord_135837).sum := by decide
  have hdescent : baseEnd_135837 < baseStart_135837 := by decide
  rcases family_descends (prefixWord ++ tailWord_135837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135844 : List Nat := [2, 3, 1, 2, 2, 1, 2, 5, 1, 4]
def baseStart_135844 : Nat := 118140960795 + 135844 * 2 ^ 59
def prefixEnd_135844 : Nat := 4983230072969 + 3 ^ 40 * 135844 * 2
def baseEnd_135844 : Nat := 23251088676490581141757

theorem tailTrace_135844 : CollatzResearch.WordTrace tailWord_135844 prefixEnd_135844 23251088676490581141757 := by
  unfold tailWord_135844
  simp only [CollatzResearch.WordTrace]
  refine ⟨2477318859933931576619293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3303091813245242102159057 2477318859933931576619293)
  ·
    refine ⟨928994572475224341232235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2477318859933931576619293 928994572475224341232235)
    ·
      refine ⟨1393491858712836511848353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 928994572475224341232235 1393491858712836511848353)
      ·
        refine ⟨1045118894034627383886265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1393491858712836511848353 1045118894034627383886265)
        ·
          refine ⟨783839170525970537914699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1045118894034627383886265 783839170525970537914699)
          ·
            refine ⟨1175758755788955806872049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 783839170525970537914699 1175758755788955806872049)
            ·
              refine ⟨881819066841716855154037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1175758755788955806872049 881819066841716855154037)
              ·
                refine ⟨82670537516410955170691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 881819066841716855154037 82670537516410955170691)
                ·
                  refine ⟨124005806274616432756037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82670537516410955170691 124005806274616432756037)
                  ·
                    refine ⟨23251088676490581141757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 124005806274616432756037 23251088676490581141757)
                    ·
                      rfl

theorem cell23_135844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_135844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135844 prefixEnd_135844 := by exact prefixLift 135844
  have htrace : WordTrace (prefixWord ++ tailWord_135844) baseStart_135844 baseEnd_135844 := by
    simpa [prefixWord, tailWord_135844, baseEnd_135844] using wordTrace_append hprefix tailTrace_135844
  have hstable : (prefixWord ++ tailWord_135844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135844).length < 2 ^ (prefixWord ++ tailWord_135844).sum := by decide
  have hdescent : baseEnd_135844 < baseStart_135844 := by decide
  rcases family_descends (prefixWord ++ tailWord_135844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135861 : List Nat := [1, 3, 3, 3, 1, 2, 1, 4, 1, 4]
def baseStart_135861 : Nat := 118140960795 + 135861 * 2 ^ 59
def prefixEnd_135861 : Nat := 4983230072969 + 3 ^ 40 * 135861 * 2
def baseEnd_135861 : Nat := 23253998400199392304231

theorem tailTrace_135861 : CollatzResearch.WordTrace tailWord_135861 prefixEnd_135861 23253998400199392304231 := by
  unfold tailWord_135861
  simp only [CollatzResearch.WordTrace]
  refine ⟨4955257760806275056607437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3303505173870850037738291 4955257760806275056607437)
  ·
    refine ⟨1858221660302353146227789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4955257760806275056607437 1858221660302353146227789)
    ·
      refine ⟨696833122613382429835421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1858221660302353146227789 696833122613382429835421)
      ·
        refine ⟨261312420980018411188283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 696833122613382429835421 261312420980018411188283)
        ·
          refine ⟨391968631470027616782425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261312420980018411188283 391968631470027616782425)
          ·
            refine ⟨293976473602520712586819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 391968631470027616782425 293976473602520712586819)
            ·
              refine ⟨440964710403781068880229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293976473602520712586819 440964710403781068880229)
              ·
                refine ⟨82680883200708950415043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 440964710403781068880229 82680883200708950415043)
                ·
                  refine ⟨124021324801063425622565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82680883200708950415043 124021324801063425622565)
                  ·
                    refine ⟨23253998400199392304231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 124021324801063425622565 23253998400199392304231)
                    ·
                      rfl

theorem cell23_135861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_135861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135861 prefixEnd_135861 := by exact prefixLift 135861
  have htrace : WordTrace (prefixWord ++ tailWord_135861) baseStart_135861 baseEnd_135861 := by
    simpa [prefixWord, tailWord_135861, baseEnd_135861] using wordTrace_append hprefix tailTrace_135861
  have hstable : (prefixWord ++ tailWord_135861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135861).length < 2 ^ (prefixWord ++ tailWord_135861).sum := by decide
  have hdescent : baseEnd_135861 < baseStart_135861 := by decide
  rcases family_descends (prefixWord ++ tailWord_135861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135878 : List Nat := [6, 1, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_135878 : Nat := 118140960795 + 135878 * 2 ^ 59
def prefixEnd_135878 : Nat := 4983230072969 + 3 ^ 40 * 135878 * 2
def baseEnd_135878 : Nat := 23256908123908203466705

theorem tailTrace_135878 : CollatzResearch.WordTrace tailWord_135878 prefixEnd_135878 23256908123908203466705 := by
  unfold tailWord_135878
  simp only [CollatzResearch.WordTrace]
  refine ⟨154871181304521467499259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3303918534496457973317525 154871181304521467499259)
  ·
    refine ⟨232306771956782201248889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154871181304521467499259 232306771956782201248889)
    ·
      refine ⟨174230078967586650936667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232306771956782201248889 174230078967586650936667)
      ·
        refine ⟨261345118451379976405001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174230078967586650936667 261345118451379976405001)
        ·
          refine ⟨196008838838534982303751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261345118451379976405001 196008838838534982303751)
          ·
            refine ⟨294013258257802473455627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196008838838534982303751 294013258257802473455627)
            ·
              refine ⟨441019887386703710183441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294013258257802473455627 441019887386703710183441)
              ·
                refine ⟨330764915540027782637581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 441019887386703710183441 330764915540027782637581)
                ·
                  refine ⟨124036843327510418489093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 330764915540027782637581 124036843327510418489093)
                  ·
                    refine ⟨23256908123908203466705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 124036843327510418489093 23256908123908203466705)
                    ·
                      rfl

theorem cell23_135878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_135878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135878 prefixEnd_135878 := by exact prefixLift 135878
  have htrace : WordTrace (prefixWord ++ tailWord_135878) baseStart_135878 baseEnd_135878 := by
    simpa [prefixWord, tailWord_135878, baseEnd_135878] using wordTrace_append hprefix tailTrace_135878
  have hstable : (prefixWord ++ tailWord_135878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135878).length < 2 ^ (prefixWord ++ tailWord_135878).sum := by decide
  have hdescent : baseEnd_135878 < baseStart_135878 := by decide
  rcases family_descends (prefixWord ++ tailWord_135878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135884 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 5, 1, 3]
def baseStart_135884 : Nat := 118140960795 + 135884 * 2 ^ 59
def prefixEnd_135884 : Nat := 4983230072969 + 3 ^ 40 * 135884 * 2
def baseEnd_135884 : Nat := 69773805255651586925087

theorem tailTrace_135884 : CollatzResearch.WordTrace tailWord_135884 prefixEnd_135884 69773805255651586925087 := by
  unfold tailWord_135884
  simp only [CollatzResearch.WordTrace]
  refine ⟨2478048319861474992347353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3304064426481966656463137 2478048319861474992347353)
  ·
    refine ⟨1858536239896106244260515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2478048319861474992347353 1858536239896106244260515)
    ·
      refine ⟨2787804359844159366390773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1858536239896106244260515 2787804359844159366390773)
      ·
        refine ⟨261356658735389940599135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2787804359844159366390773 261356658735389940599135)
        ·
          refine ⟨392034988103084910898703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261356658735389940599135 392034988103084910898703)
          ·
            refine ⟨588052482154627366348055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392034988103084910898703 588052482154627366348055)
            ·
              refine ⟨882078723231941049522083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588052482154627366348055 882078723231941049522083)
              ·
                refine ⟨1323118084847911574283125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 882078723231941049522083 1323118084847911574283125)
                ·
                  refine ⟨124042320454491710089043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1323118084847911574283125 124042320454491710089043)
                  ·
                    refine ⟨186063480681737565133565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 124042320454491710089043 186063480681737565133565)
                    ·
                      refine ⟨69773805255651586925087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 186063480681737565133565 69773805255651586925087)
                      ·
                        rfl

theorem cell23_135884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_135884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135884 prefixEnd_135884 := by exact prefixLift 135884
  have htrace : WordTrace (prefixWord ++ tailWord_135884) baseStart_135884 baseEnd_135884 := by
    simpa [prefixWord, tailWord_135884, baseEnd_135884] using wordTrace_append hprefix tailTrace_135884
  have hstable : (prefixWord ++ tailWord_135884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135884).length < 2 ^ (prefixWord ++ tailWord_135884).sum := by decide
  have hdescent : baseEnd_135884 < baseStart_135884 := by decide
  rcases family_descends (prefixWord ++ tailWord_135884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135920 : List Nat := [2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 6]
def baseStart_135920 : Nat := 118140960795 + 135920 * 2 ^ 59
def prefixEnd_135920 : Nat := 4983230072969 + 3 ^ 40 * 135920 * 2
def baseEnd_135920 : Nat := 69792290559213446074921

theorem tailTrace_135920 : CollatzResearch.WordTrace tailWord_135920 prefixEnd_135920 69792290559213446074921 := by
  unfold tailWord_135920
  simp only [CollatzResearch.WordTrace]
  refine ⟨2478704833796264066502607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3304939778395018755336809 2478704833796264066502607)
  ·
    refine ⟨3718057250694396099753911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2478704833796264066502607 3718057250694396099753911)
    ·
      refine ⟨5577085876041594149630867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3718057250694396099753911 5577085876041594149630867)
      ·
        refine ⟨8365628814062391224446301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5577085876041594149630867 8365628814062391224446301)
        ·
          refine ⟨3137110805273396709167363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8365628814062391224446301 3137110805273396709167363)
          ·
            refine ⟨4705666207910095063751045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3137110805273396709167363 4705666207910095063751045)
            ·
              refine ⟨882312413983142824453321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4705666207910095063751045 882312413983142824453321)
              ·
                refine ⟨661734310487357118339991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 882312413983142824453321 661734310487357118339991)
                ·
                  refine ⟨992601465731035677509987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 661734310487357118339991 992601465731035677509987)
                  ·
                    refine ⟨1488902198596553516264981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 992601465731035677509987 1488902198596553516264981)
                    ·
                      refine ⟨69792290559213446074921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1488902198596553516264981 69792290559213446074921)
                      ·
                        rfl

theorem cell23_135920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 6].length) (baseStart_135920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135920 prefixEnd_135920 := by exact prefixLift 135920
  have htrace : WordTrace (prefixWord ++ tailWord_135920) baseStart_135920 baseEnd_135920 := by
    simpa [prefixWord, tailWord_135920, baseEnd_135920] using wordTrace_append hprefix tailTrace_135920
  have hstable : (prefixWord ++ tailWord_135920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135920).length < 2 ^ (prefixWord ++ tailWord_135920).sum := by decide
  have hdescent : baseEnd_135920 < baseStart_135920 := by decide
  rcases family_descends (prefixWord ++ tailWord_135920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135934 : List Nat := [4, 2, 2, 1, 2, 1, 3, 1, 1, 6]
def baseStart_135934 : Nat := 118140960795 + 135934 * 2 ^ 59
def prefixEnd_135934 : Nat := 4983230072969 + 3 ^ 40 * 135934 * 2
def baseEnd_135934 : Nat := 23266493096125463766619

theorem tailTrace_135934 : CollatzResearch.WordTrace tailWord_135934 prefixEnd_135934 23266493096125463766619 := by
  unfold tailWord_135934
  simp only [CollatzResearch.WordTrace]
  refine ⟨619740036192726065501857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3305280193027872349343237 619740036192726065501857)
  ·
    refine ⟨464805027144544549126393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 619740036192726065501857 464805027144544549126393)
    ·
      refine ⟨348603770358408411844795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 464805027144544549126393 348603770358408411844795)
      ·
        refine ⟨522905655537612617767193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348603770358408411844795 522905655537612617767193)
        ·
          refine ⟨392179241653209463325395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 522905655537612617767193 392179241653209463325395)
          ·
            refine ⟨588268862479814194988093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392179241653209463325395 588268862479814194988093)
            ·
              refine ⟨220600823429930323120535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 588268862479814194988093 220600823429930323120535)
              ·
                refine ⟨330901235144895484680803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220600823429930323120535 330901235144895484680803)
                ·
                  refine ⟨496351852717343227021205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 330901235144895484680803 496351852717343227021205)
                  ·
                    refine ⟨23266493096125463766619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 496351852717343227021205 23266493096125463766619)
                    ·
                      rfl

theorem cell23_135934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_135934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135934 prefixEnd_135934 := by exact prefixLift 135934
  have htrace : WordTrace (prefixWord ++ tailWord_135934) baseStart_135934 baseEnd_135934 := by
    simpa [prefixWord, tailWord_135934, baseEnd_135934] using wordTrace_append hprefix tailTrace_135934
  have hstable : (prefixWord ++ tailWord_135934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135934).length < 2 ^ (prefixWord ++ tailWord_135934).sum := by decide
  have hdescent : baseEnd_135934 < baseStart_135934 := by decide
  rcases family_descends (prefixWord ++ tailWord_135934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135944 : List Nat := [2, 1, 3, 2, 2, 2, 1, 4, 1, 2, 3]
def baseStart_135944 : Nat := 118140960795 + 135944 * 2 ^ 59
def prefixEnd_135944 : Nat := 4983230072969 + 3 ^ 40 * 135944 * 2
def baseEnd_135944 : Nat := 69804614094921352174811

theorem tailTrace_135944 : CollatzResearch.WordTrace tailWord_135944 prefixEnd_135944 69804614094921352174811 := by
  unfold tailWord_135944
  simp only [CollatzResearch.WordTrace]
  refine ⟨2479142509752790115939443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3305523346337053487919257 2479142509752790115939443)
  ·
    refine ⟨3718713764629185173909165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2479142509752790115939443 3718713764629185173909165)
    ·
      refine ⟨1394517661735944440215937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3718713764629185173909165 1394517661735944440215937)
      ·
        refine ⟨1045888246301958330161953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1394517661735944440215937 1045888246301958330161953)
        ·
          refine ⟨784416184726468747621465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1045888246301958330161953 784416184726468747621465)
          ·
            refine ⟨588312138544851560716099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 784416184726468747621465 588312138544851560716099)
            ·
              refine ⟨882468207817277341074149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588312138544851560716099 882468207817277341074149)
              ·
                refine ⟨165462788965739501451403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 882468207817277341074149 165462788965739501451403)
                ·
                  refine ⟨248194183448609252177105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165462788965739501451403 248194183448609252177105)
                  ·
                    refine ⟨186145637586456939132829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 248194183448609252177105 186145637586456939132829)
                    ·
                      refine ⟨69804614094921352174811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 186145637586456939132829 69804614094921352174811)
                      ·
                        rfl

theorem cell23_135944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_135944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135944 prefixEnd_135944 := by exact prefixLift 135944
  have htrace : WordTrace (prefixWord ++ tailWord_135944) baseStart_135944 baseEnd_135944 := by
    simpa [prefixWord, tailWord_135944, baseEnd_135944] using wordTrace_append hprefix tailTrace_135944
  have hstable : (prefixWord ++ tailWord_135944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135944).length < 2 ^ (prefixWord ++ tailWord_135944).sum := by decide
  have hdescent : baseEnd_135944 < baseStart_135944 := by decide
  rcases family_descends (prefixWord ++ tailWord_135944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135957 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 3, 3, 3]
def baseStart_135957 : Nat := 118140960795 + 135957 * 2 ^ 59
def prefixEnd_135957 : Nat := 4983230072969 + 3 ^ 40 * 135957 * 2
def baseEnd_135957 : Nat := 69811289343429801312251

theorem tailTrace_135957 : CollatzResearch.WordTrace tailWord_135957 prefixEnd_135957 69811289343429801312251 := by
  unfold tailWord_135957
  simp only [CollatzResearch.WordTrace]
  refine ⟨4958759168458483452102125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3305839445638988968068083 4958759168458483452102125)
  ·
    refine ⟨1859534688171931294538297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4958759168458483452102125 1859534688171931294538297)
    ·
      refine ⟨1394651016128948470903723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1859534688171931294538297 1394651016128948470903723)
      ·
        refine ⟨2091976524193422706355585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1394651016128948470903723 2091976524193422706355585)
        ·
          refine ⟨1568982393145067029766689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2091976524193422706355585 1568982393145067029766689)
          ·
            refine ⟨1176736794858800272325017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1568982393145067029766689 1176736794858800272325017)
            ·
              refine ⟨882552596144100204243763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1176736794858800272325017 882552596144100204243763)
              ·
                refine ⟨1323828894216150306365645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 882552596144100204243763 1323828894216150306365645)
                ·
                  refine ⟨496435835331056364887117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1323828894216150306365645 496435835331056364887117)
                  ·
                    refine ⟨186163438249146136832669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 496435835331056364887117 186163438249146136832669)
                    ·
                      refine ⟨69811289343429801312251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 186163438249146136832669 69811289343429801312251)
                      ·
                        rfl

theorem cell23_135957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_135957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135957 prefixEnd_135957 := by exact prefixLift 135957
  have htrace : WordTrace (prefixWord ++ tailWord_135957) baseStart_135957 baseEnd_135957 := by
    simpa [prefixWord, tailWord_135957, baseEnd_135957] using wordTrace_append hprefix tailTrace_135957
  have hstable : (prefixWord ++ tailWord_135957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135957).length < 2 ^ (prefixWord ++ tailWord_135957).sum := by decide
  have hdescent : baseEnd_135957 < baseStart_135957 := by decide
  rcases family_descends (prefixWord ++ tailWord_135957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135960 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 1, 9]
def baseStart_135960 : Nat := 118140960795 + 135960 * 2 ^ 59
def prefixEnd_135960 : Nat := 4983230072969 + 3 ^ 40 * 135960 * 2
def baseEnd_135960 : Nat := 23270943261797763191579

theorem tailTrace_135960 : CollatzResearch.WordTrace tailWord_135960 prefixEnd_135960 23270943261797763191579 := by
  unfold tailWord_135960
  simp only [CollatzResearch.WordTrace]
  refine ⟨2479434293723807482230667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3305912391631743309640889 2479434293723807482230667)
  ·
    refine ⟨3719151440585711223346001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2479434293723807482230667 3719151440585711223346001)
    ·
      refine ⟨2789363580439283417509501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3719151440585711223346001 2789363580439283417509501)
      ·
        refine ⟨1046011342664731281566063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2789363580439283417509501 1046011342664731281566063)
        ·
          refine ⟨1569017013997096922349095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1046011342664731281566063 1569017013997096922349095)
          ·
            refine ⟨2353525520995645383523643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1569017013997096922349095 2353525520995645383523643)
            ·
              refine ⟨3530288281493468075285465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2353525520995645383523643 3530288281493468075285465)
              ·
                refine ⟨2647716211120101056464099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3530288281493468075285465 2647716211120101056464099)
                ·
                  refine ⟨3971574316680151584696149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2647716211120101056464099 3971574316680151584696149)
                  ·
                    refine ⟨23270943261797763191579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 3971574316680151584696149 23270943261797763191579)
                    ·
                      rfl

theorem cell23_135960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 1, 9].length) (baseStart_135960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135960 prefixEnd_135960 := by exact prefixLift 135960
  have htrace : WordTrace (prefixWord ++ tailWord_135960) baseStart_135960 baseEnd_135960 := by
    simpa [prefixWord, tailWord_135960, baseEnd_135960] using wordTrace_append hprefix tailTrace_135960
  have hstable : (prefixWord ++ tailWord_135960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135960).length < 2 ^ (prefixWord ++ tailWord_135960).sum := by decide
  have hdescent : baseEnd_135960 < baseStart_135960 := by decide
  rcases family_descends (prefixWord ++ tailWord_135960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135981 : List Nat := [1, 5, 3, 2, 1, 1, 2, 8]
def baseStart_135981 : Nat := 118140960795 + 135981 * 2 ^ 59
def prefixEnd_135981 : Nat := 4983230072969 + 3 ^ 40 * 135981 * 2
def baseEnd_135981 : Nat := 2586059736264359533783

theorem tailTrace_135981 : CollatzResearch.WordTrace tailWord_135981 prefixEnd_135981 2586059736264359533783 := by
  unfold tailWord_135981
  simp only [CollatzResearch.WordTrace]
  refine ⟨4959634520371535550975797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3306423013581023700650531 4959634520371535550975797)
  ·
    refine ⟨464965736284831457903981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4959634520371535550975797 464965736284831457903981)
    ·
      refine ⟨174362151106811796713993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 464965736284831457903981 174362151106811796713993)
      ·
        refine ⟨130771613330108847535495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174362151106811796713993 130771613330108847535495)
        ·
          refine ⟨196157419995163271303243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130771613330108847535495 196157419995163271303243)
          ·
            refine ⟨294236129992744906954865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196157419995163271303243 294236129992744906954865)
            ·
              refine ⟨220677097494558680216149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 294236129992744906954865 220677097494558680216149)
              ·
                refine ⟨2586059736264359533783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 220677097494558680216149 2586059736264359533783)
                ·
                  rfl

theorem cell23_135981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 8].length) (baseStart_135981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_135981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_135981 prefixEnd_135981 := by exact prefixLift 135981
  have htrace : WordTrace (prefixWord ++ tailWord_135981) baseStart_135981 baseEnd_135981 := by
    simpa [prefixWord, tailWord_135981, baseEnd_135981] using wordTrace_append hprefix tailTrace_135981
  have hstable : (prefixWord ++ tailWord_135981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135981).length < 2 ^ (prefixWord ++ tailWord_135981).sum := by decide
  have hdescent : baseEnd_135981 < baseStart_135981 := by decide
  rcases family_descends (prefixWord ++ tailWord_135981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136018 : List Nat := [3, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2]
def baseStart_136018 : Nat := 118140960795 + 136018 * 2 ^ 59
def prefixEnd_136018 : Nat := 4983230072969 + 3 ^ 40 * 136018 * 2
def baseEnd_136018 : Nat := 69842611663354062649471

theorem tailTrace_136018 : CollatzResearch.WordTrace tailWord_136018 prefixEnd_136018 69842611663354062649471 := by
  unfold tailWord_136018
  simp only [CollatzResearch.WordTrace]
  refine ⟨1240246005309372717518177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3307322680824993913381805 1240246005309372717518177)
  ·
    refine ⟨930184503982029538138633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1240246005309372717518177 930184503982029538138633)
    ·
      refine ⟨697638377986522153603975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 930184503982029538138633 697638377986522153603975)
      ·
        refine ⟨1046457566979783230405963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 697638377986522153603975 1046457566979783230405963)
        ·
          refine ⟨1569686350469674845608945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1046457566979783230405963 1569686350469674845608945)
          ·
            refine ⟨1177264762852256134206709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1569686350469674845608945 1177264762852256134206709)
            ·
              refine ⟨110368571517399012581879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1177264762852256134206709 110368571517399012581879)
              ·
                refine ⟨165552857276098518872819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110368571517399012581879 165552857276098518872819)
                ·
                  refine ⟨248329285914147778309229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165552857276098518872819 248329285914147778309229)
                  ·
                    refine ⟨93123482217805416865961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 248329285914147778309229 93123482217805416865961)
                    ·
                      refine ⟨69842611663354062649471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 93123482217805416865961 69842611663354062649471)
                      ·
                        rfl

theorem cell23_136018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_136018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136018 prefixEnd_136018 := by exact prefixLift 136018
  have htrace : WordTrace (prefixWord ++ tailWord_136018) baseStart_136018 baseEnd_136018 := by
    simpa [prefixWord, tailWord_136018, baseEnd_136018] using wordTrace_append hprefix tailTrace_136018
  have hstable : (prefixWord ++ tailWord_136018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136018).length < 2 ^ (prefixWord ++ tailWord_136018).sum := by decide
  have hdescent : baseEnd_136018 < baseStart_136018 := by decide
  rcases family_descends (prefixWord ++ tailWord_136018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136054 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 9]
def baseStart_136054 : Nat := 118140960795 + 136054 * 2 ^ 59
def prefixEnd_136054 : Nat := 4983230072969 + 3 ^ 40 * 136054 * 2
def baseEnd_136054 : Nat := 7762344107435102422145

theorem tailTrace_136054 : CollatzResearch.WordTrace tailWord_136054 prefixEnd_136054 7762344107435102422145 := by
  unfold tailWord_136054
  simp only [CollatzResearch.WordTrace]
  refine ⟨310143565569191813648951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3308198032738046012255477 310143565569191813648951)
  ·
    refine ⟨465215348353787720473427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 310143565569191813648951 465215348353787720473427)
    ·
      refine ⟨697823022530681580710141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 465215348353787720473427 697823022530681580710141)
      ·
        refine ⟨261683633449005592766303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 697823022530681580710141 261683633449005592766303)
        ·
          refine ⟨392525450173508389149455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261683633449005592766303 392525450173508389149455)
          ·
            refine ⟨588788175260262583724183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392525450173508389149455 588788175260262583724183)
            ·
              refine ⟨883182262890393875586275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588788175260262583724183 883182262890393875586275)
              ·
                refine ⟨1324773394335590813379413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 883182262890393875586275 1324773394335590813379413)
                ·
                  refine ⟨7762344107435102422145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1324773394335590813379413 7762344107435102422145)
                  ·
                    rfl

theorem cell23_136054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_136054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136054 prefixEnd_136054 := by exact prefixLift 136054
  have htrace : WordTrace (prefixWord ++ tailWord_136054) baseStart_136054 baseEnd_136054 := by
    simpa [prefixWord, tailWord_136054, baseEnd_136054] using wordTrace_append hprefix tailTrace_136054
  have hstable : (prefixWord ++ tailWord_136054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136054).length < 2 ^ (prefixWord ++ tailWord_136054).sum := by decide
  have hdescent : baseEnd_136054 < baseStart_136054 := by decide
  rcases family_descends (prefixWord ++ tailWord_136054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136067 : List Nat := [1, 1, 1, 3, 4, 1, 3, 1, 1, 7]
def baseStart_136067 : Nat := 118140960795 + 136067 * 2 ^ 59
def prefixEnd_136067 : Nat := 4983230072969 + 3 ^ 40 * 136067 * 2
def baseEnd_136067 : Nat := 23289257405141456978915

theorem tailTrace_136067 : CollatzResearch.WordTrace tailWord_136067 prefixEnd_136067 23289257405141456978915 := by
  unfold tailWord_136067
  simp only [CollatzResearch.WordTrace]
  refine ⟨4962771198059972238606455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3308514132039981492404303 4962771198059972238606455)
  ·
    refine ⟨7444156797089958357909683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4962771198059972238606455 7444156797089958357909683)
    ·
      refine ⟨11166235195634937536864525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7444156797089958357909683 11166235195634937536864525)
      ·
        refine ⟨4187338198363101576324197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11166235195634937536864525 4187338198363101576324197)
        ·
          refine ⟨785125912193081545560787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4187338198363101576324197 785125912193081545560787)
          ·
            refine ⟨1177688868289622318341181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 785125912193081545560787 1177688868289622318341181)
            ·
              refine ⟨441633325608608369377943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1177688868289622318341181 441633325608608369377943)
              ·
                refine ⟨662449988412912554066915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 441633325608608369377943 662449988412912554066915)
                ·
                  refine ⟨993674982619368831100373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 662449988412912554066915 993674982619368831100373)
                  ·
                    refine ⟨23289257405141456978915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 993674982619368831100373 23289257405141456978915)
                    ·
                      rfl

theorem cell23_136067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 7].length) (baseStart_136067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136067 prefixEnd_136067 := by exact prefixLift 136067
  have htrace : WordTrace (prefixWord ++ tailWord_136067) baseStart_136067 baseEnd_136067 := by
    simpa [prefixWord, tailWord_136067, baseEnd_136067] using wordTrace_append hprefix tailTrace_136067
  have hstable : (prefixWord ++ tailWord_136067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136067).length < 2 ^ (prefixWord ++ tailWord_136067).sum := by decide
  have hdescent : baseEnd_136067 < baseStart_136067 := by decide
  rcases family_descends (prefixWord ++ tailWord_136067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136071 : List Nat := [1, 1, 4, 2, 3, 2, 2, 3, 5]
def baseStart_136071 : Nat := 118140960795 + 136071 * 2 ^ 59
def prefixEnd_136071 : Nat := 4983230072969 + 3 ^ 40 * 136071 * 2
def baseEnd_136071 : Nat := 7763314015338039476303

theorem tailTrace_136071 : CollatzResearch.WordTrace tailWord_136071 prefixEnd_136071 7763314015338039476303 := by
  unfold tailWord_136071
  simp only [CollatzResearch.WordTrace]
  refine ⟨4962917090045480921752067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3308611393363653947834711 4962917090045480921752067)
  ·
    refine ⟨7444375635068221382628101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4962917090045480921752067 7444375635068221382628101)
    ·
      refine ⟨1395820431575291509242769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7444375635068221382628101 1395820431575291509242769)
      ·
        refine ⟨1046865323681468631932077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1395820431575291509242769 1046865323681468631932077)
        ·
          refine ⟨392574496380550736974529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1046865323681468631932077 392574496380550736974529)
          ·
            refine ⟨294430872285413052730897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 392574496380550736974529 294430872285413052730897)
            ·
              refine ⟨220823154214059789548173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 294430872285413052730897 220823154214059789548173)
              ·
                refine ⟨82808682830272421080565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 220823154214059789548173 82808682830272421080565)
                ·
                  refine ⟨7763314015338039476303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82808682830272421080565 7763314015338039476303)
                  ·
                    rfl

theorem cell23_136071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3, 5].length) (baseStart_136071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136071 prefixEnd_136071 := by exact prefixLift 136071
  have htrace : WordTrace (prefixWord ++ tailWord_136071) baseStart_136071 baseEnd_136071 := by
    simpa [prefixWord, tailWord_136071, baseEnd_136071] using wordTrace_append hprefix tailTrace_136071
  have hstable : (prefixWord ++ tailWord_136071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136071).length < 2 ^ (prefixWord ++ tailWord_136071).sum := by decide
  have hdescent : baseEnd_136071 < baseStart_136071 := by decide
  rcases family_descends (prefixWord ++ tailWord_136071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136082 : List Nat := [3, 2, 3, 2, 2, 2, 1, 2, 2, 2, 2]
def baseStart_136082 : Nat := 118140960795 + 136082 * 2 ^ 59
def prefixEnd_136082 : Nat := 4983230072969 + 3 ^ 40 * 136082 * 2
def baseEnd_136082 : Nat := 69875474425241812249177

theorem tailTrace_136082 : CollatzResearch.WordTrace tailWord_136082 prefixEnd_136082 69875474425241812249177 := by
  unfold tailWord_136082
  simp only [CollatzResearch.WordTrace]
  refine ⟨1240829573251407450100625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3308878862003753200268333 1240829573251407450100625)
  ·
    refine ⟨930622179938555587575469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1240829573251407450100625 930622179938555587575469)
    ·
      refine ⟨348983317476958345340801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 930622179938555587575469 348983317476958345340801)
      ·
        refine ⟨261737488107718759005601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 348983317476958345340801 261737488107718759005601)
        ·
          refine ⟨196303116080789069254201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261737488107718759005601 196303116080789069254201)
          ·
            refine ⟨147227337060591801940651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196303116080789069254201 147227337060591801940651)
            ·
              refine ⟨220841005590887702910977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147227337060591801940651 220841005590887702910977)
              ·
                refine ⟨165630754193165777183233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220841005590887702910977 165630754193165777183233)
                ·
                  refine ⟨124223065644874332887425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165630754193165777183233 124223065644874332887425)
                  ·
                    refine ⟨93167299233655749665569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 124223065644874332887425 93167299233655749665569)
                    ·
                      refine ⟨69875474425241812249177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 93167299233655749665569 69875474425241812249177)
                      ·
                        rfl

theorem cell23_136082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_136082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136082 prefixEnd_136082 := by exact prefixLift 136082
  have htrace : WordTrace (prefixWord ++ tailWord_136082) baseStart_136082 baseEnd_136082 := by
    simpa [prefixWord, tailWord_136082, baseEnd_136082] using wordTrace_append hprefix tailTrace_136082
  have hstable : (prefixWord ++ tailWord_136082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136082).length < 2 ^ (prefixWord ++ tailWord_136082).sum := by decide
  have hdescent : baseEnd_136082 < baseStart_136082 := by decide
  rcases family_descends (prefixWord ++ tailWord_136082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136084 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 4, 5]
def baseStart_136084 : Nat := 118140960795 + 136084 * 2 ^ 59
def prefixEnd_136084 : Nat := 4983230072969 + 3 ^ 40 * 136084 * 2
def baseEnd_136084 : Nat := 23292167128850268141389

theorem tailTrace_136084 : CollatzResearch.WordTrace tailWord_136084 prefixEnd_136084 23292167128850268141389 := by
  unfold tailWord_136084
  simp only [CollatzResearch.WordTrace]
  refine ⟨2481695619499192070987653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3308927492665589427983537 2481695619499192070987653)
  ·
    refine ⟨465317928656098513310185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2481695619499192070987653 465317928656098513310185)
    ·
      refine ⟨348988446492073884982639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 465317928656098513310185 348988446492073884982639)
      ·
        refine ⟨523482669738110827473959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348988446492073884982639 523482669738110827473959)
        ·
          refine ⟨785224004607166241210939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 523482669738110827473959 785224004607166241210939)
          ·
            refine ⟨1177836006910749361816409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 785224004607166241210939 1177836006910749361816409)
            ·
              refine ⟨883377005183062021362307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1177836006910749361816409 883377005183062021362307)
              ·
                refine ⟨1325065507774593032043461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 883377005183062021362307 1325065507774593032043461)
                ·
                  refine ⟨248449782707736193508149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1325065507774593032043461 248449782707736193508149)
                  ·
                    refine ⟨23292167128850268141389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 248449782707736193508149 23292167128850268141389)
                    ·
                      rfl

theorem cell23_136084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_136084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136084 prefixEnd_136084 := by exact prefixLift 136084
  have htrace : WordTrace (prefixWord ++ tailWord_136084) baseStart_136084 baseEnd_136084 := by
    simpa [prefixWord, tailWord_136084, baseEnd_136084] using wordTrace_append hprefix tailTrace_136084
  have hstable : (prefixWord ++ tailWord_136084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136084).length < 2 ^ (prefixWord ++ tailWord_136084).sum := by decide
  have hdescent : baseEnd_136084 < baseStart_136084 := by decide
  rcases family_descends (prefixWord ++ tailWord_136084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136148 : List Nat := [2, 4, 1, 2, 1, 4, 1, 1, 3, 4]
def baseStart_136148 : Nat := 118140960795 + 136148 * 2 ^ 59
def prefixEnd_136148 : Nat := 4983230072969 + 3 ^ 40 * 136148 * 2
def baseEnd_136148 : Nat := 23303121382812851341291

theorem tailTrace_136148 : CollatzResearch.WordTrace tailWord_136148 prefixEnd_136148 23303121382812851341291 := by
  unfold tailWord_136148
  simp only [CollatzResearch.WordTrace]
  refine ⟨2482862755383261536152549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3310483673844348714870065 2482862755383261536152549)
  ·
    refine ⟨465536766634361538028603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2482862755383261536152549 465536766634361538028603)
    ·
      refine ⟨698305149951542307042905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 465536766634361538028603 698305149951542307042905)
      ·
        refine ⟨523728862463656730282179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 698305149951542307042905 523728862463656730282179)
        ·
          refine ⟨785593293695485095423269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 523728862463656730282179 785593293695485095423269)
          ·
            refine ⟨147298742567903455391863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 785593293695485095423269 147298742567903455391863)
            ·
              refine ⟨220948113851855183087795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147298742567903455391863 220948113851855183087795)
              ·
                refine ⟨331422170777782774631693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220948113851855183087795 331422170777782774631693)
                ·
                  refine ⟨124283314041668540486885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 331422170777782774631693 124283314041668540486885)
                  ·
                    refine ⟨23303121382812851341291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 124283314041668540486885 23303121382812851341291)
                    ·
                      rfl

theorem cell23_136148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_136148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136148 prefixEnd_136148 := by exact prefixLift 136148
  have htrace : WordTrace (prefixWord ++ tailWord_136148) baseStart_136148 baseEnd_136148 := by
    simpa [prefixWord, tailWord_136148, baseEnd_136148] using wordTrace_append hprefix tailTrace_136148
  have hstable : (prefixWord ++ tailWord_136148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136148).length < 2 ^ (prefixWord ++ tailWord_136148).sum := by decide
  have hdescent : baseEnd_136148 < baseStart_136148 := by decide
  rcases family_descends (prefixWord ++ tailWord_136148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136248 : List Nat := [2, 1, 2, 1, 5, 2, 1, 3, 1, 2, 3]
def baseStart_136248 : Nat := 118140960795 + 136248 * 2 ^ 59
def prefixEnd_136248 : Nat := 4983230072969 + 3 ^ 40 * 136248 * 2
def baseEnd_136248 : Nat := 69960712213888162773413

theorem tailTrace_136248 : CollatzResearch.WordTrace tailWord_136248 prefixEnd_136248 69960712213888162773413 := by
  unfold tailWord_136248
  simp only [CollatzResearch.WordTrace]
  refine ⟨2484686405202120075472699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3312915206936160100630265 2484686405202120075472699)
  ·
    refine ⟨3727029607803180113209049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2484686405202120075472699 3727029607803180113209049)
    ·
      refine ⟨2795272205852385084906787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3727029607803180113209049 2795272205852385084906787)
      ·
        refine ⟨4192908308778577627360181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2795272205852385084906787 4192908308778577627360181)
        ·
          refine ⟨393085153947991652565017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4192908308778577627360181 393085153947991652565017)
          ·
            refine ⟨294813865460993739423763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 393085153947991652565017 294813865460993739423763)
            ·
              refine ⟨442220798191490609135645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294813865460993739423763 442220798191490609135645)
              ·
                refine ⟨165832799321808978425867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 442220798191490609135645 165832799321808978425867)
                ·
                  refine ⟨248749198982713467638801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165832799321808978425867 248749198982713467638801)
                  ·
                    refine ⟨186561899237035100729101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 248749198982713467638801 186561899237035100729101)
                    ·
                      refine ⟨69960712213888162773413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 186561899237035100729101 69960712213888162773413)
                      ·
                        rfl

theorem cell23_136248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 1, 2, 3].length) (baseStart_136248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136248 prefixEnd_136248 := by exact prefixLift 136248
  have htrace : WordTrace (prefixWord ++ tailWord_136248) baseStart_136248 baseEnd_136248 := by
    simpa [prefixWord, tailWord_136248, baseEnd_136248] using wordTrace_append hprefix tailTrace_136248
  have hstable : (prefixWord ++ tailWord_136248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136248).length < 2 ^ (prefixWord ++ tailWord_136248).sum := by decide
  have hdescent : baseEnd_136248 < baseStart_136248 := by decide
  rcases family_descends (prefixWord ++ tailWord_136248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136262 : List Nat := [6, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2]
def baseStart_136262 : Nat := 118140960795 + 136262 * 2 ^ 59
def prefixEnd_136262 : Nat := 4983230072969 + 3 ^ 40 * 136262 * 2
def baseEnd_136262 : Nat := 69967900943051107998349

theorem tailTrace_136262 : CollatzResearch.WordTrace tailWord_136262 prefixEnd_136262 69967900943051107998349 := by
  unfold tailWord_136262
  simp only [CollatzResearch.WordTrace]
  refine ⟨155308857261047516936095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3313255621569013694636693 155308857261047516936095)
  ·
    refine ⟨232963285891571275404143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155308857261047516936095 232963285891571275404143)
    ·
      refine ⟨349444928837356913106215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232963285891571275404143 349444928837356913106215)
      ·
        refine ⟨524167393256035369659323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349444928837356913106215 524167393256035369659323)
        ·
          refine ⟨786251089884053054488985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 524167393256035369659323 786251089884053054488985)
          ·
            refine ⟨589688317413039790866739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 786251089884053054488985 589688317413039790866739)
            ·
              refine ⟨884532476119559686300109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 589688317413039790866739 884532476119559686300109)
              ·
                refine ⟨331699678544834882362541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 884532476119559686300109 331699678544834882362541)
                ·
                  refine ⟨124387379454313080885953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 331699678544834882362541 124387379454313080885953)
                  ·
                    refine ⟨93290534590734810664465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 124387379454313080885953 93290534590734810664465)
                    ·
                      refine ⟨69967900943051107998349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 93290534590734810664465 69967900943051107998349)
                      ·
                        rfl

theorem cell23_136262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_136262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136262 prefixEnd_136262 := by exact prefixLift 136262
  have htrace : WordTrace (prefixWord ++ tailWord_136262) baseStart_136262 baseEnd_136262 := by
    simpa [prefixWord, tailWord_136262, baseEnd_136262] using wordTrace_append hprefix tailTrace_136262
  have hstable : (prefixWord ++ tailWord_136262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136262).length < 2 ^ (prefixWord ++ tailWord_136262).sum := by decide
  have hdescent : baseEnd_136262 < baseStart_136262 := by decide
  rcases family_descends (prefixWord ++ tailWord_136262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136285 : List Nat := [1, 4, 4, 1, 2, 2, 2, 7]
def baseStart_136285 : Nat := 118140960795 + 136285 * 2 ^ 59
def prefixEnd_136285 : Nat := 4983230072969 + 3 ^ 40 * 136285 * 2
def baseEnd_136285 : Nat := 2591841148077945111509

theorem tailTrace_136285 : CollatzResearch.WordTrace tailWord_136285 prefixEnd_136285 2591841148077945111509 := by
  unfold tailWord_136285
  simp only [CollatzResearch.WordTrace]
  refine ⟨4970722311270195470042309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3313814874180130313361539 4970722311270195470042309)
  ·
    refine ⟨932010433363161650632933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4970722311270195470042309 932010433363161650632933)
    ·
      refine ⟨174751956255592809493675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 932010433363161650632933 174751956255592809493675)
      ·
        refine ⟨262127934383389214240513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174751956255592809493675 262127934383389214240513)
        ·
          refine ⟨196595950787541910680385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262127934383389214240513 196595950787541910680385)
          ·
            refine ⟨147446963090656433010289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196595950787541910680385 147446963090656433010289)
            ·
              refine ⟨110585222317992324757717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147446963090656433010289 110585222317992324757717)
              ·
                refine ⟨2591841148077945111509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 110585222317992324757717 2591841148077945111509)
                ·
                  rfl

theorem cell23_136285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 7].length) (baseStart_136285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136285 prefixEnd_136285 := by exact prefixLift 136285
  have htrace : WordTrace (prefixWord ++ tailWord_136285) baseStart_136285 baseEnd_136285 := by
    simpa [prefixWord, tailWord_136285, baseEnd_136285] using wordTrace_append hprefix tailTrace_136285
  have hstable : (prefixWord ++ tailWord_136285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136285).length < 2 ^ (prefixWord ++ tailWord_136285).sum := by decide
  have hdescent : baseEnd_136285 < baseStart_136285 := by decide
  rcases family_descends (prefixWord ++ tailWord_136285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136296 : List Nat := [2, 1, 4, 4, 1, 2, 1, 3, 1, 2, 2]
def baseStart_136296 : Nat := 118140960795 + 136296 * 2 ^ 59
def prefixEnd_136296 : Nat := 4983230072969 + 3 ^ 40 * 136296 * 2
def baseEnd_136296 : Nat := 69985359285303974973193

theorem tailTrace_136296 : CollatzResearch.WordTrace tailWord_136296 prefixEnd_136296 69985359285303974973193 := by
  unfold tailWord_136296
  simp only [CollatzResearch.WordTrace]
  refine ⟨2485561757115172174346371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3314082342820229565795161 2485561757115172174346371)
  ·
    refine ⟨3728342635672758261519557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2485561757115172174346371 3728342635672758261519557)
    ·
      refine ⟨699064244188642174034917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3728342635672758261519557 699064244188642174034917)
      ·
        refine ⟨131074545785370407631547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 699064244188642174034917 131074545785370407631547)
        ·
          refine ⟨196611818678055611447321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131074545785370407631547 196611818678055611447321)
          ·
            refine ⟨147458864008541708585491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196611818678055611447321 147458864008541708585491)
            ·
              refine ⟨221188296012812562878237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147458864008541708585491 221188296012812562878237)
              ·
                refine ⟨82945611004804711079339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 221188296012812562878237 82945611004804711079339)
                ·
                  refine ⟨124418416507207066619009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82945611004804711079339 124418416507207066619009)
                  ·
                    refine ⟨93313812380405299964257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 124418416507207066619009 93313812380405299964257)
                    ·
                      refine ⟨69985359285303974973193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 93313812380405299964257 69985359285303974973193)
                      ·
                        rfl

theorem cell23_136296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_136296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136296 prefixEnd_136296 := by exact prefixLift 136296
  have htrace : WordTrace (prefixWord ++ tailWord_136296) baseStart_136296 baseEnd_136296 := by
    simpa [prefixWord, tailWord_136296, baseEnd_136296] using wordTrace_append hprefix tailTrace_136296
  have hstable : (prefixWord ++ tailWord_136296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136296).length < 2 ^ (prefixWord ++ tailWord_136296).sum := by decide
  have hdescent : baseEnd_136296 < baseStart_136296 := by decide
  rcases family_descends (prefixWord ++ tailWord_136296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136371 : List Nat := [1, 1, 1, 2, 3, 2, 4, 2, 2, 5]
def baseStart_136371 : Nat := 118140960795 + 136371 * 2 ^ 59
def prefixEnd_136371 : Nat := 4983230072969 + 3 ^ 40 * 136371 * 2
def baseEnd_136371 : Nat := 23341290111463727178449

theorem tailTrace_136371 : CollatzResearch.WordTrace tailWord_136371 prefixEnd_136371 23341290111463727178449 := by
  unfold tailWord_136371
  simp only [CollatzResearch.WordTrace]
  refine ⟨4973858988958632157672967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3315905992639088105115311 4973858988958632157672967)
  ·
    refine ⟨7460788483437948236509451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4973858988958632157672967 7460788483437948236509451)
    ·
      refine ⟨11191182725156922354764177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7460788483437948236509451 11191182725156922354764177)
      ·
        refine ⟨8393387043867691766073133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11191182725156922354764177 8393387043867691766073133)
        ·
          refine ⟨3147520141450384412277425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8393387043867691766073133 3147520141450384412277425)
          ·
            refine ⟨2360640106087788309208069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3147520141450384412277425 2360640106087788309208069)
            ·
              refine ⟨442620019891460307976513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2360640106087788309208069 442620019891460307976513)
              ·
                refine ⟨331965014918595230982385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 442620019891460307976513 331965014918595230982385)
                ·
                  refine ⟨248973761188946423236789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 331965014918595230982385 248973761188946423236789)
                  ·
                    refine ⟨23341290111463727178449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 248973761188946423236789 23341290111463727178449)
                    ·
                      rfl

theorem cell23_136371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 5].length) (baseStart_136371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136371 prefixEnd_136371 := by exact prefixLift 136371
  have htrace : WordTrace (prefixWord ++ tailWord_136371) baseStart_136371 baseEnd_136371 := by
    simpa [prefixWord, tailWord_136371, baseEnd_136371] using wordTrace_append hprefix tailTrace_136371
  have hstable : (prefixWord ++ tailWord_136371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136371).length < 2 ^ (prefixWord ++ tailWord_136371).sum := by decide
  have hdescent : baseEnd_136371 < baseStart_136371 := by decide
  rcases family_descends (prefixWord ++ tailWord_136371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136381 : List Nat := [1, 4, 1, 2, 1, 1, 4, 1, 1, 2, 5]
def baseStart_136381 : Nat := 118140960795 + 136381 * 2 ^ 59
def prefixEnd_136381 : Nat := 4983230072969 + 3 ^ 40 * 136381 * 2
def baseEnd_136381 : Nat := 70029005140936142410301

theorem tailTrace_136381 : CollatzResearch.WordTrace tailWord_136381 prefixEnd_136381 70029005140936142410301 := by
  unfold tailWord_136381
  simp only [CollatzResearch.WordTrace]
  refine ⟨4974223718922403865536997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3316149145948269243691331 4974223718922403865536997)
  ·
    refine ⟨932666947297950724788187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4974223718922403865536997 932666947297950724788187)
    ·
      refine ⟨1399000420946926087182281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 932666947297950724788187 1399000420946926087182281)
      ·
        refine ⟨1049250315710194565386711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1399000420946926087182281 1049250315710194565386711)
        ·
          refine ⟨1573875473565291848080067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1049250315710194565386711 1573875473565291848080067)
          ·
            refine ⟨2360813210347937772120101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1573875473565291848080067 2360813210347937772120101)
            ·
              refine ⟨442652476940238332272519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2360813210347937772120101 442652476940238332272519)
              ·
                refine ⟨663978715410357498408779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 442652476940238332272519 663978715410357498408779)
                ·
                  refine ⟨995968073115536247613169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 663978715410357498408779 995968073115536247613169)
                  ·
                    refine ⟨746976054836652185709877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 995968073115536247613169 746976054836652185709877)
                    ·
                      refine ⟨70029005140936142410301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 746976054836652185709877 70029005140936142410301)
                      ·
                        rfl

theorem cell23_136381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_136381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136381 prefixEnd_136381 := by exact prefixLift 136381
  have htrace : WordTrace (prefixWord ++ tailWord_136381) baseStart_136381 baseEnd_136381 := by
    simpa [prefixWord, tailWord_136381, baseEnd_136381] using wordTrace_append hprefix tailTrace_136381
  have hstable : (prefixWord ++ tailWord_136381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136381).length < 2 ^ (prefixWord ++ tailWord_136381).sum := by decide
  have hdescent : baseEnd_136381 < baseStart_136381 := by decide
  rcases family_descends (prefixWord ++ tailWord_136381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136385 : List Nat := [1, 2, 6, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_136385 : Nat := 118140960795 + 136385 * 2 ^ 59
def prefixEnd_136385 : Nat := 4983230072969 + 3 ^ 40 * 136385 * 2
def baseEnd_136385 : Nat := 70031059063554126760283

theorem tailTrace_136385 : CollatzResearch.WordTrace tailWord_136385 prefixEnd_136385 70031059063554126760283 := by
  unfold tailWord_136385
  simp only [CollatzResearch.WordTrace]
  refine ⟨4974369610907912548682609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3316246407271941699121739 4974369610907912548682609)
  ·
    refine ⟨3730777208180934411511957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4974369610907912548682609 3730777208180934411511957)
    ·
      refine ⟨174880181633481300539623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3730777208180934411511957 174880181633481300539623)
      ·
        refine ⟨262320272450221950809435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174880181633481300539623 262320272450221950809435)
        ·
          refine ⟨393480408675332926214153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262320272450221950809435 393480408675332926214153)
          ·
            refine ⟨295110306506499694660615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 393480408675332926214153 295110306506499694660615)
            ·
              refine ⟨442665459759749541990923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295110306506499694660615 442665459759749541990923)
              ·
                refine ⟨663998189639624312986385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 442665459759749541990923 663998189639624312986385)
                ·
                  refine ⟨497998642229718234739789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 663998189639624312986385 497998642229718234739789)
                  ·
                    refine ⟨186749490836144338027421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 497998642229718234739789 186749490836144338027421)
                    ·
                      refine ⟨70031059063554126760283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 186749490836144338027421 70031059063554126760283)
                      ·
                        rfl

theorem cell23_136385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_136385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136385 prefixEnd_136385 := by exact prefixLift 136385
  have htrace : WordTrace (prefixWord ++ tailWord_136385) baseStart_136385 baseEnd_136385 := by
    simpa [prefixWord, tailWord_136385, baseEnd_136385] using wordTrace_append hprefix tailTrace_136385
  have hstable : (prefixWord ++ tailWord_136385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136385).length < 2 ^ (prefixWord ++ tailWord_136385).sum := by decide
  have hdescent : baseEnd_136385 < baseStart_136385 := by decide
  rcases family_descends (prefixWord ++ tailWord_136385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136391 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 4]
def baseStart_136391 : Nat := 118140960795 + 136391 * 2 ^ 59
def prefixEnd_136391 : Nat := 4983230072969 + 3 ^ 40 * 136391 * 2
def baseEnd_136391 : Nat := 70034139947481103285255

theorem tailTrace_136391 : CollatzResearch.WordTrace tailWord_136391 prefixEnd_136391 70034139947481103285255 := by
  unfold tailWord_136391
  simp only [CollatzResearch.WordTrace]
  refine ⟨4974588448886175573401027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3316392299257450382267351 4974588448886175573401027)
  ·
    refine ⟨7461882673329263360101541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4974588448886175573401027 7461882673329263360101541)
    ·
      refine ⟨1399103001249236880019039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7461882673329263360101541 1399103001249236880019039)
      ·
        refine ⟨2098654501873855320028559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1399103001249236880019039 2098654501873855320028559)
        ·
          refine ⟨3147981752810782980042839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2098654501873855320028559 3147981752810782980042839)
          ·
            refine ⟨4721972629216174470064259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3147981752810782980042839 4721972629216174470064259)
            ·
              refine ⟨7082958943824261705096389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4721972629216174470064259 7082958943824261705096389)
              ·
                refine ⟨1328054801967049069705573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7082958943824261705096389 1328054801967049069705573)
                ·
                  refine ⟨249010275368821700569795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1328054801967049069705573 249010275368821700569795)
                  ·
                    refine ⟨373515413053232550854693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 249010275368821700569795 373515413053232550854693)
                    ·
                      refine ⟨70034139947481103285255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 373515413053232550854693 70034139947481103285255)
                      ·
                        rfl

theorem cell23_136391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_136391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136391 prefixEnd_136391 := by exact prefixLift 136391
  have htrace : WordTrace (prefixWord ++ tailWord_136391) baseStart_136391 baseEnd_136391 := by
    simpa [prefixWord, tailWord_136391, baseEnd_136391] using wordTrace_append hprefix tailTrace_136391
  have hstable : (prefixWord ++ tailWord_136391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136391).length < 2 ^ (prefixWord ++ tailWord_136391).sum := by decide
  have hdescent : baseEnd_136391 < baseStart_136391 := by decide
  rcases family_descends (prefixWord ++ tailWord_136391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
