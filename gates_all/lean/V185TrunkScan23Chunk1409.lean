import V185TrunkScan23Chunk1408

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8346243 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 2, 5, 2]
def baseStart_8346243 : Nat := 118140960795 + 8346243 * 2 ^ 59
def prefixEnd_8346243 : Nat := 4983230072969 + 3 ^ 40 * 8346243 * 2
def baseEnd_8346243 : Nat := 4285634318223494019578833

theorem tailTrace_8346243 : CollatzResearch.WordTrace tailWord_8346243 prefixEnd_8346243 4285634318223494019578833 := by
  unfold tailWord_8346243
  simp only [CollatzResearch.WordTrace]
  refine ⟨304412490701994510665643383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202941660467996340443762255 304412490701994510665643383)
  ·
    refine ⟨456618736052991765998465075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304412490701994510665643383 456618736052991765998465075)
    ·
      refine ⟨684928104079487648997697613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456618736052991765998465075 684928104079487648997697613)
      ·
        refine ⟨256848039029807868374136605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 684928104079487648997697613 256848039029807868374136605)
        ·
          refine ⟨96318014636177950640301227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256848039029807868374136605 96318014636177950640301227)
          ·
            refine ⟨144477021954266925960451841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96318014636177950640301227 144477021954266925960451841)
            ·
              refine ⟨108357766465700194470338881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144477021954266925960451841 108357766465700194470338881)
              ·
                refine ⟨81268324849275145852754161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108357766465700194470338881 81268324849275145852754161)
                ·
                  refine ⟨60951243636956359389565621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81268324849275145852754161 60951243636956359389565621)
                  ·
                    refine ⟨5714179090964658692771777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60951243636956359389565621 5714179090964658692771777)
                    ·
                      refine ⟨4285634318223494019578833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5714179090964658692771777 4285634318223494019578833)
                      ·
                        rfl

theorem cell23_8346243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 5, 2].length) (baseStart_8346243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346243 prefixEnd_8346243 := by exact prefixLift 8346243
  have htrace : WordTrace (prefixWord ++ tailWord_8346243) baseStart_8346243 baseEnd_8346243 := by
    simpa [prefixWord, tailWord_8346243, baseEnd_8346243] using wordTrace_append hprefix tailTrace_8346243
  have hstable : (prefixWord ++ tailWord_8346243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346243).length < 2 ^ (prefixWord ++ tailWord_8346243).sum := by decide
  have hdescent : baseEnd_8346243 < baseStart_8346243 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346270 : List Nat := [4, 3, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_8346270 : Nat := 118140960795 + 8346270 * 2 ^ 59
def prefixEnd_8346270 : Nat := 4983230072969 + 3 ^ 40 * 8346270 * 2
def baseEnd_8346270 : Nat := 1428549394067055137980403

theorem tailTrace_8346270 : CollatzResearch.WordTrace tailWord_8346270 prefixEnd_8346270 1428549394067055137980403 := by
  unfold tailWord_8346270
  simp only [CollatzResearch.WordTrace]
  refine ⟨38051684434112086784609533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202942316981931129517917509 38051684434112086784609533)
  ·
    refine ⟨14269381662792032544228575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38051684434112086784609533 14269381662792032544228575)
    ·
      refine ⟨21404072494188048816342863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14269381662792032544228575 21404072494188048816342863)
      ·
        refine ⟨32106108741282073224514295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21404072494188048816342863 32106108741282073224514295)
        ·
          refine ⟨48159163111923109836771443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32106108741282073224514295 48159163111923109836771443)
          ·
            refine ⟨72238744667884664755157165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48159163111923109836771443 72238744667884664755157165)
            ·
              refine ⟨27089529250456749283183937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72238744667884664755157165 27089529250456749283183937)
              ·
                refine ⟨20317146937842561962387953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27089529250456749283183937 20317146937842561962387953)
                ·
                  refine ⟨15237860203381921471790965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20317146937842561962387953 15237860203381921471790965)
                  ·
                    refine ⟨1428549394067055137980403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15237860203381921471790965 1428549394067055137980403)
                    ·
                      rfl

theorem cell23_8346270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_8346270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346270 prefixEnd_8346270 := by exact prefixLift 8346270
  have htrace : WordTrace (prefixWord ++ tailWord_8346270) baseStart_8346270 baseEnd_8346270 := by
    simpa [prefixWord, tailWord_8346270, baseEnd_8346270] using wordTrace_append hprefix tailTrace_8346270
  have hstable : (prefixWord ++ tailWord_8346270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346270).length < 2 ^ (prefixWord ++ tailWord_8346270).sum := by decide
  have hdescent : baseEnd_8346270 < baseStart_8346270 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346383 : List Nat := [1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 5]
def baseStart_8346383 : Nat := 118140960795 + 8346383 * 2 ^ 59
def prefixEnd_8346383 : Nat := 4983230072969 + 3 ^ 40 * 8346383 * 2
def baseEnd_8346383 : Nat := 4285706205515123471828189

theorem tailTrace_8346383 : CollatzResearch.WordTrace tailWord_8346383 prefixEnd_8346383 4285706205515123471828189 := by
  unfold tailWord_8346383
  simp only [CollatzResearch.WordTrace]
  refine ⟨304417596921487314575739803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202945064614324876383826535 304417596921487314575739803)
  ·
    refine ⟨456626395382230971863609705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304417596921487314575739803 456626395382230971863609705)
    ·
      refine ⟨342469796536673228897707279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456626395382230971863609705 342469796536673228897707279)
      ·
        refine ⟨513704694805009843346560919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342469796536673228897707279 513704694805009843346560919)
        ·
          refine ⟨770557042207514765019841379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513704694805009843346560919 770557042207514765019841379)
          ·
            refine ⟨1155835563311272147529762069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770557042207514765019841379 1155835563311272147529762069)
            ·
              refine ⟨54179792030215881915457597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1155835563311272147529762069 54179792030215881915457597)
              ·
                refine ⟨20317422011330955718296599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54179792030215881915457597 20317422011330955718296599)
                ·
                  refine ⟨30476133016996433577444899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20317422011330955718296599 30476133016996433577444899)
                  ·
                    refine ⟨45714199525494650366167349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30476133016996433577444899 45714199525494650366167349)
                    ·
                      refine ⟨4285706205515123471828189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45714199525494650366167349 4285706205515123471828189)
                      ·
                        rfl

theorem cell23_8346383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 5].length) (baseStart_8346383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346383 prefixEnd_8346383 := by exact prefixLift 8346383
  have htrace : WordTrace (prefixWord ++ tailWord_8346383) baseStart_8346383 baseEnd_8346383 := by
    simpa [prefixWord, tailWord_8346383, baseEnd_8346383] using wordTrace_append hprefix tailTrace_8346383
  have hstable : (prefixWord ++ tailWord_8346383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346383).length < 2 ^ (prefixWord ++ tailWord_8346383).sum := by decide
  have hdescent : baseEnd_8346383 < baseStart_8346383 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346400 : List Nat := [2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 5]
def baseStart_8346400 : Nat := 118140960795 + 8346400 * 2 ^ 59
def prefixEnd_8346400 : Nat := 4983230072969 + 3 ^ 40 * 8346400 * 2
def baseEnd_8346400 : Nat := 4285714934686249905315611

theorem tailTrace_8346400 : CollatzResearch.WordTrace tailWord_8346400 prefixEnd_8346400 4285714934686249905315611 := by
  unfold tailWord_8346400
  simp only [CollatzResearch.WordTrace]
  refine ⟨152209108481212863239554327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202945477974950484319405769 152209108481212863239554327)
  ·
    refine ⟨228313662721819294859331491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152209108481212863239554327 228313662721819294859331491)
    ·
      refine ⟨342470494082728942288997237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228313662721819294859331491 342470494082728942288997237)
      ·
        refine ⟨32106608820255838339593491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 342470494082728942288997237 32106608820255838339593491)
        ·
          refine ⟨48159913230383757509390237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32106608820255838339593491 48159913230383757509390237)
          ·
            refine ⟨18059967461393909066021339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48159913230383757509390237 18059967461393909066021339)
            ·
              refine ⟨27089951192090863599032009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18059967461393909066021339 27089951192090863599032009)
              ·
                refine ⟨20317463394068147699274007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27089951192090863599032009 20317463394068147699274007)
                ·
                  refine ⟨30476195091102221548911011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20317463394068147699274007 30476195091102221548911011)
                  ·
                    refine ⟨45714292636653332323366517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30476195091102221548911011 45714292636653332323366517)
                    ·
                      refine ⟨4285714934686249905315611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45714292636653332323366517 4285714934686249905315611)
                      ·
                        rfl

theorem cell23_8346400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_8346400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346400 prefixEnd_8346400 := by exact prefixLift 8346400
  have htrace : WordTrace (prefixWord ++ tailWord_8346400) baseStart_8346400 baseEnd_8346400 := by
    simpa [prefixWord, tailWord_8346400, baseEnd_8346400] using wordTrace_append hprefix tailTrace_8346400
  have hstable : (prefixWord ++ tailWord_8346400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346400).length < 2 ^ (prefixWord ++ tailWord_8346400).sum := by decide
  have hdescent : baseEnd_8346400 < baseStart_8346400 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346414 : List Nat := [4, 1, 3, 2, 1, 2, 2, 2, 1, 1, 4]
def baseStart_8346414 : Nat := 118140960795 + 8346414 * 2 ^ 59
def prefixEnd_8346414 : Nat := 4983230072969 + 3 ^ 40 * 8346414 * 2
def baseEnd_8346414 : Nat := 4285722123415412850540547

theorem tailTrace_8346414 : CollatzResearch.WordTrace tailWord_8346414 prefixEnd_8346414 4285722123415412850540547 := by
  unfold tailWord_8346414
  simp only [CollatzResearch.WordTrace]
  refine ⟨38052340948046875858764787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202945818389583337913412197 38052340948046875858764787)
  ·
    refine ⟨57078511422070313788147181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38052340948046875858764787 57078511422070313788147181)
    ·
      refine ⟨21404441783276367670555193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57078511422070313788147181 21404441783276367670555193)
      ·
        refine ⟨16053331337457275752916395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21404441783276367670555193 16053331337457275752916395)
        ·
          refine ⟨24079997006185913629374593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16053331337457275752916395 24079997006185913629374593)
          ·
            refine ⟨18059997754639435222030945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24079997006185913629374593 18059997754639435222030945)
            ·
              refine ⟨13544998315979576416523209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18059997754639435222030945 13544998315979576416523209)
              ·
                refine ⟨10158748736984682312392407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13544998315979576416523209 10158748736984682312392407)
                ·
                  refine ⟨15238123105477023468588611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10158748736984682312392407 15238123105477023468588611)
                  ·
                    refine ⟨22857184658215535202882917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15238123105477023468588611 22857184658215535202882917)
                    ·
                      refine ⟨4285722123415412850540547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22857184658215535202882917 4285722123415412850540547)
                      ·
                        rfl

theorem cell23_8346414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_8346414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346414 prefixEnd_8346414 := by exact prefixLift 8346414
  have htrace : WordTrace (prefixWord ++ tailWord_8346414) baseStart_8346414 baseEnd_8346414 := by
    simpa [prefixWord, tailWord_8346414, baseEnd_8346414] using wordTrace_append hprefix tailTrace_8346414
  have hstable : (prefixWord ++ tailWord_8346414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346414).length < 2 ^ (prefixWord ++ tailWord_8346414).sum := by decide
  have hdescent : baseEnd_8346414 < baseStart_8346414 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346417 : List Nat := [1, 2, 2, 3, 2, 1, 4, 2, 1, 2, 3]
def baseStart_8346417 : Nat := 118140960795 + 8346417 * 2 ^ 59
def prefixEnd_8346417 : Nat := 4983230072969 + 3 ^ 40 * 8346417 * 2
def baseEnd_8346417 : Nat := 4285723663857376338803033

theorem tailTrace_8346417 : CollatzResearch.WordTrace tailWord_8346417 prefixEnd_8346417 4285723663857376338803033 := by
  unfold tailWord_8346417
  simp only [CollatzResearch.WordTrace]
  refine ⟨304418837003364138382477505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202945891335576092254985003 304418837003364138382477505)
  ·
    refine ⟨228314127752523103786858129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304418837003364138382477505 228314127752523103786858129)
    ·
      refine ⟨171235595814392327840143597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228314127752523103786858129 171235595814392327840143597)
      ·
        refine ⟨64213348430397122940053849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171235595814392327840143597 64213348430397122940053849)
        ·
          refine ⟨48160011322797842205040387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64213348430397122940053849 48160011322797842205040387)
          ·
            refine ⟨72240016984196763307560581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48160011322797842205040387 72240016984196763307560581)
            ·
              refine ⟨13545003184536893120167609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72240016984196763307560581 13545003184536893120167609)
              ·
                refine ⟨10158752388402669840125707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13545003184536893120167609 10158752388402669840125707)
                ·
                  refine ⟨15238128582604004760188561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10158752388402669840125707 15238128582604004760188561)
                  ·
                    refine ⟨11428596436953003570141421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15238128582604004760188561 11428596436953003570141421)
                    ·
                      refine ⟨4285723663857376338803033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11428596436953003570141421 4285723663857376338803033)
                      ·
                        rfl

theorem cell23_8346417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_8346417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346417 prefixEnd_8346417 := by exact prefixLift 8346417
  have htrace : WordTrace (prefixWord ++ tailWord_8346417) baseStart_8346417 baseEnd_8346417 := by
    simpa [prefixWord, tailWord_8346417, baseEnd_8346417] using wordTrace_append hprefix tailTrace_8346417
  have hstable : (prefixWord ++ tailWord_8346417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346417).length < 2 ^ (prefixWord ++ tailWord_8346417).sum := by decide
  have hdescent : baseEnd_8346417 < baseStart_8346417 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346431 : List Nat := [1, 1, 2, 2, 5, 1, 3, 3, 1, 2, 2]
def baseStart_8346431 : Nat := 118140960795 + 8346431 * 2 ^ 59
def prefixEnd_8346431 : Nat := 4983230072969 + 3 ^ 40 * 8346431 * 2
def baseEnd_8346431 : Nat := 4285730852586539284027969

theorem tailTrace_8346431 : CollatzResearch.WordTrace tailWord_8346431 prefixEnd_8346431 4285730852586539284027969 := by
  unfold tailWord_8346431
  simp only [CollatzResearch.WordTrace]
  refine ⟨304419347625313418773487147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202946231750208945848991431 304419347625313418773487147)
  ·
    refine ⟨456629021437970128160230721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304419347625313418773487147 456629021437970128160230721)
    ·
      refine ⟨342471766078477596120173041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456629021437970128160230721 342471766078477596120173041)
      ·
        refine ⟨256853824558858197090129781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342471766078477596120173041 256853824558858197090129781)
        ·
          refine ⟨24080046052392955977199667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 256853824558858197090129781 24080046052392955977199667)
          ·
            refine ⟨36120069078589433965799501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24080046052392955977199667 36120069078589433965799501)
            ·
              refine ⟨13545025904471037737174813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36120069078589433965799501 13545025904471037737174813)
              ·
                refine ⟨5079384714176639151440555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13545025904471037737174813 5079384714176639151440555)
                ·
                  refine ⟨7619077071264958727160833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5079384714176639151440555 7619077071264958727160833)
                  ·
                    refine ⟨5714307803448719045370625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7619077071264958727160833 5714307803448719045370625)
                    ·
                      refine ⟨4285730852586539284027969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5714307803448719045370625 4285730852586539284027969)
                      ·
                        rfl

theorem cell23_8346431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3, 1, 2, 2].length) (baseStart_8346431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346431 prefixEnd_8346431 := by exact prefixLift 8346431
  have htrace : WordTrace (prefixWord ++ tailWord_8346431) baseStart_8346431 baseEnd_8346431 := by
    simpa [prefixWord, tailWord_8346431, baseEnd_8346431] using wordTrace_append hprefix tailTrace_8346431
  have hstable : (prefixWord ++ tailWord_8346431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346431).length < 2 ^ (prefixWord ++ tailWord_8346431).sum := by decide
  have hdescent : baseEnd_8346431 < baseStart_8346431 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346463 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 1, 8]
def baseStart_8346463 : Nat := 118140960795 + 8346463 * 2 ^ 59
def prefixEnd_8346463 : Nat := 4983230072969 + 3 ^ 40 * 8346463 * 2
def baseEnd_8346463 : Nat := 1428582427989161052942607

theorem tailTrace_8346463 : CollatzResearch.WordTrace tailWord_8346463 prefixEnd_8346463 1428582427989161052942607 := by
  unfold tailWord_8346463
  simp only [CollatzResearch.WordTrace]
  refine ⟨304420514761197488238652043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202947009840798325492434695 304420514761197488238652043)
  ·
    refine ⟨456630772141796232357978065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304420514761197488238652043 456630772141796232357978065)
    ·
      refine ⟨342473079106347174268483549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456630772141796232357978065 342473079106347174268483549)
      ·
        refine ⟨128427404664880190350681331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342473079106347174268483549 128427404664880190350681331)
        ·
          refine ⟨192641106997320285526021997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128427404664880190350681331 192641106997320285526021997)
          ·
            refine ⟨72240415123995107072258249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192641106997320285526021997 72240415123995107072258249)
            ·
              refine ⟨54180311342996330304193687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72240415123995107072258249 54180311342996330304193687)
              ·
                refine ⟨81270467014494495456290531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54180311342996330304193687 81270467014494495456290531)
                ·
                  refine ⟨121905700521741743184435797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81270467014494495456290531 121905700521741743184435797)
                  ·
                    refine ⟨1428582427989161052942607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 121905700521741743184435797 1428582427989161052942607)
                    ·
                      rfl

theorem cell23_8346463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 8].length) (baseStart_8346463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346463 prefixEnd_8346463 := by exact prefixLift 8346463
  have htrace : WordTrace (prefixWord ++ tailWord_8346463) baseStart_8346463 baseEnd_8346463 := by
    simpa [prefixWord, tailWord_8346463, baseEnd_8346463] using wordTrace_append hprefix tailTrace_8346463
  have hstable : (prefixWord ++ tailWord_8346463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346463).length < 2 ^ (prefixWord ++ tailWord_8346463).sum := by decide
  have hdescent : baseEnd_8346463 < baseStart_8346463 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346487 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 6, 2, 2]
def baseStart_8346487 : Nat := 118140960795 + 8346487 * 2 ^ 59
def prefixEnd_8346487 : Nat := 4983230072969 + 3 ^ 40 * 8346487 * 2
def baseEnd_8346487 : Nat := 4285759607503191064927711

theorem tailTrace_8346487 : CollatzResearch.WordTrace tailWord_8346487 prefixEnd_8346487 4285759607503191064927711 := by
  unfold tailWord_8346487
  simp only [CollatzResearch.WordTrace]
  refine ⟨304421390113110540337525715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202947593408740360225017143 304421390113110540337525715)
  ·
    refine ⟨456632085169665810506288573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304421390113110540337525715 456632085169665810506288573)
    ·
      refine ⟨171237031938624678939858215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456632085169665810506288573 171237031938624678939858215)
      ·
        refine ⟨256855547907937018409787323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171237031938624678939858215 256855547907937018409787323)
        ·
          refine ⟨385283321861905527614680985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256855547907937018409787323 385283321861905527614680985)
          ·
            refine ⟨288962491396429145711010739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385283321861905527614680985 288962491396429145711010739)
            ·
              refine ⟨433443737094643718566516109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288962491396429145711010739 433443737094643718566516109)
              ·
                refine ⟨162541401410491394462443541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 433443737094643718566516109 162541401410491394462443541)
                ·
                  refine ⟨7619128191116784115427041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 162541401410491394462443541 7619128191116784115427041)
                  ·
                    refine ⟨5714346143337588086570281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7619128191116784115427041 5714346143337588086570281)
                    ·
                      refine ⟨4285759607503191064927711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5714346143337588086570281 4285759607503191064927711)
                      ·
                        rfl

theorem cell23_8346487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6, 2, 2].length) (baseStart_8346487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346487 prefixEnd_8346487 := by exact prefixLift 8346487
  have htrace : WordTrace (prefixWord ++ tailWord_8346487) baseStart_8346487 baseEnd_8346487 := by
    simpa [prefixWord, tailWord_8346487, baseEnd_8346487] using wordTrace_append hprefix tailTrace_8346487
  have hstable : (prefixWord ++ tailWord_8346487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346487).length < 2 ^ (prefixWord ++ tailWord_8346487).sum := by decide
  have hdescent : baseEnd_8346487 < baseStart_8346487 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346500 : List Nat := [2, 3, 2, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_8346500 : Nat := 118140960795 + 8346500 * 2 ^ 59
def prefixEnd_8346500 : Nat := 4983230072969 + 3 ^ 40 * 8346500 * 2
def baseEnd_8346500 : Nat := 4285766282751699514065151

theorem tailTrace_8346500 : CollatzResearch.WordTrace tailWord_8346500 prefixEnd_8346500 4285766282751699514065151 := by
  unfold tailWord_8346500
  simp only [CollatzResearch.WordTrace]
  refine ⟨152210932131031721778874477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202947909508042295705165969 152210932131031721778874477)
  ·
    refine ⟨57079099549136895667077929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152210932131031721778874477 57079099549136895667077929)
    ·
      refine ⟨42809324661852671750308447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57079099549136895667077929 42809324661852671750308447)
      ·
        refine ⟨64213986992779007625462671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42809324661852671750308447 64213986992779007625462671)
        ·
          refine ⟨96320980489168511438194007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64213986992779007625462671 96320980489168511438194007)
          ·
            refine ⟨144481470733752767157291011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96320980489168511438194007 144481470733752767157291011)
            ·
              refine ⟨216722206100629150735936517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144481470733752767157291011 216722206100629150735936517)
              ·
                refine ⟨40635413643867965762988097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216722206100629150735936517 40635413643867965762988097)
                ·
                  refine ⟨30476560232900974322241073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40635413643867965762988097 30476560232900974322241073)
                  ·
                    refine ⟨22857420174675730741680805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30476560232900974322241073 22857420174675730741680805)
                    ·
                      refine ⟨4285766282751699514065151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22857420174675730741680805 4285766282751699514065151)
                      ·
                        rfl

theorem cell23_8346500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_8346500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346500 prefixEnd_8346500 := by exact prefixLift 8346500
  have htrace : WordTrace (prefixWord ++ tailWord_8346500) baseStart_8346500 baseEnd_8346500 := by
    simpa [prefixWord, tailWord_8346500, baseEnd_8346500] using wordTrace_append hprefix tailTrace_8346500
  have hstable : (prefixWord ++ tailWord_8346500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346500).length < 2 ^ (prefixWord ++ tailWord_8346500).sum := by decide
  have hdescent : baseEnd_8346500 < baseStart_8346500 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346513 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 8]
def baseStart_8346513 : Nat := 118140960795 + 8346513 * 2 ^ 59
def prefixEnd_8346513 : Nat := 4983230072969 + 3 ^ 40 * 8346513 * 2
def baseEnd_8346513 : Nat := 4285772958000207963202591

theorem tailTrace_8346513 : CollatzResearch.WordTrace tailWord_8346513 prefixEnd_8346513 4285772958000207963202591 := by
  unfold tailWord_8346513
  simp only [CollatzResearch.WordTrace]
  refine ⟨304422338411016346777972193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202948225607344231185314795 304422338411016346777972193)
  ·
    refine ⟨228316753808262260083479145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304422338411016346777972193 228316753808262260083479145)
    ·
      refine ⟨171237565356196695062609359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228316753808262260083479145 171237565356196695062609359)
      ·
        refine ⟨256856348034295042593914039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171237565356196695062609359 256856348034295042593914039)
        ·
          refine ⟨385284522051442563890871059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256856348034295042593914039 385284522051442563890871059)
          ·
            refine ⟨577926783077163845836306589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385284522051442563890871059 577926783077163845836306589)
            ·
              refine ⟨216722543653936442188614971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 577926783077163845836306589 216722543653936442188614971)
              ·
                refine ⟨325083815480904663282922457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216722543653936442188614971 325083815480904663282922457)
                ·
                  refine ⟨243812861610678497462191843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 325083815480904663282922457 243812861610678497462191843)
                  ·
                    refine ⟨365719292416017746193287765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 243812861610678497462191843 365719292416017746193287765)
                    ·
                      refine ⟨4285772958000207963202591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 365719292416017746193287765 4285772958000207963202591)
                      ·
                        rfl

theorem cell23_8346513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_8346513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346513 prefixEnd_8346513 := by exact prefixLift 8346513
  have htrace : WordTrace (prefixWord ++ tailWord_8346513) baseStart_8346513 baseEnd_8346513 := by
    simpa [prefixWord, tailWord_8346513, baseEnd_8346513] using wordTrace_append hprefix tailTrace_8346513
  have hstable : (prefixWord ++ tailWord_8346513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346513).length < 2 ^ (prefixWord ++ tailWord_8346513).sum := by decide
  have hdescent : baseEnd_8346513 < baseStart_8346513 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346577 : List Nat := [1, 2, 2, 1, 2, 1, 3, 3, 2, 4, 2]
def baseStart_8346577 : Nat := 118140960795 + 8346577 * 2 ^ 59
def prefixEnd_8346577 : Nat := 4983230072969 + 3 ^ 40 * 8346577 * 2
def baseEnd_8346577 : Nat := 4285805820762095712802297

theorem tailTrace_8346577 : CollatzResearch.WordTrace tailWord_8346577 prefixEnd_8346577 4285805820762095712802297 := by
  unfold tailWord_8346577
  simp only [CollatzResearch.WordTrace]
  refine ⟨304424672682784485708301985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202949781788522990472201323 304424672682784485708301985)
  ·
    refine ⟨228318504512088364281226489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304424672682784485708301985 228318504512088364281226489)
    ·
      refine ⟨171238878384066273210919867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228318504512088364281226489 171238878384066273210919867)
      ·
        refine ⟨256858317576099409816379801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171238878384066273210919867 256858317576099409816379801)
        ·
          refine ⟨192643738182074557362284851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256858317576099409816379801 192643738182074557362284851)
          ·
            refine ⟨288965607273111836043427277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192643738182074557362284851 288965607273111836043427277)
            ·
              refine ⟨108362102727416938516285229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288965607273111836043427277 108362102727416938516285229)
              ·
                refine ⟨40635788522781351943606961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108362102727416938516285229 40635788522781351943606961)
                ·
                  refine ⟨30476841392086013957705221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40635788522781351943606961 30476841392086013957705221)
                  ·
                    refine ⟨5714407761016127617069729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30476841392086013957705221 5714407761016127617069729)
                    ·
                      refine ⟨4285805820762095712802297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5714407761016127617069729 4285805820762095712802297)
                      ·
                        rfl

theorem cell23_8346577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 4, 2].length) (baseStart_8346577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346577 prefixEnd_8346577 := by exact prefixLift 8346577
  have htrace : WordTrace (prefixWord ++ tailWord_8346577) baseStart_8346577 baseEnd_8346577 := by
    simpa [prefixWord, tailWord_8346577, baseEnd_8346577] using wordTrace_append hprefix tailTrace_8346577
  have hstable : (prefixWord ++ tailWord_8346577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346577).length < 2 ^ (prefixWord ++ tailWord_8346577).sum := by decide
  have hdescent : baseEnd_8346577 < baseStart_8346577 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346594 : List Nat := [3, 3, 3, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_8346594 : Nat := 118140960795 + 8346594 * 2 ^ 59
def prefixEnd_8346594 : Nat := 4983230072969 + 3 ^ 40 * 8346594 * 2
def baseEnd_8346594 : Nat := 4285814549933222146289719

theorem tailTrace_8346594 : CollatzResearch.WordTrace tailWord_8346594 prefixEnd_8346594 4285814549933222146289719 := by
  unfold tailWord_8346594
  simp only [CollatzResearch.WordTrace]
  refine ⟨76106323180930724402917709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202950195149148598407780557 76106323180930724402917709)
  ·
    refine ⟨28539871192849021651094141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76106323180930724402917709 28539871192849021651094141)
    ·
      refine ⟨10702451697318383119160303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28539871192849021651094141 10702451697318383119160303)
      ·
        refine ⟨16053677545977574678740455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10702451697318383119160303 16053677545977574678740455)
        ·
          refine ⟨24080516318966362018110683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16053677545977574678740455 24080516318966362018110683)
          ·
            refine ⟨36120774478449543027166025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24080516318966362018110683 36120774478449543027166025)
            ·
              refine ⟨27090580858837157270374519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36120774478449543027166025 27090580858837157270374519)
              ·
                refine ⟨40635871288255735905561779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27090580858837157270374519 40635871288255735905561779)
                ·
                  refine ⟨60953806932383603858342669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40635871288255735905561779 60953806932383603858342669)
                  ·
                    refine ⟨22857677599643851446878501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60953806932383603858342669 22857677599643851446878501)
                    ·
                      refine ⟨4285814549933222146289719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22857677599643851446878501 4285814549933222146289719)
                      ·
                        rfl

theorem cell23_8346594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_8346594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346594 prefixEnd_8346594 := by exact prefixLift 8346594
  have htrace : WordTrace (prefixWord ++ tailWord_8346594) baseStart_8346594 baseEnd_8346594 := by
    simpa [prefixWord, tailWord_8346594, baseEnd_8346594] using wordTrace_append hprefix tailTrace_8346594
  have hstable : (prefixWord ++ tailWord_8346594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346594).length < 2 ^ (prefixWord ++ tailWord_8346594).sum := by decide
  have hdescent : baseEnd_8346594 < baseStart_8346594 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346600 : List Nat := [2, 1, 4, 1, 1, 1, 3, 2, 8]
def baseStart_8346600 : Nat := 118140960795 + 8346600 * 2 ^ 59
def prefixEnd_8346600 : Nat := 4983230072969 + 3 ^ 40 * 8346600 * 2
def baseEnd_8346600 : Nat := 476201958979683235868299

theorem tailTrace_8346600 : CollatzResearch.WordTrace tailWord_8346600 prefixEnd_8346600 476201958979683235868299 := by
  unfold tailWord_8346600
  simp only [CollatzResearch.WordTrace]
  refine ⟨152212755780850580318194627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202950341041134107090926169 152212755780850580318194627)
  ·
    refine ⟨228319133671275870477291941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152212755780850580318194627 228319133671275870477291941)
    ·
      refine ⟨42809837563364225714492239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228319133671275870477291941 42809837563364225714492239)
      ·
        refine ⟨64214756345046338571738359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42809837563364225714492239 64214756345046338571738359)
        ·
          refine ⟨96322134517569507857607539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64214756345046338571738359 96322134517569507857607539)
          ·
            refine ⟨144483201776354261786411309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96322134517569507857607539 144483201776354261786411309)
            ·
              refine ⟨54181200666132848169904241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144483201776354261786411309 54181200666132848169904241)
              ·
                refine ⟨40635900499599636127428181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54181200666132848169904241 40635900499599636127428181)
                ·
                  refine ⟨476201958979683235868299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40635900499599636127428181 476201958979683235868299)
                  ·
                    rfl

theorem cell23_8346600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 8].length) (baseStart_8346600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346600 prefixEnd_8346600 := by exact prefixLift 8346600
  have htrace : WordTrace (prefixWord ++ tailWord_8346600) baseStart_8346600 baseEnd_8346600 := by
    simpa [prefixWord, tailWord_8346600, baseEnd_8346600] using wordTrace_append hprefix tailTrace_8346600
  have hstable : (prefixWord ++ tailWord_8346600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346600).length < 2 ^ (prefixWord ++ tailWord_8346600).sum := by decide
  have hdescent : baseEnd_8346600 < baseStart_8346600 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346612 : List Nat := [2, 6, 2, 1, 1, 1, 3, 2, 5]
def baseStart_8346612 : Nat := 118140960795 + 8346612 * 2 ^ 59
def prefixEnd_8346612 : Nat := 4983230072969 + 3 ^ 40 * 8346612 * 2
def baseEnd_8346612 : Nat := 476202643620555897318293

theorem tailTrace_8346612 : CollatzResearch.WordTrace tailWord_8346612 prefixEnd_8346612 476202643620555897318293 := by
  unfold tailWord_8346612
  simp only [CollatzResearch.WordTrace]
  refine ⟨152212974618828843342913045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202950632825105124457217393 152212974618828843342913045)
  ·
    refine ⟨7134983185257602031699049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152212974618828843342913045 7134983185257602031699049)
    ·
      refine ⟨5351237388943201523774287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7134983185257602031699049 5351237388943201523774287)
      ·
        refine ⟨8026856083414802285661431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5351237388943201523774287 8026856083414802285661431)
        ·
          refine ⟨12040284125122203428492147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8026856083414802285661431 12040284125122203428492147)
          ·
            refine ⟨18060426187683305142738221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12040284125122203428492147 18060426187683305142738221)
            ·
              refine ⟨6772659820381239428526833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18060426187683305142738221 6772659820381239428526833)
              ·
                refine ⟨5079494865285929571395125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6772659820381239428526833 5079494865285929571395125)
                ·
                  refine ⟨476202643620555897318293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5079494865285929571395125 476202643620555897318293)
                  ·
                    rfl

theorem cell23_8346612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_8346612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346612 prefixEnd_8346612 := by exact prefixLift 8346612
  have htrace : WordTrace (prefixWord ++ tailWord_8346612) baseStart_8346612 baseEnd_8346612 := by
    simpa [prefixWord, tailWord_8346612, baseEnd_8346612] using wordTrace_append hprefix tailTrace_8346612
  have hstable : (prefixWord ++ tailWord_8346612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346612).length < 2 ^ (prefixWord ++ tailWord_8346612).sum := by decide
  have hdescent : baseEnd_8346612 < baseStart_8346612 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346614 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3]
def baseStart_8346614 : Nat := 118140960795 + 8346614 * 2 ^ 59
def prefixEnd_8346614 : Nat := 4983230072969 + 3 ^ 40 * 8346614 * 2
def baseEnd_8346614 : Nat := 4285824819546312068039627

theorem tailTrace_8346614 : CollatzResearch.WordTrace tailWord_8346614 prefixEnd_8346614 4285824819546312068039627 := by
  unfold tailWord_8346614
  simp only [CollatzResearch.WordTrace]
  refine ⟨19026626386478152564212431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202950681455766960684932597 19026626386478152564212431)
  ·
    refine ⟨28539939579717228846318647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19026626386478152564212431 28539939579717228846318647)
    ·
      refine ⟨42809909369575843269477971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28539939579717228846318647 42809909369575843269477971)
      ·
        refine ⟨64214864054363764904216957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42809909369575843269477971 64214864054363764904216957)
        ·
          refine ⟨24080574020386411839081359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64214864054363764904216957 24080574020386411839081359)
          ·
            refine ⟨36120861030579617758622039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24080574020386411839081359 36120861030579617758622039)
            ·
              refine ⟨54181291545869426637933059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36120861030579617758622039 54181291545869426637933059)
              ·
                refine ⟨81271937318804139956899589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54181291545869426637933059 81271937318804139956899589)
                ·
                  refine ⟨15238488247275776241918673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81271937318804139956899589 15238488247275776241918673)
                  ·
                    refine ⟨11428866185456832181439005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15238488247275776241918673 11428866185456832181439005)
                    ·
                      refine ⟨4285824819546312068039627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11428866185456832181439005 4285824819546312068039627)
                      ·
                        rfl

theorem cell23_8346614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_8346614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346614 prefixEnd_8346614 := by exact prefixLift 8346614
  have htrace : WordTrace (prefixWord ++ tailWord_8346614) baseStart_8346614 baseEnd_8346614 := by
    simpa [prefixWord, tailWord_8346614, baseEnd_8346614] using wordTrace_append hprefix tailTrace_8346614
  have hstable : (prefixWord ++ tailWord_8346614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346614).length < 2 ^ (prefixWord ++ tailWord_8346614).sum := by decide
  have hdescent : baseEnd_8346614 < baseStart_8346614 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346634 : List Nat := [3, 1, 2, 2, 3, 1, 4, 1, 6]
def baseStart_8346634 : Nat := 118140960795 + 8346634 * 2 ^ 59
def prefixEnd_8346634 : Nat := 4983230072969 + 3 ^ 40 * 8346634 * 2
def baseEnd_8346634 : Nat := 476203898795489109976615

theorem tailTrace_8346634 : CollatzResearch.WordTrace tailWord_8346634 prefixEnd_8346634 476203898795489109976615 := by
  unfold tailWord_8346634
  simp only [CollatzResearch.WordTrace]
  refine ⟨76106687910894496110781739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202951167762385322962084637 76106687910894496110781739)
  ·
    refine ⟨114160031866341744166172609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76106687910894496110781739 114160031866341744166172609)
    ·
      refine ⟨85620023899756308124629457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114160031866341744166172609 85620023899756308124629457)
      ·
        refine ⟨64215017924817231093472093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85620023899756308124629457 64215017924817231093472093)
        ·
          refine ⟨24080631721806461660052035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64215017924817231093472093 24080631721806461660052035)
          ·
            refine ⟨36120947582709692490078053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24080631721806461660052035 36120947582709692490078053)
            ·
              refine ⟨6772677671758067341889635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36120947582709692490078053 6772677671758067341889635)
              ·
                refine ⟨10159016507637101012834453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6772677671758067341889635 10159016507637101012834453)
                ·
                  refine ⟨476203898795489109976615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10159016507637101012834453 476203898795489109976615)
                  ·
                    rfl

theorem cell23_8346634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 6].length) (baseStart_8346634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346634 prefixEnd_8346634 := by exact prefixLift 8346634
  have htrace : WordTrace (prefixWord ++ tailWord_8346634) baseStart_8346634 baseEnd_8346634 := by
    simpa [prefixWord, tailWord_8346634, baseEnd_8346634] using wordTrace_append hprefix tailTrace_8346634
  have hstable : (prefixWord ++ tailWord_8346634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346634).length < 2 ^ (prefixWord ++ tailWord_8346634).sum := by decide
  have hdescent : baseEnd_8346634 < baseStart_8346634 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346661 : List Nat := [1, 3, 1, 2, 2, 2, 2, 5, 1, 1, 3]
def baseStart_8346661 : Nat := 118140960795 + 8346661 * 2 ^ 59
def prefixEnd_8346661 : Nat := 4983230072969 + 3 ^ 40 * 8346661 * 2
def baseEnd_8346661 : Nat := 4285848953137073384151911

theorem tailTrace_8346661 : CollatzResearch.WordTrace tailWord_8346661 prefixEnd_8346661 4285848953137073384151911 := by
  unfold tailWord_8346661
  simp only [CollatzResearch.WordTrace]
  refine ⟨304427736414480168054359837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202951824276320112036239891 304427736414480168054359837)
  ·
    refine ⟨114160401155430063020384939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304427736414480168054359837 114160401155430063020384939)
    ·
      refine ⟨171240601733145094530577409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114160401155430063020384939 171240601733145094530577409)
      ·
        refine ⟨128430451299858820897933057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171240601733145094530577409 128430451299858820897933057)
        ·
          refine ⟨96322838474894115673449793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128430451299858820897933057 96322838474894115673449793)
          ·
            refine ⟨72242128856170586755087345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96322838474894115673449793 72242128856170586755087345)
            ·
              refine ⟨54181596642127940066315509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72242128856170586755087345 54181596642127940066315509)
              ·
                refine ⟨5079524685199494381217079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54181596642127940066315509 5079524685199494381217079)
                ·
                  refine ⟨7619287027799241571825619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5079524685199494381217079 7619287027799241571825619)
                  ·
                    refine ⟨11428930541698862357738429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7619287027799241571825619 11428930541698862357738429)
                    ·
                      refine ⟨4285848953137073384151911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11428930541698862357738429 4285848953137073384151911)
                      ·
                        rfl

theorem cell23_8346661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5, 1, 1, 3].length) (baseStart_8346661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346661 prefixEnd_8346661 := by exact prefixLift 8346661
  have htrace : WordTrace (prefixWord ++ tailWord_8346661) baseStart_8346661 baseEnd_8346661 := by
    simpa [prefixWord, tailWord_8346661, baseEnd_8346661] using wordTrace_append hprefix tailTrace_8346661
  have hstable : (prefixWord ++ tailWord_8346661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346661).length < 2 ^ (prefixWord ++ tailWord_8346661).sum := by decide
  have hdescent : baseEnd_8346661 < baseStart_8346661 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346721 : List Nat := [1, 2, 3, 1, 1, 2, 6, 1, 1, 2, 3]
def baseStart_8346721 : Nat := 118140960795 + 8346721 * 2 ^ 59
def prefixEnd_8346721 : Nat := 4983230072969 + 3 ^ 40 * 8346721 * 2
def baseEnd_8346721 : Nat := 4285879761976343149401635

theorem tailTrace_8346721 : CollatzResearch.WordTrace tailWord_8346721 prefixEnd_8346721 4285879761976343149401635 := by
  unfold tailWord_8346721
  simp only [CollatzResearch.WordTrace]
  refine ⟨304429924794262798301544017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202953283196175198867696011 304429924794262798301544017)
  ·
    refine ⟨228322443595697098726158013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304429924794262798301544017 228322443595697098726158013)
    ·
      refine ⟨85620916348386412022309255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228322443595697098726158013 85620916348386412022309255)
      ·
        refine ⟨128431374522579618033463883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85620916348386412022309255 128431374522579618033463883)
        ·
          refine ⟨192647061783869427050195825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128431374522579618033463883 192647061783869427050195825)
          ·
            refine ⟨144485296337902070287646869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192647061783869427050195825 144485296337902070287646869)
            ·
              refine ⟨6772748265839159544733447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144485296337902070287646869 6772748265839159544733447)
              ·
                refine ⟨10159122398758739317100171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6772748265839159544733447 10159122398758739317100171)
                ·
                  refine ⟨15238683598138108975650257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10159122398758739317100171 15238683598138108975650257)
                  ·
                    refine ⟨11429012698603581731737693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15238683598138108975650257 11429012698603581731737693)
                    ·
                      refine ⟨4285879761976343149401635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11429012698603581731737693 4285879761976343149401635)
                      ·
                        rfl

theorem cell23_8346721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 1, 2, 3].length) (baseStart_8346721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346721 prefixEnd_8346721 := by exact prefixLift 8346721
  have htrace : WordTrace (prefixWord ++ tailWord_8346721) baseStart_8346721 baseEnd_8346721 := by
    simpa [prefixWord, tailWord_8346721, baseEnd_8346721] using wordTrace_append hprefix tailTrace_8346721
  have hstable : (prefixWord ++ tailWord_8346721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346721).length < 2 ^ (prefixWord ++ tailWord_8346721).sum := by decide
  have hdescent : baseEnd_8346721 < baseStart_8346721 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346744 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 5, 3, 2]
def baseStart_8346744 : Nat := 118140960795 + 8346744 * 2 ^ 59
def prefixEnd_8346744 : Nat := 4983230072969 + 3 ^ 40 * 8346744 * 2
def baseEnd_8346744 : Nat := 4285891572031396559414029

theorem tailTrace_8346744 : CollatzResearch.WordTrace tailWord_8346744 prefixEnd_8346744 4285891572031396559414029 := by
  unfold tailWord_8346744
  simp only [CollatzResearch.WordTrace]
  refine ⟨152215381836589736614815643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202953842448786315486420857 152215381836589736614815643)
  ·
    refine ⟨228323072754884604922223465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152215381836589736614815643 228323072754884604922223465)
    ·
      refine ⟨171242304566163453691667599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228323072754884604922223465 171242304566163453691667599)
      ·
        refine ⟨256863456849245180537501399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171242304566163453691667599 256863456849245180537501399)
        ·
          refine ⟨385295185273867770806252099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256863456849245180537501399 385295185273867770806252099)
          ·
            refine ⟨577942777910801656209378149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385295185273867770806252099 577942777910801656209378149)
            ·
              refine ⟨108364270858275310539258403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 577942777910801656209378149 108364270858275310539258403)
              ·
                refine ⟨162546406287412965808887605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108364270858275310539258403 162546406287412965808887605)
                ·
                  refine ⟨15238725589444965544583213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162546406287412965808887605 15238725589444965544583213)
                  ·
                    refine ⟨5714522096041862079218705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15238725589444965544583213 5714522096041862079218705)
                    ·
                      refine ⟨4285891572031396559414029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5714522096041862079218705 4285891572031396559414029)
                      ·
                        rfl

theorem cell23_8346744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 5, 3, 2].length) (baseStart_8346744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346744 prefixEnd_8346744 := by exact prefixLift 8346744
  have htrace : WordTrace (prefixWord ++ tailWord_8346744) baseStart_8346744 baseEnd_8346744 := by
    simpa [prefixWord, tailWord_8346744, baseEnd_8346744] using wordTrace_append hprefix tailTrace_8346744
  have hstable : (prefixWord ++ tailWord_8346744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346744).length < 2 ^ (prefixWord ++ tailWord_8346744).sum := by decide
  have hdescent : baseEnd_8346744 < baseStart_8346744 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346761 : List Nat := [1, 2, 1, 1, 4, 3, 1, 4, 1, 3, 2]
def baseStart_8346761 : Nat := 118140960795 + 8346761 * 2 ^ 59
def prefixEnd_8346761 : Nat := 4983230072969 + 3 ^ 40 * 8346761 * 2
def baseEnd_8346761 : Nat := 4285900301202522992901451

theorem tailTrace_8346761 : CollatzResearch.WordTrace tailWord_8346761 prefixEnd_8346761 4285900301202522992901451 := by
  unfold tailWord_8346761
  simp only [CollatzResearch.WordTrace]
  refine ⟨304431383714117885133000137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202954255809411923422000091 304431383714117885133000137)
  ·
    refine ⟨228323537785588413849750103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304431383714117885133000137 228323537785588413849750103)
    ·
      refine ⟨342485306678382620774625155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228323537785588413849750103 342485306678382620774625155)
      ·
        refine ⟨513727960017573931161937733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342485306678382620774625155 513727960017573931161937733)
        ·
          refine ⟨96323992503295112092863325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 513727960017573931161937733 96323992503295112092863325)
          ·
            refine ⟨36121497188735667034823747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96323992503295112092863325 36121497188735667034823747)
            ·
              refine ⟨54182245783103500552235621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36121497188735667034823747 54182245783103500552235621)
              ·
                refine ⟨10159171084331906353544179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54182245783103500552235621 10159171084331906353544179)
                ·
                  refine ⟨15238756626497859530316269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10159171084331906353544179 15238756626497859530316269)
                  ·
                    refine ⟨5714533734936697323868601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15238756626497859530316269 5714533734936697323868601)
                    ·
                      refine ⟨4285900301202522992901451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5714533734936697323868601 4285900301202522992901451)
                      ·
                        rfl

theorem cell23_8346761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 3, 2].length) (baseStart_8346761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346761 prefixEnd_8346761 := by exact prefixLift 8346761
  have htrace : WordTrace (prefixWord ++ tailWord_8346761) baseStart_8346761 baseEnd_8346761 := by
    simpa [prefixWord, tailWord_8346761, baseEnd_8346761] using wordTrace_append hprefix tailTrace_8346761
  have hstable : (prefixWord ++ tailWord_8346761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346761).length < 2 ^ (prefixWord ++ tailWord_8346761).sum := by decide
  have hdescent : baseEnd_8346761 < baseStart_8346761 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346777 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 3, 6, 3]
def baseStart_8346777 : Nat := 118140960795 + 8346777 * 2 ^ 59
def prefixEnd_8346777 : Nat := 4983230072969 + 3 ^ 40 * 8346777 * 2
def baseEnd_8346777 : Nat := 4285908516892994930301377

theorem tailTrace_8346777 : CollatzResearch.WordTrace tailWord_8346777 prefixEnd_8346777 4285908516892994930301377 := by
  unfold tailWord_8346777
  simp only [CollatzResearch.WordTrace]
  refine ⟨304431967282059919865582585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202954644854706613243721723 304431967282059919865582585)
  ·
    refine ⟨228323975461544939899186939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304431967282059919865582585 228323975461544939899186939)
    ·
      refine ⟨342485963192317409848780409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228323975461544939899186939 342485963192317409848780409)
      ·
        refine ⟨256864472394238057386585307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342485963192317409848780409 256864472394238057386585307)
        ·
          refine ⟨385296708591357086079877961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256864472394238057386585307 385296708591357086079877961)
          ·
            refine ⟨288972531443517814559908471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385296708591357086079877961 288972531443517814559908471)
            ·
              refine ⟨433458797165276721839862707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288972531443517814559908471 433458797165276721839862707)
              ·
                refine ⟨650188195747915082759794061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433458797165276721839862707 650188195747915082759794061)
                ·
                  refine ⟨243820573405468156034922773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 650188195747915082759794061 243820573405468156034922773)
                  ·
                    refine ⟨11429089378381319814137005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 243820573405468156034922773 11429089378381319814137005)
                    ·
                      refine ⟨4285908516892994930301377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11429089378381319814137005 4285908516892994930301377)
                      ·
                        rfl

theorem cell23_8346777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 6, 3].length) (baseStart_8346777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346777 prefixEnd_8346777 := by exact prefixLift 8346777
  have htrace : WordTrace (prefixWord ++ tailWord_8346777) baseStart_8346777 baseEnd_8346777 := by
    simpa [prefixWord, tailWord_8346777, baseEnd_8346777] using wordTrace_append hprefix tailTrace_8346777
  have hstable : (prefixWord ++ tailWord_8346777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346777).length < 2 ^ (prefixWord ++ tailWord_8346777).sum := by decide
  have hdescent : baseEnd_8346777 < baseStart_8346777 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346778 : List Nat := [3, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2]
def baseStart_8346778 : Nat := 118140960795 + 8346778 * 2 ^ 59
def prefixEnd_8346778 : Nat := 4983230072969 + 3 ^ 40 * 8346778 * 2
def baseEnd_8346778 : Nat := 4285909030373649426388873

theorem tailTrace_8346778 : CollatzResearch.WordTrace tailWord_8346778 prefixEnd_8346778 4285909030373649426388873 := by
  unfold tailWord_8346778
  simp only [CollatzResearch.WordTrace]
  refine ⟨76108000938764074259092247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202954669170037531357579325 76108000938764074259092247)
  ·
    refine ⟨114162001408146111388638371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76108000938764074259092247 114162001408146111388638371)
    ·
      refine ⟨171243002112219167082957557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114162001408146111388638371 171243002112219167082957557)
      ·
        refine ⟨16054031448020546914027271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171243002112219167082957557 16054031448020546914027271)
        ·
          refine ⟨24081047172030820371040907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16054031448020546914027271 24081047172030820371040907)
          ·
            refine ⟨36121570758046230556561361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24081047172030820371040907 36121570758046230556561361)
            ·
              refine ⟨27091178068534672917421021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36121570758046230556561361 27091178068534672917421021)
              ·
                refine ⟨10159191775700502344032883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27091178068534672917421021 10159191775700502344032883)
                ·
                  refine ⟨15238787663550753516049325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10159191775700502344032883 15238787663550753516049325)
                  ·
                    refine ⟨5714545373831532568518497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15238787663550753516049325 5714545373831532568518497)
                    ·
                      refine ⟨4285909030373649426388873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5714545373831532568518497 4285909030373649426388873)
                      ·
                        rfl

theorem cell23_8346778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_8346778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346778 prefixEnd_8346778 := by exact prefixLift 8346778
  have htrace : WordTrace (prefixWord ++ tailWord_8346778) baseStart_8346778 baseEnd_8346778 := by
    simpa [prefixWord, tailWord_8346778, baseEnd_8346778] using wordTrace_append hprefix tailTrace_8346778
  have hstable : (prefixWord ++ tailWord_8346778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346778).length < 2 ^ (prefixWord ++ tailWord_8346778).sum := by decide
  have hdescent : baseEnd_8346778 < baseStart_8346778 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346787 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 4]
def baseStart_8346787 : Nat := 118140960795 + 8346787 * 2 ^ 59
def prefixEnd_8346787 : Nat := 4983230072969 + 3 ^ 40 * 8346787 * 2
def baseEnd_8346787 : Nat := 4285913651699539891176331

theorem tailTrace_8346787 : CollatzResearch.WordTrace tailWord_8346787 prefixEnd_8346787 4285913651699539891176331 := by
  unfold tailWord_8346787
  simp only [CollatzResearch.WordTrace]
  refine ⟨304432332012023691573446615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202954888008015794382297743 304432332012023691573446615)
  ·
    refine ⟨456648498018035537360169923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304432332012023691573446615 456648498018035537360169923)
    ·
      refine ⟨684972747027053306040254885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456648498018035537360169923 684972747027053306040254885)
      ·
        refine ⟨128432390067572494882547791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 684972747027053306040254885 128432390067572494882547791)
        ·
          refine ⟨192648585101358742323821687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128432390067572494882547791 192648585101358742323821687)
          ·
            refine ⟨288972877652038113485732531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192648585101358742323821687 288972877652038113485732531)
            ·
              refine ⟨433459316478057170228598797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288972877652038113485732531 433459316478057170228598797)
              ·
                refine ⟨162547243679271438835724549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 433459316478057170228598797 162547243679271438835724549)
                ·
                  refine ⟨30477608189863394781698353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162547243679271438835724549 30477608189863394781698353)
                  ·
                    refine ⟨22858206142397546086273765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30477608189863394781698353 22858206142397546086273765)
                    ·
                      refine ⟨4285913651699539891176331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22858206142397546086273765 4285913651699539891176331)
                      ·
                        rfl

theorem cell23_8346787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_8346787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346787 prefixEnd_8346787 := by exact prefixLift 8346787
  have htrace : WordTrace (prefixWord ++ tailWord_8346787) baseStart_8346787 baseEnd_8346787 := by
    simpa [prefixWord, tailWord_8346787, baseEnd_8346787] using wordTrace_append hprefix tailTrace_8346787
  have hstable : (prefixWord ++ tailWord_8346787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346787).length < 2 ^ (prefixWord ++ tailWord_8346787).sum := by decide
  have hdescent : baseEnd_8346787 < baseStart_8346787 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346829 : List Nat := [1, 6, 2, 2, 1, 1, 3, 1, 1, 3, 2]
def baseStart_8346829 : Nat := 118140960795 + 8346829 * 2 ^ 59
def prefixEnd_8346829 : Nat := 4983230072969 + 3 ^ 40 * 8346829 * 2
def baseEnd_8346829 : Nat := 4285935217887028726851139

theorem tailTrace_8346829 : CollatzResearch.WordTrace tailWord_8346829 prefixEnd_8346829 4285935217887028726851139 := by
  unfold tailWord_8346829
  simp only [CollatzResearch.WordTrace]
  refine ⟨304433863877871532746475541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202955909251914355164317027 304433863877871532746475541)
  ·
    refine ⟨14270337369275228097491041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 304433863877871532746475541 14270337369275228097491041)
    ·
      refine ⟨10702753026956421073118281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14270337369275228097491041 10702753026956421073118281)
      ·
        refine ⟨8027064770217315804838711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10702753026956421073118281 8027064770217315804838711)
        ·
          refine ⟨12040597155325973707258067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8027064770217315804838711 12040597155325973707258067)
          ·
            refine ⟨18060895732988960560887101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12040597155325973707258067 18060895732988960560887101)
            ·
              refine ⟨6772835899870860210332663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18060895732988960560887101 6772835899870860210332663)
              ·
                refine ⟨10159253849806290315498995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6772835899870860210332663 10159253849806290315498995)
                ·
                  refine ⟨15238880774709435473248493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10159253849806290315498995 15238880774709435473248493)
                  ·
                    refine ⟨5714580290516038302468185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15238880774709435473248493 5714580290516038302468185)
                    ·
                      refine ⟨4285935217887028726851139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5714580290516038302468185 4285935217887028726851139)
                      ·
                        rfl

theorem cell23_8346829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_8346829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346829 prefixEnd_8346829 := by exact prefixLift 8346829
  have htrace : WordTrace (prefixWord ++ tailWord_8346829) baseStart_8346829 baseEnd_8346829 := by
    simpa [prefixWord, tailWord_8346829, baseEnd_8346829] using wordTrace_append hprefix tailTrace_8346829
  have hstable : (prefixWord ++ tailWord_8346829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346829).length < 2 ^ (prefixWord ++ tailWord_8346829).sum := by decide
  have hdescent : baseEnd_8346829 < baseStart_8346829 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346848 : List Nat := [2, 1, 1, 3, 1, 6, 2, 2, 5]
def baseStart_8346848 : Nat := 118140960795 + 8346848 * 2 ^ 59
def prefixEnd_8346848 : Nat := 4983230072969 + 3 ^ 40 * 8346848 * 2
def baseEnd_8346848 : Nat := 476216108224384905834839

theorem tailTrace_8346848 : CollatzResearch.WordTrace tailWord_8346848 prefixEnd_8346848 476216108224384905834839 := by
  unfold tailWord_8346848
  simp only [CollatzResearch.WordTrace]
  refine ⟨152217278432401349495708599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202956371243201799327611465 152217278432401349495708599)
  ·
    refine ⟨228325917648602024243562899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152217278432401349495708599 228325917648602024243562899)
    ·
      refine ⟨342488876472903036365344349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228325917648602024243562899 342488876472903036365344349)
      ·
        refine ⟨128433328677338638637004131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342488876472903036365344349 128433328677338638637004131)
        ·
          refine ⟨192649993016007957955506197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128433328677338638637004131 192649993016007957955506197)
          ·
            refine ⟨9030468422625373029164353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 192649993016007957955506197 9030468422625373029164353)
            ·
              refine ⟨6772851316969029771873265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9030468422625373029164353 6772851316969029771873265)
              ·
                refine ⟨5079638487726772328904949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6772851316969029771873265 5079638487726772328904949)
                ·
                  refine ⟨476216108224384905834839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5079638487726772328904949 476216108224384905834839)
                  ·
                    rfl

theorem cell23_8346848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2, 5].length) (baseStart_8346848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346848 prefixEnd_8346848 := by exact prefixLift 8346848
  have htrace : WordTrace (prefixWord ++ tailWord_8346848) baseStart_8346848 baseEnd_8346848 := by
    simpa [prefixWord, tailWord_8346848, baseEnd_8346848] using wordTrace_append hprefix tailTrace_8346848
  have hstable : (prefixWord ++ tailWord_8346848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346848).length < 2 ^ (prefixWord ++ tailWord_8346848).sum := by decide
  have hdescent : baseEnd_8346848 < baseStart_8346848 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346878 : List Nat := [4, 2, 2, 1, 1, 4, 1, 1, 2, 5]
def baseStart_8346878 : Nat := 118140960795 + 8346878 * 2 ^ 59
def prefixEnd_8346878 : Nat := 4983230072969 + 3 ^ 40 * 8346878 * 2
def baseEnd_8346878 : Nat := 1428653459479699678379471

theorem tailTrace_8346878 : CollatzResearch.WordTrace tailWord_8346878 prefixEnd_8346878 1428653459479699678379471 := by
  unfold tailWord_8346878
  simp only [CollatzResearch.WordTrace]
  refine ⟨38054456381836751764376161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202957100703129342743339525 38054456381836751764376161)
  ·
    refine ⟨28540842286377563823282121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38054456381836751764376161 28540842286377563823282121)
    ·
      refine ⟨21405631714783172867461591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28540842286377563823282121 21405631714783172867461591)
      ·
        refine ⟨32108447572174759301192387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21405631714783172867461591 32108447572174759301192387)
        ·
          refine ⟨48162671358262138951788581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32108447572174759301192387 48162671358262138951788581)
          ·
            refine ⟨9030500879674151053460359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48162671358262138951788581 9030500879674151053460359)
            ·
              refine ⟨13545751319511226580190539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9030500879674151053460359 13545751319511226580190539)
              ·
                refine ⟨20318626979266839870285809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13545751319511226580190539 20318626979266839870285809)
                ·
                  refine ⟨15238970234450129902714357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20318626979266839870285809 15238970234450129902714357)
                  ·
                    refine ⟨1428653459479699678379471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15238970234450129902714357 1428653459479699678379471)
                    ·
                      rfl

theorem cell23_8346878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_8346878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346878 prefixEnd_8346878 := by exact prefixLift 8346878
  have htrace : WordTrace (prefixWord ++ tailWord_8346878) baseStart_8346878 baseEnd_8346878 := by
    simpa [prefixWord, tailWord_8346878, baseEnd_8346878] using wordTrace_append hprefix tailTrace_8346878
  have hstable : (prefixWord ++ tailWord_8346878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346878).length < 2 ^ (prefixWord ++ tailWord_8346878).sum := by decide
  have hdescent : baseEnd_8346878 < baseStart_8346878 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346881 : List Nat := [1, 2, 4, 1, 1, 3, 3, 1, 2, 1, 4]
def baseStart_8346881 : Nat := 118140960795 + 8346881 * 2 ^ 59
def prefixEnd_8346881 : Nat := 4983230072969 + 3 ^ 40 * 8346881 * 2
def baseEnd_8346881 : Nat := 4285961918881062523400899

theorem tailTrace_8346881 : CollatzResearch.WordTrace tailWord_8346881 prefixEnd_8346881 4285961918881062523400899 := by
  unfold tailWord_8346881
  simp only [CollatzResearch.WordTrace]
  refine ⟨304435760473683145627368497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202957173649122097084912331 304435760473683145627368497)
  ·
    refine ⟨228326820355262359220526373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304435760473683145627368497 228326820355262359220526373)
    ·
      refine ⟨42811278816611692353848695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228326820355262359220526373 42811278816611692353848695)
      ·
        refine ⟨64216918224917538530773043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42811278816611692353848695 64216918224917538530773043)
        ·
          refine ⟨96325377337376307796159565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64216918224917538530773043 96325377337376307796159565)
          ·
            refine ⟨36122016501516115423559837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96325377337376307796159565 36122016501516115423559837)
            ·
              refine ⟨13545756188068543283834939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36122016501516115423559837 13545756188068543283834939)
              ·
                refine ⟨20318634282102814925752409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13545756188068543283834939 20318634282102814925752409)
                ·
                  refine ⟨15238975711577111194314307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20318634282102814925752409 15238975711577111194314307)
                  ·
                    refine ⟨22858463567365666791471461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15238975711577111194314307 22858463567365666791471461)
                    ·
                      refine ⟨4285961918881062523400899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22858463567365666791471461 4285961918881062523400899)
                      ·
                        rfl

theorem cell23_8346881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_8346881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346881 prefixEnd_8346881 := by exact prefixLift 8346881
  have htrace : WordTrace (prefixWord ++ tailWord_8346881) baseStart_8346881 baseEnd_8346881 := by
    simpa [prefixWord, tailWord_8346881, baseEnd_8346881] using wordTrace_append hprefix tailTrace_8346881
  have hstable : (prefixWord ++ tailWord_8346881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346881).length < 2 ^ (prefixWord ++ tailWord_8346881).sum := by decide
  have hdescent : baseEnd_8346881 < baseStart_8346881 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346894 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6]
def baseStart_8346894 : Nat := 118140960795 + 8346894 * 2 ^ 59
def prefixEnd_8346894 : Nat := 4983230072969 + 3 ^ 40 * 8346894 * 2
def baseEnd_8346894 : Nat := 4285968594129570972538339

theorem tailTrace_8346894 : CollatzResearch.WordTrace tailWord_8346894 prefixEnd_8346894 4285968594129570972538339 := by
  unfold tailWord_8346894
  simp only [CollatzResearch.WordTrace]
  refine ⟨38054529327829506105948967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202957489748424032565061157 38054529327829506105948967)
  ·
    refine ⟨57081793991744259158923451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38054529327829506105948967 57081793991744259158923451)
    ·
      refine ⟨85622690987616388738385177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57081793991744259158923451 85622690987616388738385177)
      ·
        refine ⟨64217018240712291553788883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85622690987616388738385177 64217018240712291553788883)
        ·
          refine ⟨96325527361068437330683325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64217018240712291553788883 96325527361068437330683325)
          ·
            refine ⟨36122072760400663999006247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96325527361068437330683325 36122072760400663999006247)
            ·
              refine ⟨54183109140600995998509371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36122072760400663999006247 54183109140600995998509371)
              ·
                refine ⟨81274663710901493997764057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54183109140600995998509371 81274663710901493997764057)
                ·
                  refine ⟨60955997783176120498323043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81274663710901493997764057 60955997783176120498323043)
                  ·
                    refine ⟨91433996674764180747484565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60955997783176120498323043 91433996674764180747484565)
                    ·
                      refine ⟨4285968594129570972538339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91433996674764180747484565 4285968594129570972538339)
                      ·
                        rfl

theorem cell23_8346894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_8346894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346894 prefixEnd_8346894 := by exact prefixLift 8346894
  have htrace : WordTrace (prefixWord ++ tailWord_8346894) baseStart_8346894 baseEnd_8346894 := by
    simpa [prefixWord, tailWord_8346894, baseEnd_8346894] using wordTrace_append hprefix tailTrace_8346894
  have hstable : (prefixWord ++ tailWord_8346894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346894).length < 2 ^ (prefixWord ++ tailWord_8346894).sum := by decide
  have hdescent : baseEnd_8346894 < baseStart_8346894 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346904 : List Nat := [2, 1, 2, 3, 1, 4, 1, 1, 8]
def baseStart_8346904 : Nat := 118140960795 + 8346904 * 2 ^ 59
def prefixEnd_8346904 : Nat := 4983230072969 + 3 ^ 40 * 8346904 * 2
def baseEnd_8346904 : Nat := 476219303215123992601477

theorem tailTrace_8346904 : CollatzResearch.WordTrace tailWord_8346904 prefixEnd_8346904 476219303215123992601477 := by
  unfold tailWord_8346904
  simp only [CollatzResearch.WordTrace]
  refine ⟨152218299676299910277727883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202957732901733213703637177 152218299676299910277727883)
  ·
    refine ⟨228327449514449865416591825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152218299676299910277727883 228327449514449865416591825)
    ·
      refine ⟨171245587135837399062443869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228327449514449865416591825 171245587135837399062443869)
      ·
        refine ⟨64217095175939024648416451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171245587135837399062443869 64217095175939024648416451)
        ·
          refine ⟨96325642763908536972624677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64217095175939024648416451 96325642763908536972624677)
          ·
            refine ⟨18061058018232850682367127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96325642763908536972624677 18061058018232850682367127)
            ·
              refine ⟨27091587027349276023550691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18061058018232850682367127 27091587027349276023550691)
              ·
                refine ⟨40637380541023914035326037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27091587027349276023550691 40637380541023914035326037)
                ·
                  refine ⟨476219303215123992601477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40637380541023914035326037 476219303215123992601477)
                  ·
                    rfl

theorem cell23_8346904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 8].length) (baseStart_8346904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346904 prefixEnd_8346904 := by exact prefixLift 8346904
  have htrace : WordTrace (prefixWord ++ tailWord_8346904) baseStart_8346904 baseEnd_8346904 := by
    simpa [prefixWord, tailWord_8346904, baseEnd_8346904] using wordTrace_append hprefix tailTrace_8346904
  have hstable : (prefixWord ++ tailWord_8346904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346904).length < 2 ^ (prefixWord ++ tailWord_8346904).sum := by decide
  have hdescent : baseEnd_8346904 < baseStart_8346904 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346908 : List Nat := [2, 2, 3, 1, 1, 1, 4, 4, 1, 4]
def baseStart_8346908 : Nat := 118140960795 + 8346908 * 2 ^ 59
def prefixEnd_8346908 : Nat := 4983230072969 + 3 ^ 40 * 8346908 * 2
def baseEnd_8346908 : Nat := 1428658594286244639254425

theorem tailTrace_8346908 : CollatzResearch.WordTrace tailWord_8346908 prefixEnd_8346908 1428658594286244639254425 := by
  unfold tailWord_8346908
  simp only [CollatzResearch.WordTrace]
  refine ⟨152218372622292664619300689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202957830163056886159067585 152218372622292664619300689)
  ·
    refine ⟨114163779466719498464475517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152218372622292664619300689 114163779466719498464475517)
    ·
      refine ⟨42811417300019811924178319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114163779466719498464475517 42811417300019811924178319)
      ·
        refine ⟨64217125950029717886267479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42811417300019811924178319 64217125950029717886267479)
        ·
          refine ⟨96325688925044576829401219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64217125950029717886267479 96325688925044576829401219)
          ·
            refine ⟨144488533387566865244101829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96325688925044576829401219 144488533387566865244101829)
            ·
              refine ⟨27091600010168787233269093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144488533387566865244101829 27091600010168787233269093)
              ·
                refine ⟨5079675001906647606237955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27091600010168787233269093 5079675001906647606237955)
                ·
                  refine ⟨7619512502859971409356933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5079675001906647606237955 7619512502859971409356933)
                  ·
                    refine ⟨1428658594286244639254425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7619512502859971409356933 1428658594286244639254425)
                    ·
                      rfl

theorem cell23_8346908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_8346908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346908 prefixEnd_8346908 := by exact prefixLift 8346908
  have htrace : WordTrace (prefixWord ++ tailWord_8346908) baseStart_8346908 baseEnd_8346908 := by
    simpa [prefixWord, tailWord_8346908, baseEnd_8346908] using wordTrace_append hprefix tailTrace_8346908
  have hstable : (prefixWord ++ tailWord_8346908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346908).length < 2 ^ (prefixWord ++ tailWord_8346908).sum := by decide
  have hdescent : baseEnd_8346908 < baseStart_8346908 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346951 : List Nat := [1, 1, 4, 1, 2, 3, 2, 3, 1, 5]
def baseStart_8346951 : Nat := 118140960795 + 8346951 * 2 ^ 59
def prefixEnd_8346951 : Nat := 4983230072969 + 3 ^ 40 * 8346951 * 2
def baseEnd_8346951 : Nat := 1428665954175625749841859

theorem tailTrace_8346951 : CollatzResearch.WordTrace tailWord_8346951 prefixEnd_8346951 1428665954175625749841859 := by
  unfold tailWord_8346951
  simp only [CollatzResearch.WordTrace]
  refine ⟨304438313583429547582416707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202958875722286365054944471 304438313583429547582416707)
  ·
    refine ⟨456657470375144321373625061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304438313583429547582416707 456657470375144321373625061)
    ·
      refine ⟨85623275695339560257554699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 456657470375144321373625061 85623275695339560257554699)
      ·
        refine ⟨128434913543009340386332049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85623275695339560257554699 128434913543009340386332049)
        ·
          refine ⟨96326185157257005289749037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128434913543009340386332049 96326185157257005289749037)
          ·
            refine ⟨36122319433971376983655889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96326185157257005289749037 36122319433971376983655889)
            ·
              refine ⟨27091739575478532737741917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36122319433971376983655889 27091739575478532737741917)
              ·
                refine ⟨10159402340804449776653219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27091739575478532737741917 10159402340804449776653219)
                ·
                  refine ⟨15239103511206674664979829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10159402340804449776653219 15239103511206674664979829)
                  ·
                    refine ⟨1428665954175625749841859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15239103511206674664979829 1428665954175625749841859)
                    ·
                      rfl

theorem cell23_8346951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_8346951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346951 prefixEnd_8346951 := by exact prefixLift 8346951
  have htrace : WordTrace (prefixWord ++ tailWord_8346951) baseStart_8346951 baseEnd_8346951 := by
    simpa [prefixWord, tailWord_8346951, baseEnd_8346951] using wordTrace_append hprefix tailTrace_8346951
  have hstable : (prefixWord ++ tailWord_8346951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346951).length < 2 ^ (prefixWord ++ tailWord_8346951).sum := by decide
  have hdescent : baseEnd_8346951 < baseStart_8346951 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346958 : List Nat := [4, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2]
def baseStart_8346958 : Nat := 118140960795 + 8346958 * 2 ^ 59
def prefixEnd_8346958 : Nat := 4983230072969 + 3 ^ 40 * 8346958 * 2
def baseEnd_8346958 : Nat := 4286001456891458722138045

theorem tailTrace_8346958 : CollatzResearch.WordTrace tailWord_8346958 prefixEnd_8346958 4286001456891458722138045 := by
  unfold tailWord_8346958
  simp only [CollatzResearch.WordTrace]
  refine ⟨38054821111800523472240191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202959045929602791851947685 38054821111800523472240191)
  ·
    refine ⟨57082231667700785208360287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38054821111800523472240191 57082231667700785208360287)
    ·
      refine ⟨85623347501551177812540431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57082231667700785208360287 85623347501551177812540431)
      ·
        refine ⟨128435021252326766718810647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85623347501551177812540431 128435021252326766718810647)
        ·
          refine ⟨192652531878490150078215971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128435021252326766718810647 192652531878490150078215971)
          ·
            refine ⟨288978797817735225117323957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192652531878490150078215971 288978797817735225117323957)
            ·
              refine ⟨27091762295412677354749121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 288978797817735225117323957 27091762295412677354749121)
              ·
                refine ⟨20318821721559508016061841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27091762295412677354749121 20318821721559508016061841)
                ·
                  refine ⟨15239116291169631012046381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20318821721559508016061841 15239116291169631012046381)
                  ·
                    refine ⟨5714668609188611629517393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15239116291169631012046381 5714668609188611629517393)
                    ·
                      refine ⟨4286001456891458722138045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5714668609188611629517393 4286001456891458722138045)
                      ·
                        rfl

theorem cell23_8346958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2].length) (baseStart_8346958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346958 prefixEnd_8346958 := by exact prefixLift 8346958
  have htrace : WordTrace (prefixWord ++ tailWord_8346958) baseStart_8346958 baseEnd_8346958 := by
    simpa [prefixWord, tailWord_8346958, baseEnd_8346958] using wordTrace_append hprefix tailTrace_8346958
  have hstable : (prefixWord ++ tailWord_8346958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346958).length < 2 ^ (prefixWord ++ tailWord_8346958).sum := by decide
  have hdescent : baseEnd_8346958 < baseStart_8346958 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346965 : List Nat := [1, 3, 2, 2, 3, 3, 1, 1, 3, 1, 3]
def baseStart_8346965 : Nat := 118140960795 + 8346965 * 2 ^ 59
def prefixEnd_8346965 : Nat := 4983230072969 + 3 ^ 40 * 8346965 * 2
def baseEnd_8346965 : Nat := 4286005051256040194750513

theorem tailTrace_8346965 : CollatzResearch.WordTrace tailWord_8346965 prefixEnd_8346965 4286005051256040194750513 := by
  unfold tailWord_8346965
  simp only [CollatzResearch.WordTrace]
  refine ⟨304438824205378827973426349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202959216136919218648950899 304438824205378827973426349)
  ·
    refine ⟨114164559077017060490034881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304438824205378827973426349 114164559077017060490034881)
    ·
      refine ⟨85623419307762795367526161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114164559077017060490034881 85623419307762795367526161)
      ·
        refine ⟨64217564480822096525644621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85623419307762795367526161 64217564480822096525644621)
        ·
          refine ⟨24081586680308286197116733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64217564480822096525644621 24081586680308286197116733)
          ·
            refine ⟨9030595005115607323918775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24081586680308286197116733 9030595005115607323918775)
            ·
              refine ⟨13545892507673410985878163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9030595005115607323918775 13545892507673410985878163)
              ·
                refine ⟨20318838761510116478817245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13545892507673410985878163 20318838761510116478817245)
                ·
                  refine ⟨7619564535566293679556467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20318838761510116478817245 7619564535566293679556467)
                  ·
                    refine ⟨11429346803349440519334701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7619564535566293679556467 11429346803349440519334701)
                    ·
                      refine ⟨4286005051256040194750513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11429346803349440519334701 4286005051256040194750513)
                      ·
                        rfl

theorem cell23_8346965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_8346965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346965 prefixEnd_8346965 := by exact prefixLift 8346965
  have htrace : WordTrace (prefixWord ++ tailWord_8346965) baseStart_8346965 baseEnd_8346965 := by
    simpa [prefixWord, tailWord_8346965, baseEnd_8346965] using wordTrace_append hprefix tailTrace_8346965
  have hstable : (prefixWord ++ tailWord_8346965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346965).length < 2 ^ (prefixWord ++ tailWord_8346965).sum := by decide
  have hdescent : baseEnd_8346965 < baseStart_8346965 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346988 : List Nat := [2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 4]
def baseStart_8346988 : Nat := 118140960795 + 8346988 * 2 ^ 59
def prefixEnd_8346988 : Nat := 4983230072969 + 3 ^ 40 * 8346988 * 2
def baseEnd_8346988 : Nat := 4286016861311093604762907

theorem tailTrace_8346988 : CollatzResearch.WordTrace tailWord_8346988 prefixEnd_8346988 4286016861311093604762907 := by
  unfold tailWord_8346988
  simp only [CollatzResearch.WordTrace]
  refine ⟨152219831542147751450756809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202959775389530335267675745 152219831542147751450756809)
  ·
    refine ⟨114164873656610813588067607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152219831542147751450756809 114164873656610813588067607)
    ·
      refine ⟨171247310484916220382101411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114164873656610813588067607 171247310484916220382101411)
      ·
        refine ⟨256870965727374330573152117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171247310484916220382101411 256870965727374330573152117)
        ·
          refine ⟨24081653036941343491233011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 256870965727374330573152117 24081653036941343491233011)
          ·
            refine ⟨36122479555412015236849517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24081653036941343491233011 36122479555412015236849517)
            ·
              refine ⟨13545929833279505713818569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36122479555412015236849517 13545929833279505713818569)
              ·
                refine ⟨10159447374959629285363927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13545929833279505713818569 10159447374959629285363927)
                ·
                  refine ⟨15239171062439443928045891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10159447374959629285363927 15239171062439443928045891)
                  ·
                    refine ⟨22858756593659165892068837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15239171062439443928045891 22858756593659165892068837)
                    ·
                      refine ⟨4286016861311093604762907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22858756593659165892068837 4286016861311093604762907)
                      ·
                        rfl

theorem cell23_8346988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 4].length) (baseStart_8346988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346988 prefixEnd_8346988 := by exact prefixLift 8346988
  have htrace : WordTrace (prefixWord ++ tailWord_8346988) baseStart_8346988 baseEnd_8346988 := by
    simpa [prefixWord, tailWord_8346988, baseEnd_8346988] using wordTrace_append hprefix tailTrace_8346988
  have hstable : (prefixWord ++ tailWord_8346988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346988).length < 2 ^ (prefixWord ++ tailWord_8346988).sum := by decide
  have hdescent : baseEnd_8346988 < baseStart_8346988 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346991 : List Nat := [1, 1, 2, 1, 3, 1, 5, 1, 3, 2, 3]
def baseStart_8346991 : Nat := 118140960795 + 8346991 * 2 ^ 59
def prefixEnd_8346991 : Nat := 4983230072969 + 3 ^ 40 * 8346991 * 2
def baseEnd_8346991 : Nat := 4286018401753057093025393

theorem tailTrace_8346991 : CollatzResearch.WordTrace tailWord_8346991 prefixEnd_8346991 4286018401753057093025393 := by
  unfold tailWord_8346991
  simp only [CollatzResearch.WordTrace]
  refine ⟨304439772503284634413872827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202959848335523089609248551 304439772503284634413872827)
  ·
    refine ⟨456659658754926951620809241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304439772503284634413872827 456659658754926951620809241)
    ·
      refine ⟨342494744066195213715606931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456659658754926951620809241 342494744066195213715606931)
      ·
        refine ⟨513742116099292820573410397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342494744066195213715606931 513742116099292820573410397)
        ·
          refine ⟨192653293537234807715028899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 513742116099292820573410397 192653293537234807715028899)
          ·
            refine ⟨288979940305852211572543349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192653293537234807715028899 288979940305852211572543349)
            ·
              refine ⟨27091869403673644834925939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 288979940305852211572543349 27091869403673644834925939)
              ·
                refine ⟨40637804105510467252388909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27091869403673644834925939 40637804105510467252388909)
                ·
                  refine ⟨15239176539566425219645841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40637804105510467252388909 15239176539566425219645841)
                  ·
                    refine ⟨11429382404674818914734381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15239176539566425219645841 11429382404674818914734381)
                    ·
                      refine ⟨4286018401753057093025393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11429382404674818914734381 4286018401753057093025393)
                      ·
                        rfl

theorem cell23_8346991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2, 3].length) (baseStart_8346991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346991 prefixEnd_8346991 := by exact prefixLift 8346991
  have htrace : WordTrace (prefixWord ++ tailWord_8346991) baseStart_8346991 baseEnd_8346991 := by
    simpa [prefixWord, tailWord_8346991, baseEnd_8346991] using wordTrace_append hprefix tailTrace_8346991
  have hstable : (prefixWord ++ tailWord_8346991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346991).length < 2 ^ (prefixWord ++ tailWord_8346991).sum := by decide
  have hdescent : baseEnd_8346991 < baseStart_8346991 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8346994 : List Nat := [3, 2, 1, 2, 1, 2, 1, 11]
def baseStart_8346994 : Nat := 118140960795 + 8346994 * 2 ^ 59
def prefixEnd_8346994 : Nat := 4983230072969 + 3 ^ 40 * 8346994 * 2
def baseEnd_8346994 : Nat := 158741479340556317825477

theorem tailTrace_8346994 : CollatzResearch.WordTrace tailWord_8346994 prefixEnd_8346994 158741479340556317825477 := by
  unfold tailWord_8346994
  simp only [CollatzResearch.WordTrace]
  refine ⟨76109970480568441481558009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202959921281515843950821357 76109970480568441481558009)
  ·
    refine ⟨57082477860426331111168507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76109970480568441481558009 57082477860426331111168507)
    ·
      refine ⟨85623716790639496666752761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57082477860426331111168507 85623716790639496666752761)
      ·
        refine ⟨64217787592979622500064571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85623716790639496666752761 64217787592979622500064571)
        ·
          refine ⟨96326681389469433750096857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64217787592979622500064571 96326681389469433750096857)
          ·
            refine ⟨72245011042102075312572643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96326681389469433750096857 72245011042102075312572643)
            ·
              refine ⟨108367516563153112968858965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72245011042102075312572643 108367516563153112968858965)
              ·
                refine ⟨158741479340556317825477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 108367516563153112968858965 158741479340556317825477)
                ·
                  rfl

theorem cell23_8346994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 11].length) (baseStart_8346994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8346994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8346994 prefixEnd_8346994 := by exact prefixLift 8346994
  have htrace : WordTrace (prefixWord ++ tailWord_8346994) baseStart_8346994 baseEnd_8346994 := by
    simpa [prefixWord, tailWord_8346994, baseEnd_8346994] using wordTrace_append hprefix tailTrace_8346994
  have hstable : (prefixWord ++ tailWord_8346994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8346994).length < 2 ^ (prefixWord ++ tailWord_8346994).sum := by decide
  have hdescent : baseEnd_8346994 < baseStart_8346994 := by decide
  rcases family_descends (prefixWord ++ tailWord_8346994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347028 : List Nat := [2, 4, 2, 1, 2, 3, 1, 8]
def baseStart_8347028 : Nat := 118140960795 + 8347028 * 2 ^ 59
def prefixEnd_8347028 : Nat := 4983230072969 + 3 ^ 40 * 8347028 * 2
def baseEnd_8347028 : Nat := 158742125945824942528249

theorem tailTrace_8347028 : CollatzResearch.WordTrace tailWord_8347028 prefixEnd_8347028 158742125945824942528249 := by
  unfold tailWord_8347028
  simp only [CollatzResearch.WordTrace]
  refine ⟨152220561002075294866484869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202960748002767059821979825 152220561002075294866484869)
  ·
    refine ⟨28541355187889117787465913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152220561002075294866484869 28541355187889117787465913)
    ·
      refine ⟨21406016390916838340599435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28541355187889117787465913 21406016390916838340599435)
      ·
        refine ⟨32109024586375257510899153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21406016390916838340599435 32109024586375257510899153)
        ·
          refine ⟨24081768439781443133174365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32109024586375257510899153 24081768439781443133174365)
          ·
            refine ⟨9030663164918041174940387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24081768439781443133174365 9030663164918041174940387)
            ·
              refine ⟨13545994747377061762410581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9030663164918041174940387 13545994747377061762410581)
              ·
                refine ⟨158742125945824942528249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13545994747377061762410581 158742125945824942528249)
                ·
                  rfl

theorem cell23_8347028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 8].length) (baseStart_8347028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347028 prefixEnd_8347028 := by exact prefixLift 8347028
  have htrace : WordTrace (prefixWord ++ tailWord_8347028) baseStart_8347028 baseEnd_8347028 := by
    simpa [prefixWord, tailWord_8347028, baseEnd_8347028] using wordTrace_append hprefix tailTrace_8347028
  have hstable : (prefixWord ++ tailWord_8347028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347028).length < 2 ^ (prefixWord ++ tailWord_8347028).sum := by decide
  have hdescent : baseEnd_8347028 < baseStart_8347028 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347095 : List Nat := [1, 1, 3, 2, 1, 1, 1, 7, 2, 2, 2]
def baseStart_8347095 : Nat := 118140960795 + 8347095 * 2 ^ 59
def prefixEnd_8347095 : Nat := 4983230072969 + 3 ^ 40 * 8347095 * 2
def baseEnd_8347095 : Nat := 4286071803741124686124915

theorem tailTrace_8347095 : CollatzResearch.WordTrace tailWord_8347095 prefixEnd_8347095 4286071803741124686124915 := by
  unfold tailWord_8347095
  simp only [CollatzResearch.WordTrace]
  refine ⟨304443565694907860175658739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202962377129938573450439159 304443565694907860175658739)
  ·
    refine ⟨456665348542361790263488109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304443565694907860175658739 456665348542361790263488109)
    ·
      refine ⟨171249505703385671348808041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456665348542361790263488109 171249505703385671348808041)
      ·
        refine ⟨128437129277539253511606031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171249505703385671348808041 128437129277539253511606031)
        ·
          refine ⟨192655693916308880267409047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128437129277539253511606031 192655693916308880267409047)
          ·
            refine ⟨288983540874463320401113571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192655693916308880267409047 288983540874463320401113571)
            ·
              refine ⟨433475311311694980601670357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288983540874463320401113571 433475311311694980601670357)
              ·
                refine ⟨10159577608867851107851649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 433475311311694980601670357 10159577608867851107851649)
                ·
                  refine ⟨7619683206650888330888737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10159577608867851107851649 7619683206650888330888737)
                  ·
                    refine ⟨5714762404988166248166553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7619683206650888330888737 5714762404988166248166553)
                    ·
                      refine ⟨4286071803741124686124915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5714762404988166248166553 4286071803741124686124915)
                      ·
                        rfl

theorem cell23_8347095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2, 2, 2].length) (baseStart_8347095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347095 prefixEnd_8347095 := by exact prefixLift 8347095
  have htrace : WordTrace (prefixWord ++ tailWord_8347095) baseStart_8347095 baseEnd_8347095 := by
    simpa [prefixWord, tailWord_8347095, baseEnd_8347095] using wordTrace_append hprefix tailTrace_8347095
  have hstable : (prefixWord ++ tailWord_8347095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347095).length < 2 ^ (prefixWord ++ tailWord_8347095).sum := by decide
  have hdescent : baseEnd_8347095 < baseStart_8347095 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347131 : List Nat := [1, 1, 1, 1, 1, 3, 2, 6, 2, 5]
def baseStart_8347131 : Nat := 118140960795 + 8347131 * 2 ^ 59
def prefixEnd_8347131 : Nat := 4983230072969 + 3 ^ 40 * 8347131 * 2
def baseEnd_8347131 : Nat := 1428696763014895515091583

theorem tailTrace_8347131 : CollatzResearch.WordTrace tailWord_8347131 prefixEnd_8347131 1428696763014895515091583 := by
  unfold tailWord_8347131
  simp only [CollatzResearch.WordTrace]
  refine ⟨304444878722777438323969247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202963252481851625549312831 304444878722777438323969247)
  ·
    refine ⟨456667318084166157485953871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304444878722777438323969247 456667318084166157485953871)
    ·
      refine ⟨685000977126249236228930807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456667318084166157485953871 685000977126249236228930807)
      ·
        refine ⟨1027501465689373854343396211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685000977126249236228930807 1027501465689373854343396211)
        ·
          refine ⟨1541252198534060781515094317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1027501465689373854343396211 1541252198534060781515094317)
          ·
            refine ⟨577969574450272793068160369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1541252198534060781515094317 577969574450272793068160369)
            ·
              refine ⟨433477180837704594801120277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577969574450272793068160369 433477180837704594801120277)
              ·
                refine ⟨20319242851767402881302513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 433477180837704594801120277 20319242851767402881302513)
                ·
                  refine ⟨15239432138825552160976885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20319242851767402881302513 15239432138825552160976885)
                  ·
                    refine ⟨1428696763014895515091583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15239432138825552160976885 1428696763014895515091583)
                    ·
                      rfl

theorem cell23_8347131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 5].length) (baseStart_8347131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347131 prefixEnd_8347131 := by exact prefixLift 8347131
  have htrace : WordTrace (prefixWord ++ tailWord_8347131) baseStart_8347131 baseEnd_8347131 := by
    simpa [prefixWord, tailWord_8347131, baseEnd_8347131] using wordTrace_append hprefix tailTrace_8347131
  have hstable : (prefixWord ++ tailWord_8347131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347131).length < 2 ^ (prefixWord ++ tailWord_8347131).sum := by decide
  have hdescent : baseEnd_8347131 < baseStart_8347131 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347231 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 5]
def baseStart_8347231 : Nat := 118140960795 + 8347231 * 2 ^ 59
def prefixEnd_8347231 : Nat := 4983230072969 + 3 ^ 40 * 8347231 * 2
def baseEnd_8347231 : Nat := 4286141637110136154024289

theorem tailTrace_8347231 : CollatzResearch.WordTrace tailWord_8347231 prefixEnd_8347231 4286141637110136154024289 := by
  unfold tailWord_8347231
  simp only [CollatzResearch.WordTrace]
  refine ⟨304448526022415155402609547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202965684014943436935073031 304448526022415155402609547)
  ·
    refine ⟨456672789033622733103914321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304448526022415155402609547 456672789033622733103914321)
    ·
      refine ⟨342504591775217049827935741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456672789033622733103914321 342504591775217049827935741)
      ·
        refine ⟨128439221915706393685475903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342504591775217049827935741 128439221915706393685475903)
        ·
          refine ⟨192658832873559590528213855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128439221915706393685475903 192658832873559590528213855)
          ·
            refine ⟨288988249310339385792320783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192658832873559590528213855 288988249310339385792320783)
            ·
              refine ⟨433482373965509078688481175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288988249310339385792320783 433482373965509078688481175)
              ·
                refine ⟨650223560948263618032721763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433482373965509078688481175 650223560948263618032721763)
                ·
                  refine ⟨975335341422395427049082645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 650223560948263618032721763 975335341422395427049082645)
                  ·
                    refine ⟨45718844129174785642925749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 975335341422395427049082645 45718844129174785642925749)
                    ·
                      refine ⟨4286141637110136154024289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45718844129174785642925749 4286141637110136154024289)
                      ·
                        rfl

theorem cell23_8347231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_8347231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347231 prefixEnd_8347231 := by exact prefixLift 8347231
  have htrace : WordTrace (prefixWord ++ tailWord_8347231) baseStart_8347231 baseEnd_8347231 := by
    simpa [prefixWord, tailWord_8347231, baseEnd_8347231] using wordTrace_append hprefix tailTrace_8347231
  have hstable : (prefixWord ++ tailWord_8347231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347231).length < 2 ^ (prefixWord ++ tailWord_8347231).sum := by decide
  have hdescent : baseEnd_8347231 < baseStart_8347231 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347258 : List Nat := [3, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4]
def baseStart_8347258 : Nat := 118140960795 + 8347258 * 2 ^ 59
def prefixEnd_8347258 : Nat := 4983230072969 + 3 ^ 40 * 8347258 * 2
def baseEnd_8347258 : Nat := 4286155501087807548386665

theorem tailTrace_8347258 : CollatzResearch.WordTrace tailWord_8347258 prefixEnd_8347258 4286155501087807548386665 := by
  unfold tailWord_8347258
  simp only [CollatzResearch.WordTrace]
  refine ⟨76112377698329334753460607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202966340528878226009228285 76112377698329334753460607)
  ·
    refine ⟨114168566547494002130190911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76112377698329334753460607 114168566547494002130190911)
    ·
      refine ⟨171252849821241003195286367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114168566547494002130190911 171252849821241003195286367)
      ·
        refine ⟨256879274731861504792929551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171252849821241003195286367 256879274731861504792929551)
        ·
          refine ⟨385318912097792257189394327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256879274731861504792929551 385318912097792257189394327)
          ·
            refine ⟨577978368146688385784091491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385318912097792257189394327 577978368146688385784091491)
            ·
              refine ⟨866967552220032578676137237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577978368146688385784091491 866967552220032578676137237)
              ·
                refine ⟨40639104010314027125443933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 866967552220032578676137237 40639104010314027125443933)
                ·
                  refine ⟨15239664003867760172041475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40639104010314027125443933 15239664003867760172041475)
                  ·
                    refine ⟨22859496005801640258062213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15239664003867760172041475 22859496005801640258062213)
                    ·
                      refine ⟨4286155501087807548386665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22859496005801640258062213 4286155501087807548386665)
                      ·
                        rfl

theorem cell23_8347258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_8347258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347258 prefixEnd_8347258 := by exact prefixLift 8347258
  have htrace : WordTrace (prefixWord ++ tailWord_8347258) baseStart_8347258 baseEnd_8347258 := by
    simpa [prefixWord, tailWord_8347258, baseEnd_8347258] using wordTrace_append hprefix tailTrace_8347258
  have hstable : (prefixWord ++ tailWord_8347258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347258).length < 2 ^ (prefixWord ++ tailWord_8347258).sum := by decide
  have hdescent : baseEnd_8347258 < baseStart_8347258 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347275 : List Nat := [1, 1, 1, 1, 4, 1, 6, 2, 1, 1, 4]
def baseStart_8347275 : Nat := 118140960795 + 8347275 * 2 ^ 59
def prefixEnd_8347275 : Nat := 4983230072969 + 3 ^ 40 * 8347275 * 2
def baseEnd_8347275 : Nat := 4286164230258933981874087

theorem tailTrace_8347275 : CollatzResearch.WordTrace tailWord_8347275 prefixEnd_8347275 4286164230258933981874087 := by
  unfold tailWord_8347275
  simp only [CollatzResearch.WordTrace]
  refine ⟨304450130834255750917211279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202966753889503833944807519 304450130834255750917211279)
  ·
    refine ⟨456675196251383626375816919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304450130834255750917211279 456675196251383626375816919)
    ·
      refine ⟨685012794377075439563725379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456675196251383626375816919 685012794377075439563725379)
      ·
        refine ⟨1027519191565613159345588069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685012794377075439563725379 1027519191565613159345588069)
        ·
          refine ⟨192659848418552467377297763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1027519191565613159345588069 192659848418552467377297763)
          ·
            refine ⟨288989772627828701065946645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192659848418552467377297763 288989772627828701065946645)
            ·
              refine ⟨13546395591929470362466249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 288989772627828701065946645 13546395591929470362466249)
              ·
                refine ⟨10159796693947102771849687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13546395591929470362466249 10159796693947102771849687)
                ·
                  refine ⟨15239695040920654157774531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10159796693947102771849687 15239695040920654157774531)
                  ·
                    refine ⟨22859542561380981236661797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15239695040920654157774531 22859542561380981236661797)
                    ·
                      refine ⟨4286164230258933981874087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22859542561380981236661797 4286164230258933981874087)
                      ·
                        rfl

theorem cell23_8347275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 1, 4].length) (baseStart_8347275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347275 prefixEnd_8347275 := by exact prefixLift 8347275
  have htrace : WordTrace (prefixWord ++ tailWord_8347275) baseStart_8347275 baseEnd_8347275 := by
    simpa [prefixWord, tailWord_8347275, baseEnd_8347275] using wordTrace_append hprefix tailTrace_8347275
  have hstable : (prefixWord ++ tailWord_8347275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347275).length < 2 ^ (prefixWord ++ tailWord_8347275).sum := by decide
  have hdescent : baseEnd_8347275 < baseStart_8347275 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347319 : List Nat := [1, 1, 3, 1, 5, 3, 2, 1, 2, 4]
def baseStart_8347319 : Nat := 118140960795 + 8347319 * 2 ^ 59
def prefixEnd_8347319 : Nat := 4983230072969 + 3 ^ 40 * 8347319 * 2
def baseEnd_8347319 : Nat := 1428728941135910603241295

theorem tailTrace_8347319 : CollatzResearch.WordTrace tailWord_8347319 prefixEnd_8347319 1428728941135910603241295 := by
  unfold tailWord_8347319
  simp only [CollatzResearch.WordTrace]
  refine ⟨304451735646096346431813011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202967823764064230954542007 304451735646096346431813011)
  ·
    refine ⟨456677603469144519647719517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304451735646096346431813011 456677603469144519647719517)
    ·
      refine ⟨171254101300929194867894819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456677603469144519647719517 171254101300929194867894819)
      ·
        refine ⟨256881151951393792301842229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171254101300929194867894819 256881151951393792301842229)
        ·
          refine ⟨24082607995443168028297709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 256881151951393792301842229 24082607995443168028297709)
          ·
            refine ⟨9030977998291188010611641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24082607995443168028297709 9030977998291188010611641)
            ·
              refine ⟨6773233498718391007958731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9030977998291188010611641 6773233498718391007958731)
              ·
                refine ⟨10159850248077586511938097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6773233498718391007958731 10159850248077586511938097)
                ·
                  refine ⟨7619887686058189883953573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10159850248077586511938097 7619887686058189883953573)
                  ·
                    refine ⟨1428728941135910603241295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7619887686058189883953573 1428728941135910603241295)
                    ·
                      rfl

theorem cell23_8347319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 2, 4].length) (baseStart_8347319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347319 prefixEnd_8347319 := by exact prefixLift 8347319
  have htrace : WordTrace (prefixWord ++ tailWord_8347319) baseStart_8347319 baseEnd_8347319 := by
    simpa [prefixWord, tailWord_8347319, baseEnd_8347319] using wordTrace_append hprefix tailTrace_8347319
  have hstable : (prefixWord ++ tailWord_8347319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347319).length < 2 ^ (prefixWord ++ tailWord_8347319).sum := by decide
  have hdescent : baseEnd_8347319 < baseStart_8347319 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347325 : List Nat := [1, 4, 1, 2, 1, 2, 2, 3, 1, 3, 3]
def baseStart_8347325 : Nat := 118140960795 + 8347325 * 2 ^ 59
def prefixEnd_8347325 : Nat := 4983230072969 + 3 ^ 40 * 8347325 * 2
def baseEnd_8347325 : Nat := 4286189904291658786248857

theorem tailTrace_8347325 : CollatzResearch.WordTrace tailWord_8347325 prefixEnd_8347325 4286189904291658786248857 := by
  unfold tailWord_8347325
  simp only [CollatzResearch.WordTrace]
  refine ⟨304451954484074609456531429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202967969656049739637687619 304451954484074609456531429)
  ·
    refine ⟨57084741465763989273099643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304451954484074609456531429 57084741465763989273099643)
    ·
      refine ⟨85627112198645983909649465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57084741465763989273099643 85627112198645983909649465)
      ·
        refine ⟨64220334148984487932237099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85627112198645983909649465 64220334148984487932237099)
        ·
          refine ⟨96330501223476731898355649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64220334148984487932237099 96330501223476731898355649)
          ·
            refine ⟨72247875917607548923766737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96330501223476731898355649 72247875917607548923766737)
            ·
              refine ⟨54185906938205661692825053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72247875917607548923766737 54185906938205661692825053)
              ·
                refine ⟨20319715101827123134809395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54185906938205661692825053 20319715101827123134809395)
                ·
                  refine ⟨30479572652740684702214093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20319715101827123134809395 30479572652740684702214093)
                  ·
                    refine ⟨11429839744777756763330285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30479572652740684702214093 11429839744777756763330285)
                    ·
                      refine ⟨4286189904291658786248857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11429839744777756763330285 4286189904291658786248857)
                      ·
                        rfl

theorem cell23_8347325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_8347325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347325 prefixEnd_8347325 := by exact prefixLift 8347325
  have htrace : WordTrace (prefixWord ++ tailWord_8347325) baseStart_8347325 baseEnd_8347325 := by
    simpa [prefixWord, tailWord_8347325, baseEnd_8347325] using wordTrace_append hprefix tailTrace_8347325
  have hstable : (prefixWord ++ tailWord_8347325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347325).length < 2 ^ (prefixWord ++ tailWord_8347325).sum := by decide
  have hdescent : baseEnd_8347325 < baseStart_8347325 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347432 : List Nat := [2, 1, 5, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_8347432 : Nat := 118140960795 + 8347432 * 2 ^ 59
def prefixEnd_8347432 : Nat := 4983230072969 + 3 ^ 40 * 8347432 * 2
def baseEnd_8347432 : Nat := 4286244846721689867610865

theorem tailTrace_8347432 : CollatzResearch.WordTrace tailWord_8347432 prefixEnd_8347432 4286244846721689867610865 := by
  unfold tailWord_8347432
  simp only [CollatzResearch.WordTrace]
  refine ⟨152227928547343483365338275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202970571396457977820451033 152227928547343483365338275)
  ·
    refine ⟨228341892821015225048007413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152227928547343483365338275 228341892821015225048007413)
    ·
      refine ⟨21407052451970177348250695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228341892821015225048007413 21407052451970177348250695)
      ·
        refine ⟨32110578677955266022376043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21407052451970177348250695 32110578677955266022376043)
        ·
          refine ⟨48165868016932899033564065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32110578677955266022376043 48165868016932899033564065)
          ·
            refine ⟨36124401012699674275173049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48165868016932899033564065 36124401012699674275173049)
            ·
              refine ⟨27093300759524755706379787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36124401012699674275173049 27093300759524755706379787)
              ·
                refine ⟨40639951139287133559569681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27093300759524755706379787 40639951139287133559569681)
                ·
                  refine ⟨30479963354465350169677261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40639951139287133559569681 30479963354465350169677261)
                  ·
                    refine ⟨11429986257924506313628973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30479963354465350169677261 11429986257924506313628973)
                    ·
                      refine ⟨4286244846721689867610865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11429986257924506313628973 4286244846721689867610865)
                      ·
                        rfl

theorem cell23_8347432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_8347432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347432 prefixEnd_8347432 := by exact prefixLift 8347432
  have htrace : WordTrace (prefixWord ++ tailWord_8347432) baseStart_8347432 baseEnd_8347432 := by
    simpa [prefixWord, tailWord_8347432, baseEnd_8347432] using wordTrace_append hprefix tailTrace_8347432
  have hstable : (prefixWord ++ tailWord_8347432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347432).length < 2 ^ (prefixWord ++ tailWord_8347432).sum := by decide
  have hdescent : baseEnd_8347432 < baseStart_8347432 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347469 : List Nat := [1, 6, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_8347469 : Nat := 118140960795 + 8347469 * 2 ^ 59
def prefixEnd_8347469 : Nat := 4983230072969 + 3 ^ 40 * 8347469 * 2
def baseEnd_8347469 : Nat := 1428754615168635407616065

theorem tailTrace_8347469 : CollatzResearch.WordTrace tailWord_8347469 prefixEnd_8347469 1428754615168635407616065 := by
  unfold tailWord_8347469
  simp only [CollatzResearch.WordTrace]
  refine ⟨304457206595552922049773461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202971471063701948033182307 304457206595552922049773461)
  ·
    refine ⟨14271431559166543221083131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 304457206595552922049773461 14271431559166543221083131)
    ·
      refine ⟨21407147338749814831624697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14271431559166543221083131 21407147338749814831624697)
      ·
        refine ⟨16055360504062361123718523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21407147338749814831624697 16055360504062361123718523)
        ·
          refine ⟨24083040756093541685577785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16055360504062361123718523 24083040756093541685577785)
          ·
            refine ⟨18062280567070156264183339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24083040756093541685577785 18062280567070156264183339)
            ·
              refine ⟨27093420850605234396275009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18062280567070156264183339 27093420850605234396275009)
              ·
                refine ⟨20320065637953925797206257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27093420850605234396275009 20320065637953925797206257)
                ·
                  refine ⟨15240049228465444347904693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20320065637953925797206257 15240049228465444347904693)
                  ·
                    refine ⟨1428754615168635407616065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15240049228465444347904693 1428754615168635407616065)
                    ·
                      rfl

theorem cell23_8347469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_8347469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347469 prefixEnd_8347469 := by exact prefixLift 8347469
  have htrace : WordTrace (prefixWord ++ tailWord_8347469) baseStart_8347469 baseEnd_8347469 := by
    simpa [prefixWord, tailWord_8347469, baseEnd_8347469] using wordTrace_append hprefix tailTrace_8347469
  have hstable : (prefixWord ++ tailWord_8347469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347469).length < 2 ^ (prefixWord ++ tailWord_8347469).sum := by decide
  have hdescent : baseEnd_8347469 < baseStart_8347469 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347509 : List Nat := [1, 3, 4, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_8347509 : Nat := 118140960795 + 8347509 * 2 ^ 59
def prefixEnd_8347509 : Nat := 4983230072969 + 3 ^ 40 * 8347509 * 2
def baseEnd_8347509 : Nat := 4286284384732086066348011

theorem tailTrace_8347509 : CollatzResearch.WordTrace tailWord_8347509 prefixEnd_8347509 4286284384732086066348011 := by
  unfold tailWord_8347509
  simp only [CollatzResearch.WordTrace]
  refine ⟨304458665515408008881229581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202972443676938672587486387 304458665515408008881229581)
  ·
    refine ⟨114171999568278003330461093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304458665515408008881229581 114171999568278003330461093)
    ·
      refine ⟨21407249919052125624461455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114171999568278003330461093 21407249919052125624461455)
      ·
        refine ⟨32110874878578188436692183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21407249919052125624461455 32110874878578188436692183)
        ·
          refine ⟨48166312317867282655038275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32110874878578188436692183 48166312317867282655038275)
          ·
            refine ⟨72249468476800923982557413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48166312317867282655038275 72249468476800923982557413)
            ·
              refine ⟨13546775339400173246729515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72249468476800923982557413 13546775339400173246729515)
              ·
                refine ⟨20320163009100259870094273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13546775339400173246729515 20320163009100259870094273)
                ·
                  refine ⟨15240122256825194902570705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20320163009100259870094273 15240122256825194902570705)
                  ·
                    refine ⟨11430091692618896176928029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15240122256825194902570705 11430091692618896176928029)
                    ·
                      refine ⟨4286284384732086066348011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11430091692618896176928029 4286284384732086066348011)
                      ·
                        rfl

theorem cell23_8347509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_8347509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347509 prefixEnd_8347509 := by exact prefixLift 8347509
  have htrace : WordTrace (prefixWord ++ tailWord_8347509) baseStart_8347509 baseEnd_8347509 := by
    simpa [prefixWord, tailWord_8347509, baseEnd_8347509] using wordTrace_append hprefix tailTrace_8347509
  have hstable : (prefixWord ++ tailWord_8347509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347509).length < 2 ^ (prefixWord ++ tailWord_8347509).sum := by decide
  have hdescent : baseEnd_8347509 < baseStart_8347509 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347532 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 3, 5, 2]
def baseStart_8347532 : Nat := 118140960795 + 8347532 * 2 ^ 59
def prefixEnd_8347532 : Nat := 4983230072969 + 3 ^ 40 * 8347532 * 2
def baseEnd_8347532 : Nat := 4286296194787139476360405

theorem tailTrace_8347532 : CollatzResearch.WordTrace tailWord_8347532 prefixEnd_8347532 4286296194787139476360405 := by
  unfold tailWord_8347532
  simp only [CollatzResearch.WordTrace]
  refine ⟨152229752197162341904658425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202973002929549789206211233 152229752197162341904658425)
  ·
    refine ⟨114172314147871756428493819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152229752197162341904658425 114172314147871756428493819)
    ·
      refine ⟨171258471221807634642740729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114172314147871756428493819 171258471221807634642740729)
      ·
        refine ⟨128443853416355725982055547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171258471221807634642740729 128443853416355725982055547)
        ·
          refine ⟨192665780124533588973083321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128443853416355725982055547 192665780124533588973083321)
          ·
            refine ⟨144499335093400191729812491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192665780124533588973083321 144499335093400191729812491)
            ·
              refine ⟨216749002640100287594718737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144499335093400191729812491 216749002640100287594718737)
              ·
                refine ⟨162561751980075215696039053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216749002640100287594718737 162561751980075215696039053)
                ·
                  refine ⟨60960656992528205886014645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162561751980075215696039053 60960656992528205886014645)
                  ·
                    refine ⟨5715061593049519301813873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60960656992528205886014645 5715061593049519301813873)
                    ·
                      refine ⟨4286296194787139476360405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5715061593049519301813873 4286296194787139476360405)
                      ·
                        rfl

theorem cell23_8347532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 3, 5, 2].length) (baseStart_8347532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347532 prefixEnd_8347532 := by exact prefixLift 8347532
  have htrace : WordTrace (prefixWord ++ tailWord_8347532) baseStart_8347532 baseEnd_8347532 := by
    simpa [prefixWord, tailWord_8347532, baseEnd_8347532] using wordTrace_append hprefix tailTrace_8347532
  have hstable : (prefixWord ++ tailWord_8347532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347532).length < 2 ^ (prefixWord ++ tailWord_8347532).sum := by decide
  have hdescent : baseEnd_8347532 < baseStart_8347532 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347560 : List Nat := [2, 1, 6, 2, 2, 1, 1, 1, 2, 2, 3]
def baseStart_8347560 : Nat := 118140960795 + 8347560 * 2 ^ 59
def prefixEnd_8347560 : Nat := 4983230072969 + 3 ^ 40 * 8347560 * 2
def baseEnd_8347560 : Nat := 4286310572245465366810277

theorem tailTrace_8347560 : CollatzResearch.WordTrace tailWord_8347560 prefixEnd_8347560 4286310572245465366810277 := by
  unfold tailWord_8347560
  simp only [CollatzResearch.WordTrace]
  refine ⟨152230262819111622295668067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202973683758815496394224089 152230262819111622295668067)
  ·
    refine ⟨228345394228667433443502101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152230262819111622295668067 228345394228667433443502101)
    ·
      refine ⟨10703690354468785942664161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 228345394228667433443502101 10703690354468785942664161)
      ·
        refine ⟨8027767765851589456998121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10703690354468785942664161 8027767765851589456998121)
        ·
          refine ⟨6020825824388692092748591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8027767765851589456998121 6020825824388692092748591)
          ·
            refine ⟨9031238736583038139122887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6020825824388692092748591 9031238736583038139122887)
            ·
              refine ⟨13546858104874557208684331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9031238736583038139122887 13546858104874557208684331)
              ·
                refine ⟨20320287157311835813026497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13546858104874557208684331 20320287157311835813026497)
                ·
                  refine ⟨15240215367983876859769873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20320287157311835813026497 15240215367983876859769873)
                  ·
                    refine ⟨11430161525987907644827405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15240215367983876859769873 11430161525987907644827405)
                    ·
                      refine ⟨4286310572245465366810277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11430161525987907644827405 4286310572245465366810277)
                      ·
                        rfl

theorem cell23_8347560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_8347560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347560 prefixEnd_8347560 := by exact prefixLift 8347560
  have htrace : WordTrace (prefixWord ++ tailWord_8347560) baseStart_8347560 baseEnd_8347560 := by
    simpa [prefixWord, tailWord_8347560, baseEnd_8347560] using wordTrace_append hprefix tailTrace_8347560
  have hstable : (prefixWord ++ tailWord_8347560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347560).length < 2 ^ (prefixWord ++ tailWord_8347560).sum := by decide
  have hdescent : baseEnd_8347560 < baseStart_8347560 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347573 : List Nat := [1, 3, 3, 2, 1, 3, 2, 3, 1, 1, 3]
def baseStart_8347573 : Nat := 118140960795 + 8347573 * 2 ^ 59
def prefixEnd_8347573 : Nat := 4983230072969 + 3 ^ 40 * 8347573 * 2
def baseEnd_8347573 : Nat := 4286317247493973815947717

theorem tailTrace_8347573 : CollatzResearch.WordTrace tailWord_8347573 prefixEnd_8347573 4286317247493973815947717 := by
  unfold tailWord_8347573
  simp only [CollatzResearch.WordTrace]
  refine ⟨304460999787176147811559373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202973999858117431874372915 304460999787176147811559373)
  ·
    refine ⟨114172874920191055429334765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304460999787176147811559373 114172874920191055429334765)
    ·
      refine ⟨42814828095071645786000537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114172874920191055429334765 42814828095071645786000537)
      ·
        refine ⟨32111121071303734339500403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42814828095071645786000537 32111121071303734339500403)
        ·
          refine ⟨48166681606955601509250605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32111121071303734339500403 48166681606955601509250605)
          ·
            refine ⟨18062505602608350565968977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48166681606955601509250605 18062505602608350565968977)
            ·
              refine ⟨13546879201956262924476733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18062505602608350565968977 13546879201956262924476733)
              ·
                refine ⟨5080079700733598596678775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13546879201956262924476733 5080079700733598596678775)
                ·
                  refine ⟨7620119551100397895018163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5080079700733598596678775 7620119551100397895018163)
                  ·
                    refine ⟨11430179326650596842527245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7620119551100397895018163 11430179326650596842527245)
                    ·
                      refine ⟨4286317247493973815947717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11430179326650596842527245 4286317247493973815947717)
                      ·
                        rfl

theorem cell23_8347573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_8347573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347573 prefixEnd_8347573 := by exact prefixLift 8347573
  have htrace : WordTrace (prefixWord ++ tailWord_8347573) baseStart_8347573 baseEnd_8347573 := by
    simpa [prefixWord, tailWord_8347573, baseEnd_8347573] using wordTrace_append hprefix tailTrace_8347573
  have hstable : (prefixWord ++ tailWord_8347573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347573).length < 2 ^ (prefixWord ++ tailWord_8347573).sum := by decide
  have hdescent : baseEnd_8347573 < baseStart_8347573 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347575 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 6]
def baseStart_8347575 : Nat := 118140960795 + 8347575 * 2 ^ 59
def prefixEnd_8347575 : Nat := 4983230072969 + 3 ^ 40 * 8347575 * 2
def baseEnd_8347575 : Nat := 4286318274455282808122707

theorem tailTrace_8347575 : CollatzResearch.WordTrace tailWord_8347575 prefixEnd_8347575 4286318274455282808122707 := by
  unfold tailWord_8347575
  simp only [CollatzResearch.WordTrace]
  refine ⟨304461072733168902153132179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202974048488779268102088119 304461072733168902153132179)
  ·
    refine ⟨456691609099753353229698269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304461072733168902153132179 456691609099753353229698269)
    ·
      refine ⟨171259353412407507461136851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456691609099753353229698269 171259353412407507461136851)
      ·
        refine ⟨256889030118611261191705277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171259353412407507461136851 256889030118611261191705277)
        ·
          refine ⟨96333386294479222946889479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256889030118611261191705277 96333386294479222946889479)
          ·
            refine ⟨144500079441718834420334219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96333386294479222946889479 144500079441718834420334219)
            ·
              refine ⟨216750119162578251630501329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144500079441718834420334219 216750119162578251630501329)
              ·
                refine ⟨162562589371933688722875997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216750119162578251630501329 162562589371933688722875997)
                ·
                  refine ⟨60960971014475133271078499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162562589371933688722875997 60960971014475133271078499)
                  ·
                    refine ⟨91441456521712699906617749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60960971014475133271078499 91441456521712699906617749)
                    ·
                      refine ⟨4286318274455282808122707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91441456521712699906617749 4286318274455282808122707)
                      ·
                        rfl

theorem cell23_8347575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_8347575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347575 prefixEnd_8347575 := by exact prefixLift 8347575
  have htrace : WordTrace (prefixWord ++ tailWord_8347575) baseStart_8347575 baseEnd_8347575 := by
    simpa [prefixWord, tailWord_8347575, baseEnd_8347575] using wordTrace_append hprefix tailTrace_8347575
  have hstable : (prefixWord ++ tailWord_8347575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347575).length < 2 ^ (prefixWord ++ tailWord_8347575).sum := by decide
  have hdescent : baseEnd_8347575 < baseStart_8347575 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347596 : List Nat := [2, 2, 1, 4, 1, 2, 1, 3, 3, 2, 2]
def baseStart_8347596 : Nat := 118140960795 + 8347596 * 2 ^ 59
def prefixEnd_8347596 : Nat := 4983230072969 + 3 ^ 40 * 8347596 * 2
def baseEnd_8347596 : Nat := 4286329057549027225960111

theorem tailTrace_8347596 : CollatzResearch.WordTrace tailWord_8347596 prefixEnd_8347596 4286329057549027225960111 := by
  unfold tailWord_8347596
  simp only [CollatzResearch.WordTrace]
  refine ⟨152230919333046411369823321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202974559110728548493097761 152230919333046411369823321)
  ·
    refine ⟨114173189499784808527367491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152230919333046411369823321 114173189499784808527367491)
    ·
      refine ⟨171259784249677212791051237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114173189499784808527367491 171259784249677212791051237)
      ·
        refine ⟨32111209546814477398322107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171259784249677212791051237 32111209546814477398322107)
        ·
          refine ⟨48166814320221716097483161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32111209546814477398322107 48166814320221716097483161)
          ·
            refine ⟨36125110740166287073112371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48166814320221716097483161 36125110740166287073112371)
            ·
              refine ⟨54187666110249430609668557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36125110740166287073112371 54187666110249430609668557)
              ·
                refine ⟨20320374791343536478625709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54187666110249430609668557 20320374791343536478625709)
                ·
                  refine ⟨7620140546753826179484641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20320374791343536478625709 7620140546753826179484641)
                  ·
                    refine ⟨5715105410065369634613481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7620140546753826179484641 5715105410065369634613481)
                    ·
                      refine ⟨4286329057549027225960111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5715105410065369634613481 4286329057549027225960111)
                      ·
                        rfl

theorem cell23_8347596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_8347596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347596 prefixEnd_8347596 := by exact prefixLift 8347596
  have htrace : WordTrace (prefixWord ++ tailWord_8347596) baseStart_8347596 baseEnd_8347596 := by
    simpa [prefixWord, tailWord_8347596, baseEnd_8347596] using wordTrace_append hprefix tailTrace_8347596
  have hstable : (prefixWord ++ tailWord_8347596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347596).length < 2 ^ (prefixWord ++ tailWord_8347596).sum := by decide
  have hdescent : baseEnd_8347596 < baseStart_8347596 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347619 : List Nat := [1, 1, 1, 6, 1, 4, 2, 7]
def baseStart_8347619 : Nat := 118140960795 + 8347619 * 2 ^ 59
def prefixEnd_8347619 : Nat := 4983230072969 + 3 ^ 40 * 8347619 * 2
def baseEnd_8347619 : Nat := 158753365466817801332315

theorem tailTrace_8347619 : CollatzResearch.WordTrace tailWord_8347619 prefixEnd_8347619 158753365466817801332315 := by
  unfold tailWord_8347619
  simp only [CollatzResearch.WordTrace]
  refine ⟨304462677545009497667733911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202975118363339665111822607 304462677545009497667733911)
  ·
    refine ⟨456694016317514246501600867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304462677545009497667733911 456694016317514246501600867)
    ·
      refine ⟨685041024476271369752401301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456694016317514246501600867 685041024476271369752401301)
      ·
        refine ⟨32111298022325220457143811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 685041024476271369752401301 32111298022325220457143811)
        ·
          refine ⟨48166947033487830685715717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32111298022325220457143811 48166947033487830685715717)
          ·
            refine ⟨9031302568778968253571697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48166947033487830685715717 9031302568778968253571697)
            ·
              refine ⟨6773476926584226190178773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9031302568778968253571697 6773476926584226190178773)
              ·
                refine ⟨158753365466817801332315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6773476926584226190178773 158753365466817801332315)
                ·
                  rfl

theorem cell23_8347619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 7].length) (baseStart_8347619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347619 prefixEnd_8347619 := by exact prefixLift 8347619
  have htrace : WordTrace (prefixWord ++ tailWord_8347619) baseStart_8347619 baseEnd_8347619 := by
    simpa [prefixWord, tailWord_8347619, baseEnd_8347619] using wordTrace_append hprefix tailTrace_8347619
  have hstable : (prefixWord ++ tailWord_8347619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347619).length < 2 ^ (prefixWord ++ tailWord_8347619).sum := by decide
  have hdescent : baseEnd_8347619 < baseStart_8347619 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347630 : List Nat := [4, 1, 2, 1, 3, 1, 3, 3, 1, 2, 2]
def baseStart_8347630 : Nat := 118140960795 + 8347630 * 2 ^ 59
def prefixEnd_8347630 : Nat := 4983230072969 + 3 ^ 40 * 8347630 * 2
def baseEnd_8347630 : Nat := 4286346515891280092934955

theorem tailTrace_8347630 : CollatzResearch.WordTrace tailWord_8347630 prefixEnd_8347630 4286346515891280092934955 := by
  unfold tailWord_8347630
  simp only [CollatzResearch.WordTrace]
  refine ⟨38057884843496205818298043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202975385831979764364256229 38057884843496205818298043)
  ·
    refine ⟨57086827265244308727447065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38057884843496205818298043 57086827265244308727447065)
    ·
      refine ⟨42815120448933231545585299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57086827265244308727447065 42815120448933231545585299)
      ·
        refine ⟨64222680673399847318377949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42815120448933231545585299 64222680673399847318377949)
        ·
          refine ⟨24083505252524942744391731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64222680673399847318377949 24083505252524942744391731)
          ·
            refine ⟨36125257878787414116587597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24083505252524942744391731 36125257878787414116587597)
            ·
              refine ⟨13546971704545280293720349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36125257878787414116587597 13546971704545280293720349)
              ·
                refine ⟨5080114389204480110145131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13546971704545280293720349 5080114389204480110145131)
                ·
                  refine ⟨7620171583806720165217697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5080114389204480110145131 7620171583806720165217697)
                  ·
                    refine ⟨5715128687855040123913273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7620171583806720165217697 5715128687855040123913273)
                    ·
                      refine ⟨4286346515891280092934955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5715128687855040123913273 4286346515891280092934955)
                      ·
                        rfl

theorem cell23_8347630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_8347630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347630 prefixEnd_8347630 := by exact prefixLift 8347630
  have htrace : WordTrace (prefixWord ++ tailWord_8347630) baseStart_8347630 baseEnd_8347630 := by
    simpa [prefixWord, tailWord_8347630, baseEnd_8347630] using wordTrace_append hprefix tailTrace_8347630
  have hstable : (prefixWord ++ tailWord_8347630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347630).length < 2 ^ (prefixWord ++ tailWord_8347630).sum := by decide
  have hdescent : baseEnd_8347630 < baseStart_8347630 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347635 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 8]
def baseStart_8347635 : Nat := 118140960795 + 8347635 * 2 ^ 59
def prefixEnd_8347635 : Nat := 4983230072969 + 3 ^ 40 * 8347635 * 2
def baseEnd_8347635 : Nat := 4286349083294552573372431

theorem tailTrace_8347635 : CollatzResearch.WordTrace tailWord_8347635 prefixEnd_8347635 4286349083294552573372431 := by
  unfold tailWord_8347635
  simp only [CollatzResearch.WordTrace]
  refine ⟨304463261112951532400316359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202975507408634354933544239 304463261112951532400316359)
  ·
    refine ⟨456694891669427298600474539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304463261112951532400316359 456694891669427298600474539)
    ·
      refine ⟨685042337504140947900711809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456694891669427298600474539 685042337504140947900711809)
      ·
        refine ⟨513781753128105710925533857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 685042337504140947900711809 513781753128105710925533857)
        ·
          refine ⟨385336314846079283194150393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513781753128105710925533857 385336314846079283194150393)
          ·
            refine ⟨289002236134559462395612795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385336314846079283194150393 289002236134559462395612795)
            ·
              refine ⟨433503354201839193593419193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289002236134559462395612795 433503354201839193593419193)
              ·
                refine ⟨325127515651379395195064395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433503354201839193593419193 325127515651379395195064395)
                ·
                  refine ⟨487691273477069092792596593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 325127515651379395195064395 487691273477069092792596593)
                  ·
                    refine ⟨365768455107801819594447445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 487691273477069092792596593 365768455107801819594447445)
                    ·
                      refine ⟨4286349083294552573372431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 365768455107801819594447445 4286349083294552573372431)
                      ·
                        rfl

theorem cell23_8347635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 8].length) (baseStart_8347635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347635 prefixEnd_8347635 := by exact prefixLift 8347635
  have htrace : WordTrace (prefixWord ++ tailWord_8347635) baseStart_8347635 baseEnd_8347635 := by
    simpa [prefixWord, tailWord_8347635, baseEnd_8347635] using wordTrace_append hprefix tailTrace_8347635
  have hstable : (prefixWord ++ tailWord_8347635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347635).length < 2 ^ (prefixWord ++ tailWord_8347635).sum := by decide
  have hdescent : baseEnd_8347635 < baseStart_8347635 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347662 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 1, 8]
def baseStart_8347662 : Nat := 118140960795 + 8347662 * 2 ^ 59
def prefixEnd_8347662 : Nat := 4983230072969 + 3 ^ 40 * 8347662 * 2
def baseEnd_8347662 : Nat := 1428787649090741322578269

theorem tailTrace_8347662 : CollatzResearch.WordTrace tailWord_8347662 prefixEnd_8347662 1428787649090741322578269 := by
  unfold tailWord_8347662
  simp only [CollatzResearch.WordTrace]
  refine ⟨38058030735481714501443655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202976163922569144007699493 38058030735481714501443655)
  ·
    refine ⟨57087046103222571752165483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38058030735481714501443655 57087046103222571752165483)
    ·
      refine ⟨85630569154833857628248225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57087046103222571752165483 85630569154833857628248225)
      ·
        refine ⟨64222926866125393221186169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85630569154833857628248225 64222926866125393221186169)
        ·
          refine ⟨48167195149594044915889627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64222926866125393221186169 48167195149594044915889627)
          ·
            refine ⟨72250792724391067373834441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48167195149594044915889627 72250792724391067373834441)
            ·
              refine ⟨54188094543293300530375831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72250792724391067373834441 54188094543293300530375831)
              ·
                refine ⟨81282141814939950795563747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54188094543293300530375831 81282141814939950795563747)
                ·
                  refine ⟨121923212722409926193345621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81282141814939950795563747 121923212722409926193345621)
                  ·
                    refine ⟨1428787649090741322578269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 121923212722409926193345621 1428787649090741322578269)
                    ·
                      rfl

theorem cell23_8347662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_8347662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347662 prefixEnd_8347662 := by exact prefixLift 8347662
  have htrace : WordTrace (prefixWord ++ tailWord_8347662) baseStart_8347662 baseEnd_8347662 := by
    simpa [prefixWord, tailWord_8347662, baseEnd_8347662] using wordTrace_append hprefix tailTrace_8347662
  have hstable : (prefixWord ++ tailWord_8347662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347662).length < 2 ^ (prefixWord ++ tailWord_8347662).sum := by decide
  have hdescent : baseEnd_8347662 < baseStart_8347662 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347672 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 4, 1, 5]
def baseStart_8347672 : Nat := 118140960795 + 8347672 * 2 ^ 59
def prefixEnd_8347672 : Nat := 4983230072969 + 3 ^ 40 * 8347672 * 2
def baseEnd_8347672 : Nat := 4286368082078768928609761

theorem tailTrace_8347672 : CollatzResearch.WordTrace tailWord_8347672 prefixEnd_8347672 4286368082078768928609761 := by
  unfold tailWord_8347672
  simp only [CollatzResearch.WordTrace]
  refine ⟨152232305306908743859706635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202976407075878325146275513 152232305306908743859706635)
  ·
    refine ⟨228348457960363115789559953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152232305306908743859706635 228348457960363115789559953)
    ·
      refine ⟨171261343470272336842169965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228348457960363115789559953 171261343470272336842169965)
      ·
        refine ⟨64223003801352126315813737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171261343470272336842169965 64223003801352126315813737)
        ·
          refine ⟨48167252851014094736860303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64223003801352126315813737 48167252851014094736860303)
          ·
            refine ⟨72250879276521142105290455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48167252851014094736860303 72250879276521142105290455)
            ·
              refine ⟨108376318914781713157935683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72250879276521142105290455 108376318914781713157935683)
              ·
                refine ⟨162564478372172569736903525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108376318914781713157935683 162564478372172569736903525)
                ·
                  refine ⟨30480839694782356825669411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162564478372172569736903525 30480839694782356825669411)
                  ·
                    refine ⟨45721259542173535238504117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30480839694782356825669411 45721259542173535238504117)
                    ·
                      refine ⟨4286368082078768928609761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45721259542173535238504117 4286368082078768928609761)
                      ·
                        rfl

theorem cell23_8347672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_8347672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347672 prefixEnd_8347672 := by exact prefixLift 8347672
  have htrace : WordTrace (prefixWord ++ tailWord_8347672) baseStart_8347672 baseEnd_8347672 := by
    simpa [prefixWord, tailWord_8347672, baseEnd_8347672] using wordTrace_append hprefix tailTrace_8347672
  have hstable : (prefixWord ++ tailWord_8347672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347672).length < 2 ^ (prefixWord ++ tailWord_8347672).sum := by decide
  have hdescent : baseEnd_8347672 < baseStart_8347672 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347690 : List Nat := [3, 1, 4, 1, 2, 2, 3, 1, 1, 3, 2]
def baseStart_8347690 : Nat := 118140960795 + 8347690 * 2 ^ 59
def prefixEnd_8347690 : Nat := 4983230072969 + 3 ^ 40 * 8347690 * 2
def baseEnd_8347690 : Nat := 4286377324730549858184679

theorem tailTrace_8347690 : CollatzResearch.WordTrace tailWord_8347690 prefixEnd_8347690 4286377324730549858184679 := by
  unfold tailWord_8347690
  simp only [CollatzResearch.WordTrace]
  refine ⟨76116316781938069198392131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202976844751834851195712349 76116316781938069198392131)
  ·
    refine ⟨114174475172907103797588197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76116316781938069198392131 114174475172907103797588197)
    ·
      refine ⟨21407714094920081962047787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114174475172907103797588197 21407714094920081962047787)
      ·
        refine ⟨32111571142380122943071681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21407714094920081962047787 32111571142380122943071681)
        ·
          refine ⟨24083678356785092207303761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32111571142380122943071681 24083678356785092207303761)
          ·
            refine ⟨18062758767588819155477821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24083678356785092207303761 18062758767588819155477821)
            ·
              refine ⟨6773534537845807183304183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18062758767588819155477821 6773534537845807183304183)
              ·
                refine ⟨10160301806768710774956275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6773534537845807183304183 10160301806768710774956275)
                ·
                  refine ⟨15240452710153066162434413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10160301806768710774956275 15240452710153066162434413)
                  ·
                    refine ⟨5715169766307399810912905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15240452710153066162434413 5715169766307399810912905)
                    ·
                      refine ⟨4286377324730549858184679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5715169766307399810912905 4286377324730549858184679)
                      ·
                        rfl

theorem cell23_8347690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_8347690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347690 prefixEnd_8347690 := by exact prefixLift 8347690
  have htrace : WordTrace (prefixWord ++ tailWord_8347690) baseStart_8347690 baseEnd_8347690 := by
    simpa [prefixWord, tailWord_8347690, baseEnd_8347690] using wordTrace_append hprefix tailTrace_8347690
  have hstable : (prefixWord ++ tailWord_8347690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347690).length < 2 ^ (prefixWord ++ tailWord_8347690).sum := by decide
  have hdescent : baseEnd_8347690 < baseStart_8347690 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347719 : List Nat := [1, 1, 4, 1, 3, 1, 3, 1, 2, 3, 3]
def baseStart_8347719 : Nat := 118140960795 + 8347719 * 2 ^ 59
def prefixEnd_8347719 : Nat := 4983230072969 + 3 ^ 40 * 8347719 * 2
def baseEnd_8347719 : Nat := 4286392215669530244722045

theorem tailTrace_8347719 : CollatzResearch.WordTrace tailWord_8347719 prefixEnd_8347719 4286392215669530244722045 := by
  unfold tailWord_8347719
  simp only [CollatzResearch.WordTrace]
  refine ⟨304466324844647214746374211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202977549896431476497582807 304466324844647214746374211)
  ·
    refine ⟨456699487266970822119561317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304466324844647214746374211 456699487266970822119561317)
    ·
      refine ⟨85631153862557029147417747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 456699487266970822119561317 85631153862557029147417747)
      ·
        refine ⟨128446730793835543721126621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85631153862557029147417747 128446730793835543721126621)
        ·
          refine ⟨48167524047688328895422483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128446730793835543721126621 48167524047688328895422483)
          ·
            refine ⟨72251286071532493343133725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48167524047688328895422483 72251286071532493343133725)
            ·
              refine ⟨27094232276824685003675147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72251286071532493343133725 27094232276824685003675147)
              ·
                refine ⟨40641348415237027505512721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27094232276824685003675147 40641348415237027505512721)
                ·
                  refine ⟨30481011311427770629134541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40641348415237027505512721 30481011311427770629134541)
                  ·
                    refine ⟨11430379241785413985925453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30481011311427770629134541 11430379241785413985925453)
                    ·
                      refine ⟨4286392215669530244722045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11430379241785413985925453 4286392215669530244722045)
                      ·
                        rfl

theorem cell23_8347719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_8347719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347719 prefixEnd_8347719 := by exact prefixLift 8347719
  have htrace : WordTrace (prefixWord ++ tailWord_8347719) baseStart_8347719 baseEnd_8347719 := by
    simpa [prefixWord, tailWord_8347719, baseEnd_8347719] using wordTrace_append hprefix tailTrace_8347719
  have hstable : (prefixWord ++ tailWord_8347719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347719).length < 2 ^ (prefixWord ++ tailWord_8347719).sum := by decide
  have hdescent : baseEnd_8347719 < baseStart_8347719 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347722 : List Nat := [3, 1, 2, 1, 1, 2, 1, 4, 1, 7]
def baseStart_8347722 : Nat := 118140960795 + 8347722 * 2 ^ 59
def prefixEnd_8347722 : Nat := 4983230072969 + 3 ^ 40 * 8347722 * 2
def baseEnd_8347722 : Nat := 1428797918703831244328177

theorem tailTrace_8347722 : CollatzResearch.WordTrace tailWord_8347722 prefixEnd_8347722 1428797918703831244328177 := by
  unfold tailWord_8347722
  simp only [CollatzResearch.WordTrace]
  refine ⟨76116608565909086564683355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202977622842424230839155613 76116608565909086564683355)
  ·
    refine ⟨114174912848863629847025033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76116608565909086564683355 114174912848863629847025033)
    ·
      refine ⟨85631184636647722385268775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114174912848863629847025033 85631184636647722385268775)
      ·
        refine ⟨128446776954971583577903163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85631184636647722385268775 128446776954971583577903163)
        ·
          refine ⟨192670165432457375366854745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128446776954971583577903163 192670165432457375366854745)
          ·
            refine ⟨144502624074343031525141059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192670165432457375366854745 144502624074343031525141059)
            ·
              refine ⟨216753936111514547287711589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144502624074343031525141059 216753936111514547287711589)
              ·
                refine ⟨40641363020908977616445923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216753936111514547287711589 40641363020908977616445923)
                ·
                  refine ⟨60962044531363466424668885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40641363020908977616445923 60962044531363466424668885)
                  ·
                    refine ⟨1428797918703831244328177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60962044531363466424668885 1428797918703831244328177)
                    ·
                      rfl

theorem cell23_8347722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_8347722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347722 prefixEnd_8347722 := by exact prefixLift 8347722
  have htrace : WordTrace (prefixWord ++ tailWord_8347722) baseStart_8347722 baseEnd_8347722 := by
    simpa [prefixWord, tailWord_8347722, baseEnd_8347722] using wordTrace_append hprefix tailTrace_8347722
  have hstable : (prefixWord ++ tailWord_8347722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347722).length < 2 ^ (prefixWord ++ tailWord_8347722).sum := by decide
  have hdescent : baseEnd_8347722 < baseStart_8347722 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347729 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 4, 5, 2]
def baseStart_8347729 : Nat := 118140960795 + 8347729 * 2 ^ 59
def prefixEnd_8347729 : Nat := 4983230072969 + 3 ^ 40 * 8347729 * 2
def baseEnd_8347729 : Nat := 4286397350476075205596999

theorem tailTrace_8347729 : CollatzResearch.WordTrace tailWord_8347729 prefixEnd_8347729 4286397350476075205596999 := by
  unfold tailWord_8347729
  simp only [CollatzResearch.WordTrace]
  refine ⟨304466689574610986454238241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202977793049740657636158827 304466689574610986454238241)
  ·
    refine ⟨228350017180958239840678681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304466689574610986454238241 228350017180958239840678681)
    ·
      refine ⟨171262512885718679880509011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228350017180958239840678681 171262512885718679880509011)
      ·
        refine ⟨256893769328578019820763517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171262512885718679880509011 256893769328578019820763517)
        ·
          refine ⟨96335163498216757432786319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256893769328578019820763517 96335163498216757432786319)
          ·
            refine ⟨144502745247325136149179479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96335163498216757432786319 144502745247325136149179479)
            ·
              refine ⟨216754117870987704223769219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144502745247325136149179479 216754117870987704223769219)
              ·
                refine ⟨325131176806481556335653829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216754117870987704223769219 325131176806481556335653829)
                ·
                  refine ⟨60962095651215291812935093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 325131176806481556335653829 60962095651215291812935093)
                  ·
                    refine ⟨5715196467301433607462665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60962095651215291812935093 5715196467301433607462665)
                    ·
                      refine ⟨4286397350476075205596999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5715196467301433607462665 4286397350476075205596999)
                      ·
                        rfl

theorem cell23_8347729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 5, 2].length) (baseStart_8347729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347729 prefixEnd_8347729 := by exact prefixLift 8347729
  have htrace : WordTrace (prefixWord ++ tailWord_8347729) baseStart_8347729 baseEnd_8347729 := by
    simpa [prefixWord, tailWord_8347729, baseEnd_8347729] using wordTrace_append hprefix tailTrace_8347729
  have hstable : (prefixWord ++ tailWord_8347729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347729).length < 2 ^ (prefixWord ++ tailWord_8347729).sum := by decide
  have hdescent : baseEnd_8347729 < baseStart_8347729 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347779 : List Nat := [1, 1, 1, 3, 3, 3, 1, 2, 1, 4, 3]
def baseStart_8347779 : Nat := 118140960795 + 8347779 * 2 ^ 59
def prefixEnd_8347779 : Nat := 4983230072969 + 3 ^ 40 * 8347779 * 2
def baseEnd_8347779 : Nat := 4286423024508800009971769

theorem tailTrace_8347779 : CollatzResearch.WordTrace tailWord_8347779 prefixEnd_8347779 4286423024508800009971769 := by
  unfold tailWord_8347779
  simp only [CollatzResearch.WordTrace]
  refine ⟨304468513224429844993558391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202979008816286563329038927 304468513224429844993558391)
  ·
    refine ⟨456702769836644767490337587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304468513224429844993558391 456702769836644767490337587)
    ·
      refine ⟨685054154754967151235506381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456702769836644767490337587 685054154754967151235506381)
      ·
        refine ⟨256895308033112681713314893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 685054154754967151235506381 256895308033112681713314893)
        ·
          refine ⟨96335740512417255642493085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256895308033112681713314893 96335740512417255642493085)
          ·
            refine ⟨36125902692156470865934907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96335740512417255642493085 36125902692156470865934907)
            ·
              refine ⟨54188854038234706298902361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36125902692156470865934907 54188854038234706298902361)
              ·
                refine ⟨40641640528676029724176771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54188854038234706298902361 40641640528676029724176771)
                ·
                  refine ⟨60962460793014044586265157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40641640528676029724176771 60962460793014044586265157)
                  ·
                    refine ⟨11430461398690133359924717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60962460793014044586265157 11430461398690133359924717)
                    ·
                      refine ⟨4286423024508800009971769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11430461398690133359924717 4286423024508800009971769)
                      ·
                        rfl

theorem cell23_8347779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4, 3].length) (baseStart_8347779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347779 prefixEnd_8347779 := by exact prefixLift 8347779
  have htrace : WordTrace (prefixWord ++ tailWord_8347779) baseStart_8347779 baseEnd_8347779 := by
    simpa [prefixWord, tailWord_8347779, baseEnd_8347779] using wordTrace_append hprefix tailTrace_8347779
  have hstable : (prefixWord ++ tailWord_8347779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347779).length < 2 ^ (prefixWord ++ tailWord_8347779).sum := by decide
  have hdescent : baseEnd_8347779 < baseStart_8347779 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347786 : List Nat := [3, 1, 2, 3, 1, 2, 2, 2, 3, 4]
def baseStart_8347786 : Nat := 118140960795 + 8347786 * 2 ^ 59
def prefixEnd_8347786 : Nat := 4983230072969 + 3 ^ 40 * 8347786 * 2
def baseEnd_8347786 : Nat := 1428808872957793827528079

theorem tailTrace_8347786 : CollatzResearch.WordTrace tailWord_8347786 prefixEnd_8347786 1428808872957793827528079 := by
  unfold tailWord_8347786
  simp only [CollatzResearch.WordTrace]
  refine ⟨76117192133851121297265803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202979179023602990126042141 76117192133851121297265803)
  ·
    refine ⟨114175788200776681945898705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76117192133851121297265803 114175788200776681945898705)
    ·
      refine ⟨85631841150582511459424029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114175788200776681945898705 85631841150582511459424029)
      ·
        refine ⟨32111940431468441797284011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85631841150582511459424029 32111940431468441797284011)
        ·
          refine ⟨48167910647202662695926017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32111940431468441797284011 48167910647202662695926017)
          ·
            refine ⟨36125932985401997021944513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48167910647202662695926017 36125932985401997021944513)
            ·
              refine ⟨27094449739051497766458385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36125932985401997021944513 27094449739051497766458385)
              ·
                refine ⟨20320837304288623324843789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27094449739051497766458385 20320837304288623324843789)
                ·
                  refine ⟨7620313989108233746816421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20320837304288623324843789 7620313989108233746816421)
                  ·
                    refine ⟨1428808872957793827528079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7620313989108233746816421 1428808872957793827528079)
                    ·
                      rfl

theorem cell23_8347786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_8347786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347786 prefixEnd_8347786 := by exact prefixLift 8347786
  have htrace : WordTrace (prefixWord ++ tailWord_8347786) baseStart_8347786 baseEnd_8347786 := by
    simpa [prefixWord, tailWord_8347786, baseEnd_8347786] using wordTrace_append hprefix tailTrace_8347786
  have hstable : (prefixWord ++ tailWord_8347786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347786).length < 2 ^ (prefixWord ++ tailWord_8347786).sum := by decide
  have hdescent : baseEnd_8347786 < baseStart_8347786 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347866 : List Nat := [3, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4]
def baseStart_8347866 : Nat := 118140960795 + 8347866 * 2 ^ 59
def prefixEnd_8347866 : Nat := 4983230072969 + 3 ^ 40 * 8347866 * 2
def baseEnd_8347866 : Nat := 4286467697325741169583869

theorem tailTrace_8347866 : CollatzResearch.WordTrace tailWord_8347866 prefixEnd_8347866 4286467697325741169583869 := by
  unfold tailWord_8347866
  simp only [CollatzResearch.WordTrace]
  refine ⟨76117921593778664712993863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202981124250076439234650301 76117921593778664712993863)
  ·
    refine ⟨114176882390667997069490795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76117921593778664712993863 114176882390667997069490795)
    ·
      refine ⟨171265323586001995604236193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114176882390667997069490795 171265323586001995604236193)
      ·
        refine ⟨128448992689501496703177145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171265323586001995604236193 128448992689501496703177145)
        ·
          refine ⟨96336744517126122527382859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128448992689501496703177145 96336744517126122527382859)
          ·
            refine ⟨144505116775689183791074289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96336744517126122527382859 144505116775689183791074289)
            ·
              refine ⟨108378837581766887843305717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144505116775689183791074289 108378837581766887843305717)
              ·
                refine ⟨10160516023290645735309911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108378837581766887843305717 10160516023290645735309911)
                ·
                  refine ⟨15240774034935968602964867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10160516023290645735309911 15240774034935968602964867)
                  ·
                    refine ⟨22861161052403952904447301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15240774034935968602964867 22861161052403952904447301)
                    ·
                      refine ⟨4286467697325741169583869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22861161052403952904447301 4286467697325741169583869)
                      ·
                        rfl

theorem cell23_8347866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_8347866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347866 prefixEnd_8347866 := by exact prefixLift 8347866
  have htrace : WordTrace (prefixWord ++ tailWord_8347866) baseStart_8347866 baseEnd_8347866 := by
    simpa [prefixWord, tailWord_8347866, baseEnd_8347866] using wordTrace_append hprefix tailTrace_8347866
  have hstable : (prefixWord ++ tailWord_8347866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347866).length < 2 ^ (prefixWord ++ tailWord_8347866).sum := by decide
  have hdescent : baseEnd_8347866 < baseStart_8347866 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347877 : List Nat := [1, 3, 1, 4, 2, 1, 4, 2, 1, 1, 3]
def baseStart_8347877 : Nat := 118140960795 + 8347877 * 2 ^ 59
def prefixEnd_8347877 : Nat := 4983230072969 + 3 ^ 40 * 8347877 * 2
def baseEnd_8347877 : Nat := 4286473345612940626546319

theorem tailTrace_8347877 : CollatzResearch.WordTrace tailWord_8347877 prefixEnd_8347877 4286473345612940626546319 := by
  unfold tailWord_8347877
  simp only [CollatzResearch.WordTrace]
  refine ⟨304472087578074807730625885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202981391718716538487083923 304472087578074807730625885)
  ·
    refine ⟨114177032841778052898984707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304472087578074807730625885 114177032841778052898984707)
    ·
      refine ⟨171265549262667079348477061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114177032841778052898984707 171265549262667079348477061)
      ·
        refine ⟨32112290486750077377839449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171265549262667079348477061 32112290486750077377839449)
        ·
          refine ⟨24084217865062558033379587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32112290486750077377839449 24084217865062558033379587)
          ·
            refine ⟨36126326797593837050069381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24084217865062558033379587 36126326797593837050069381)
            ·
              refine ⟨6773686274548844446888009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36126326797593837050069381 6773686274548844446888009)
              ·
                refine ⟨5080264705911633335166007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6773686274548844446888009 5080264705911633335166007)
                ·
                  refine ⟨7620397058867450002749011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5080264705911633335166007 7620397058867450002749011)
                  ·
                    refine ⟨11430595588301175004123517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7620397058867450002749011 11430595588301175004123517)
                    ·
                      refine ⟨4286473345612940626546319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11430595588301175004123517 4286473345612940626546319)
                      ·
                        rfl

theorem cell23_8347877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_8347877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347877 prefixEnd_8347877 := by exact prefixLift 8347877
  have htrace : WordTrace (prefixWord ++ tailWord_8347877) baseStart_8347877 baseEnd_8347877 := by
    simpa [prefixWord, tailWord_8347877, baseEnd_8347877] using wordTrace_append hprefix tailTrace_8347877
  have hstable : (prefixWord ++ tailWord_8347877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347877).length < 2 ^ (prefixWord ++ tailWord_8347877).sum := by decide
  have hdescent : baseEnd_8347877 < baseStart_8347877 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347883 : List Nat := [1, 1, 1, 1, 2, 5, 2, 3, 3, 2, 2]
def baseStart_8347883 : Nat := 118140960795 + 8347883 * 2 ^ 59
def prefixEnd_8347883 : Nat := 4983230072969 + 3 ^ 40 * 8347883 * 2
def baseEnd_8347883 : Nat := 4286476426496867603071291

theorem tailTrace_8347883 : CollatzResearch.WordTrace tailWord_8347883 prefixEnd_8347883 4286476426496867603071291 := by
  unfold tailWord_8347883
  simp only [CollatzResearch.WordTrace]
  refine ⟨304472306416053070755344303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202981537610702047170229535 304472306416053070755344303)
  ·
    refine ⟨456708459624079606133016455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304472306416053070755344303 456708459624079606133016455)
    ·
      refine ⟨685062689436119409199524683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456708459624079606133016455 685062689436119409199524683)
      ·
        refine ⟨1027594034154179113799287025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685062689436119409199524683 1027594034154179113799287025)
        ·
          refine ⟨770695525615634335349465269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1027594034154179113799287025 770695525615634335349465269)
          ·
            refine ⟨72252705526465718939012369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 770695525615634335349465269 72252705526465718939012369)
            ·
              refine ⟨54189529144849289204259277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72252705526465718939012369 54189529144849289204259277)
              ·
                refine ⟨20321073429318483451597229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54189529144849289204259277 20321073429318483451597229)
                ·
                  refine ⟨7620402535994431294348961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20321073429318483451597229 7620402535994431294348961)
                  ·
                    refine ⟨5715301901995823470761721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7620402535994431294348961 5715301901995823470761721)
                    ·
                      refine ⟨4286476426496867603071291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5715301901995823470761721 4286476426496867603071291)
                      ·
                        rfl

theorem cell23_8347883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3, 2, 2].length) (baseStart_8347883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347883 prefixEnd_8347883 := by exact prefixLift 8347883
  have htrace : WordTrace (prefixWord ++ tailWord_8347883) baseStart_8347883 baseEnd_8347883 := by
    simpa [prefixWord, tailWord_8347883, baseEnd_8347883] using wordTrace_append hprefix tailTrace_8347883
  have hstable : (prefixWord ++ tailWord_8347883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347883).length < 2 ^ (prefixWord ++ tailWord_8347883).sum := by decide
  have hdescent : baseEnd_8347883 < baseStart_8347883 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347889 : List Nat := [1, 2, 2, 2, 2, 1, 5, 8]
def baseStart_8347889 : Nat := 118140960795 + 8347889 * 2 ^ 59
def prefixEnd_8347889 : Nat := 4983230072969 + 3 ^ 40 * 8347889 * 2
def baseEnd_8347889 : Nat := 158758500273362762207269

theorem tailTrace_8347889 : CollatzResearch.WordTrace tailWord_8347889 prefixEnd_8347889 158758500273362762207269 := by
  unfold tailWord_8347889
  simp only [CollatzResearch.WordTrace]
  refine ⟨304472525254031333780062721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202981683502687555853375147 304472525254031333780062721)
  ·
    refine ⟨228354393940523500335047041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304472525254031333780062721 228354393940523500335047041)
    ·
      refine ⟨171265795455392625251285281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228354393940523500335047041 171265795455392625251285281)
      ·
        refine ⟨128449346591544468938463961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171265795455392625251285281 128449346591544468938463961)
        ·
          refine ⟨96337009943658351703847971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128449346591544468938463961 96337009943658351703847971)
          ·
            refine ⟨144505514915487527555771957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96337009943658351703847971 144505514915487527555771957)
            ·
              refine ⟨13547392023326955708353621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144505514915487527555771957 13547392023326955708353621)
              ·
                refine ⟨158758500273362762207269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13547392023326955708353621 158758500273362762207269)
                ·
                  rfl

theorem cell23_8347889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 8].length) (baseStart_8347889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347889 prefixEnd_8347889 := by exact prefixLift 8347889
  have htrace : WordTrace (prefixWord ++ tailWord_8347889) baseStart_8347889 baseEnd_8347889 := by
    simpa [prefixWord, tailWord_8347889, baseEnd_8347889] using wordTrace_append hprefix tailTrace_8347889
  have hstable : (prefixWord ++ tailWord_8347889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347889).length < 2 ^ (prefixWord ++ tailWord_8347889).sum := by decide
  have hdescent : baseEnd_8347889 < baseStart_8347889 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347900 : List Nat := [2, 2, 2, 1, 4, 2, 1, 2, 3, 2, 2]
def baseStart_8347900 : Nat := 118140960795 + 8347900 * 2 ^ 59
def prefixEnd_8347900 : Nat := 4983230072969 + 3 ^ 40 * 8347900 * 2
def baseEnd_8347900 : Nat := 4286485155667994036558713

theorem tailTrace_8347900 : CollatzResearch.WordTrace tailWord_8347900 prefixEnd_8347900 4286485155667994036558713 := by
  unfold tailWord_8347900
  simp only [CollatzResearch.WordTrace]
  refine ⟨152236463228495741329356577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202981950971327655105808769 152236463228495741329356577)
  ·
    refine ⟨114177347421371805997017433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152236463228495741329356577 114177347421371805997017433)
    ·
      refine ⟨85633010566028854497763075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114177347421371805997017433 85633010566028854497763075)
      ·
        refine ⟨128449515849043281746644613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85633010566028854497763075 128449515849043281746644613)
        ·
          refine ⟨24084284221695615327495865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128449515849043281746644613 24084284221695615327495865)
          ·
            refine ⟨18063213166271711495621899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24084284221695615327495865 18063213166271711495621899)
            ·
              refine ⟨27094819749407567243432849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18063213166271711495621899 27094819749407567243432849)
              ·
                refine ⟨20321114812055675432574637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27094819749407567243432849 20321114812055675432574637)
                ·
                  refine ⟨7620418054520878287215489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20321114812055675432574637 7620418054520878287215489)
                  ·
                    refine ⟨5715313540890658715411617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7620418054520878287215489 5715313540890658715411617)
                    ·
                      refine ⟨4286485155667994036558713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5715313540890658715411617 4286485155667994036558713)
                      ·
                        rfl

theorem cell23_8347900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 3, 2, 2].length) (baseStart_8347900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347900 prefixEnd_8347900 := by exact prefixLift 8347900
  have htrace : WordTrace (prefixWord ++ tailWord_8347900) baseStart_8347900 baseEnd_8347900 := by
    simpa [prefixWord, tailWord_8347900, baseEnd_8347900] using wordTrace_append hprefix tailTrace_8347900
  have hstable : (prefixWord ++ tailWord_8347900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347900).length < 2 ^ (prefixWord ++ tailWord_8347900).sum := by decide
  have hdescent : baseEnd_8347900 < baseStart_8347900 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347916 : List Nat := [2, 2, 1, 2, 2, 2, 1, 4, 1, 3, 3]
def baseStart_8347916 : Nat := 118140960795 + 8347916 * 2 ^ 59
def prefixEnd_8347916 : Nat := 4983230072969 + 3 ^ 40 * 8347916 * 2
def baseEnd_8347916 : Nat := 4286493371358465973958639

theorem tailTrace_8347916 : CollatzResearch.WordTrace tailWord_8347916 prefixEnd_8347916 4286493371358465973958639 := by
  unfold tailWord_8347916
  simp only [CollatzResearch.WordTrace]
  refine ⟨152236755012466758695647801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202982340016622344927530401 152236755012466758695647801)
  ·
    refine ⟨114177566259350069021735851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152236755012466758695647801 114177566259350069021735851)
    ·
      refine ⟨171266349389025103532603777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114177566259350069021735851 171266349389025103532603777)
      ·
        refine ⟨128449762041768827649452833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171266349389025103532603777 128449762041768827649452833)
        ·
          refine ⟨96337321531326620737089625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128449762041768827649452833 96337321531326620737089625)
          ·
            refine ⟨72252991148494965552817219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96337321531326620737089625 72252991148494965552817219)
            ·
              refine ⟨108379486722742448329225829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72252991148494965552817219 108379486722742448329225829)
              ·
                refine ⟨20321153760514209061729843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108379486722742448329225829 20321153760514209061729843)
                ·
                  refine ⟨30481730640771313592594765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20321153760514209061729843 30481730640771313592594765)
                  ·
                    refine ⟨11430648990289242597223037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30481730640771313592594765 11430648990289242597223037)
                    ·
                      refine ⟨4286493371358465973958639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11430648990289242597223037 4286493371358465973958639)
                      ·
                        rfl

theorem cell23_8347916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_8347916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347916 prefixEnd_8347916 := by exact prefixLift 8347916
  have htrace : WordTrace (prefixWord ++ tailWord_8347916) baseStart_8347916 baseEnd_8347916 := by
    simpa [prefixWord, tailWord_8347916, baseEnd_8347916] using wordTrace_append hprefix tailTrace_8347916
  have hstable : (prefixWord ++ tailWord_8347916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347916).length < 2 ^ (prefixWord ++ tailWord_8347916).sum := by decide
  have hdescent : baseEnd_8347916 < baseStart_8347916 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347934 : List Nat := [4, 3, 2, 1, 1, 2, 2, 1, 3, 2, 2]
def baseStart_8347934 : Nat := 118140960795 + 8347934 * 2 ^ 59
def prefixEnd_8347934 : Nat := 4983230072969 + 3 ^ 40 * 8347934 * 2
def baseEnd_8347934 : Nat := 4286502614010246903533557

theorem tailTrace_8347934 : CollatzResearch.WordTrace tailWord_8347934 prefixEnd_8347934 4286502614010246903533557 := by
  unfold tailWord_8347934
  simp only [CollatzResearch.WordTrace]
  refine ⟨38059270817358538308181357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202982777692578870976967237 38059270817358538308181357)
  ·
    refine ⟨14272226556509451865568009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38059270817358538308181357 14272226556509451865568009)
    ·
      refine ⟨10704169917382088899176007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14272226556509451865568009 10704169917382088899176007)
      ·
        refine ⟨16056254876073133348764011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10704169917382088899176007 16056254876073133348764011)
        ·
          refine ⟨24084382314109700023146017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16056254876073133348764011 24084382314109700023146017)
          ·
            refine ⟨18063286735582275017359513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24084382314109700023146017 18063286735582275017359513)
            ·
              refine ⟨13547465051686706263019635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18063286735582275017359513 13547465051686706263019635)
              ·
                refine ⟨20321197577530059394529453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13547465051686706263019635 20321197577530059394529453)
                ·
                  refine ⟨7620449091573772272948545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20321197577530059394529453 7620449091573772272948545)
                  ·
                    refine ⟨5715336818680329204711409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7620449091573772272948545 5715336818680329204711409)
                    ·
                      refine ⟨4286502614010246903533557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5715336818680329204711409 4286502614010246903533557)
                      ·
                        rfl

theorem cell23_8347934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_8347934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347934 prefixEnd_8347934 := by exact prefixLift 8347934
  have htrace : WordTrace (prefixWord ++ tailWord_8347934) baseStart_8347934 baseEnd_8347934 := by
    simpa [prefixWord, tailWord_8347934, baseEnd_8347934] using wordTrace_append hprefix tailTrace_8347934
  have hstable : (prefixWord ++ tailWord_8347934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347934).length < 2 ^ (prefixWord ++ tailWord_8347934).sum := by decide
  have hdescent : baseEnd_8347934 < baseStart_8347934 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347959 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 5]
def baseStart_8347959 : Nat := 118140960795 + 8347959 * 2 ^ 59
def prefixEnd_8347959 : Nat := 4983230072969 + 3 ^ 40 * 8347959 * 2
def baseEnd_8347959 : Nat := 4286515451026609305720941

theorem tailTrace_8347959 : CollatzResearch.WordTrace tailWord_8347959 prefixEnd_8347959 4286515451026609305720941 := by
  unfold tailWord_8347959
  simp only [CollatzResearch.WordTrace]
  refine ⟨304475078363777735735110931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202983385575851823823407287 304475078363777735735110931)
  ·
    refine ⟨456712617545666603602666397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304475078363777735735110931 456712617545666603602666397)
    ·
      refine ⟨171267231579624976350999899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456712617545666603602666397 171267231579624976350999899)
      ·
        refine ⟨256900847369437464526499849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171267231579624976350999899 256900847369437464526499849)
        ·
          refine ⟨192675635527078098394874887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256900847369437464526499849 192675635527078098394874887)
          ·
            refine ⟨289013453290617147592312331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192675635527078098394874887 289013453290617147592312331)
            ·
              refine ⟨433520179935925721388468497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289013453290617147592312331 433520179935925721388468497)
              ·
                refine ⟨325140134951944291041351373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433520179935925721388468497 325140134951944291041351373)
                ·
                  refine ⟨121927550606979109140506765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 325140134951944291041351373 121927550606979109140506765)
                  ·
                    refine ⟨45722831477617165927690037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121927550606979109140506765 45722831477617165927690037)
                    ·
                      refine ⟨4286515451026609305720941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45722831477617165927690037 4286515451026609305720941)
                      ·
                        rfl

theorem cell23_8347959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_8347959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347959 prefixEnd_8347959 := by exact prefixLift 8347959
  have htrace : WordTrace (prefixWord ++ tailWord_8347959) baseStart_8347959 baseEnd_8347959 := by
    simpa [prefixWord, tailWord_8347959, baseEnd_8347959] using wordTrace_append hprefix tailTrace_8347959
  have hstable : (prefixWord ++ tailWord_8347959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347959).length < 2 ^ (prefixWord ++ tailWord_8347959).sum := by decide
  have hdescent : baseEnd_8347959 < baseStart_8347959 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8347986 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_8347986 : Nat := 118140960795 + 8347986 * 2 ^ 59
def prefixEnd_8347986 : Nat := 4983230072969 + 3 ^ 40 * 8347986 * 2
def baseEnd_8347986 : Nat := 4286529315004280700083317

theorem tailTrace_8347986 : CollatzResearch.WordTrace tailWord_8347986 prefixEnd_8347986 4286529315004280700083317 := by
  unfold tailWord_8347986
  simp only [CollatzResearch.WordTrace]
  refine ⟨76119015783669979836585953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202984042089786612897562541 76119015783669979836585953)
  ·
    refine ⟨57089261837752484877439465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76119015783669979836585953 57089261837752484877439465)
    ·
      refine ⟨42816946378314363658079599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57089261837752484877439465 42816946378314363658079599)
      ·
        refine ⟨64225419567471545487119399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42816946378314363658079599 64225419567471545487119399)
        ·
          refine ⟨96338129351207318230679099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64225419567471545487119399 96338129351207318230679099)
          ·
            refine ⟨144507194026810977346018649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96338129351207318230679099 144507194026810977346018649)
            ·
              refine ⟨108380395520108233009513987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144507194026810977346018649 108380395520108233009513987)
              ·
                refine ⟨162570593280162349514270981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108380395520108233009513987 162570593280162349514270981)
                ·
                  refine ⟨30481986240030440533925809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162570593280162349514270981 30481986240030440533925809)
                  ·
                    refine ⟨22861489680022830400444357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30481986240030440533925809 22861489680022830400444357)
                    ·
                      refine ⟨4286529315004280700083317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22861489680022830400444357 4286529315004280700083317)
                      ·
                        rfl

theorem cell23_8347986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_8347986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8347986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8347986 prefixEnd_8347986 := by exact prefixLift 8347986
  have htrace : WordTrace (prefixWord ++ tailWord_8347986) baseStart_8347986 baseEnd_8347986 := by
    simpa [prefixWord, tailWord_8347986, baseEnd_8347986] using wordTrace_append hprefix tailTrace_8347986
  have hstable : (prefixWord ++ tailWord_8347986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8347986).length < 2 ^ (prefixWord ++ tailWord_8347986).sum := by decide
  have hdescent : baseEnd_8347986 < baseStart_8347986 := by decide
  rcases family_descends (prefixWord ++ tailWord_8347986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348007 : List Nat := [1, 1, 5, 1, 3, 2, 1, 3, 2, 2, 2]
def baseStart_8348007 : Nat := 118140960795 + 8348007 * 2 ^ 59
def prefixEnd_8348007 : Nat := 4983230072969 + 3 ^ 40 * 8348007 * 2
def baseEnd_8348007 : Nat := 4286540098098025117920721

theorem tailTrace_8348007 : CollatzResearch.WordTrace tailWord_8348007 prefixEnd_8348007 4286540098098025117920721 := by
  unfold tailWord_8348007
  simp only [CollatzResearch.WordTrace]
  refine ⟨304476829067603839932858275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202984552711735893288572183 304476829067603839932858275)
  ·
    refine ⟨456715243601405759899287413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304476829067603839932858275 456715243601405759899287413)
    ·
      refine ⟨42817054087631789990558195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 456715243601405759899287413 42817054087631789990558195)
      ·
        refine ⟨64225581131447684985837293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42817054087631789990558195 64225581131447684985837293)
        ·
          refine ⟨24084592924292881869688985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64225581131447684985837293 24084592924292881869688985)
          ·
            refine ⟨18063444693219661402266739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24084592924292881869688985 18063444693219661402266739)
            ·
              refine ⟨27095167039829492103400109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18063444693219661402266739 27095167039829492103400109)
              ·
                refine ⟨10160687639936059538775041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27095167039829492103400109 10160687639936059538775041)
                ·
                  refine ⟨7620515729952044654081281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10160687639936059538775041 7620515729952044654081281)
                  ·
                    refine ⟨5715386797464033490560961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7620515729952044654081281 5715386797464033490560961)
                    ·
                      refine ⟨4286540098098025117920721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5715386797464033490560961 4286540098098025117920721)
                      ·
                        rfl

theorem cell23_8348007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_8348007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348007 prefixEnd_8348007 := by exact prefixLift 8348007
  have htrace : WordTrace (prefixWord ++ tailWord_8348007) baseStart_8348007 baseEnd_8348007 := by
    simpa [prefixWord, tailWord_8348007, baseEnd_8348007] using wordTrace_append hprefix tailTrace_8348007
  have hstable : (prefixWord ++ tailWord_8348007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348007).length < 2 ^ (prefixWord ++ tailWord_8348007).sum := by decide
  have hdescent : baseEnd_8348007 < baseStart_8348007 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348036 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_8348036 : Nat := 118140960795 + 8348036 * 2 ^ 59
def prefixEnd_8348036 : Nat := 4983230072969 + 3 ^ 40 * 8348036 * 2
def baseEnd_8348036 : Nat := 4286554989037005504458087

theorem tailTrace_8348036 : CollatzResearch.WordTrace tailWord_8348036 prefixEnd_8348036 4286554989037005504458087 := by
  unfold tailWord_8348036
  simp only [CollatzResearch.WordTrace]
  refine ⟨152238943392249388942831981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202985257856332518590442641 152238943392249388942831981)
  ·
    refine ⟨57089603772093520853561993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152238943392249388942831981 57089603772093520853561993)
    ·
      refine ⟨42817202829070140640171495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57089603772093520853561993 42817202829070140640171495)
      ·
        refine ⟨64225804243605210960257243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42817202829070140640171495 64225804243605210960257243)
        ·
          refine ⟨96338706365407816440385865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64225804243605210960257243 96338706365407816440385865)
          ·
            refine ⟨72254029774055862330289399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96338706365407816440385865 72254029774055862330289399)
            ·
              refine ⟨108381044661083793495434099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72254029774055862330289399 108381044661083793495434099)
              ·
                refine ⟨162571566991625690243151149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108381044661083793495434099 162571566991625690243151149)
                ·
                  refine ⟨60964337621859633841181681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162571566991625690243151149 60964337621859633841181681)
                  ·
                    refine ⟨45723253216394725380886261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60964337621859633841181681 45723253216394725380886261)
                    ·
                      refine ⟨4286554989037005504458087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45723253216394725380886261 4286554989037005504458087)
                      ·
                        rfl

theorem cell23_8348036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_8348036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348036 prefixEnd_8348036 := by exact prefixLift 8348036
  have htrace : WordTrace (prefixWord ++ tailWord_8348036) baseStart_8348036 baseEnd_8348036 := by
    simpa [prefixWord, tailWord_8348036, baseEnd_8348036] using wordTrace_append hprefix tailTrace_8348036
  have hstable : (prefixWord ++ tailWord_8348036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348036).length < 2 ^ (prefixWord ++ tailWord_8348036).sum := by decide
  have hdescent : baseEnd_8348036 < baseStart_8348036 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348054 : List Nat := [5, 3, 1, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_8348054 : Nat := 118140960795 + 8348054 * 2 ^ 59
def prefixEnd_8348054 : Nat := 4983230072969 + 3 ^ 40 * 8348054 * 2
def baseEnd_8348054 : Nat := 4286564231688786434033005

theorem tailTrace_8348054 : CollatzResearch.WordTrace tailWord_8348054 prefixEnd_8348054 4286564231688786434033005 := by
  unfold tailWord_8348054
  simp only [CollatzResearch.WordTrace]
  refine ⟨19029908956152097934988701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202985695532289044639879477 19029908956152097934988701)
  ·
    refine ⟨7136215858557036725620763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19029908956152097934988701 7136215858557036725620763)
    ·
      refine ⟨10704323787835555088431145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7136215858557036725620763 10704323787835555088431145)
      ·
        refine ⟨8028242840876666316323359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10704323787835555088431145 8028242840876666316323359)
        ·
          refine ⟨12042364261314999474485039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8028242840876666316323359 12042364261314999474485039)
          ·
            refine ⟨18063546391972499211727559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12042364261314999474485039 18063546391972499211727559)
            ·
              refine ⟨27095319587958748817591339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18063546391972499211727559 27095319587958748817591339)
              ·
                refine ⟨40642979381938123226387009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27095319587958748817591339 40642979381938123226387009)
                ·
                  refine ⟨30482234536453592419790257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40642979381938123226387009 30482234536453592419790257)
                  ·
                    refine ⟨22861675902340194314842693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30482234536453592419790257 22861675902340194314842693)
                    ·
                      refine ⟨4286564231688786434033005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22861675902340194314842693 4286564231688786434033005)
                      ·
                        rfl

theorem cell23_8348054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_8348054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348054 prefixEnd_8348054 := by exact prefixLift 8348054
  have htrace : WordTrace (prefixWord ++ tailWord_8348054) baseStart_8348054 baseEnd_8348054 := by
    simpa [prefixWord, tailWord_8348054, baseEnd_8348054] using wordTrace_append hprefix tailTrace_8348054
  have hstable : (prefixWord ++ tailWord_8348054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348054).length < 2 ^ (prefixWord ++ tailWord_8348054).sum := by decide
  have hdescent : baseEnd_8348054 < baseStart_8348054 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348077 : List Nat := [1, 5, 2, 2, 2, 2, 1, 1, 2, 5]
def baseStart_8348077 : Nat := 118140960795 + 8348077 * 2 ^ 59
def prefixEnd_8348077 : Nat := 4983230072969 + 3 ^ 40 * 8348077 * 2
def baseEnd_8348077 : Nat := 1428858680581279948015133

theorem tailTrace_8348077 : CollatzResearch.WordTrace tailWord_8348077 prefixEnd_8348077 1428858680581279948015133 := by
  unfold tailWord_8348077
  simp only [CollatzResearch.WordTrace]
  refine ⟨304479382177350241887906485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202986254784900161258604323 304479382177350241887906485)
  ·
    refine ⟨28544942079126585176991233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 304479382177350241887906485 28544942079126585176991233)
    ·
      refine ⟨21408706559344938882743425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28544942079126585176991233 21408706559344938882743425)
      ·
        refine ⟨16056529919508704162057569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21408706559344938882743425 16056529919508704162057569)
        ·
          refine ⟨12042397439631528121543177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16056529919508704162057569 12042397439631528121543177)
          ·
            refine ⟨9031798079723646091157383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12042397439631528121543177 9031798079723646091157383)
            ·
              refine ⟨13547697119585469136736075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9031798079723646091157383 13547697119585469136736075)
              ·
                refine ⟨20321545679378203705104113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13547697119585469136736075 20321545679378203705104113)
                ·
                  refine ⟨15241159259533652778828085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20321545679378203705104113 15241159259533652778828085)
                  ·
                    refine ⟨1428858680581279948015133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15241159259533652778828085 1428858680581279948015133)
                    ·
                      rfl

theorem cell23_8348077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_8348077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348077 prefixEnd_8348077 := by exact prefixLift 8348077
  have htrace : WordTrace (prefixWord ++ tailWord_8348077) baseStart_8348077 baseEnd_8348077 := by
    simpa [prefixWord, tailWord_8348077, baseEnd_8348077] using wordTrace_append hprefix tailTrace_8348077
  have hstable : (prefixWord ++ tailWord_8348077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348077).length < 2 ^ (prefixWord ++ tailWord_8348077).sum := by decide
  have hdescent : baseEnd_8348077 < baseStart_8348077 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348103 : List Nat := [1, 1, 4, 1, 1, 4, 3, 2, 6]
def baseStart_8348103 : Nat := 118140960795 + 8348103 * 2 ^ 59
def prefixEnd_8348103 : Nat := 4983230072969 + 3 ^ 40 * 8348103 * 2
def baseEnd_8348103 : Nat := 476287710248984082480031

theorem tailTrace_8348103 : CollatzResearch.WordTrace tailWord_8348103 prefixEnd_8348103 476287710248984082480031 := by
  unfold tailWord_8348103
  simp only [CollatzResearch.WordTrace]
  refine ⟨304480330475256048328352963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202986886983504032218901975 304480330475256048328352963)
  ·
    refine ⟨456720495712884072492529445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304480330475256048328352963 456720495712884072492529445)
    ·
      refine ⟨85635092946165763592349271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 456720495712884072492529445 85635092946165763592349271)
      ·
        refine ⟨128452639419248645388523907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85635092946165763592349271 128452639419248645388523907)
        ·
          refine ⟨192678959128872968082785861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128452639419248645388523907 192678959128872968082785861)
          ·
            refine ⟨36127304836663681515522349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192678959128872968082785861 36127304836663681515522349)
            ·
              refine ⟨13547739313748880568320881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36127304836663681515522349 13547739313748880568320881)
              ·
                refine ⟨10160804485311660426240661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13547739313748880568320881 10160804485311660426240661)
                ·
                  refine ⟨476287710248984082480031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10160804485311660426240661 476287710248984082480031)
                  ·
                    rfl

theorem cell23_8348103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 6].length) (baseStart_8348103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348103 prefixEnd_8348103 := by exact prefixLift 8348103
  have htrace : WordTrace (prefixWord ++ tailWord_8348103) baseStart_8348103 baseEnd_8348103 := by
    simpa [prefixWord, tailWord_8348103, baseEnd_8348103] using wordTrace_append hprefix tailTrace_8348103
  have hstable : (prefixWord ++ tailWord_8348103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348103).length < 2 ^ (prefixWord ++ tailWord_8348103).sum := by decide
  have hdescent : baseEnd_8348103 < baseStart_8348103 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348106 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 1, 1, 8]
def baseStart_8348106 : Nat := 118140960795 + 8348106 * 2 ^ 59
def prefixEnd_8348106 : Nat := 4983230072969 + 3 ^ 40 * 8348106 * 2
def baseEnd_8348106 : Nat := 4286590932682820230582765

theorem tailTrace_8348106 : CollatzResearch.WordTrace tailWord_8348106 prefixEnd_8348106 4286590932682820230582765 := by
  unfold tailWord_8348106
  simp only [CollatzResearch.WordTrace]
  refine ⟨76120109973561294960178043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202986959929496786560474781 76120109973561294960178043)
  ·
    refine ⟨114180164960341942440267065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76120109973561294960178043 114180164960341942440267065)
    ·
      refine ⟨85635123720256456830200299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114180164960341942440267065 85635123720256456830200299)
      ·
        refine ⟨128452685580384685245300449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85635123720256456830200299 128452685580384685245300449)
        ·
          refine ⟨96339514185288513933975337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128452685580384685245300449 96339514185288513933975337)
          ·
            refine ⟨72254635638966385450481503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96339514185288513933975337 72254635638966385450481503)
            ·
              refine ⟨108381953458449578175722255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72254635638966385450481503 108381953458449578175722255)
              ·
                refine ⟨162572930187674367263583383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108381953458449578175722255 162572930187674367263583383)
                ·
                  refine ⟨243859395281511550895375075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162572930187674367263583383 243859395281511550895375075)
                  ·
                    refine ⟨365789092922267326343062613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 243859395281511550895375075 365789092922267326343062613)
                    ·
                      refine ⟨4286590932682820230582765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 365789092922267326343062613 4286590932682820230582765)
                      ·
                        rfl

theorem cell23_8348106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_8348106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348106 prefixEnd_8348106 := by exact prefixLift 8348106
  have htrace : WordTrace (prefixWord ++ tailWord_8348106) baseStart_8348106 baseEnd_8348106 := by
    simpa [prefixWord, tailWord_8348106, baseEnd_8348106] using wordTrace_append hprefix tailTrace_8348106
  have hstable : (prefixWord ++ tailWord_8348106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348106).length < 2 ^ (prefixWord ++ tailWord_8348106).sum := by decide
  have hdescent : baseEnd_8348106 < baseStart_8348106 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348140 : List Nat := [2, 2, 1, 1, 2, 1, 4, 3, 2, 3, 2]
def baseStart_8348140 : Nat := 118140960795 + 8348140 * 2 ^ 59
def prefixEnd_8348140 : Nat := 4983230072969 + 3 ^ 40 * 8348140 * 2
def baseEnd_8348140 : Nat := 4286608391025073097557609

theorem tailTrace_8348140 : CollatzResearch.WordTrace tailWord_8348140 prefixEnd_8348140 4286608391025073097557609 := by
  unfold tailWord_8348140
  simp only [CollatzResearch.WordTrace]
  refine ⟨152240839988061001823724937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202987786650748002431633249 152240839988061001823724937)
  ·
    refine ⟨114180629991045751367793703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152240839988061001823724937 114180629991045751367793703)
    ·
      refine ⟨171270944986568627051690555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114180629991045751367793703 171270944986568627051690555)
      ·
        refine ⟨256906417479852940577535833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171270944986568627051690555 256906417479852940577535833)
        ·
          refine ⟨192679813109889705433151875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256906417479852940577535833 192679813109889705433151875)
          ·
            refine ⟨289019719664834558149727813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192679813109889705433151875 289019719664834558149727813)
            ·
              refine ⟨54191197437156479653073965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 289019719664834558149727813 54191197437156479653073965)
              ·
                refine ⟨20321699038933679869902737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54191197437156479653073965 20321699038933679869902737)
                ·
                  refine ⟨15241274279200259902427053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20321699038933679869902737 15241274279200259902427053)
                  ·
                    refine ⟨5715477854700097463410145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15241274279200259902427053 5715477854700097463410145)
                    ·
                      refine ⟨4286608391025073097557609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5715477854700097463410145 4286608391025073097557609)
                      ·
                        rfl

theorem cell23_8348140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 3, 2].length) (baseStart_8348140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348140 prefixEnd_8348140 := by exact prefixLift 8348140
  have htrace : WordTrace (prefixWord ++ tailWord_8348140) baseStart_8348140 baseEnd_8348140 := by
    simpa [prefixWord, tailWord_8348140, baseEnd_8348140] using wordTrace_append hprefix tailTrace_8348140
  have hstable : (prefixWord ++ tailWord_8348140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348140).length < 2 ^ (prefixWord ++ tailWord_8348140).sum := by decide
  have hdescent : baseEnd_8348140 < baseStart_8348140 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348150 : List Nat := [5, 1, 1, 1, 2, 1, 1, 5, 1, 5]
def baseStart_8348150 : Nat := 118140960795 + 8348150 * 2 ^ 59
def prefixEnd_8348150 : Nat := 4983230072969 + 3 ^ 40 * 8348150 * 2
def baseEnd_8348150 : Nat := 1428871175277206019477521

theorem tailTrace_8348150 : CollatzResearch.WordTrace tailWord_8348150 prefixEnd_8348150 1428871175277206019477521 := by
  unfold tailWord_8348150
  simp only [CollatzResearch.WordTrace]
  refine ⟨19030127794130360959707119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202988029804057183570209269 19030127794130360959707119)
  ·
    refine ⟨28545191691195541439560679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19030127794130360959707119 28545191691195541439560679)
    ·
      refine ⟨42817787536793312159341019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28545191691195541439560679 42817787536793312159341019)
      ·
        refine ⟨64226681305189968239011529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42817787536793312159341019 64226681305189968239011529)
        ·
          refine ⟨48170010978892476179258647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64226681305189968239011529 48170010978892476179258647)
          ·
            refine ⟨72255016468338714268887971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48170010978892476179258647 72255016468338714268887971)
            ·
              refine ⟨108382524702508071403331957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72255016468338714268887971 108382524702508071403331957)
              ·
                refine ⟨10160861690860131694062371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108382524702508071403331957 10160861690860131694062371)
                ·
                  refine ⟨15241292536290197541093557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10160861690860131694062371 15241292536290197541093557)
                  ·
                    refine ⟨1428871175277206019477521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15241292536290197541093557 1428871175277206019477521)
                    ·
                      rfl

theorem cell23_8348150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_8348150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348150 prefixEnd_8348150 := by exact prefixLift 8348150
  have htrace : WordTrace (prefixWord ++ tailWord_8348150) baseStart_8348150 baseEnd_8348150 := by
    simpa [prefixWord, tailWord_8348150, baseEnd_8348150] using wordTrace_append hprefix tailTrace_8348150
  have hstable : (prefixWord ++ tailWord_8348150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348150).length < 2 ^ (prefixWord ++ tailWord_8348150).sum := by decide
  have hdescent : baseEnd_8348150 < baseStart_8348150 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348163 : List Nat := [1, 1, 1, 3, 2, 1, 3, 3, 4, 4]
def baseStart_8348163 : Nat := 118140960795 + 8348163 * 2 ^ 59
def prefixEnd_8348163 : Nat := 4983230072969 + 3 ^ 40 * 8348163 * 2
def baseEnd_8348163 : Nat := 1428873400360042169190001

theorem tailTrace_8348163 : CollatzResearch.WordTrace tailWord_8348163 prefixEnd_8348163 1428873400360042169190001 := by
  unfold tailWord_8348163
  simp only [CollatzResearch.WordTrace]
  refine ⟨304482518855038678575537143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202988345903359119050358095 304482518855038678575537143)
  ·
    refine ⟨456723778282558017863305715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304482518855038678575537143 456723778282558017863305715)
    ·
      refine ⟨685085667423837026794958573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456723778282558017863305715 685085667423837026794958573)
      ·
        refine ⟨256907125283938885048109465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 685085667423837026794958573 256907125283938885048109465)
        ·
          refine ⟨192680343962954163786082099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256907125283938885048109465 192680343962954163786082099)
          ·
            refine ⟨289020515944431245679123149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192680343962954163786082099 289020515944431245679123149)
            ·
              refine ⟨108382693479161717129671181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289020515944431245679123149 108382693479161717129671181)
              ·
                refine ⟨40643510054685643923626693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108382693479161717129671181 40643510054685643923626693)
                ·
                  refine ⟨7620658135253558235680005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40643510054685643923626693 7620658135253558235680005)
                  ·
                    refine ⟨1428873400360042169190001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7620658135253558235680005 1428873400360042169190001)
                    ·
                      rfl

theorem cell23_8348163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4, 4].length) (baseStart_8348163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348163 prefixEnd_8348163 := by exact prefixLift 8348163
  have htrace : WordTrace (prefixWord ++ tailWord_8348163) baseStart_8348163 baseEnd_8348163 := by
    simpa [prefixWord, tailWord_8348163, baseEnd_8348163] using wordTrace_append hprefix tailTrace_8348163
  have hstable : (prefixWord ++ tailWord_8348163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348163).length < 2 ^ (prefixWord ++ tailWord_8348163).sum := by decide
  have hdescent : baseEnd_8348163 < baseStart_8348163 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348164 : List Nat := [2, 3, 2, 3, 1, 3, 1, 1, 3, 1, 3]
def baseStart_8348164 : Nat := 118140960795 + 8348164 * 2 ^ 59
def prefixEnd_8348164 : Nat := 4983230072969 + 3 ^ 40 * 8348164 * 2
def baseEnd_8348164 : Nat := 4286620714560781003657499

theorem tailTrace_8348164 : CollatzResearch.WordTrace tailWord_8348164 prefixEnd_8348164 4286620714560781003657499 := by
  unfold tailWord_8348164
  simp only [CollatzResearch.WordTrace]
  refine ⟨152241277664017527873161773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202988370218690037164215697 152241277664017527873161773)
  ·
    refine ⟨57090479124006572952435665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152241277664017527873161773 57090479124006572952435665)
    ·
      refine ⟨42817859343004929714326749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57090479124006572952435665 42817859343004929714326749)
      ·
        refine ⟨16056697253626848642872531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42817859343004929714326749 16056697253626848642872531)
        ·
          refine ⟨24085045880440272964308797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16056697253626848642872531 24085045880440272964308797)
          ·
            refine ⟨9031892205165102361615799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24085045880440272964308797 9031892205165102361615799)
            ·
              refine ⟨13547838307747653542423699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9031892205165102361615799 13547838307747653542423699)
              ·
                refine ⟨20321757461621480313635549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13547838307747653542423699 20321757461621480313635549)
                ·
                  refine ⟨7620659048108055117613331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20321757461621480313635549 7620659048108055117613331)
                  ·
                    refine ⟨11430988572162082676419997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7620659048108055117613331 11430988572162082676419997)
                    ·
                      refine ⟨4286620714560781003657499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11430988572162082676419997 4286620714560781003657499)
                      ·
                        rfl

theorem cell23_8348164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_8348164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348164 prefixEnd_8348164 := by exact prefixLift 8348164
  have htrace : WordTrace (prefixWord ++ tailWord_8348164) baseStart_8348164 baseEnd_8348164 := by
    simpa [prefixWord, tailWord_8348164, baseEnd_8348164] using wordTrace_append hprefix tailTrace_8348164
  have hstable : (prefixWord ++ tailWord_8348164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348164).length < 2 ^ (prefixWord ++ tailWord_8348164).sum := by decide
  have hdescent : baseEnd_8348164 < baseStart_8348164 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348200 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_8348200 : Nat := 118140960795 + 8348200 * 2 ^ 59
def prefixEnd_8348200 : Nat := 4983230072969 + 3 ^ 40 * 8348200 * 2
def baseEnd_8348200 : Nat := 4286639199864342862807333

theorem tailTrace_8348200 : CollatzResearch.WordTrace tailWord_8348200 prefixEnd_8348200 4286639199864342862807333 := by
  unfold tailWord_8348200
  simp only [CollatzResearch.WordTrace]
  refine ⟨152241934177952316947317027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202989245570603089263089369 152241934177952316947317027)
  ·
    refine ⟨228362901266928475420975541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152241934177952316947317027 228362901266928475420975541)
    ·
      refine ⟨21409021993774544570716457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228362901266928475420975541 21409021993774544570716457)
      ·
        refine ⟨16056766495330908428037343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21409021993774544570716457 16056766495330908428037343)
        ·
          refine ⟨24085149742996362642056015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16056766495330908428037343 24085149742996362642056015)
          ·
            refine ⟨36127724614494543963084023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24085149742996362642056015 36127724614494543963084023)
            ·
              refine ⟨54191586921741815944626035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36127724614494543963084023 54191586921741815944626035)
              ·
                refine ⟨81287380382612723916939053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54191586921741815944626035 81287380382612723916939053)
                ·
                  refine ⟨30482767643479771468852145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81287380382612723916939053 30482767643479771468852145)
                  ·
                    refine ⟨22862075732609828601639109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30482767643479771468852145 22862075732609828601639109)
                    ·
                      refine ⟨4286639199864342862807333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22862075732609828601639109 4286639199864342862807333)
                      ·
                        rfl

theorem cell23_8348200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_8348200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348200 prefixEnd_8348200 := by exact prefixLift 8348200
  have htrace : WordTrace (prefixWord ++ tailWord_8348200) baseStart_8348200 baseEnd_8348200 := by
    simpa [prefixWord, tailWord_8348200, baseEnd_8348200] using wordTrace_append hprefix tailTrace_8348200
  have hstable : (prefixWord ++ tailWord_8348200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348200).length < 2 ^ (prefixWord ++ tailWord_8348200).sum := by decide
  have hdescent : baseEnd_8348200 < baseStart_8348200 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348214 : List Nat := [5, 1, 2, 1, 2, 2, 2, 2, 2, 4]
def baseStart_8348214 : Nat := 118140960795 + 8348214 * 2 ^ 59
def prefixEnd_8348214 : Nat := 4983230072969 + 3 ^ 40 * 8348214 * 2
def baseEnd_8348214 : Nat := 1428882129531168602677423

theorem tailTrace_8348214 : CollatzResearch.WordTrace tailWord_8348214 prefixEnd_8348214 1428882129531168602677423 := by
  unfold tailWord_8348214
  simp only [CollatzResearch.WordTrace]
  refine ⟨19030273686115869642852731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202989585985235942857095797 19030273686115869642852731)
  ·
    refine ⟨28545410529173804464279097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19030273686115869642852731 28545410529173804464279097)
    ·
      refine ⟨21409057896880353348209323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28545410529173804464279097 21409057896880353348209323)
      ·
        refine ⟨32113586845320530022313985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21409057896880353348209323 32113586845320530022313985)
        ·
          refine ⟨24085190133990397516735489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32113586845320530022313985 24085190133990397516735489)
          ·
            refine ⟨18063892600492798137551617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24085190133990397516735489 18063892600492798137551617)
            ·
              refine ⟨13547919450369598603163713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18063892600492798137551617 13547919450369598603163713)
              ·
                refine ⟨10160939587777198952372785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13547919450369598603163713 10160939587777198952372785)
                ·
                  refine ⟨7620704690832899214279589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10160939587777198952372785 7620704690832899214279589)
                  ·
                    refine ⟨1428882129531168602677423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7620704690832899214279589 1428882129531168602677423)
                    ·
                      rfl

theorem cell23_8348214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_8348214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348214 prefixEnd_8348214 := by exact prefixLift 8348214
  have htrace : WordTrace (prefixWord ++ tailWord_8348214) baseStart_8348214 baseEnd_8348214 := by
    simpa [prefixWord, tailWord_8348214, baseEnd_8348214] using wordTrace_append hprefix tailTrace_8348214
  have hstable : (prefixWord ++ tailWord_8348214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348214).length < 2 ^ (prefixWord ++ tailWord_8348214).sum := by decide
  have hdescent : baseEnd_8348214 < baseStart_8348214 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348221 : List Nat := [1, 4, 1, 3, 2, 2, 1, 4, 1, 2, 2]
def baseStart_8348221 : Nat := 118140960795 + 8348221 * 2 ^ 59
def prefixEnd_8348221 : Nat := 4983230072969 + 3 ^ 40 * 8348221 * 2
def baseEnd_8348221 : Nat := 4286649982958087280644737

theorem tailTrace_8348221 : CollatzResearch.WordTrace tailWord_8348221 prefixEnd_8348221 4286649982958087280644737 := by
  unfold tailWord_8348221
  simp only [CollatzResearch.WordTrace]
  refine ⟨304484634288828554481148517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202989756192552369654099011 304484634288828554481148517)
  ·
    refine ⟨57090868929155353965215347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304484634288828554481148517 57090868929155353965215347)
    ·
      refine ⟨85636303393733030947823021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57090868929155353965215347 85636303393733030947823021)
      ·
        refine ⟨32113613772649886605433633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85636303393733030947823021 32113613772649886605433633)
        ·
          refine ⟨24085210329487414954075225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32113613772649886605433633 24085210329487414954075225)
          ·
            refine ⟨18063907747115561215556419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24085210329487414954075225 18063907747115561215556419)
            ·
              refine ⟨27095861620673341823334629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18063907747115561215556419 27095861620673341823334629)
              ·
                refine ⟨5080474053876251591875243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27095861620673341823334629 5080474053876251591875243)
                ·
                  refine ⟨7620711080814377387812865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5080474053876251591875243 7620711080814377387812865)
                  ·
                    refine ⟨5715533310610783040859649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7620711080814377387812865 5715533310610783040859649)
                    ·
                      refine ⟨4286649982958087280644737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5715533310610783040859649 4286649982958087280644737)
                      ·
                        rfl

theorem cell23_8348221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_8348221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348221 prefixEnd_8348221 := by exact prefixLift 8348221
  have htrace : WordTrace (prefixWord ++ tailWord_8348221) baseStart_8348221 baseEnd_8348221 := by
    simpa [prefixWord, tailWord_8348221, baseEnd_8348221] using wordTrace_append hprefix tailTrace_8348221
  have hstable : (prefixWord ++ tailWord_8348221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348221).length < 2 ^ (prefixWord ++ tailWord_8348221).sum := by decide
  have hdescent : baseEnd_8348221 < baseStart_8348221 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348237 : List Nat := [1, 6, 1, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_8348237 : Nat := 118140960795 + 8348237 * 2 ^ 59
def prefixEnd_8348237 : Nat := 4983230072969 + 3 ^ 40 * 8348237 * 2
def baseEnd_8348237 : Nat := 4286658198648559218044663

theorem tailTrace_8348237 : CollatzResearch.WordTrace tailWord_8348237 prefixEnd_8348237 4286658198648559218044663 := by
  unfold tailWord_8348237
  simp only [CollatzResearch.WordTrace]
  refine ⟨304485217856770589213730965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202990145237847059475820643 304485217856770589213730965)
  ·
    refine ⟨14272744587036121369393639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 304485217856770589213730965 14272744587036121369393639)
    ·
      refine ⟨21409116880554182054090459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14272744587036121369393639 21409116880554182054090459)
      ·
        refine ⟨32113675320831273081135689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21409116880554182054090459 32113675320831273081135689)
        ·
          refine ⟨24085256490623454810851767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32113675320831273081135689 24085256490623454810851767)
          ·
            refine ⟨36127884735935182216277651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24085256490623454810851767 36127884735935182216277651)
            ·
              refine ⟨54191827103902773324416477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36127884735935182216277651 54191827103902773324416477)
              ·
                refine ⟨20321935163963539996656179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54191827103902773324416477 20321935163963539996656179)
                ·
                  refine ⟨30482902745945309994984269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20321935163963539996656179 30482902745945309994984269)
                  ·
                    refine ⟨11431088529729491248119101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30482902745945309994984269 11431088529729491248119101)
                    ·
                      refine ⟨4286658198648559218044663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11431088529729491248119101 4286658198648559218044663)
                      ·
                        rfl

theorem cell23_8348237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_8348237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348237 prefixEnd_8348237 := by exact prefixLift 8348237
  have htrace : WordTrace (prefixWord ++ tailWord_8348237) baseStart_8348237 baseEnd_8348237 := by
    simpa [prefixWord, tailWord_8348237, baseEnd_8348237] using wordTrace_append hprefix tailTrace_8348237
  have hstable : (prefixWord ++ tailWord_8348237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348237).length < 2 ^ (prefixWord ++ tailWord_8348237).sum := by decide
  have hdescent : baseEnd_8348237 < baseStart_8348237 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348247 : List Nat := [1, 1, 3, 2, 2, 2, 2, 4, 1, 3, 2]
def baseStart_8348247 : Nat := 118140960795 + 8348247 * 2 ^ 59
def prefixEnd_8348247 : Nat := 4983230072969 + 3 ^ 40 * 8348247 * 2
def baseEnd_8348247 : Nat := 4286663333455104178919617

theorem tailTrace_8348247 : CollatzResearch.WordTrace tailWord_8348247 prefixEnd_8348247 4286663333455104178919617 := by
  unfold tailWord_8348247
  simp only [CollatzResearch.WordTrace]
  refine ⟨304485582586734360921594995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202990388391156240614396663 304485582586734360921594995)
  ·
    refine ⟨456728373880101541382392493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304485582586734360921594995 456728373880101541382392493)
    ·
      refine ⟨171273140205038078018397185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456728373880101541382392493 171273140205038078018397185)
      ·
        refine ⟨128454855153778558513797889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171273140205038078018397185 128454855153778558513797889)
        ·
          refine ⟨96341141365333918885348417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128454855153778558513797889 96341141365333918885348417)
          ·
            refine ⟨72255856024000439164011313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96341141365333918885348417 72255856024000439164011313)
            ·
              refine ⟨54191892018000329373008485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72255856024000439164011313 54191892018000329373008485)
              ·
                refine ⟨10160979753375061757439091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54191892018000329373008485 10160979753375061757439091)
                ·
                  refine ⟨15241469630062592636158637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10160979753375061757439091 15241469630062592636158637)
                  ·
                    refine ⟨5715551111273472238559489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15241469630062592636158637 5715551111273472238559489)
                    ·
                      refine ⟨4286663333455104178919617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5715551111273472238559489 4286663333455104178919617)
                      ·
                        rfl

theorem cell23_8348247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 3, 2].length) (baseStart_8348247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348247 prefixEnd_8348247 := by exact prefixLift 8348247
  have htrace : WordTrace (prefixWord ++ tailWord_8348247) baseStart_8348247 baseEnd_8348247 := by
    simpa [prefixWord, tailWord_8348247, baseEnd_8348247] using wordTrace_append hprefix tailTrace_8348247
  have hstable : (prefixWord ++ tailWord_8348247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348247).length < 2 ^ (prefixWord ++ tailWord_8348247).sum := by decide
  have hdescent : baseEnd_8348247 < baseStart_8348247 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348258 : List Nat := [3, 3, 2, 3, 1, 2, 2, 1, 1, 2, 3]
def baseStart_8348258 : Nat := 118140960795 + 8348258 * 2 ^ 59
def prefixEnd_8348258 : Nat := 4983230072969 + 3 ^ 40 * 8348258 * 2
def baseEnd_8348258 : Nat := 4286668981742303635882067

theorem tailTrace_8348258 : CollatzResearch.WordTrace tailWord_8348258 prefixEnd_8348258 4286668981742303635882067 := by
  unfold tailWord_8348258
  simp only [CollatzResearch.WordTrace]
  refine ⟨76121495947423627450061357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202990655859796339866830285 76121495947423627450061357)
  ·
    refine ⟨28545560980283860293773009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76121495947423627450061357 28545560980283860293773009)
    ·
      refine ⟨21409170735212895220329757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28545560980283860293773009 21409170735212895220329757)
      ·
        refine ⟨8028439025704835707623659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21409170735212895220329757 8028439025704835707623659)
        ·
          refine ⟨12042658538557253561435489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8028439025704835707623659 12042658538557253561435489)
          ·
            refine ⟨9031993903917940171076617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12042658538557253561435489 9031993903917940171076617)
            ·
              refine ⟨6773995427938455128307463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9031993903917940171076617 6773995427938455128307463)
              ·
                refine ⟨10160993141907682692461195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6773995427938455128307463 10160993141907682692461195)
                ·
                  refine ⟨15241489712861524038691793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10160993141907682692461195 15241489712861524038691793)
                  ·
                    refine ⟨11431117284646143029018845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15241489712861524038691793 11431117284646143029018845)
                    ·
                      refine ⟨4286668981742303635882067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11431117284646143029018845 4286668981742303635882067)
                      ·
                        rfl

theorem cell23_8348258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_8348258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348258 prefixEnd_8348258 := by exact prefixLift 8348258
  have htrace : WordTrace (prefixWord ++ tailWord_8348258) baseStart_8348258 baseEnd_8348258 := by
    simpa [prefixWord, tailWord_8348258, baseEnd_8348258] using wordTrace_append hprefix tailTrace_8348258
  have hstable : (prefixWord ++ tailWord_8348258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348258).length < 2 ^ (prefixWord ++ tailWord_8348258).sum := by decide
  have hdescent : baseEnd_8348258 < baseStart_8348258 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348263 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_8348263 : Nat := 118140960795 + 8348263 * 2 ^ 59
def prefixEnd_8348263 : Nat := 4983230072969 + 3 ^ 40 * 8348263 * 2
def baseEnd_8348263 : Nat := 4286671549145576116319543

theorem tailTrace_8348263 : CollatzResearch.WordTrace tailWord_8348263 prefixEnd_8348263 4286671549145576116319543 := by
  unfold tailWord_8348263
  simp only [CollatzResearch.WordTrace]
  refine ⟨304486166154676395654177443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202990777436450930436118295 304486166154676395654177443)
  ·
    refine ⟨456729249232014593481266165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304486166154676395654177443 456729249232014593481266165)
    ·
      refine ⟨42818367115501368138868703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 456729249232014593481266165 42818367115501368138868703)
      ·
        refine ⟨64227550673252052208303055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42818367115501368138868703 64227550673252052208303055)
        ·
          refine ⟨96341326009878078312454583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64227550673252052208303055 96341326009878078312454583)
          ·
            refine ⟨144511989014817117468681875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96341326009878078312454583 144511989014817117468681875)
            ·
              refine ⟨216767983522225676203022813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144511989014817117468681875 216767983522225676203022813)
              ·
                refine ⟨81287993820834628576133555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216767983522225676203022813 81287993820834628576133555)
                ·
                  refine ⟨121931990731251942864200333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81287993820834628576133555 121931990731251942864200333)
                  ·
                    refine ⟨45724496524219478574075125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121931990731251942864200333 45724496524219478574075125)
                    ·
                      refine ⟨4286671549145576116319543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45724496524219478574075125 4286671549145576116319543)
                      ·
                        rfl

theorem cell23_8348263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_8348263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348263 prefixEnd_8348263 := by exact prefixLift 8348263
  have htrace : WordTrace (prefixWord ++ tailWord_8348263) baseStart_8348263 baseEnd_8348263 := by
    simpa [prefixWord, tailWord_8348263, baseEnd_8348263] using wordTrace_append hprefix tailTrace_8348263
  have hstable : (prefixWord ++ tailWord_8348263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348263).length < 2 ^ (prefixWord ++ tailWord_8348263).sum := by decide
  have hdescent : baseEnd_8348263 < baseStart_8348263 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348270 : List Nat := [4, 1, 2, 2, 2, 1, 1, 2, 2, 6]
def baseStart_8348270 : Nat := 118140960795 + 8348270 * 2 ^ 59
def prefixEnd_8348270 : Nat := 4983230072969 + 3 ^ 40 * 8348270 * 2
def baseEnd_8348270 : Nat := 1428891714503385862977337

theorem tailTrace_8348270 : CollatzResearch.WordTrace tailWord_8348270 prefixEnd_8348270 1428891714503385862977337 := by
  unfold tailWord_8348270
  simp only [CollatzResearch.WordTrace]
  refine ⟨38060802683206379481210283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202990947643767357233121509 38060802683206379481210283)
  ·
    refine ⟨57091204024809569221815425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38060802683206379481210283 57091204024809569221815425)
    ·
      refine ⟨42818403018607176916361569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57091204024809569221815425 42818403018607176916361569)
      ·
        refine ⟨32113802263955382687271177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42818403018607176916361569 32113802263955382687271177)
        ·
          refine ⟨24085351697966537015453383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32113802263955382687271177 24085351697966537015453383)
          ·
            refine ⟨36128027546949805523180075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24085351697966537015453383 36128027546949805523180075)
            ·
              refine ⟨54192041320424708284770113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36128027546949805523180075 54192041320424708284770113)
              ·
                refine ⟨40644030990318531213577585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54192041320424708284770113 40644030990318531213577585)
                ·
                  refine ⟨30483023242738898410183189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40644030990318531213577585 30483023242738898410183189)
                  ·
                    refine ⟨1428891714503385862977337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30483023242738898410183189 1428891714503385862977337)
                    ·
                      rfl

theorem cell23_8348270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_8348270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348270 prefixEnd_8348270 := by exact prefixLift 8348270
  have htrace : WordTrace (prefixWord ++ tailWord_8348270) baseStart_8348270 baseEnd_8348270 := by
    simpa [prefixWord, tailWord_8348270, baseEnd_8348270] using wordTrace_append hprefix tailTrace_8348270
  have hstable : (prefixWord ++ tailWord_8348270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348270).length < 2 ^ (prefixWord ++ tailWord_8348270).sum := by decide
  have hdescent : baseEnd_8348270 < baseStart_8348270 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348313 : List Nat := [1, 2, 1, 2, 1, 2, 3, 3, 1, 7]
def baseStart_8348313 : Nat := 118140960795 + 8348313 * 2 ^ 59
def prefixEnd_8348313 : Nat := 4983230072969 + 3 ^ 40 * 8348313 * 2
def baseEnd_8348313 : Nat := 1428899074392766973564771

theorem tailTrace_8348313 : CollatzResearch.WordTrace tailWord_8348313 prefixEnd_8348313 1428899074392766973564771 := by
  unfold tailWord_8348313
  simp only [CollatzResearch.WordTrace]
  refine ⟨304487989804495254193497593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202991993202996836128998395 304487989804495254193497593)
  ·
    refine ⟨228365992353371440645123195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304487989804495254193497593 228365992353371440645123195)
    ·
      refine ⟨342548988530057160967684793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228365992353371440645123195 342548988530057160967684793)
      ·
        refine ⟨256911741397542870725763595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342548988530057160967684793 256911741397542870725763595)
        ·
          refine ⟨385367612096314306088645393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256911741397542870725763595 385367612096314306088645393)
          ·
            refine ⟨289025709072235729566484045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385367612096314306088645393 289025709072235729566484045)
            ·
              refine ⟨108384640902088398587431517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289025709072235729566484045 108384640902088398587431517)
              ·
                refine ⟨40644240338283149470286819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108384640902088398587431517 40644240338283149470286819)
                ·
                  refine ⟨60966360507424724205430229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40644240338283149470286819 60966360507424724205430229)
                  ·
                    refine ⟨1428899074392766973564771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60966360507424724205430229 1428899074392766973564771)
                    ·
                      rfl

theorem cell23_8348313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 7].length) (baseStart_8348313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348313 prefixEnd_8348313 := by exact prefixLift 8348313
  have htrace : WordTrace (prefixWord ++ tailWord_8348313) baseStart_8348313 baseEnd_8348313 := by
    simpa [prefixWord, tailWord_8348313, baseEnd_8348313] using wordTrace_append hprefix tailTrace_8348313
  have hstable : (prefixWord ++ tailWord_8348313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348313).length < 2 ^ (prefixWord ++ tailWord_8348313).sum := by decide
  have hdescent : baseEnd_8348313 < baseStart_8348313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348317 : List Nat := [1, 4, 2, 1, 1, 1, 5, 3, 5]
def baseStart_8348317 : Nat := 118140960795 + 8348317 * 2 ^ 59
def prefixEnd_8348317 : Nat := 4983230072969 + 3 ^ 40 * 8348317 * 2
def baseEnd_8348317 : Nat := 476299919677879878338255

theorem tailTrace_8348317 : CollatzResearch.WordTrace tailWord_8348317 prefixEnd_8348317 476299919677879878338255 := by
  unfold tailWord_8348317
  simp only [CollatzResearch.WordTrace]
  refine ⟨304488135696480762876643205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202992090464320508584428803 304488135696480762876643205)
  ·
    refine ⟨57091525443090143039370601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304488135696480762876643205 57091525443090143039370601)
    ·
      refine ⟨42818644082317607279527951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57091525443090143039370601 42818644082317607279527951)
      ·
        refine ⟨64227966123476410919291927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42818644082317607279527951 64227966123476410919291927)
        ·
          refine ⟨96341949185214616378937891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64227966123476410919291927 96341949185214616378937891)
          ·
            refine ⟨144512923777821924568406837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96341949185214616378937891 144512923777821924568406837)
            ·
              refine ⟨13548086604170805428288141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144512923777821924568406837 13548086604170805428288141)
              ·
                refine ⟨5080532476564052035608053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13548086604170805428288141 5080532476564052035608053)
                ·
                  refine ⟨476299919677879878338255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5080532476564052035608053 476299919677879878338255)
                  ·
                    rfl

theorem cell23_8348317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3, 5].length) (baseStart_8348317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348317 prefixEnd_8348317 := by exact prefixLift 8348317
  have htrace : WordTrace (prefixWord ++ tailWord_8348317) baseStart_8348317 baseEnd_8348317 := by
    simpa [prefixWord, tailWord_8348317, baseEnd_8348317] using wordTrace_append hprefix tailTrace_8348317
  have hstable : (prefixWord ++ tailWord_8348317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348317).length < 2 ^ (prefixWord ++ tailWord_8348317).sum := by decide
  have hdescent : baseEnd_8348317 < baseStart_8348317 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348334 : List Nat := [4, 1, 4, 1, 1, 3, 1, 1, 7]
def baseStart_8348334 : Nat := 118140960795 + 8348334 * 2 ^ 59
def prefixEnd_8348334 : Nat := 4983230072969 + 3 ^ 40 * 8348334 * 2
def baseEnd_8348334 : Nat := 476300889585782815392413

theorem tailTrace_8348334 : CollatzResearch.WordTrace tailWord_8348334 prefixEnd_8348334 476300889585782815392413 := by
  unfold tailWord_8348334
  simp only [CollatzResearch.WordTrace]
  refine ⟨38061094467177396847501507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202992503824946116520008037 38061094467177396847501507)
  ·
    refine ⟨57091641700766095271252261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38061094467177396847501507 57091641700766095271252261)
    ·
      refine ⟨10704682818893642863359799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57091641700766095271252261 10704682818893642863359799)
      ·
        refine ⟨16057024228340464295039699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10704682818893642863359799 16057024228340464295039699)
        ·
          refine ⟨24085536342510696442559549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16057024228340464295039699 24085536342510696442559549)
          ·
            refine ⟨9032076128441511165959831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24085536342510696442559549 9032076128441511165959831)
            ·
              refine ⟨13548114192662266748939747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9032076128441511165959831 13548114192662266748939747)
              ·
                refine ⟨20322171288993400123409621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13548114192662266748939747 20322171288993400123409621)
                ·
                  refine ⟨476300889585782815392413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20322171288993400123409621 476300889585782815392413)
                  ·
                    rfl

theorem cell23_8348334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 7].length) (baseStart_8348334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348334 prefixEnd_8348334 := by exact prefixLift 8348334
  have htrace : WordTrace (prefixWord ++ tailWord_8348334) baseStart_8348334 baseEnd_8348334 := by
    simpa [prefixWord, tailWord_8348334, baseEnd_8348334] using wordTrace_append hprefix tailTrace_8348334
  have hstable : (prefixWord ++ tailWord_8348334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348334).length < 2 ^ (prefixWord ++ tailWord_8348334).sum := by decide
  have hdescent : baseEnd_8348334 < baseStart_8348334 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348363 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 6]
def baseStart_8348363 : Nat := 118140960795 + 8348363 * 2 ^ 59
def prefixEnd_8348363 : Nat := 4983230072969 + 3 ^ 40 * 8348363 * 2
def baseEnd_8348363 : Nat := 4286722897211025725069083

theorem tailTrace_8348363 : CollatzResearch.WordTrace tailWord_8348363 prefixEnd_8348363 4286722897211025725069083 := by
  unfold tailWord_8348363
  simp only [CollatzResearch.WordTrace]
  refine ⟨304489813454314112732817743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202993208969542741821878495 304489813454314112732817743)
  ·
    refine ⟨456734720181471169099226615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304489813454314112732817743 456734720181471169099226615)
    ·
      refine ⟨685102080272206753648839923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456734720181471169099226615 685102080272206753648839923)
      ·
        refine ⟨1027653120408310130473259885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685102080272206753648839923 1027653120408310130473259885)
        ·
          refine ⟨385369920153116298927472457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1027653120408310130473259885 385369920153116298927472457)
          ·
            refine ⟨289027440114837224195604343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385369920153116298927472457 289027440114837224195604343)
            ·
              refine ⟨433541160172255836293406515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289027440114837224195604343 433541160172255836293406515)
              ·
                refine ⟨650311740258383754440109773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433541160172255836293406515 650311740258383754440109773)
                ·
                  refine ⟨243866902596893907915041165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 650311740258383754440109773 243866902596893907915041165)
                  ·
                    refine ⟨91450088473835215468140437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 243866902596893907915041165 91450088473835215468140437)
                    ·
                      refine ⟨4286722897211025725069083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91450088473835215468140437 4286722897211025725069083)
                      ·
                        rfl

theorem cell23_8348363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 6].length) (baseStart_8348363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348363 prefixEnd_8348363 := by exact prefixLift 8348363
  have htrace : WordTrace (prefixWord ++ tailWord_8348363) baseStart_8348363 baseEnd_8348363 := by
    simpa [prefixWord, tailWord_8348363, baseEnd_8348363] using wordTrace_append hprefix tailTrace_8348363
  have hstable : (prefixWord ++ tailWord_8348363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348363).length < 2 ^ (prefixWord ++ tailWord_8348363).sum := by decide
  have hdescent : baseEnd_8348363 < baseStart_8348363 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348430 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5]
def baseStart_8348430 : Nat := 118140960795 + 8348430 * 2 ^ 59
def prefixEnd_8348430 : Nat := 4983230072969 + 3 ^ 40 * 8348430 * 2
def baseEnd_8348430 : Nat := 4286757300414876962931275

theorem tailTrace_8348430 : CollatzResearch.WordTrace tailWord_8348430 prefixEnd_8348430 4286757300414876962931275 := by
  unfold tailWord_8348430
  simp only [CollatzResearch.WordTrace]
  refine ⟨38061532143133922896938343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202994838096714255450337829 38061532143133922896938343)
  ·
    refine ⟨57092298214700884345407515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38061532143133922896938343 57092298214700884345407515)
    ·
      refine ⟨85638447322051326518111273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57092298214700884345407515 85638447322051326518111273)
      ·
        refine ⟨64228835491538494888583455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85638447322051326518111273 64228835491538494888583455)
        ·
          refine ⟨96343253237307742332875183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64228835491538494888583455 96343253237307742332875183)
          ·
            refine ⟨144514879855961613499312775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96343253237307742332875183 144514879855961613499312775)
            ·
              refine ⟨216772319783942420248969163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144514879855961613499312775 216772319783942420248969163)
              ·
                refine ⟨325158479675913630373453745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216772319783942420248969163 325158479675913630373453745)
                ·
                  refine ⟨243868859756935222780090309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 325158479675913630373453745 243868859756935222780090309)
                  ·
                    refine ⟨45725411204425354271266933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 243868859756935222780090309 45725411204425354271266933)
                    ·
                      refine ⟨4286757300414876962931275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45725411204425354271266933 4286757300414876962931275)
                      ·
                        rfl

theorem cell23_8348430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_8348430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348430 prefixEnd_8348430 := by exact prefixLift 8348430
  have htrace : WordTrace (prefixWord ++ tailWord_8348430) baseStart_8348430 baseEnd_8348430 := by
    simpa [prefixWord, tailWord_8348430, baseEnd_8348430] using wordTrace_append hprefix tailTrace_8348430
  have hstable : (prefixWord ++ tailWord_8348430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348430).length < 2 ^ (prefixWord ++ tailWord_8348430).sum := by decide
  have hdescent : baseEnd_8348430 < baseStart_8348430 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348437 : List Nat := [1, 3, 2, 1, 2, 2, 3, 3, 1, 5]
def baseStart_8348437 : Nat := 118140960795 + 8348437 * 2 ^ 59
def prefixEnd_8348437 : Nat := 4983230072969 + 3 ^ 40 * 8348437 * 2
def baseEnd_8348437 : Nat := 1428920298259819478514581

theorem tailTrace_8348437 : CollatzResearch.WordTrace tailWord_8348437 prefixEnd_8348437 1428920298259819478514581 := by
  unfold tailWord_8348437
  simp only [CollatzResearch.WordTrace]
  refine ⟨304492512456046023371011565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202995008304030682247341043 304492512456046023371011565)
  ·
    refine ⟨114184692171017258764129337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304492512456046023371011565 114184692171017258764129337)
    ·
      refine ⟨85638519128262944073097003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114184692171017258764129337 85638519128262944073097003)
      ·
        refine ⟨128457778692394416109645505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85638519128262944073097003 128457778692394416109645505)
        ·
          refine ⟨96343334019295812082234129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128457778692394416109645505 96343334019295812082234129)
          ·
            refine ⟨72257500514471859061675597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96343334019295812082234129 72257500514471859061675597)
            ·
              refine ⟨27096562692926947148128349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72257500514471859061675597 27096562692926947148128349)
              ·
                refine ⟨10161211009847605180548131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27096562692926947148128349 10161211009847605180548131)
                ·
                  refine ⟨15241816514771407770822197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10161211009847605180548131 15241816514771407770822197)
                  ·
                    refine ⟨1428920298259819478514581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15241816514771407770822197 1428920298259819478514581)
                    ·
                      rfl

theorem cell23_8348437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_8348437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348437 prefixEnd_8348437 := by exact prefixLift 8348437
  have htrace : WordTrace (prefixWord ++ tailWord_8348437) baseStart_8348437 baseEnd_8348437 := by
    simpa [prefixWord, tailWord_8348437, baseEnd_8348437] using wordTrace_append hprefix tailTrace_8348437
  have hstable : (prefixWord ++ tailWord_8348437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348437).length < 2 ^ (prefixWord ++ tailWord_8348437).sum := by decide
  have hdescent : baseEnd_8348437 < baseStart_8348437 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348467 : List Nat := [1, 1, 1, 2, 6, 1, 3, 1, 1, 6]
def baseStart_8348467 : Nat := 118140960795 + 8348467 * 2 ^ 59
def prefixEnd_8348467 : Nat := 4983230072969 + 3 ^ 40 * 8348467 * 2
def baseEnd_8348467 : Nat := 1428925433066364439389535

theorem tailTrace_8348467 : CollatzResearch.WordTrace tailWord_8348467 prefixEnd_8348467 1428925433066364439389535 := by
  unfold tailWord_8348467
  simp only [CollatzResearch.WordTrace]
  refine ⟨304493606645937338494603655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202995737763958225663069103 304493606645937338494603655)
  ·
    refine ⟨456740409968906007741905483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304493606645937338494603655 456740409968906007741905483)
    ·
      refine ⟨685110614953359011612858225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456740409968906007741905483 685110614953359011612858225)
      ·
        refine ⟨513832961215019258709643669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 685110614953359011612858225 513832961215019258709643669)
        ·
          refine ⟨24085920056954027752014547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 513832961215019258709643669 24085920056954027752014547)
          ·
            refine ⟨36128880085431041628021821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24085920056954027752014547 36128880085431041628021821)
            ·
              refine ⟨13548330032036640610508183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36128880085431041628021821 13548330032036640610508183)
              ·
                refine ⟨20322495048054960915762275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13548330032036640610508183 20322495048054960915762275)
                ·
                  refine ⟨30483742572082441373643413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20322495048054960915762275 30483742572082441373643413)
                  ·
                    refine ⟨1428925433066364439389535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30483742572082441373643413 1428925433066364439389535)
                    ·
                      rfl

theorem cell23_8348467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 6].length) (baseStart_8348467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348467 prefixEnd_8348467 := by exact prefixLift 8348467
  have htrace : WordTrace (prefixWord ++ tailWord_8348467) baseStart_8348467 baseEnd_8348467 := by
    simpa [prefixWord, tailWord_8348467, baseEnd_8348467] using wordTrace_append hprefix tailTrace_8348467
  have hstable : (prefixWord ++ tailWord_8348467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348467).length < 2 ^ (prefixWord ++ tailWord_8348467).sum := by decide
  have hdescent : baseEnd_8348467 < baseStart_8348467 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348497 : List Nat := [1, 2, 2, 1, 6, 2, 9]
def baseStart_8348497 : Nat := 118140960795 + 8348497 * 2 ^ 59
def prefixEnd_8348497 : Nat := 4983230072969 + 3 ^ 40 * 8348497 * 2
def baseEnd_8348497 : Nat := 52923354365663311120907

theorem tailTrace_8348497 : CollatzResearch.WordTrace tailWord_8348497 prefixEnd_8348497 52923354365663311120907 := by
  unfold tailWord_8348497
  simp only [CollatzResearch.WordTrace]
  refine ⟨304494700835828653618195745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202996467223885769078797163 304494700835828653618195745)
  ·
    refine ⟨228371025626871490213646809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304494700835828653618195745 228371025626871490213646809)
    ·
      refine ⟨171278269220153617660235107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228371025626871490213646809 171278269220153617660235107)
      ·
        refine ⟨256917403830230426490352661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171278269220153617660235107 256917403830230426490352661)
        ·
          refine ⟨12043003304542051241735281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 256917403830230426490352661 12043003304542051241735281)
          ·
            refine ⟨9032252478406538431301461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12043003304542051241735281 9032252478406538431301461)
            ·
              refine ⟨52923354365663311120907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 9032252478406538431301461 52923354365663311120907)
              ·
                rfl

theorem cell23_8348497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 9].length) (baseStart_8348497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348497 prefixEnd_8348497 := by exact prefixLift 8348497
  have htrace : WordTrace (prefixWord ++ tailWord_8348497) baseStart_8348497 baseEnd_8348497 := by
    simpa [prefixWord, tailWord_8348497, baseEnd_8348497] using wordTrace_append hprefix tailTrace_8348497
  have hstable : (prefixWord ++ tailWord_8348497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348497).length < 2 ^ (prefixWord ++ tailWord_8348497).sum := by decide
  have hdescent : baseEnd_8348497 < baseStart_8348497 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348508 : List Nat := [2, 2, 4, 2, 1, 1, 3, 1, 3, 2, 2]
def baseStart_8348508 : Nat := 118140960795 + 8348508 * 2 ^ 59
def prefixEnd_8348508 : Nat := 4983230072969 + 3 ^ 40 * 8348508 * 2
def baseEnd_8348508 : Nat := 4286797351905927657755917

theorem tailTrace_8348508 : CollatzResearch.WordTrace tailWord_8348508 prefixEnd_8348508 4286797351905927657755917 := by
  unfold tailWord_8348508
  simp only [CollatzResearch.WordTrace]
  refine ⟨152247551019394401248423089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202996734692525868331230785 152247551019394401248423089)
  ·
    refine ⟨114185663264545800936317317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152247551019394401248423089 114185663264545800936317317)
    ·
      refine ⟨21409811862102337675559497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114185663264545800936317317 21409811862102337675559497)
      ·
        refine ⟨16057358896576753256669623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21409811862102337675559497 16057358896576753256669623)
        ·
          refine ⟨24086038344865129885004435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16057358896576753256669623 24086038344865129885004435)
          ·
            refine ⟨36129057517297694827506653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24086038344865129885004435 36129057517297694827506653)
            ·
              refine ⟨13548396568986635560314995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36129057517297694827506653 13548396568986635560314995)
              ·
                refine ⟨20322594853479953340472493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13548396568986635560314995 20322594853479953340472493)
                ·
                  refine ⟨7620973070054982502677185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20322594853479953340472493 7620973070054982502677185)
                  ·
                    refine ⟨5715729802541236877007889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7620973070054982502677185 5715729802541236877007889)
                    ·
                      refine ⟨4286797351905927657755917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5715729802541236877007889 4286797351905927657755917)
                      ·
                        rfl

theorem cell23_8348508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_8348508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348508 prefixEnd_8348508 := by exact prefixLift 8348508
  have htrace : WordTrace (prefixWord ++ tailWord_8348508) baseStart_8348508 baseEnd_8348508 := by
    simpa [prefixWord, tailWord_8348508, baseEnd_8348508] using wordTrace_append hprefix tailTrace_8348508
  have hstable : (prefixWord ++ tailWord_8348508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348508).length < 2 ^ (prefixWord ++ tailWord_8348508).sum := by decide
  have hdescent : baseEnd_8348508 < baseStart_8348508 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348514 : List Nat := [3, 3, 2, 1, 3, 1, 2, 8]
def baseStart_8348514 : Nat := 118140960795 + 8348514 * 2 ^ 59
def prefixEnd_8348514 : Nat := 4983230072969 + 3 ^ 40 * 8348514 * 2
def baseEnd_8348514 : Nat := 158770386399624245714107

theorem tailTrace_8348514 : CollatzResearch.WordTrace tailWord_8348514 prefixEnd_8348514 158770386399624245714107 := by
  unfold tailWord_8348514
  simp only [CollatzResearch.WordTrace]
  refine ⟨76123830219191766380391149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202996880584511377014376397 76123830219191766380391149)
  ·
    refine ⟨28546436332196912392646681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76123830219191766380391149 28546436332196912392646681)
    ·
      refine ⟨21409827249147684294485011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28546436332196912392646681 21409827249147684294485011)
      ·
        refine ⟨32114740873721526441727517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21409827249147684294485011 32114740873721526441727517)
        ·
          refine ⟨12043027827645572415647819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32114740873721526441727517 12043027827645572415647819)
          ·
            refine ⟨18064541741468358623471729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12043027827645572415647819 18064541741468358623471729)
            ·
              refine ⟨13548406306101268967603797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18064541741468358623471729 13548406306101268967603797)
              ·
                refine ⟨158770386399624245714107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13548406306101268967603797 158770386399624245714107)
                ·
                  rfl

theorem cell23_8348514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 8].length) (baseStart_8348514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348514 prefixEnd_8348514 := by exact prefixLift 8348514
  have htrace : WordTrace (prefixWord ++ tailWord_8348514) baseStart_8348514 baseEnd_8348514 := by
    simpa [prefixWord, tailWord_8348514, baseEnd_8348514] using wordTrace_append hprefix tailTrace_8348514
  have hstable : (prefixWord ++ tailWord_8348514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348514).length < 2 ^ (prefixWord ++ tailWord_8348514).sum := by decide
  have hdescent : baseEnd_8348514 < baseStart_8348514 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348567 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 1, 6, 3]
def baseStart_8348567 : Nat := 118140960795 + 8348567 * 2 ^ 59
def prefixEnd_8348567 : Nat := 4983230072969 + 3 ^ 40 * 8348567 * 2
def baseEnd_8348567 : Nat := 4286827647264542926918145

theorem tailTrace_8348567 : CollatzResearch.WordTrace tailWord_8348567 prefixEnd_8348567 4286827647264542926918145 := by
  unfold tailWord_8348567
  simp only [CollatzResearch.WordTrace]
  refine ⟨304497253945575055573243955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202998169297050037048829303 304497253945575055573243955)
  ·
    refine ⟨456745880918362583359865933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304497253945575055573243955 456745880918362583359865933)
    ·
      refine ⟨171279705344385968759949725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456745880918362583359865933 171279705344385968759949725)
      ·
        refine ⟨64229889504144738284981147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171279705344385968759949725 64229889504144738284981147)
        ·
          refine ⟨96344834256217107427471721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64229889504144738284981147 96344834256217107427471721)
          ·
            refine ⟨72258625692162830570603791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96344834256217107427471721 72258625692162830570603791)
            ·
              refine ⟨108387938538244245855905687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72258625692162830570603791 108387938538244245855905687)
              ·
                refine ⟨162581907807366368783858531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108387938538244245855905687 162581907807366368783858531)
                ·
                  refine ⟨243872861711049553175787797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162581907807366368783858531 243872861711049553175787797)
                  ·
                    refine ⟨11431540392705447805115053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 243872861711049553175787797 11431540392705447805115053)
                    ·
                      refine ⟨4286827647264542926918145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11431540392705447805115053 4286827647264542926918145)
                      ·
                        rfl

theorem cell23_8348567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_8348567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348567 prefixEnd_8348567 := by exact prefixLift 8348567
  have htrace : WordTrace (prefixWord ++ tailWord_8348567) baseStart_8348567 baseEnd_8348567 := by
    simpa [prefixWord, tailWord_8348567, baseEnd_8348567] using wordTrace_append hprefix tailTrace_8348567
  have hstable : (prefixWord ++ tailWord_8348567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348567).length < 2 ^ (prefixWord ++ tailWord_8348567).sum := by decide
  have hdescent : baseEnd_8348567 < baseStart_8348567 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348677 : List Nat := [1, 3, 1, 1, 2, 3, 1, 3, 8]
def baseStart_8348677 : Nat := 118140960795 + 8348677 * 2 ^ 59
def prefixEnd_8348677 : Nat := 4983230072969 + 3 ^ 40 * 8348677 * 2
def baseEnd_8348677 : Nat := 476320458904059721838071

theorem tailTrace_8348677 : CollatzResearch.WordTrace tailWord_8348677 prefixEnd_8348677 476320458904059721838071 := by
  unfold tailWord_8348677
  simp only [CollatzResearch.WordTrace]
  refine ⟨304501265975176544359748285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203000843983451029573165523 304501265975176544359748285)
  ·
    refine ⟨114187974740691204134905607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304501265975176544359748285 114187974740691204134905607)
    ·
      refine ⟨171281962111036806202358411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114187974740691204134905607 171281962111036806202358411)
      ·
        refine ⟨256922943166555209303537617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171281962111036806202358411 256922943166555209303537617)
        ·
          refine ⟨192692207374916406977653213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256922943166555209303537617 192692207374916406977653213)
          ·
            refine ⟨72259577765593652616619955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192692207374916406977653213 72259577765593652616619955)
            ·
              refine ⟨108389366648390478924929933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72259577765593652616619955 108389366648390478924929933)
              ·
                refine ⟨40646012493146429596848725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108389366648390478924929933 40646012493146429596848725)
                ·
                  refine ⟨476320458904059721838071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40646012493146429596848725 476320458904059721838071)
                  ·
                    rfl

theorem cell23_8348677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 8].length) (baseStart_8348677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348677 prefixEnd_8348677 := by exact prefixLift 8348677
  have htrace : WordTrace (prefixWord ++ tailWord_8348677) baseStart_8348677 baseEnd_8348677 := by
    simpa [prefixWord, tailWord_8348677, baseEnd_8348677] using wordTrace_append hprefix tailTrace_8348677
  have hstable : (prefixWord ++ tailWord_8348677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348677).length < 2 ^ (prefixWord ++ tailWord_8348677).sum := by decide
  have hdescent : baseEnd_8348677 < baseStart_8348677 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348681 : List Nat := [1, 2, 1, 1, 3, 1, 1, 8, 1, 4]
def baseStart_8348681 : Nat := 118140960795 + 8348681 * 2 ^ 59
def prefixEnd_8348681 : Nat := 4983230072969 + 3 ^ 40 * 8348681 * 2
def baseEnd_8348681 : Nat := 1428962061353051826964207

theorem tailTrace_8348681 : CollatzResearch.WordTrace tailWord_8348681 prefixEnd_8348681 1428962061353051826964207 := by
  unfold tailWord_8348681
  simp only [CollatzResearch.WordTrace]
  refine ⟨304501411867162053042893897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203000941244774702028595931 304501411867162053042893897)
  ·
    refine ⟨228376058900371539782170423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304501411867162053042893897 228376058900371539782170423)
    ·
      refine ⟨342564088350557309673255635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228376058900371539782170423 342564088350557309673255635)
      ·
        refine ⟨513846132525835964509883453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342564088350557309673255635 513846132525835964509883453)
        ·
          refine ⟨192692299697188486691206295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 513846132525835964509883453 192692299697188486691206295)
          ·
            refine ⟨289038449545782730036809443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192692299697188486691206295 289038449545782730036809443)
            ·
              refine ⟨433557674318674095055214165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289038449545782730036809443 433557674318674095055214165)
              ·
                refine ⟨5080753995921962051428291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 433557674318674095055214165 5080753995921962051428291)
                ·
                  refine ⟨7621130993882943077142437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5080753995921962051428291 7621130993882943077142437)
                  ·
                    refine ⟨1428962061353051826964207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7621130993882943077142437 1428962061353051826964207)
                    ·
                      rfl

theorem cell23_8348681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8, 1, 4].length) (baseStart_8348681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348681 prefixEnd_8348681 := by exact prefixLift 8348681
  have htrace : WordTrace (prefixWord ++ tailWord_8348681) baseStart_8348681 baseEnd_8348681 := by
    simpa [prefixWord, tailWord_8348681, baseEnd_8348681] using wordTrace_append hprefix tailTrace_8348681
  have hstable : (prefixWord ++ tailWord_8348681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348681).length < 2 ^ (prefixWord ++ tailWord_8348681).sum := by decide
  have hdescent : baseEnd_8348681 < baseStart_8348681 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348697 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 1, 2, 6]
def baseStart_8348697 : Nat := 118140960795 + 8348697 * 2 ^ 59
def prefixEnd_8348697 : Nat := 4983230072969 + 3 ^ 40 * 8348697 * 2
def baseEnd_8348697 : Nat := 4286894399749627418292547

theorem tailTrace_8348697 : CollatzResearch.WordTrace tailWord_8348697 prefixEnd_8348697 4286894399749627418292547 := by
  unfold tailWord_8348697
  simp only [CollatzResearch.WordTrace]
  refine ⟨304501995435104087775476345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203001330290069391850317563 304501995435104087775476345)
  ·
    refine ⟨228376496576328065831607259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304501995435104087775476345 228376496576328065831607259)
    ·
      refine ⟨342564744864492098747410889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228376496576328065831607259 342564744864492098747410889)
      ·
        refine ⟨256923558648369074060558167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342564744864492098747410889 256923558648369074060558167)
        ·
          refine ⟨385385337972553611090837251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256923558648369074060558167 385385337972553611090837251)
          ·
            refine ⟨578078006958830416636255877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385385337972553611090837251 578078006958830416636255877)
            ·
              refine ⟨108389626304780703119297977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 578078006958830416636255877 108389626304780703119297977)
              ·
                refine ⟨81292219728585527339473483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108389626304780703119297977 81292219728585527339473483)
                ·
                  refine ⟨121938329592878291009210225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81292219728585527339473483 121938329592878291009210225)
                  ·
                    refine ⟨91453747194658718256907669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121938329592878291009210225 91453747194658718256907669)
                    ·
                      refine ⟨4286894399749627418292547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91453747194658718256907669 4286894399749627418292547)
                      ·
                        rfl

theorem cell23_8348697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_8348697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348697 prefixEnd_8348697 := by exact prefixLift 8348697
  have htrace : WordTrace (prefixWord ++ tailWord_8348697) baseStart_8348697 baseEnd_8348697 := by
    simpa [prefixWord, tailWord_8348697, baseEnd_8348697] using wordTrace_append hprefix tailTrace_8348697
  have hstable : (prefixWord ++ tailWord_8348697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348697).length < 2 ^ (prefixWord ++ tailWord_8348697).sum := by decide
  have hdescent : baseEnd_8348697 < baseStart_8348697 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348708 : List Nat := [2, 3, 1, 4, 1, 2, 2, 1, 2, 2, 3]
def baseStart_8348708 : Nat := 118140960795 + 8348708 * 2 ^ 59
def prefixEnd_8348708 : Nat := 4983230072969 + 3 ^ 40 * 8348708 * 2
def baseEnd_8348708 : Nat := 4286900048036826875254997

theorem tailTrace_8348708 : CollatzResearch.WordTrace tailWord_8348708 prefixEnd_8348708 4286900048036826875254997 := by
  unfold tailWord_8348708
  simp only [CollatzResearch.WordTrace]
  refine ⟨152251198319032118327063389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203001597758709491102751185 152251198319032118327063389)
  ·
    refine ⟨57094199369637044372648771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152251198319032118327063389 57094199369637044372648771)
    ·
      refine ⟨85641299054455566558973157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57094199369637044372648771 85641299054455566558973157)
      ·
        refine ⟨16057743572710418729807467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85641299054455566558973157 16057743572710418729807467)
        ·
          refine ⟨24086615359065628094711201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16057743572710418729807467 24086615359065628094711201)
          ·
            refine ⟨18064961519299221071033401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24086615359065628094711201 18064961519299221071033401)
            ·
              refine ⟨13548721139474415803275051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18064961519299221071033401 13548721139474415803275051)
              ·
                refine ⟨20323081709211623704912577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13548721139474415803275051 20323081709211623704912577)
                ·
                  refine ⟨15242311281908717778684433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20323081709211623704912577 15242311281908717778684433)
                  ·
                    refine ⟨11431733461431538334013325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15242311281908717778684433 11431733461431538334013325)
                    ·
                      refine ⟨4286900048036826875254997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11431733461431538334013325 4286900048036826875254997)
                      ·
                        rfl

theorem cell23_8348708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_8348708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348708 prefixEnd_8348708 := by exact prefixLift 8348708
  have htrace : WordTrace (prefixWord ++ tailWord_8348708) baseStart_8348708 baseEnd_8348708 := by
    simpa [prefixWord, tailWord_8348708, baseEnd_8348708] using wordTrace_append hprefix tailTrace_8348708
  have hstable : (prefixWord ++ tailWord_8348708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348708).length < 2 ^ (prefixWord ++ tailWord_8348708).sum := by decide
  have hdescent : baseEnd_8348708 < baseStart_8348708 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348744 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 5, 1, 4]
def baseStart_8348744 : Nat := 118140960795 + 8348744 * 2 ^ 59
def prefixEnd_8348744 : Nat := 4983230072969 + 3 ^ 40 * 8348744 * 2
def baseEnd_8348744 : Nat := 4286918533340388734404831

theorem tailTrace_8348744 : CollatzResearch.WordTrace tailWord_8348744 prefixEnd_8348744 4286918533340388734404831 := by
  unfold tailWord_8348744
  simp only [CollatzResearch.WordTrace]
  refine ⟨152251854832966907401218643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203002473110622543201624857 152251854832966907401218643)
  ·
    refine ⟨228377782249450361101827965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152251854832966907401218643 228377782249450361101827965)
    ·
      refine ⟨85641668343543885413185487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228377782249450361101827965 85641668343543885413185487)
      ·
        refine ⟨128462502515315828119778231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85641668343543885413185487 128462502515315828119778231)
        ·
          refine ⟨192693753772973742179667347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128462502515315828119778231 192693753772973742179667347)
          ·
            refine ⟨289040630659460613269501021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192693753772973742179667347 289040630659460613269501021)
            ·
              refine ⟨108390236497297729976062883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289040630659460613269501021 108390236497297729976062883)
              ·
                refine ⟨162585354745946594964094325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108390236497297729976062883 162585354745946594964094325)
                ·
                  refine ⟨15242377007432493277883843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162585354745946594964094325 15242377007432493277883843)
                  ·
                    refine ⟨22863565511148739916825765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15242377007432493277883843 22863565511148739916825765)
                    ·
                      refine ⟨4286918533340388734404831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22863565511148739916825765 4286918533340388734404831)
                      ·
                        rfl

theorem cell23_8348744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_8348744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348744 prefixEnd_8348744 := by exact prefixLift 8348744
  have htrace : WordTrace (prefixWord ++ tailWord_8348744) baseStart_8348744 baseEnd_8348744 := by
    simpa [prefixWord, tailWord_8348744, baseEnd_8348744] using wordTrace_append hprefix tailTrace_8348744
  have hstable : (prefixWord ++ tailWord_8348744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348744).length < 2 ^ (prefixWord ++ tailWord_8348744).sum := by decide
  have hdescent : baseEnd_8348744 < baseStart_8348744 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348765 : List Nat := [1, 4, 4, 1, 2, 1, 1, 1, 1, 5, 2]
def baseStart_8348765 : Nat := 118140960795 + 8348765 * 2 ^ 59
def prefixEnd_8348765 : Nat := 4983230072969 + 3 ^ 40 * 8348765 * 2
def baseEnd_8348765 : Nat := 4286929316434133152242235

theorem tailTrace_8348765 : CollatzResearch.WordTrace tailWord_8348765 prefixEnd_8348765 4286929316434133152242235 := by
  unfold tailWord_8348765
  simp only [CollatzResearch.WordTrace]
  refine ⟨304504475598857735388951749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203002983732571823592634499 304504475598857735388951749)
  ·
    refine ⟨57094589174785825385428453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304504475598857735388951749 57094589174785825385428453)
    ·
      refine ⟨10705235470272342259767835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57094589174785825385428453 10705235470272342259767835)
      ·
        refine ⟨16057853205408513389651753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10705235470272342259767835 16057853205408513389651753)
        ·
          refine ⟨12043389904056385042238815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16057853205408513389651753 12043389904056385042238815)
          ·
            refine ⟨18065084856084577563358223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12043389904056385042238815 18065084856084577563358223)
            ·
              refine ⟨27097627284126866345037335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18065084856084577563358223 27097627284126866345037335)
              ·
                refine ⟨40646440926190299517556003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27097627284126866345037335 40646440926190299517556003)
                ·
                  refine ⟨60969661389285449276334005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40646440926190299517556003 60969661389285449276334005)
                  ·
                    refine ⟨5715905755245510869656313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60969661389285449276334005 5715905755245510869656313)
                    ·
                      refine ⟨4286929316434133152242235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5715905755245510869656313 4286929316434133152242235)
                      ·
                        rfl

theorem cell23_8348765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_8348765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348765 prefixEnd_8348765 := by exact prefixLift 8348765
  have htrace : WordTrace (prefixWord ++ tailWord_8348765) baseStart_8348765 baseEnd_8348765 := by
    simpa [prefixWord, tailWord_8348765, baseEnd_8348765] using wordTrace_append hprefix tailTrace_8348765
  have hstable : (prefixWord ++ tailWord_8348765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348765).length < 2 ^ (prefixWord ++ tailWord_8348765).sum := by decide
  have hdescent : baseEnd_8348765 < baseStart_8348765 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348778 : List Nat := [3, 1, 3, 2, 2, 2, 1, 3, 1, 1, 4]
def baseStart_8348778 : Nat := 118140960795 + 8348778 * 2 ^ 59
def prefixEnd_8348778 : Nat := 4983230072969 + 3 ^ 40 * 8348778 * 2
def baseEnd_8348778 : Nat := 4286935991682641601379675

theorem tailTrace_8348778 : CollatzResearch.WordTrace tailWord_8348778 prefixEnd_8348778 4286935991682641601379675 := by
  unfold tailWord_8348778
  simp only [CollatzResearch.WordTrace]
  refine ⟨76126237436952659652293747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203003299831873759072783325 76126237436952659652293747)
  ·
    refine ⟨114189356155428989478440621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76126237436952659652293747 114189356155428989478440621)
    ·
      refine ⟨42821008558285871054415233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114189356155428989478440621 42821008558285871054415233)
      ·
        refine ⟨32115756418714403290811425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42821008558285871054415233 32115756418714403290811425)
        ·
          refine ⟨24086817314035802468108569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32115756418714403290811425 24086817314035802468108569)
          ·
            refine ⟨18065112985526851851081427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24086817314035802468108569 18065112985526851851081427)
            ·
              refine ⟨27097669478290277776622141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18065112985526851851081427 27097669478290277776622141)
              ·
                refine ⟨10161626054358854166233303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27097669478290277776622141 10161626054358854166233303)
                ·
                  refine ⟨15242439081538281249349955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10161626054358854166233303 15242439081538281249349955)
                  ·
                    refine ⟨22863658622307421874024933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15242439081538281249349955 22863658622307421874024933)
                    ·
                      refine ⟨4286935991682641601379675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22863658622307421874024933 4286935991682641601379675)
                      ·
                        rfl

theorem cell23_8348778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_8348778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348778 prefixEnd_8348778 := by exact prefixLift 8348778
  have htrace : WordTrace (prefixWord ++ tailWord_8348778) baseStart_8348778 baseEnd_8348778 := by
    simpa [prefixWord, tailWord_8348778, baseEnd_8348778] using wordTrace_append hprefix tailTrace_8348778
  have hstable : (prefixWord ++ tailWord_8348778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348778).length < 2 ^ (prefixWord ++ tailWord_8348778).sum := by decide
  have hdescent : baseEnd_8348778 < baseStart_8348778 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348794 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3]
def baseStart_8348794 : Nat := 118140960795 + 8348794 * 2 ^ 59
def prefixEnd_8348794 : Nat := 4983230072969 + 3 ^ 40 * 8348794 * 2
def baseEnd_8348794 : Nat := 4286944207373113538779601

theorem tailTrace_8348794 : CollatzResearch.WordTrace tailWord_8348794 prefixEnd_8348794 4286944207373113538779601 := by
  unfold tailWord_8348794
  simp only [CollatzResearch.WordTrace]
  refine ⟨76126383328938168335439359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203003688877168448894504957 76126383328938168335439359)
  ·
    refine ⟨114189574993407252503159039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76126383328938168335439359 114189574993407252503159039)
    ·
      refine ⟨171284362490110878754738559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114189574993407252503159039 171284362490110878754738559)
      ·
        refine ⟨256926543735166318132107839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171284362490110878754738559 256926543735166318132107839)
        ·
          refine ⟨385389815602749477198161759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256926543735166318132107839 385389815602749477198161759)
          ·
            refine ⟨578084723404124215797242639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385389815602749477198161759 578084723404124215797242639)
            ·
              refine ⟨867127085106186323695863959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578084723404124215797242639 867127085106186323695863959)
              ·
                refine ⟨1300690627659279485543795939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 867127085106186323695863959 1300690627659279485543795939)
                ·
                  refine ⟨1951035941488919228315693909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1300690627659279485543795939 1951035941488919228315693909)
                  ·
                    refine ⟨11431851219661636103412269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1951035941488919228315693909 11431851219661636103412269)
                    ·
                      refine ⟨4286944207373113538779601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11431851219661636103412269 4286944207373113538779601)
                      ·
                        rfl

theorem cell23_8348794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3].length) (baseStart_8348794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348794 prefixEnd_8348794 := by exact prefixLift 8348794
  have htrace : WordTrace (prefixWord ++ tailWord_8348794) baseStart_8348794 baseEnd_8348794 := by
    simpa [prefixWord, tailWord_8348794, baseEnd_8348794] using wordTrace_append hprefix tailTrace_8348794
  have hstable : (prefixWord ++ tailWord_8348794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348794).length < 2 ^ (prefixWord ++ tailWord_8348794).sum := by decide
  have hdescent : baseEnd_8348794 < baseStart_8348794 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348805 : List Nat := [1, 3, 1, 1, 6, 1, 3, 1, 2, 4]
def baseStart_8348805 : Nat := 118140960795 + 8348805 * 2 ^ 59
def prefixEnd_8348805 : Nat := 4983230072969 + 3 ^ 40 * 8348805 * 2
def baseEnd_8348805 : Nat := 1428983285220104331914017

theorem tailTrace_8348805 : CollatzResearch.WordTrace tailWord_8348805 prefixEnd_8348805 1428983285220104331914017 := by
  unfold tailWord_8348805
  simp only [CollatzResearch.WordTrace]
  refine ⟨304505934518712822220407869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203003956345808548146938579 304505934518712822220407869)
  ·
    refine ⟨114189725444517308332652951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304505934518712822220407869 114189725444517308332652951)
    ·
      refine ⟨171284588166775962498979427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114189725444517308332652951 171284588166775962498979427)
      ·
        refine ⟨256926882250163943748469141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171284588166775962498979427 256926882250163943748469141)
        ·
          refine ⟨12043447605476434863209491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 256926882250163943748469141 12043447605476434863209491)
          ·
            refine ⟨18065171408214652294814237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12043447605476434863209491 18065171408214652294814237)
            ·
              refine ⟨6774439278080494610555339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18065171408214652294814237 6774439278080494610555339)
              ·
                refine ⟨10161658917120741915833009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6774439278080494610555339 10161658917120741915833009)
                ·
                  refine ⟨7621244187840556436874757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10161658917120741915833009 7621244187840556436874757)
                  ·
                    refine ⟨1428983285220104331914017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7621244187840556436874757 1428983285220104331914017)
                    ·
                      rfl

theorem cell23_8348805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 2, 4].length) (baseStart_8348805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348805 prefixEnd_8348805 := by exact prefixLift 8348805
  have htrace : WordTrace (prefixWord ++ tailWord_8348805) baseStart_8348805 baseEnd_8348805 := by
    simpa [prefixWord, tailWord_8348805, baseEnd_8348805] using wordTrace_append hprefix tailTrace_8348805
  have hstable : (prefixWord ++ tailWord_8348805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348805).length < 2 ^ (prefixWord ++ tailWord_8348805).sum := by decide
  have hdescent : baseEnd_8348805 < baseStart_8348805 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348818 : List Nat := [3, 2, 3, 1, 1, 4, 2, 7]
def baseStart_8348818 : Nat := 118140960795 + 8348818 * 2 ^ 59
def prefixEnd_8348818 : Nat := 4983230072969 + 3 ^ 40 * 8348818 * 2
def baseEnd_8348818 : Nat := 158776167811437831291833

theorem tailTrace_8348818 : CollatzResearch.WordTrace tailWord_8348818 prefixEnd_8348818 158776167811437831291833 := by
  unfold tailWord_8348818
  simp only [CollatzResearch.WordTrace]
  refine ⟨76126602166916431360157777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203004272445110483627087405 76126602166916431360157777)
  ·
    refine ⟨57094951625187323520118333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76126602166916431360157777 57094951625187323520118333)
    ·
      refine ⟨21410606859445246320044375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57094951625187323520118333 21410606859445246320044375)
      ·
        refine ⟨32115910289167869480066563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21410606859445246320044375 32115910289167869480066563)
        ·
          refine ⟨48173865433751804220099845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32115910289167869480066563 48173865433751804220099845)
          ·
            refine ⟨9032599768828463291268721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48173865433751804220099845 9032599768828463291268721)
            ·
              refine ⟨6774449826621347468451541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9032599768828463291268721 6774449826621347468451541)
              ·
                refine ⟨158776167811437831291833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6774449826621347468451541 158776167811437831291833)
                ·
                  rfl

theorem cell23_8348818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 7].length) (baseStart_8348818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348818 prefixEnd_8348818 := by exact prefixLift 8348818
  have htrace : WordTrace (prefixWord ++ tailWord_8348818) baseStart_8348818 baseEnd_8348818 := by
    simpa [prefixWord, tailWord_8348818, baseEnd_8348818] using wordTrace_append hprefix tailTrace_8348818
  have hstable : (prefixWord ++ tailWord_8348818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348818).length < 2 ^ (prefixWord ++ tailWord_8348818).sum := by decide
  have hdescent : baseEnd_8348818 < baseStart_8348818 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348828 : List Nat := [2, 2, 3, 2, 1, 2, 1, 2, 4, 1, 3]
def baseStart_8348828 : Nat := 118140960795 + 8348828 * 2 ^ 59
def prefixEnd_8348828 : Nat := 4983230072969 + 3 ^ 40 * 8348828 * 2
def baseEnd_8348828 : Nat := 4286961665715366405754445

theorem tailTrace_8348828 : CollatzResearch.WordTrace tailWord_8348828 prefixEnd_8348828 4286961665715366405754445 := by
  unfold tailWord_8348828
  simp only [CollatzResearch.WordTrace]
  refine ⟨152253386698814748574247569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203004515598419664765663425 152253386698814748574247569)
  ·
    refine ⟨114190040024111061430685677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152253386698814748574247569 114190040024111061430685677)
    ·
      refine ⟨42821265009041648036507129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114190040024111061430685677 42821265009041648036507129)
      ·
        refine ⟨32115948756781236027380347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42821265009041648036507129 32115948756781236027380347)
        ·
          refine ⟨48173923135171854041070521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32115948756781236027380347 48173923135171854041070521)
          ·
            refine ⟨36130442351378890530802891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48173923135171854041070521 36130442351378890530802891)
            ·
              refine ⟨54195663527068335796204337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36130442351378890530802891 54195663527068335796204337)
              ·
                refine ⟨40646747645301251847153253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54195663527068335796204337 40646747645301251847153253)
                ·
                  refine ⟨7621265183493984721341235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40646747645301251847153253 7621265183493984721341235)
                  ·
                    refine ⟨11431897775240977082011853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7621265183493984721341235 11431897775240977082011853)
                    ·
                      refine ⟨4286961665715366405754445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11431897775240977082011853 4286961665715366405754445)
                      ·
                        rfl

theorem cell23_8348828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_8348828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348828 prefixEnd_8348828 := by exact prefixLift 8348828
  have htrace : WordTrace (prefixWord ++ tailWord_8348828) baseStart_8348828 baseEnd_8348828 := by
    simpa [prefixWord, tailWord_8348828, baseEnd_8348828] using wordTrace_append hprefix tailTrace_8348828
  have hstable : (prefixWord ++ tailWord_8348828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348828).length < 2 ^ (prefixWord ++ tailWord_8348828).sum := by decide
  have hdescent : baseEnd_8348828 < baseStart_8348828 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348844 : List Nat := [2, 2, 1, 1, 1, 1, 1, 6, 2, 6]
def baseStart_8348844 : Nat := 118140960795 + 8348844 * 2 ^ 59
def prefixEnd_8348844 : Nat := 4983230072969 + 3 ^ 40 * 8348844 * 2
def baseEnd_8348844 : Nat := 1428989960468612781051457

theorem tailTrace_8348844 : CollatzResearch.WordTrace tailWord_8348844 prefixEnd_8348844 1428989960468612781051457 := by
  unfold tailWord_8348844
  simp only [CollatzResearch.WordTrace]
  refine ⟨152253678482785765940538793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203004904643714354587385057 152253678482785765940538793)
  ·
    refine ⟨114190258862089324455404095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152253678482785765940538793 114190258862089324455404095)
    ·
      refine ⟨171285388293133986683106143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114190258862089324455404095 171285388293133986683106143)
      ·
        refine ⟨256928082439700980024659215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171285388293133986683106143 256928082439700980024659215)
        ·
          refine ⟨385392123659551470036988823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256928082439700980024659215 385392123659551470036988823)
          ·
            refine ⟨578088185489327205055483235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385392123659551470036988823 578088185489327205055483235)
            ·
              refine ⟨867132278233990807583224853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578088185489327205055483235 867132278233990807583224853)
              ·
                refine ⟨40646825542218319105463665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 867132278233990807583224853 40646825542218319105463665)
                ·
                  refine ⟨30485119156663739329097749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40646825542218319105463665 30485119156663739329097749)
                  ·
                    refine ⟨1428989960468612781051457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30485119156663739329097749 1428989960468612781051457)
                    ·
                      rfl

theorem cell23_8348844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 6].length) (baseStart_8348844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348844 prefixEnd_8348844 := by exact prefixLift 8348844
  have htrace : WordTrace (prefixWord ++ tailWord_8348844) baseStart_8348844 baseEnd_8348844 := by
    simpa [prefixWord, tailWord_8348844, baseEnd_8348844] using wordTrace_append hprefix tailTrace_8348844
  have hstable : (prefixWord ++ tailWord_8348844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348844).length < 2 ^ (prefixWord ++ tailWord_8348844).sum := by decide
  have hdescent : baseEnd_8348844 < baseStart_8348844 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348862 : List Nat := [4, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3]
def baseStart_8348862 : Nat := 118140960795 + 8348862 * 2 ^ 59
def prefixEnd_8348862 : Nat := 4983230072969 + 3 ^ 40 * 8348862 * 2
def baseEnd_8348862 : Nat := 4286979124057619272729289

theorem tailTrace_8348862 : CollatzResearch.WordTrace tailWord_8348862 prefixEnd_8348862 4286979124057619272729289 := by
  unfold tailWord_8348862
  simp only [CollatzResearch.WordTrace]
  refine ⟨38063501684938290119404105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203005342319670880636821893 38063501684938290119404105)
  ·
    refine ⟨28547626263703717589553079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38063501684938290119404105 28547626263703717589553079)
    ·
      refine ⟨42821439395555576384329619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28547626263703717589553079 42821439395555576384329619)
      ·
        refine ⟨64232159093333364576494429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42821439395555576384329619 64232159093333364576494429)
        ·
          refine ⟨24087059660000011716185411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64232159093333364576494429 24087059660000011716185411)
          ·
            refine ⟨36130589490000017574278117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24087059660000011716185411 36130589490000017574278117)
            ·
              refine ⟨6774485529375003295177147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36130589490000017574278117 6774485529375003295177147)
              ·
                refine ⟨10161728294062504942765721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6774485529375003295177147 10161728294062504942765721)
                ·
                  refine ⟨7621296220546878707074291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10161728294062504942765721 7621296220546878707074291)
                  ·
                    refine ⟨11431944330820318060611437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7621296220546878707074291 11431944330820318060611437)
                    ·
                      refine ⟨4286979124057619272729289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11431944330820318060611437 4286979124057619272729289)
                      ·
                        rfl

theorem cell23_8348862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_8348862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348862 prefixEnd_8348862 := by exact prefixLift 8348862
  have htrace : WordTrace (prefixWord ++ tailWord_8348862) baseStart_8348862 baseEnd_8348862 := by
    simpa [prefixWord, tailWord_8348862, baseEnd_8348862] using wordTrace_append hprefix tailTrace_8348862
  have hstable : (prefixWord ++ tailWord_8348862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348862).length < 2 ^ (prefixWord ++ tailWord_8348862).sum := by decide
  have hdescent : baseEnd_8348862 < baseStart_8348862 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348866 : List Nat := [3, 5, 1, 1, 3, 1, 1, 2, 1, 2, 3]
def baseStart_8348866 : Nat := 118140960795 + 8348866 * 2 ^ 59
def prefixEnd_8348866 : Nat := 4983230072969 + 3 ^ 40 * 8348866 * 2
def baseEnd_8348866 : Nat := 4286981177980237257079271

theorem tailTrace_8348866 : CollatzResearch.WordTrace tailWord_8348866 prefixEnd_8348866 4286981177980237257079271 := by
  unfold tailWord_8348866
  simp only [CollatzResearch.WordTrace]
  refine ⟨76127039842872957409594613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203005439580994553092252301 76127039842872957409594613)
  ·
    refine ⟨7136909985269339757149495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76127039842872957409594613 7136909985269339757149495)
    ·
      refine ⟨10705364977904009635724243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7136909985269339757149495 10705364977904009635724243)
      ·
        refine ⟨16058047466856014453586365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10705364977904009635724243 16058047466856014453586365)
        ·
          refine ⟨6021767800071005420094887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16058047466856014453586365 6021767800071005420094887)
          ·
            refine ⟨9032651700106508130142331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6021767800071005420094887 9032651700106508130142331)
            ·
              refine ⟨13548977550159762195213497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9032651700106508130142331 13548977550159762195213497)
              ·
                refine ⟨10161733162619821646410123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13548977550159762195213497 10161733162619821646410123)
                ·
                  refine ⟨15242599743929732469615185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10161733162619821646410123 15242599743929732469615185)
                  ·
                    refine ⟨11431949807947299352211389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15242599743929732469615185 11431949807947299352211389)
                    ·
                      refine ⟨4286981177980237257079271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11431949807947299352211389 4286981177980237257079271)
                      ·
                        rfl

theorem cell23_8348866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_8348866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348866 prefixEnd_8348866 := by exact prefixLift 8348866
  have htrace : WordTrace (prefixWord ++ tailWord_8348866) baseStart_8348866 baseEnd_8348866 := by
    simpa [prefixWord, tailWord_8348866, baseEnd_8348866] using wordTrace_append hprefix tailTrace_8348866
  have hstable : (prefixWord ++ tailWord_8348866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348866).length < 2 ^ (prefixWord ++ tailWord_8348866).sum := by decide
  have hdescent : baseEnd_8348866 < baseStart_8348866 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348885 : List Nat := [1, 3, 2, 4, 1, 2, 1, 2, 1, 4, 2]
def baseStart_8348885 : Nat := 118140960795 + 8348885 * 2 ^ 59
def prefixEnd_8348885 : Nat := 4983230072969 + 3 ^ 40 * 8348885 * 2
def baseEnd_8348885 : Nat := 4286990934112672682741683

theorem tailTrace_8348885 : CollatzResearch.WordTrace tailWord_8348885 prefixEnd_8348885 4286990934112672682741683 := by
  unfold tailWord_8348885
  simp only [CollatzResearch.WordTrace]
  refine ⟨304508852358422995883320109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203005901572281997255546739 304508852358422995883320109)
  ·
    refine ⟨114190819634408623456245041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304508852358422995883320109 114190819634408623456245041)
    ·
      refine ⟨85643114725806467592183781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114190819634408623456245041 85643114725806467592183781)
      ·
        refine ⟨16058084011088712673534459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85643114725806467592183781 16058084011088712673534459)
        ·
          refine ⟨24087126016633069010301689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16058084011088712673534459 24087126016633069010301689)
          ·
            refine ⟨18065344512474801757726267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24087126016633069010301689 18065344512474801757726267)
            ·
              refine ⟨27098016768712202636589401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18065344512474801757726267 27098016768712202636589401)
              ·
                refine ⟨20323512576534151977442051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27098016768712202636589401 20323512576534151977442051)
                ·
                  refine ⟨30485268864801227966163077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20323512576534151977442051 30485268864801227966163077)
                  ·
                    refine ⟨5715987912150230243655577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30485268864801227966163077 5715987912150230243655577)
                    ·
                      refine ⟨4286990934112672682741683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5715987912150230243655577 4286990934112672682741683)
                      ·
                        rfl

theorem cell23_8348885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_8348885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348885 prefixEnd_8348885 := by exact prefixLift 8348885
  have htrace : WordTrace (prefixWord ++ tailWord_8348885) baseStart_8348885 baseEnd_8348885 := by
    simpa [prefixWord, tailWord_8348885, baseEnd_8348885] using wordTrace_append hprefix tailTrace_8348885
  have hstable : (prefixWord ++ tailWord_8348885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348885).length < 2 ^ (prefixWord ++ tailWord_8348885).sum := by decide
  have hdescent : baseEnd_8348885 < baseStart_8348885 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348908 : List Nat := [2, 2, 1, 1, 2, 5, 1, 4, 5]
def baseStart_8348908 : Nat := 118140960795 + 8348908 * 2 ^ 59
def prefixEnd_8348908 : Nat := 4983230072969 + 3 ^ 40 * 8348908 * 2
def baseEnd_8348908 : Nat := 476333638240858454750453

theorem tailTrace_8348908 : CollatzResearch.WordTrace tailWord_8348908 prefixEnd_8348908 476333638240858454750453 := by
  unfold tailWord_8348908
  simp only [CollatzResearch.WordTrace]
  refine ⟨152254845618669835405703689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203006460824893113874271585 152254845618669835405703689)
  ·
    refine ⟨114191134214002376554277767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152254845618669835405703689 114191134214002376554277767)
    ·
      refine ⟨171286701321003564831416651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114191134214002376554277767 171286701321003564831416651)
      ·
        refine ⟨256930051981505347247124977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171286701321003564831416651 256930051981505347247124977)
        ·
          refine ⟨192697538986129010435343733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256930051981505347247124977 192697538986129010435343733)
          ·
            refine ⟨18065394279949594728313475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 192697538986129010435343733 18065394279949594728313475)
            ·
              refine ⟨27098091419924392092470213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18065394279949594728313475 27098091419924392092470213)
              ·
                refine ⟨5080892141235823517338165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27098091419924392092470213 5080892141235823517338165)
                ·
                  refine ⟨476333638240858454750453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5080892141235823517338165 476333638240858454750453)
                  ·
                    rfl

theorem cell23_8348908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4, 5].length) (baseStart_8348908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348908 prefixEnd_8348908 := by exact prefixLift 8348908
  have htrace : WordTrace (prefixWord ++ tailWord_8348908) baseStart_8348908 baseEnd_8348908 := by
    simpa [prefixWord, tailWord_8348908, baseEnd_8348908] using wordTrace_append hprefix tailTrace_8348908
  have hstable : (prefixWord ++ tailWord_8348908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348908).length < 2 ^ (prefixWord ++ tailWord_8348908).sum := by decide
  have hdescent : baseEnd_8348908 < baseStart_8348908 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8348978 : List Nat := [3, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3]
def baseStart_8348978 : Nat := 118140960795 + 8348978 * 2 ^ 59
def prefixEnd_8348978 : Nat := 4983230072969 + 3 ^ 40 * 8348978 * 2
def baseEnd_8348978 : Nat := 4287038687813540818878755

theorem tailTrace_8348978 : CollatzResearch.WordTrace tailWord_8348978 prefixEnd_8348978 4287038687813540818878755 := by
  unfold tailWord_8348978
  simp only [CollatzResearch.WordTrace]
  refine ⟨76128061086771518191613897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203008162898057381844303725 76128061086771518191613897)
  ·
    refine ⟨57096045815078638643710423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76128061086771518191613897 57096045815078638643710423)
    ·
      refine ⟨85644068722617957965565635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57096045815078638643710423 85644068722617957965565635)
      ·
        refine ⟨128466103083926936948348453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85644068722617957965565635 128466103083926936948348453)
        ·
          refine ⟨24087394328236300677815335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128466103083926936948348453 24087394328236300677815335)
          ·
            refine ⟨36131091492354451016723003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24087394328236300677815335 36131091492354451016723003)
            ·
              refine ⟨54196637238531676525084505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36131091492354451016723003 54196637238531676525084505)
              ·
                refine ⟨40647477928898757393813379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54196637238531676525084505 40647477928898757393813379)
                ·
                  refine ⟨60971216893348136090720069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40647477928898757393813379 60971216893348136090720069)
                  ·
                    refine ⟨11432103167502775517010013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60971216893348136090720069 11432103167502775517010013)
                    ·
                      refine ⟨4287038687813540818878755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11432103167502775517010013 4287038687813540818878755)
                      ·
                        rfl

theorem cell23_8348978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_8348978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8348978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8348978 prefixEnd_8348978 := by exact prefixLift 8348978
  have htrace : WordTrace (prefixWord ++ tailWord_8348978) baseStart_8348978 baseEnd_8348978 := by
    simpa [prefixWord, tailWord_8348978, baseEnd_8348978] using wordTrace_append hprefix tailTrace_8348978
  have hstable : (prefixWord ++ tailWord_8348978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8348978).length < 2 ^ (prefixWord ++ tailWord_8348978).sum := by decide
  have hdescent : baseEnd_8348978 < baseStart_8348978 := by decide
  rcases family_descends (prefixWord ++ tailWord_8348978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349032 : List Nat := [2, 1, 4, 2, 3, 2, 2, 1, 6]
def baseStart_8349032 : Nat := 118140960795 + 8349032 * 2 ^ 59
def prefixEnd_8349032 : Nat := 4983230072969 + 3 ^ 40 * 8349032 * 2
def baseEnd_8349032 : Nat := 476340712863209289733723

theorem tailTrace_8349032 : CollatzResearch.WordTrace tailWord_8349032 prefixEnd_8349032 476340712863209289733723 := by
  unfold tailWord_8349032
  simp only [CollatzResearch.WordTrace]
  refine ⟨152257106944445219994460675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203009475925926959992614233 152257106944445219994460675)
  ·
    refine ⟨228385660416667829991691013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152257106944445219994460675 228385660416667829991691013)
    ·
      refine ⟨42822311328125218123442065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228385660416667829991691013 42822311328125218123442065)
      ·
        refine ⟨32116733496093913592581549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42822311328125218123442065 32116733496093913592581549)
        ·
          refine ⟨12043775061035217597218081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32116733496093913592581549 12043775061035217597218081)
          ·
            refine ⟨9032831295776413197913561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12043775061035217597218081 9032831295776413197913561)
            ·
              refine ⟨6774623471832309898435171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9032831295776413197913561 6774623471832309898435171)
              ·
                refine ⟨10161935207748464847652757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6774623471832309898435171 10161935207748464847652757)
                ·
                  refine ⟨476340712863209289733723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10161935207748464847652757 476340712863209289733723)
                  ·
                    rfl

theorem cell23_8349032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 6].length) (baseStart_8349032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349032 prefixEnd_8349032 := by exact prefixLift 8349032
  have htrace : WordTrace (prefixWord ++ tailWord_8349032) baseStart_8349032 baseEnd_8349032 := by
    simpa [prefixWord, tailWord_8349032, baseEnd_8349032] using wordTrace_append hprefix tailTrace_8349032
  have hstable : (prefixWord ++ tailWord_8349032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349032).length < 2 ^ (prefixWord ++ tailWord_8349032).sum := by decide
  have hdescent : baseEnd_8349032 < baseStart_8349032 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349045 : List Nat := [1, 3, 4, 1, 3, 1, 1, 1, 3, 5]
def baseStart_8349045 : Nat := 118140960795 + 8349045 * 2 ^ 59
def prefixEnd_8349045 : Nat := 4983230072969 + 3 ^ 40 * 8349045 * 2
def baseEnd_8349045 : Nat := 1429024363672464018913649

theorem tailTrace_8349045 : CollatzResearch.WordTrace tailWord_8349045 prefixEnd_8349045 1429024363672464018913649 := by
  unfold tailWord_8349045
  simp only [CollatzResearch.WordTrace]
  refine ⟨304514688037843343209144589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203009792025228895472763059 304514688037843343209144589)
  ·
    refine ⟨114193008014191253703429221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304514688037843343209144589 114193008014191253703429221)
    ·
      refine ⟨21411189002660860069392979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114193008014191253703429221 21411189002660860069392979)
      ·
        refine ⟨32116783503991290104089469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21411189002660860069392979 32116783503991290104089469)
        ·
          refine ⟨12043793813996733789033551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32116783503991290104089469 12043793813996733789033551)
          ·
            refine ⟨18065690720995100683550327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12043793813996733789033551 18065690720995100683550327)
            ·
              refine ⟨27098536081492651025325491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18065690720995100683550327 27098536081492651025325491)
              ·
                refine ⟨40647804122238976537988237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27098536081492651025325491 40647804122238976537988237)
                ·
                  refine ⟨15242926545839616201745589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40647804122238976537988237 15242926545839616201745589)
                  ·
                    refine ⟨1429024363672464018913649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15242926545839616201745589 1429024363672464018913649)
                    ·
                      rfl

theorem cell23_8349045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_8349045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349045 prefixEnd_8349045 := by exact prefixLift 8349045
  have htrace : WordTrace (prefixWord ++ tailWord_8349045) baseStart_8349045 baseEnd_8349045 := by
    simpa [prefixWord, tailWord_8349045, baseEnd_8349045] using wordTrace_append hprefix tailTrace_8349045
  have hstable : (prefixWord ++ tailWord_8349045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349045).length < 2 ^ (prefixWord ++ tailWord_8349045).sum := by decide
  have hdescent : baseEnd_8349045 < baseStart_8349045 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349076 : List Nat := [2, 4, 2, 1, 2, 1, 4, 2, 1, 1, 3]
def baseStart_8349076 : Nat := 118140960795 + 8349076 * 2 ^ 59
def prefixEnd_8349076 : Nat := 4983230072969 + 3 ^ 40 * 8349076 * 2
def baseEnd_8349076 : Nat := 4287089008917681435453305

theorem tailTrace_8349076 : CollatzResearch.WordTrace tailWord_8349076 prefixEnd_8349076 4287089008917681435453305 := by
  unfold tailWord_8349076
  simp only [CollatzResearch.WordTrace]
  refine ⟨152257909350365517751761541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203010545800487357002348721 152257909350365517751761541)
  ·
    refine ⟨28548358003193534578455289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152257909350365517751761541 28548358003193534578455289)
    ·
      refine ⟨21411268502395150933841467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28548358003193534578455289 21411268502395150933841467)
      ·
        refine ⟨32116902753592726400762201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21411268502395150933841467 32116902753592726400762201)
        ·
          refine ⟨24087677065194544800571651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32116902753592726400762201 24087677065194544800571651)
          ·
            refine ⟨36131515597791817200857477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24087677065194544800571651 36131515597791817200857477)
            ·
              refine ⟨6774659174585965725160777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36131515597791817200857477 6774659174585965725160777)
              ·
                refine ⟨5080994380939474293870583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6774659174585965725160777 5080994380939474293870583)
                ·
                  refine ⟨7621491571409211440805875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5080994380939474293870583 7621491571409211440805875)
                  ·
                    refine ⟨11432237357113817161208813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7621491571409211440805875 11432237357113817161208813)
                    ·
                      refine ⟨4287089008917681435453305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11432237357113817161208813 4287089008917681435453305)
                      ·
                        rfl

theorem cell23_8349076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_8349076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349076 prefixEnd_8349076 := by exact prefixLift 8349076
  have htrace : WordTrace (prefixWord ++ tailWord_8349076) baseStart_8349076 baseEnd_8349076 := by
    simpa [prefixWord, tailWord_8349076, baseEnd_8349076] using wordTrace_append hprefix tailTrace_8349076
  have hstable : (prefixWord ++ tailWord_8349076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349076).length < 2 ^ (prefixWord ++ tailWord_8349076).sum := by decide
  have hdescent : baseEnd_8349076 < baseStart_8349076 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349082 : List Nat := [3, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2]
def baseStart_8349082 : Nat := 118140960795 + 8349082 * 2 ^ 59
def prefixEnd_8349082 : Nat := 4983230072969 + 3 ^ 40 * 8349082 * 2
def baseEnd_8349082 : Nat := 4287092089801608411978277

theorem tailTrace_8349082 : CollatzResearch.WordTrace tailWord_8349082 prefixEnd_8349082 4287092089801608411978277 := by
  unfold tailWord_8349082
  simp only [CollatzResearch.WordTrace]
  refine ⟨76129009384677324632060375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203010691692472865685494333 76129009384677324632060375)
  ·
    refine ⟨114193514077015986948090563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76129009384677324632060375 114193514077015986948090563)
    ·
      refine ⟨171290271115523980422135845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114193514077015986948090563 171290271115523980422135845)
      ·
        refine ⟨32116925834160746329150471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171290271115523980422135845 32116925834160746329150471)
        ·
          refine ⟨48175388751241119493725707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32116925834160746329150471 48175388751241119493725707)
          ·
            refine ⟨72263083126861679240588561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48175388751241119493725707 72263083126861679240588561)
            ·
              refine ⟨54197312345146259430441421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72263083126861679240588561 54197312345146259430441421)
              ·
                refine ⟨20323992129429847286415533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54197312345146259430441421 20323992129429847286415533)
                ·
                  refine ⟨7621497048536192732405825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20323992129429847286415533 7621497048536192732405825)
                  ·
                    refine ⟨5716122786402144549304369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7621497048536192732405825 5716122786402144549304369)
                    ·
                      refine ⟨4287092089801608411978277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5716122786402144549304369 4287092089801608411978277)
                      ·
                        rfl

theorem cell23_8349082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_8349082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349082 prefixEnd_8349082 := by exact prefixLift 8349082
  have htrace : WordTrace (prefixWord ++ tailWord_8349082) baseStart_8349082 baseEnd_8349082 := by
    simpa [prefixWord, tailWord_8349082, baseEnd_8349082] using wordTrace_append hprefix tailTrace_8349082
  have hstable : (prefixWord ++ tailWord_8349082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349082).length < 2 ^ (prefixWord ++ tailWord_8349082).sum := by decide
  have hdescent : baseEnd_8349082 < baseStart_8349082 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349085 : List Nat := [1, 4, 2, 1, 3, 1, 1, 2, 3, 2, 3]
def baseStart_8349085 : Nat := 118140960795 + 8349085 * 2 ^ 59
def prefixEnd_8349085 : Nat := 4983230072969 + 3 ^ 40 * 8349085 * 2
def baseEnd_8349085 : Nat := 4287093630243571900240763

theorem tailTrace_8349085 : CollatzResearch.WordTrace tailWord_8349085 prefixEnd_8349085 4287093630243571900240763 := by
  unfold tailWord_8349085
  simp only [CollatzResearch.WordTrace]
  refine ⟨304516146957698430040600709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203010764638465620027067139 304516146957698430040600709)
  ·
    refine ⟨57096777554568455632612633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304516146957698430040600709 57096777554568455632612633)
    ·
      refine ⟨42822583165926341724459475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57096777554568455632612633 42822583165926341724459475)
      ·
        refine ⟨64233874748889512586689213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42822583165926341724459475 64233874748889512586689213)
        ·
          refine ⟨24087703030833567220008455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64233874748889512586689213 24087703030833567220008455)
          ·
            refine ⟨36131554546250350830012683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24087703030833567220008455 36131554546250350830012683)
            ·
              refine ⟨54197331819375526245019025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36131554546250350830012683 54197331819375526245019025)
              ·
                refine ⟨40647998864531644683764269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54197331819375526245019025 40647998864531644683764269)
                ·
                  refine ⟨15242999574199366756411601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40647998864531644683764269 15242999574199366756411601)
                  ·
                    refine ⟨11432249680649525067308701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15242999574199366756411601 11432249680649525067308701)
                    ·
                      refine ⟨4287093630243571900240763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11432249680649525067308701 4287093630243571900240763)
                      ·
                        rfl

theorem cell23_8349085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_8349085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349085 prefixEnd_8349085 := by exact prefixLift 8349085
  have htrace : WordTrace (prefixWord ++ tailWord_8349085) baseStart_8349085 baseEnd_8349085 := by
    simpa [prefixWord, tailWord_8349085, baseEnd_8349085] using wordTrace_append hprefix tailTrace_8349085
  have hstable : (prefixWord ++ tailWord_8349085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349085).length < 2 ^ (prefixWord ++ tailWord_8349085).sum := by decide
  have hdescent : baseEnd_8349085 < baseStart_8349085 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349095 : List Nat := [1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_8349095 : Nat := 118140960795 + 8349095 * 2 ^ 59
def prefixEnd_8349095 : Nat := 4983230072969 + 3 ^ 40 * 8349095 * 2
def baseEnd_8349095 : Nat := 4287098765050116861115717

theorem tailTrace_8349095 : CollatzResearch.WordTrace tailWord_8349095 prefixEnd_8349095 4287098765050116861115717 := by
  unfold tailWord_8349095
  simp only [CollatzResearch.WordTrace]
  refine ⟨304516511687662201748464739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203011007791774801165643159 304516511687662201748464739)
  ·
    refine ⟨456774767531493302622697109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304516511687662201748464739 456774767531493302622697109)
    ·
      refine ⟨21411317228038748560438927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 456774767531493302622697109 21411317228038748560438927)
      ·
        refine ⟨32116975842058122840658391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21411317228038748560438927 32116975842058122840658391)
        ·
          refine ⟨48175463763087184260987587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32116975842058122840658391 48175463763087184260987587)
          ·
            refine ⟨72263195644630776391481381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48175463763087184260987587 72263195644630776391481381)
            ·
              refine ⟨13549349183368270573402759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72263195644630776391481381 13549349183368270573402759)
              ·
                refine ⟨20324023775052405860104139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13549349183368270573402759 20324023775052405860104139)
                ·
                  refine ⟨30486035662578608790156209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20324023775052405860104139 30486035662578608790156209)
                  ·
                    refine ⟨22864526746933956592617157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30486035662578608790156209 22864526746933956592617157)
                    ·
                      refine ⟨4287098765050116861115717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22864526746933956592617157 4287098765050116861115717)
                      ·
                        rfl

theorem cell23_8349095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_8349095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349095 prefixEnd_8349095 := by exact prefixLift 8349095
  have htrace : WordTrace (prefixWord ++ tailWord_8349095) baseStart_8349095 baseEnd_8349095 := by
    simpa [prefixWord, tailWord_8349095, baseEnd_8349095] using wordTrace_append hprefix tailTrace_8349095
  have hstable : (prefixWord ++ tailWord_8349095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349095).length < 2 ^ (prefixWord ++ tailWord_8349095).sum := by decide
  have hdescent : baseEnd_8349095 < baseStart_8349095 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349116 : List Nat := [2, 2, 2, 4, 3, 1, 2, 1, 1, 1, 4]
def baseStart_8349116 : Nat := 118140960795 + 8349116 * 2 ^ 59
def prefixEnd_8349116 : Nat := 4983230072969 + 3 ^ 40 * 8349116 * 2
def baseEnd_8349116 : Nat := 4287109548143861278953121

theorem tailTrace_8349116 : CollatzResearch.WordTrace tailWord_8349116 prefixEnd_8349116 4287109548143861278953121 := by
  unfold tailWord_8349116
  simp only [CollatzResearch.WordTrace]
  refine ⟨152258638810293061167489601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203011518413724081556652801 152258638810293061167489601)
  ·
    refine ⟨114193979107719795875617201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152258638810293061167489601 114193979107719795875617201)
    ·
      refine ⟨85645484330789846906712901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114193979107719795875617201 85645484330789846906712901)
      ·
        refine ⟨16058528312023096295008669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85645484330789846906712901 16058528312023096295008669)
        ·
          refine ⟨6021948117008661110628251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16058528312023096295008669 6021948117008661110628251)
          ·
            refine ⟨9032922175512991665942377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6021948117008661110628251 9032922175512991665942377)
            ·
              refine ⟨6774691631634743749456783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9032922175512991665942377 6774691631634743749456783)
              ·
                refine ⟨10162037447452115624185175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6774691631634743749456783 10162037447452115624185175)
                ·
                  refine ⟨15243056171178173436277763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10162037447452115624185175 15243056171178173436277763)
                  ·
                    refine ⟨22864584256767260154416645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15243056171178173436277763 22864584256767260154416645)
                    ·
                      refine ⟨4287109548143861278953121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22864584256767260154416645 4287109548143861278953121)
                      ·
                        rfl

theorem cell23_8349116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_8349116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349116 prefixEnd_8349116 := by exact prefixLift 8349116
  have htrace : WordTrace (prefixWord ++ tailWord_8349116) baseStart_8349116 baseEnd_8349116 := by
    simpa [prefixWord, tailWord_8349116, baseEnd_8349116] using wordTrace_append hprefix tailTrace_8349116
  have hstable : (prefixWord ++ tailWord_8349116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349116).length < 2 ^ (prefixWord ++ tailWord_8349116).sum := by decide
  have hdescent : baseEnd_8349116 < baseStart_8349116 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349132 : List Nat := [2, 2, 1, 4, 2, 2, 1, 1, 4, 1, 3]
def baseStart_8349132 : Nat := 118140960795 + 8349132 * 2 ^ 59
def prefixEnd_8349132 : Nat := 4983230072969 + 3 ^ 40 * 8349132 * 2
def baseEnd_8349132 : Nat := 4287117763834333216353047

theorem tailTrace_8349132 : CollatzResearch.WordTrace tailWord_8349132 prefixEnd_8349132 4287117763834333216353047 := by
  unfold tailWord_8349132
  simp only [CollatzResearch.WordTrace]
  refine ⟨152258930594264078533780825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203011907459018771378374433 152258930594264078533780825)
  ·
    refine ⟨114194197945698058900335619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152258930594264078533780825 114194197945698058900335619)
    ·
      refine ⟨171291296918547088350503429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114194197945698058900335619 171291296918547088350503429)
      ·
        refine ⟨32117118172227579065719393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171291296918547088350503429 32117118172227579065719393)
        ·
          refine ⟨24087838629170684299289545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32117118172227579065719393 24087838629170684299289545)
          ·
            refine ⟨18065878971878013224467159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24087838629170684299289545 18065878971878013224467159)
            ·
              refine ⟨27098818457817019836700739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18065878971878013224467159 27098818457817019836700739)
              ·
                refine ⟨40648227686725529755051109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27098818457817019836700739 40648227686725529755051109)
                ·
                  refine ⟨7621542691261036829072083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40648227686725529755051109 7621542691261036829072083)
                  ·
                    refine ⟨11432314036891555243608125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7621542691261036829072083 11432314036891555243608125)
                    ·
                      refine ⟨4287117763834333216353047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11432314036891555243608125 4287117763834333216353047)
                      ·
                        rfl

theorem cell23_8349132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_8349132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349132 prefixEnd_8349132 := by exact prefixLift 8349132
  have htrace : WordTrace (prefixWord ++ tailWord_8349132) baseStart_8349132 baseEnd_8349132 := by
    simpa [prefixWord, tailWord_8349132, baseEnd_8349132] using wordTrace_append hprefix tailTrace_8349132
  have hstable : (prefixWord ++ tailWord_8349132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349132).length < 2 ^ (prefixWord ++ tailWord_8349132).sum := by decide
  have hdescent : baseEnd_8349132 < baseStart_8349132 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349159 : List Nat := [1, 1, 5, 2, 1, 3, 2, 2, 1, 3, 2]
def baseStart_8349159 : Nat := 118140960795 + 8349159 * 2 ^ 59
def prefixEnd_8349159 : Nat := 4983230072969 + 3 ^ 40 * 8349159 * 2
def baseEnd_8349159 : Nat := 4287131627812004610715423

theorem tailTrace_8349159 : CollatzResearch.WordTrace tailWord_8349159 prefixEnd_8349159 4287131627812004610715423 := by
  unfold tailWord_8349159
  simp only [CollatzResearch.WordTrace]
  refine ⟨304518845959430340678794531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203012563972953560452529687 304518845959430340678794531)
  ·
    refine ⟨456778268939145511018191797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304518845959430340678794531 456778268939145511018191797)
    ·
      refine ⟨42822962713044891657955481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 456778268939145511018191797 42822962713044891657955481)
      ·
        refine ⟨32117222034783668743466611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42822962713044891657955481 32117222034783668743466611)
        ·
          refine ⟨48175833052175503115199917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32117222034783668743466611 48175833052175503115199917)
          ·
            refine ⟨18065937394565813668199969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48175833052175503115199917 18065937394565813668199969)
            ·
              refine ⟨13549453045924360251149977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18065937394565813668199969 13549453045924360251149977)
              ·
                refine ⟨10162089784443270188362483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13549453045924360251149977 10162089784443270188362483)
                ·
                  refine ⟨15243134676664905282543725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10162089784443270188362483 15243134676664905282543725)
                  ·
                    refine ⟨5716175503749339480953897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15243134676664905282543725 5716175503749339480953897)
                    ·
                      refine ⟨4287131627812004610715423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5716175503749339480953897 4287131627812004610715423)
                      ·
                        rfl

theorem cell23_8349159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_8349159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349159 prefixEnd_8349159 := by exact prefixLift 8349159
  have htrace : WordTrace (prefixWord ++ tailWord_8349159) baseStart_8349159 baseEnd_8349159 := by
    simpa [prefixWord, tailWord_8349159, baseEnd_8349159] using wordTrace_append hprefix tailTrace_8349159
  have hstable : (prefixWord ++ tailWord_8349159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349159).length < 2 ^ (prefixWord ++ tailWord_8349159).sum := by decide
  have hdescent : baseEnd_8349159 < baseStart_8349159 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349248 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 5]
def baseStart_8349248 : Nat := 118140960795 + 8349248 * 2 ^ 59
def prefixEnd_8349248 : Nat := 4983230072969 + 3 ^ 40 * 8349248 * 2
def baseEnd_8349248 : Nat := 4287177327590254762502513

theorem tailTrace_8349248 : CollatzResearch.WordTrace tailWord_8349248 prefixEnd_8349248 4287177327590254762502513 := by
  unfold tailWord_8349248
  simp only [CollatzResearch.WordTrace]
  refine ⟨152261046028053954439392199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203014728037405272585856265 152261046028053954439392199)
  ·
    refine ⟨228391569042080931659088299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152261046028053954439392199 228391569042080931659088299)
    ·
      refine ⟨342587353563121397488632449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228391569042080931659088299 342587353563121397488632449)
      ·
        refine ⟨256940515172341048116474337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342587353563121397488632449 256940515172341048116474337)
        ·
          refine ⟨192705386379255786087355753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256940515172341048116474337 192705386379255786087355753)
          ·
            refine ⟨144529039784441839565516815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192705386379255786087355753 144529039784441839565516815)
            ·
              refine ⟨216793559676662759348275223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144529039784441839565516815 216793559676662759348275223)
              ·
                refine ⟨325190339514994139022412835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216793559676662759348275223 325190339514994139022412835)
                ·
                  refine ⟨487785509272491208533619253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 325190339514994139022412835 487785509272491208533619253)
                  ·
                    refine ⟨45729891494296050800026805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 487785509272491208533619253 45729891494296050800026805)
                    ·
                      refine ⟨4287177327590254762502513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45729891494296050800026805 4287177327590254762502513)
                      ·
                        rfl

theorem cell23_8349248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_8349248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349248 prefixEnd_8349248 := by exact prefixLift 8349248
  have htrace : WordTrace (prefixWord ++ tailWord_8349248) baseStart_8349248 baseEnd_8349248 := by
    simpa [prefixWord, tailWord_8349248, baseEnd_8349248] using wordTrace_append hprefix tailTrace_8349248
  have hstable : (prefixWord ++ tailWord_8349248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349248).length < 2 ^ (prefixWord ++ tailWord_8349248).sum := by decide
  have hdescent : baseEnd_8349248 < baseStart_8349248 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349265 : List Nat := [1, 2, 2, 1, 3, 2, 2, 2, 1, 4, 3]
def baseStart_8349265 : Nat := 118140960795 + 8349265 * 2 ^ 59
def prefixEnd_8349265 : Nat := 4983230072969 + 3 ^ 40 * 8349265 * 2
def baseEnd_8349265 : Nat := 4287186056761381195989935

theorem tailTrace_8349265 : CollatzResearch.WordTrace tailWord_8349265 prefixEnd_8349265 4287186056761381195989935 := by
  unfold tailWord_8349265
  simp only [CollatzResearch.WordTrace]
  refine ⟨304522712097046320782153249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203015141398030880521435499 304522712097046320782153249)
  ·
    refine ⟨228392034072784740586614937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304522712097046320782153249 228392034072784740586614937)
    ·
      refine ⟨171294025554588555439961203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228392034072784740586614937 171294025554588555439961203)
      ·
        refine ⟨256941038331882833159941805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171294025554588555439961203 256941038331882833159941805)
        ·
          refine ⟨96352889374456062434978177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256941038331882833159941805 96352889374456062434978177)
          ·
            refine ⟨72264667030842046826233633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96352889374456062434978177 72264667030842046826233633)
            ·
              refine ⟨54198500273131535119675225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72264667030842046826233633 54198500273131535119675225)
              ·
                refine ⟨40648875204848651339756419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54198500273131535119675225 40648875204848651339756419)
                ·
                  refine ⟨60973312807272977009634629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40648875204848651339756419 60973312807272977009634629)
                  ·
                    refine ⟨11432496151363683189306493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60973312807272977009634629 11432496151363683189306493)
                    ·
                      refine ⟨4287186056761381195989935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11432496151363683189306493 4287186056761381195989935)
                      ·
                        rfl

theorem cell23_8349265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 4, 3].length) (baseStart_8349265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349265 prefixEnd_8349265 := by exact prefixLift 8349265
  have htrace : WordTrace (prefixWord ++ tailWord_8349265) baseStart_8349265 baseEnd_8349265 := by
    simpa [prefixWord, tailWord_8349265, baseEnd_8349265] using wordTrace_append hprefix tailTrace_8349265
  have hstable : (prefixWord ++ tailWord_8349265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349265).length < 2 ^ (prefixWord ++ tailWord_8349265).sum := by decide
  have hdescent : baseEnd_8349265 < baseStart_8349265 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349302 : List Nat := [5, 1, 1, 2, 2, 2, 1, 1, 8]
def baseStart_8349302 : Nat := 118140960795 + 8349302 * 2 ^ 59
def prefixEnd_8349302 : Nat := 4983230072969 + 3 ^ 40 * 8349302 * 2
def baseEnd_8349302 : Nat := 476356117282844172358585

theorem tailTrace_8349302 : CollatzResearch.WordTrace tailWord_8349302 prefixEnd_8349302 476356117282844172358585 := by
  unfold tailWord_8349302
  simp only [CollatzResearch.WordTrace]
  refine ⟨19032753849869517256328135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203016041065274850734166773 19032753849869517256328135)
  ·
    refine ⟨28549130774804275884492203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19032753849869517256328135 28549130774804275884492203)
    ·
      refine ⟨42823696162206413826738305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28549130774804275884492203 42823696162206413826738305)
      ·
        refine ⟨32117772121654810370053729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42823696162206413826738305 32117772121654810370053729)
        ·
          refine ⟨24088329091241107777540297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32117772121654810370053729 24088329091241107777540297)
          ·
            refine ⟨18066246818430830833155223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24088329091241107777540297 18066246818430830833155223)
            ·
              refine ⟨27099370227646246249732835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18066246818430830833155223 27099370227646246249732835)
              ·
                refine ⟨40649055341469369374599253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27099370227646246249732835 40649055341469369374599253)
                ·
                  refine ⟨476356117282844172358585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40649055341469369374599253 476356117282844172358585)
                  ·
                    rfl

theorem cell23_8349302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_8349302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349302 prefixEnd_8349302 := by exact prefixLift 8349302
  have htrace : WordTrace (prefixWord ++ tailWord_8349302) baseStart_8349302 baseEnd_8349302 := by
    simpa [prefixWord, tailWord_8349302, baseEnd_8349302] using wordTrace_append hprefix tailTrace_8349302
  have hstable : (prefixWord ++ tailWord_8349302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349302).length < 2 ^ (prefixWord ++ tailWord_8349302).sum := by decide
  have hdescent : baseEnd_8349302 < baseStart_8349302 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349362 : List Nat := [3, 2, 1, 1, 1, 2, 4, 1, 4, 4]
def baseStart_8349362 : Nat := 118140960795 + 8349362 * 2 ^ 59
def prefixEnd_8349362 : Nat := 4983230072969 + 3 ^ 40 * 8349362 * 2
def baseEnd_8349362 : Nat := 1429078621461622438825663

theorem tailTrace_8349362 : CollatzResearch.WordTrace tailWord_8349362 prefixEnd_8349362 1429078621461622438825663 := by
  unfold tailWord_8349362
  simp only [CollatzResearch.WordTrace]
  refine ⟨76131562494423726587108585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203017499985129937565622893 76131562494423726587108585)
  ·
    refine ⟨57098671870817794940331439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76131562494423726587108585 57098671870817794940331439)
    ·
      refine ⟨85648007806226692410497159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57098671870817794940331439 85648007806226692410497159)
      ·
        refine ⟨128472011709340038615745739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85648007806226692410497159 128472011709340038615745739)
        ·
          refine ⟨192708017564010057923618609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128472011709340038615745739 192708017564010057923618609)
          ·
            refine ⟨144531013173007543442713957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192708017564010057923618609 144531013173007543442713957)
            ·
              refine ⟨27099564969938914395508867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144531013173007543442713957 27099564969938914395508867)
              ·
                refine ⟨40649347454908371593263301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27099564969938914395508867 40649347454908371593263301)
                ·
                  refine ⟨7621752647795319673736869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40649347454908371593263301 7621752647795319673736869)
                  ·
                    refine ⟨1429078621461622438825663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7621752647795319673736869 1429078621461622438825663)
                    ·
                      rfl

theorem cell23_8349362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_8349362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349362 prefixEnd_8349362 := by exact prefixLift 8349362
  have htrace : WordTrace (prefixWord ++ tailWord_8349362) baseStart_8349362 baseEnd_8349362 := by
    simpa [prefixWord, tailWord_8349362, baseEnd_8349362] using wordTrace_append hprefix tailTrace_8349362
  have hstable : (prefixWord ++ tailWord_8349362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349362).length < 2 ^ (prefixWord ++ tailWord_8349362).sum := by decide
  have hdescent : baseEnd_8349362 < baseStart_8349362 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349372 : List Nat := [2, 2, 2, 3, 1, 2, 2, 2, 1, 1, 5]
def baseStart_8349372 : Nat := 118140960795 + 8349372 * 2 ^ 59
def prefixEnd_8349372 : Nat := 4983230072969 + 3 ^ 40 * 8349372 * 2
def baseEnd_8349372 : Nat := 4287240999191412277351943

theorem tailTrace_8349372 : CollatzResearch.WordTrace tailWord_8349372 prefixEnd_8349372 4287240999191412277351943 := by
  unfold tailWord_8349372
  simp only [CollatzResearch.WordTrace]
  refine ⟨152263307353829339028149185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203017743138439118704198913 152263307353829339028149185)
  ·
    refine ⟨114197480515372004271111889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152263307353829339028149185 114197480515372004271111889)
    ·
      refine ⟨85648110386529003203333917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114197480515372004271111889 85648110386529003203333917)
      ·
        refine ⟨32118041394948376201250219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85648110386529003203333917 32118041394948376201250219)
        ·
          refine ⟨48177062092422564301875329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32118041394948376201250219 48177062092422564301875329)
          ·
            refine ⟨36132796569316923226406497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48177062092422564301875329 36132796569316923226406497)
            ·
              refine ⟨27099597426987692419804873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36132796569316923226406497 27099597426987692419804873)
              ·
                refine ⟨20324698070240769314853655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27099597426987692419804873 20324698070240769314853655)
                ·
                  refine ⟨30487047105361153972280483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20324698070240769314853655 30487047105361153972280483)
                  ·
                    refine ⟨45730570658041730958420725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30487047105361153972280483 45730570658041730958420725)
                    ·
                      refine ⟨4287240999191412277351943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45730570658041730958420725 4287240999191412277351943)
                      ·
                        rfl

theorem cell23_8349372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_8349372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349372 prefixEnd_8349372 := by exact prefixLift 8349372
  have htrace : WordTrace (prefixWord ++ tailWord_8349372) baseStart_8349372 baseEnd_8349372 := by
    simpa [prefixWord, tailWord_8349372, baseEnd_8349372] using wordTrace_append hprefix tailTrace_8349372
  have hstable : (prefixWord ++ tailWord_8349372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349372).length < 2 ^ (prefixWord ++ tailWord_8349372).sum := by decide
  have hdescent : baseEnd_8349372 < baseStart_8349372 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349375 : List Nat := [1, 1, 2, 2, 2, 3, 4, 8]
def baseStart_8349375 : Nat := 118140960795 + 8349375 * 2 ^ 59
def prefixEnd_8349375 : Nat := 4983230072969 + 3 ^ 40 * 8349375 * 2
def baseEnd_8349375 : Nat := 158786760727162065393127

theorem tailTrace_8349375 : CollatzResearch.WordTrace tailWord_8349375 prefixEnd_8349375 158786760727162065393127 := by
  unfold tailWord_8349375
  simp only [CollatzResearch.WordTrace]
  refine ⟨304526724126647809568657579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203017816084431873045771719 304526724126647809568657579)
  ·
    refine ⟨456790086189971714352986369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304526724126647809568657579 456790086189971714352986369)
    ·
      refine ⟨342592564642478785764739777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456790086189971714352986369 342592564642478785764739777)
      ·
        refine ⟨256944423481859089323554833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342592564642478785764739777 256944423481859089323554833)
        ·
          refine ⟨192708317611394316992666125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256944423481859089323554833 192708317611394316992666125)
          ·
            refine ⟨72265619104272868872249797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192708317611394316992666125 72265619104272868872249797)
            ·
              refine ⟨13549803582051162913546837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72265619104272868872249797 13549803582051162913546837)
              ·
                refine ⟨158786760727162065393127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13549803582051162913546837 158786760727162065393127)
                ·
                  rfl

theorem cell23_8349375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 8].length) (baseStart_8349375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349375 prefixEnd_8349375 := by exact prefixLift 8349375
  have htrace : WordTrace (prefixWord ++ tailWord_8349375) baseStart_8349375 baseEnd_8349375 := by
    simpa [prefixWord, tailWord_8349375, baseEnd_8349375] using wordTrace_append hprefix tailTrace_8349375
  have hstable : (prefixWord ++ tailWord_8349375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349375).length < 2 ^ (prefixWord ++ tailWord_8349375).sum := by decide
  have hdescent : baseEnd_8349375 < baseStart_8349375 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349386 : List Nat := [3, 1, 2, 1, 5, 2, 1, 2, 1, 1, 4]
def baseStart_8349386 : Nat := 118140960795 + 8349386 * 2 ^ 59
def prefixEnd_8349386 : Nat := 4983230072969 + 3 ^ 40 * 8349386 * 2
def baseEnd_8349386 : Nat := 4287248187920575222576879

theorem tailTrace_8349386 : CollatzResearch.WordTrace tailWord_8349386 prefixEnd_8349386 4287248187920575222576879 := by
  unfold tailWord_8349386
  simp only [CollatzResearch.WordTrace]
  refine ⟨76131781332401989611827003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203018083553071972298205341 76131781332401989611827003)
  ·
    refine ⟨114197671998602984417740505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76131781332401989611827003 114197671998602984417740505)
    ·
      refine ⟨85648253998952238313305379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114197671998602984417740505 85648253998952238313305379)
      ·
        refine ⟨128472380998428357469958069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85648253998952238313305379 128472380998428357469958069)
        ·
          refine ⟨12044285718602658512808569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128472380998428357469958069 12044285718602658512808569)
          ·
            refine ⟨9033214288951993884606427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12044285718602658512808569 9033214288951993884606427)
            ·
              refine ⟨13549821433427990826909641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9033214288951993884606427 13549821433427990826909641)
              ·
                refine ⟨10162366075070993120182231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13549821433427990826909641 10162366075070993120182231)
                ·
                  refine ⟨15243549112606489680273347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10162366075070993120182231 15243549112606489680273347)
                  ·
                    refine ⟨22865323668909734520410021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15243549112606489680273347 22865323668909734520410021)
                    ·
                      refine ⟨4287248187920575222576879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22865323668909734520410021 4287248187920575222576879)
                      ·
                        rfl

theorem cell23_8349386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_8349386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349386 prefixEnd_8349386 := by exact prefixLift 8349386
  have htrace : WordTrace (prefixWord ++ tailWord_8349386) baseStart_8349386 baseEnd_8349386 := by
    simpa [prefixWord, tailWord_8349386, baseEnd_8349386] using wordTrace_append hprefix tailTrace_8349386
  have hstable : (prefixWord ++ tailWord_8349386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349386).length < 2 ^ (prefixWord ++ tailWord_8349386).sum := by decide
  have hdescent : baseEnd_8349386 < baseStart_8349386 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349402 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3]
def baseStart_8349402 : Nat := 118140960795 + 8349402 * 2 ^ 59
def prefixEnd_8349402 : Nat := 4983230072969 + 3 ^ 40 * 8349402 * 2
def baseEnd_8349402 : Nat := 4287256403611047159976805

theorem tailTrace_8349402 : CollatzResearch.WordTrace tailWord_8349402 prefixEnd_8349402 4287256403611047159976805 := by
  unfold tailWord_8349402
  simp only [CollatzResearch.WordTrace]
  refine ⟨76131927224387498294972615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203018472598366662119926973 76131927224387498294972615)
  ·
    refine ⟨114197890836581247442458923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76131927224387498294972615 114197890836581247442458923)
    ·
      refine ⟨171296836254871871163688385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114197890836581247442458923 171296836254871871163688385)
      ·
        refine ⟨128472627191153903372766289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171296836254871871163688385 128472627191153903372766289)
        ·
          refine ⟨96354470393365427529574717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128472627191153903372766289 96354470393365427529574717)
          ·
            refine ⟨36132926397512035323590519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96354470393365427529574717 36132926397512035323590519)
            ·
              refine ⟨54199389596268052985385779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36132926397512035323590519 54199389596268052985385779)
              ·
                refine ⟨81299084394402079478078669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54199389596268052985385779 81299084394402079478078669)
                ·
                  refine ⟨30487156647900779804279501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81299084394402079478078669 30487156647900779804279501)
                  ·
                    refine ⟨11432683742962792426604813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30487156647900779804279501 11432683742962792426604813)
                    ·
                      refine ⟨4287256403611047159976805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11432683742962792426604813 4287256403611047159976805)
                      ·
                        rfl

theorem cell23_8349402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_8349402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349402 prefixEnd_8349402 := by exact prefixLift 8349402
  have htrace : WordTrace (prefixWord ++ tailWord_8349402) baseStart_8349402 baseEnd_8349402 := by
    simpa [prefixWord, tailWord_8349402, baseEnd_8349402] using wordTrace_append hprefix tailTrace_8349402
  have hstable : (prefixWord ++ tailWord_8349402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349402).length < 2 ^ (prefixWord ++ tailWord_8349402).sum := by decide
  have hdescent : baseEnd_8349402 < baseStart_8349402 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349419 : List Nat := [1, 1, 1, 1, 2, 4, 3, 4, 2, 1, 3]
def baseStart_8349419 : Nat := 118140960795 + 8349419 * 2 ^ 59
def prefixEnd_8349419 : Nat := 4983230072969 + 3 ^ 40 * 8349419 * 2
def baseEnd_8349419 : Nat := 4287265132782173593464227

theorem tailTrace_8349419 : CollatzResearch.WordTrace tailWord_8349419 prefixEnd_8349419 4287265132782173593464227 := by
  unfold tailWord_8349419
  simp only [CollatzResearch.WordTrace]
  refine ⟨304528328938488405083259311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203018885958992270055506207 304528328938488405083259311)
  ·
    refine ⟨456792493407732607624888967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304528328938488405083259311 456792493407732607624888967)
    ·
      refine ⟨685188740111598911437333451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456792493407732607624888967 685188740111598911437333451)
      ·
        refine ⟨1027783110167398367156000177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685188740111598911437333451 1027783110167398367156000177)
        ·
          refine ⟨770837332625548775367000133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1027783110167398367156000177 770837332625548775367000133)
          ·
            refine ⟨144531999867290395381312525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 770837332625548775367000133 144531999867290395381312525)
            ·
              refine ⟨54199499950233898267992197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144531999867290395381312525 54199499950233898267992197)
              ·
                refine ⟨10162406240668855925248537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54199499950233898267992197 10162406240668855925248537)
                ·
                  refine ⟨7621804680501641943936403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10162406240668855925248537 7621804680501641943936403)
                  ·
                    refine ⟨11432707020752462915904605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7621804680501641943936403 11432707020752462915904605)
                    ·
                      refine ⟨4287265132782173593464227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11432707020752462915904605 4287265132782173593464227)
                      ·
                        rfl

theorem cell23_8349419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2, 1, 3].length) (baseStart_8349419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349419 prefixEnd_8349419 := by exact prefixLift 8349419
  have htrace : WordTrace (prefixWord ++ tailWord_8349419) baseStart_8349419 baseEnd_8349419 := by
    simpa [prefixWord, tailWord_8349419, baseEnd_8349419] using wordTrace_append hprefix tailTrace_8349419
  have hstable : (prefixWord ++ tailWord_8349419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349419).length < 2 ^ (prefixWord ++ tailWord_8349419).sum := by decide
  have hdescent : baseEnd_8349419 < baseStart_8349419 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349463 : List Nat := [1, 1, 3, 4, 2, 1, 4, 1, 1, 3, 2]
def baseStart_8349463 : Nat := 118140960795 + 8349463 * 2 ^ 59
def prefixEnd_8349463 : Nat := 4983230072969 + 3 ^ 40 * 8349463 * 2
def baseEnd_8349463 : Nat := 4287287725930971421314025

theorem tailTrace_8349463 : CollatzResearch.WordTrace tailWord_8349463 prefixEnd_8349463 4287287725930971421314025 := by
  unfold tailWord_8349463
  simp only [CollatzResearch.WordTrace]
  refine ⟨304529933750329000597861043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203019955833552667065240695 304529933750329000597861043)
  ·
    refine ⟨456794900625493500896791565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304529933750329000597861043 456794900625493500896791565)
    ·
      refine ⟨171298087734560062836296837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456794900625493500896791565 171298087734560062836296837)
      ·
        refine ⟨32118391450230011781805657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171298087734560062836296837 32118391450230011781805657)
        ·
          refine ⟨24088793587672508836354243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32118391450230011781805657 24088793587672508836354243)
          ·
            refine ⟨36133190381508763254531365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24088793587672508836354243 36133190381508763254531365)
            ·
              refine ⟨6774973196532893110224631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36133190381508763254531365 6774973196532893110224631)
              ·
                refine ⟨10162459794799339665336947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6774973196532893110224631 10162459794799339665336947)
                ·
                  refine ⟨15243689692199009498005421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10162459794799339665336947 15243689692199009498005421)
                  ·
                    refine ⟨5716383634574628561752033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15243689692199009498005421 5716383634574628561752033)
                    ·
                      refine ⟨4287287725930971421314025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5716383634574628561752033 4287287725930971421314025)
                      ·
                        rfl

theorem cell23_8349463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_8349463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349463 prefixEnd_8349463 := by exact prefixLift 8349463
  have htrace : WordTrace (prefixWord ++ tailWord_8349463) baseStart_8349463 baseEnd_8349463 := by
    simpa [prefixWord, tailWord_8349463, baseEnd_8349463] using wordTrace_append hprefix tailTrace_8349463
  have hstable : (prefixWord ++ tailWord_8349463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349463).length < 2 ^ (prefixWord ++ tailWord_8349463).sum := by decide
  have hdescent : baseEnd_8349463 < baseStart_8349463 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349470 : List Nat := [4, 3, 2, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_8349470 : Nat := 118140960795 + 8349470 * 2 ^ 59
def prefixEnd_8349470 : Nat := 4983230072969 + 3 ^ 40 * 8349470 * 2
def baseEnd_8349470 : Nat := 4287291320295552893926493

theorem tailTrace_8349470 : CollatzResearch.WordTrace tailWord_8349470 prefixEnd_8349470 4287291320295552893926493 := by
  unfold tailWord_8349470
  simp only [CollatzResearch.WordTrace]
  refine ⟨38066273632662955099170733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203020126040869093862243909 38066273632662955099170733)
  ·
    refine ⟨14274852612248608162189025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38066273632662955099170733 14274852612248608162189025)
    ·
      refine ⟨10706139459186456121641769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14274852612248608162189025 10706139459186456121641769)
      ·
        refine ⟨8029604594389842091231327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10706139459186456121641769 8029604594389842091231327)
        ·
          refine ⟨12044406891584763136846991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8029604594389842091231327 12044406891584763136846991)
          ·
            refine ⟨18066610337377144705270487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12044406891584763136846991 18066610337377144705270487)
            ·
              refine ⟨27099915506065717057905731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18066610337377144705270487 27099915506065717057905731)
              ·
                refine ⟨40649873259098575586858597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27099915506065717057905731 40649873259098575586858597)
                ·
                  refine ⟨7621851236080982922535987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40649873259098575586858597 7621851236080982922535987)
                  ·
                    refine ⟨11432776854121474383803981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7621851236080982922535987 11432776854121474383803981)
                    ·
                      refine ⟨4287291320295552893926493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11432776854121474383803981 4287291320295552893926493)
                      ·
                        rfl

theorem cell23_8349470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_8349470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349470 prefixEnd_8349470 := by exact prefixLift 8349470
  have htrace : WordTrace (prefixWord ++ tailWord_8349470) baseStart_8349470 baseEnd_8349470 := by
    simpa [prefixWord, tailWord_8349470, baseEnd_8349470] using wordTrace_append hprefix tailTrace_8349470
  have hstable : (prefixWord ++ tailWord_8349470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349470).length < 2 ^ (prefixWord ++ tailWord_8349470).sum := by decide
  have hdescent : baseEnd_8349470 < baseStart_8349470 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349472 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 4]
def baseStart_8349472 : Nat := 118140960795 + 8349472 * 2 ^ 59
def prefixEnd_8349472 : Nat := 4983230072969 + 3 ^ 40 * 8349472 * 2
def baseEnd_8349472 : Nat := 4287292347256861886101483

theorem tailTrace_8349472 : CollatzResearch.WordTrace tailWord_8349472 prefixEnd_8349472 4287292347256861886101483 := by
  unfold tailWord_8349472
  simp only [CollatzResearch.WordTrace]
  refine ⟨152265131003648197567469335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203020174671530930089959113 152265131003648197567469335)
  ·
    refine ⟨228397696505472296351204003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152265131003648197567469335 228397696505472296351204003)
    ·
      refine ⟨342596544758208444526806005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228397696505472296351204003 342596544758208444526806005)
      ·
        refine ⟨32118426071082041674388063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 342596544758208444526806005 32118426071082041674388063)
        ·
          refine ⟨48177639106623062511582095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32118426071082041674388063 48177639106623062511582095)
          ·
            refine ⟨72266458659934593767373143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48177639106623062511582095 72266458659934593767373143)
            ·
              refine ⟨108399687989901890651059715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72266458659934593767373143 108399687989901890651059715)
              ·
                refine ⟨162599531984852835976589573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108399687989901890651059715 162599531984852835976589573)
                ·
                  refine ⟨30487412247159906745610545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162599531984852835976589573 30487412247159906745610545)
                  ·
                    refine ⟨22865559185369930059207909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30487412247159906745610545 22865559185369930059207909)
                    ·
                      refine ⟨4287292347256861886101483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22865559185369930059207909 4287292347256861886101483)
                      ·
                        rfl

theorem cell23_8349472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_8349472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349472 prefixEnd_8349472 := by exact prefixLift 8349472
  have htrace : WordTrace (prefixWord ++ tailWord_8349472) baseStart_8349472 baseEnd_8349472 := by
    simpa [prefixWord, tailWord_8349472, baseEnd_8349472] using wordTrace_append hprefix tailTrace_8349472
  have hstable : (prefixWord ++ tailWord_8349472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349472).length < 2 ^ (prefixWord ++ tailWord_8349472).sum := by decide
  have hdescent : baseEnd_8349472 < baseStart_8349472 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349493 : List Nat := [1, 3, 3, 1, 4, 2, 1, 1, 1, 4, 2]
def baseStart_8349493 : Nat := 118140960795 + 8349493 * 2 ^ 59
def prefixEnd_8349493 : Nat := 4983230072969 + 3 ^ 40 * 8349493 * 2
def baseEnd_8349493 : Nat := 4287303130350606303938887

theorem tailTrace_8349493 : CollatzResearch.WordTrace tailWord_8349493 prefixEnd_8349493 4287303130350606303938887 := by
  unfold tailWord_8349493
  simp only [CollatzResearch.WordTrace]
  refine ⟨304531027940220315721453133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203020685293480210480968755 304531027940220315721453133)
  ·
    refine ⟨114199135477582618395544925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304531027940220315721453133 114199135477582618395544925)
    ·
      refine ⟨42824675804093481898329347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114199135477582618395544925 42824675804093481898329347)
      ·
        refine ⟨64237013706140222847494021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42824675804093481898329347 64237013706140222847494021)
        ·
          refine ⟨12044440069901291783905129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64237013706140222847494021 12044440069901291783905129)
          ·
            refine ⟨9033330052425968837928847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12044440069901291783905129 9033330052425968837928847)
            ·
              refine ⟨13549995078638953256893271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9033330052425968837928847 13549995078638953256893271)
              ·
                refine ⟨20324992617958429885339907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13549995078638953256893271 20324992617958429885339907)
                ·
                  refine ⟨30487488926937644828009861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20324992617958429885339907 30487488926937644828009861)
                  ·
                    refine ⟨5716404173800808405251849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30487488926937644828009861 5716404173800808405251849)
                    ·
                      refine ⟨4287303130350606303938887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5716404173800808405251849 4287303130350606303938887)
                      ·
                        rfl

theorem cell23_8349493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_8349493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349493 prefixEnd_8349493 := by exact prefixLift 8349493
  have htrace : WordTrace (prefixWord ++ tailWord_8349493) baseStart_8349493 baseEnd_8349493 := by
    simpa [prefixWord, tailWord_8349493, baseEnd_8349493] using wordTrace_append hprefix tailTrace_8349493
  have hstable : (prefixWord ++ tailWord_8349493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349493).length < 2 ^ (prefixWord ++ tailWord_8349493).sum := by decide
  have hdescent : baseEnd_8349493 < baseStart_8349493 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349510 : List Nat := [6, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2]
def baseStart_8349510 : Nat := 118140960795 + 8349510 * 2 ^ 59
def prefixEnd_8349510 : Nat := 4983230072969 + 3 ^ 40 * 8349510 * 2
def baseEnd_8349510 : Nat := 4287311859521732737426309

theorem tailTrace_8349510 : CollatzResearch.WordTrace tailWord_8349510 prefixEnd_8349510 4287311859521732737426309 := by
  unfold tailWord_8349510
  simp only [CollatzResearch.WordTrace]
  refine ⟨9516613999411210238275687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 203021098654105818416547989 9516613999411210238275687)
  ·
    refine ⟨14274920999116815357413531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9516613999411210238275687 14274920999116815357413531)
    ·
      refine ⟨21412381498675223036120297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14274920999116815357413531 21412381498675223036120297)
      ·
        refine ⟨16059286124006417277090223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21412381498675223036120297 16059286124006417277090223)
        ·
          refine ⟨24088929186009625915635335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16059286124006417277090223 24088929186009625915635335)
          ·
            refine ⟨36133393779014438873453003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24088929186009625915635335 36133393779014438873453003)
            ·
              refine ⟨54200090668521658310179505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36133393779014438873453003 54200090668521658310179505)
              ·
                refine ⟨40650068001391243732634629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54200090668521658310179505 40650068001391243732634629)
                ·
                  refine ⟨7621887750260858199868993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40650068001391243732634629 7621887750260858199868993)
                  ·
                    refine ⟨5716415812695643649901745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7621887750260858199868993 5716415812695643649901745)
                    ·
                      refine ⟨4287311859521732737426309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5716415812695643649901745 4287311859521732737426309)
                      ·
                        rfl

theorem cell23_8349510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_8349510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349510 prefixEnd_8349510 := by exact prefixLift 8349510
  have htrace : WordTrace (prefixWord ++ tailWord_8349510) baseStart_8349510 baseEnd_8349510 := by
    simpa [prefixWord, tailWord_8349510, baseEnd_8349510] using wordTrace_append hprefix tailTrace_8349510
  have hstable : (prefixWord ++ tailWord_8349510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349510).length < 2 ^ (prefixWord ++ tailWord_8349510).sum := by decide
  have hdescent : baseEnd_8349510 < baseStart_8349510 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349512 : List Nat := [2, 1, 3, 1, 1, 4, 2, 1, 1, 7]
def baseStart_8349512 : Nat := 118140960795 + 8349512 * 2 ^ 59
def prefixEnd_8349512 : Nat := 4983230072969 + 3 ^ 40 * 8349512 * 2
def baseEnd_8349512 : Nat := 1429104295494347243200433

theorem tailTrace_8349512 : CollatzResearch.WordTrace tailWord_8349512 prefixEnd_8349512 1429104295494347243200433 := by
  unfold tailWord_8349512
  simp only [CollatzResearch.WordTrace]
  refine ⟨152265860463575740983197395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203021147284767654644263193 152265860463575740983197395)
  ·
    refine ⟨228398790695363611474796093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152265860463575740983197395 228398790695363611474796093)
    ·
      refine ⟨85649546510761354303048535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228398790695363611474796093 85649546510761354303048535)
      ·
        refine ⟨128474319766142031454572803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85649546510761354303048535 128474319766142031454572803)
        ·
          refine ⟨192711479649213047181859205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128474319766142031454572803 192711479649213047181859205)
          ·
            refine ⟨36133402434227446346598601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192711479649213047181859205 36133402434227446346598601)
            ·
              refine ⟨27100051825670584759948951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36133402434227446346598601 27100051825670584759948951)
              ·
                refine ⟨40650077738505877139923427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27100051825670584759948951 40650077738505877139923427)
                ·
                  refine ⟨60975116607758815709885141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40650077738505877139923427 60975116607758815709885141)
                  ·
                    refine ⟨1429104295494347243200433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60975116607758815709885141 1429104295494347243200433)
                    ·
                      rfl

theorem cell23_8349512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_8349512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349512 prefixEnd_8349512 := by exact prefixLift 8349512
  have htrace : WordTrace (prefixWord ++ tailWord_8349512) baseStart_8349512 baseEnd_8349512 := by
    simpa [prefixWord, tailWord_8349512, baseEnd_8349512] using wordTrace_append hprefix tailTrace_8349512
  have hstable : (prefixWord ++ tailWord_8349512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349512).length < 2 ^ (prefixWord ++ tailWord_8349512).sum := by decide
  have hdescent : baseEnd_8349512 < baseStart_8349512 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349539 : List Nat := [1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 5]
def baseStart_8349539 : Nat := 118140960795 + 8349539 * 2 ^ 59
def prefixEnd_8349539 : Nat := 4983230072969 + 3 ^ 40 * 8349539 * 2
def baseEnd_8349539 : Nat := 4287326750460713123963675

theorem tailTrace_8349539 : CollatzResearch.WordTrace tailWord_8349539 prefixEnd_8349539 4287326750460713123963675 := by
  unfold tailWord_8349539
  simp only [CollatzResearch.WordTrace]
  refine ⟨304532705698053665577627671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203021803798702443718418447 304532705698053665577627671)
  ·
    refine ⟨456799058547080498366441507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304532705698053665577627671 456799058547080498366441507)
    ·
      refine ⟨685198587820620747549662261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456799058547080498366441507 685198587820620747549662261)
      ·
        refine ⟨64237367608183195082780837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 685198587820620747549662261 64237367608183195082780837)
        ·
          refine ⟨12044506426534349078021407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64237367608183195082780837 12044506426534349078021407)
          ·
            refine ⟨18066759639801523617032111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12044506426534349078021407 18066759639801523617032111)
            ·
              refine ⟨27100139459702285425548167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18066759639801523617032111 27100139459702285425548167)
              ·
                refine ⟨40650209189553428138322251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27100139459702285425548167 40650209189553428138322251)
                ·
                  refine ⟨60975313784330142207483377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40650209189553428138322251 60975313784330142207483377)
                  ·
                    refine ⟨45731485338247606655612533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60975313784330142207483377 45731485338247606655612533)
                    ·
                      refine ⟨4287326750460713123963675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45731485338247606655612533 4287326750460713123963675)
                      ·
                        rfl

theorem cell23_8349539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_8349539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349539 prefixEnd_8349539 := by exact prefixLift 8349539
  have htrace : WordTrace (prefixWord ++ tailWord_8349539) baseStart_8349539 baseEnd_8349539 := by
    simpa [prefixWord, tailWord_8349539, baseEnd_8349539] using wordTrace_append hprefix tailTrace_8349539
  have hstable : (prefixWord ++ tailWord_8349539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349539).length < 2 ^ (prefixWord ++ tailWord_8349539).sum := by decide
  have hdescent : baseEnd_8349539 < baseStart_8349539 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349562 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4]
def baseStart_8349562 : Nat := 118140960795 + 8349562 * 2 ^ 59
def prefixEnd_8349562 : Nat := 4983230072969 + 3 ^ 40 * 8349562 * 2
def baseEnd_8349562 : Nat := 4287338560515766533976069

theorem tailTrace_8349562 : CollatzResearch.WordTrace tailWord_8349562 prefixEnd_8349562 4287338560515766533976069 := by
  unfold tailWord_8349562
  simp only [CollatzResearch.WordTrace]
  refine ⟨76133386144242585126428735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203022363051313560337143293 76133386144242585126428735)
  ·
    refine ⟨114200079216363877689643103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76133386144242585126428735 114200079216363877689643103)
    ·
      refine ⟨171300118824545816534464655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114200079216363877689643103 171300118824545816534464655)
      ·
        refine ⟨256950178236818724801696983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171300118824545816534464655 256950178236818724801696983)
        ·
          refine ⟨385425267355228087202545475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256950178236818724801696983 385425267355228087202545475)
          ·
            refine ⟨578137901032842130803818213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385425267355228087202545475 578137901032842130803818213)
            ·
              refine ⟨108400856443657899525715915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 578137901032842130803818213 108400856443657899525715915)
              ·
                refine ⟨162601284665486849288573873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108400856443657899525715915 162601284665486849288573873)
                ·
                  refine ⟨121950963499115136966430405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162601284665486849288573873 121950963499115136966430405)
                  ·
                    refine ⟨22865805656084088181205701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121950963499115136966430405 22865805656084088181205701)
                    ·
                      refine ⟨4287338560515766533976069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22865805656084088181205701 4287338560515766533976069)
                      ·
                        rfl

theorem cell23_8349562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_8349562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349562 prefixEnd_8349562 := by exact prefixLift 8349562
  have htrace : WordTrace (prefixWord ++ tailWord_8349562) baseStart_8349562 baseEnd_8349562 := by
    simpa [prefixWord, tailWord_8349562, baseEnd_8349562] using wordTrace_append hprefix tailTrace_8349562
  have hstable : (prefixWord ++ tailWord_8349562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349562).length < 2 ^ (prefixWord ++ tailWord_8349562).sum := by decide
  have hdescent : baseEnd_8349562 < baseStart_8349562 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349572 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 10]
def baseStart_8349572 : Nat := 118140960795 + 8349572 * 2 ^ 59
def prefixEnd_8349572 : Nat := 4983230072969 + 3 ^ 40 * 8349572 * 2
def baseEnd_8349572 : Nat := 476371521702479054983447

theorem tailTrace_8349572 : CollatzResearch.WordTrace tailWord_8349572 prefixEnd_8349572 476371521702479054983447 := by
  unfold tailWord_8349572
  simp only [CollatzResearch.WordTrace]
  refine ⟨152266954653467056106789485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203022606204622741475719313 152266954653467056106789485)
  ·
    refine ⟨57100107995050146040046057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152266954653467056106789485 57100107995050146040046057)
    ·
      refine ⟨42825080996287609530034543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57100107995050146040046057 42825080996287609530034543)
      ·
        refine ⟨64237621494431414295051815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42825080996287609530034543 64237621494431414295051815)
        ·
          refine ⟨96356432241647121442577723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64237621494431414295051815 96356432241647121442577723)
          ·
            refine ⟨144534648362470682163866585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96356432241647121442577723 144534648362470682163866585)
            ·
              refine ⟨108400986271853011622899939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144534648362470682163866585 108400986271853011622899939)
              ·
                refine ⟨162601479407779517434349909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108400986271853011622899939 162601479407779517434349909)
                ·
                  refine ⟨476371521702479054983447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 162601479407779517434349909 476371521702479054983447)
                  ·
                    rfl

theorem cell23_8349572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 10].length) (baseStart_8349572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349572 prefixEnd_8349572 := by exact prefixLift 8349572
  have htrace : WordTrace (prefixWord ++ tailWord_8349572) baseStart_8349572 baseEnd_8349572 := by
    simpa [prefixWord, tailWord_8349572, baseEnd_8349572] using wordTrace_append hprefix tailTrace_8349572
  have hstable : (prefixWord ++ tailWord_8349572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349572).length < 2 ^ (prefixWord ++ tailWord_8349572).sum := by decide
  have hdescent : baseEnd_8349572 < baseStart_8349572 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349589 : List Nat := [1, 3, 2, 1, 1, 3, 4, 2, 6]
def baseStart_8349589 : Nat := 118140960795 + 8349589 * 2 ^ 59
def prefixEnd_8349589 : Nat := 4983230072969 + 3 ^ 40 * 8349589 * 2
def baseEnd_8349589 : Nat := 476372491610381992037605

theorem tailTrace_8349589 : CollatzResearch.WordTrace tailWord_8349589 prefixEnd_8349589 476372491610381992037605 := by
  unfold tailWord_8349589
  simp only [CollatzResearch.WordTrace]
  refine ⟨304534529347872524116947821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203023019565248349411298547 304534529347872524116947821)
  ·
    refine ⟨114200448505452196543855433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304534529347872524116947821 114200448505452196543855433)
    ·
      refine ⟨85650336379089147407891575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114200448505452196543855433 85650336379089147407891575)
      ·
        refine ⟨128475504568633721111837363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85650336379089147407891575 128475504568633721111837363)
        ·
          refine ⟨192713256852950581667756045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128475504568633721111837363 192713256852950581667756045)
          ·
            refine ⟨72267471319856468125408517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192713256852950581667756045 72267471319856468125408517)
            ·
              refine ⟨13550150872473087773514097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72267471319856468125408517 13550150872473087773514097)
              ·
                refine ⟨10162613154354815830135573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13550150872473087773514097 10162613154354815830135573)
                ·
                  refine ⟨476372491610381992037605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10162613154354815830135573 476372491610381992037605)
                  ·
                    rfl

theorem cell23_8349589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 6].length) (baseStart_8349589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349589 prefixEnd_8349589 := by exact prefixLift 8349589
  have htrace : WordTrace (prefixWord ++ tailWord_8349589) baseStart_8349589 baseEnd_8349589 := by
    simpa [prefixWord, tailWord_8349589, baseEnd_8349589] using wordTrace_append hprefix tailTrace_8349589
  have hstable : (prefixWord ++ tailWord_8349589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349589).length < 2 ^ (prefixWord ++ tailWord_8349589).sum := by decide
  have hdescent : baseEnd_8349589 < baseStart_8349589 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349593 : List Nat := [1, 2, 1, 2, 1, 3, 6, 2, 1, 4]
def baseStart_8349593 : Nat := 118140960795 + 8349593 * 2 ^ 59
def prefixEnd_8349593 : Nat := 4983230072969 + 3 ^ 40 * 8349593 * 2
def baseEnd_8349593 : Nat := 1429118159472018637562809

theorem tailTrace_8349593 : CollatzResearch.WordTrace tailWord_8349593 prefixEnd_8349593 1429118159472018637562809 := by
  unfold tailWord_8349593
  simp only [CollatzResearch.WordTrace]
  refine ⟨304534675239858032800093433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203023116826572021866728955 304534675239858032800093433)
  ·
    refine ⟨228401006429893524600070075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304534675239858032800093433 228401006429893524600070075)
    ·
      refine ⟨342601509644840286900105113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228401006429893524600070075 342601509644840286900105113)
      ·
        refine ⟨256951132233630215175078835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342601509644840286900105113 256951132233630215175078835)
        ·
          refine ⟨385426698350445322762618253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256951132233630215175078835 385426698350445322762618253)
          ·
            refine ⟨144535011881416996035981845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 385426698350445322762618253 144535011881416996035981845)
            ·
              refine ⟨6775078681941421689186649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144535011881416996035981845 6775078681941421689186649)
              ·
                refine ⟨5081309011456066266889987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6775078681941421689186649 5081309011456066266889987)
                ·
                  refine ⟨7621963517184099400334981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5081309011456066266889987 7621963517184099400334981)
                  ·
                    refine ⟨1429118159472018637562809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7621963517184099400334981 1429118159472018637562809)
                    ·
                      rfl

theorem cell23_8349593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2, 1, 4].length) (baseStart_8349593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349593 prefixEnd_8349593 := by exact prefixLift 8349593
  have htrace : WordTrace (prefixWord ++ tailWord_8349593) baseStart_8349593 baseEnd_8349593 := by
    simpa [prefixWord, tailWord_8349593, baseEnd_8349593] using wordTrace_append hprefix tailTrace_8349593
  have hstable : (prefixWord ++ tailWord_8349593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349593).length < 2 ^ (prefixWord ++ tailWord_8349593).sum := by decide
  have hdescent : baseEnd_8349593 < baseStart_8349593 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349619 : List Nat := [1, 1, 1, 2, 3, 1, 4, 4, 1, 5]
def baseStart_8349619 : Nat := 118140960795 + 8349619 * 2 ^ 59
def prefixEnd_8349619 : Nat := 4983230072969 + 3 ^ 40 * 8349619 * 2
def baseEnd_8349619 : Nat := 1429122609637690936987769

theorem tailTrace_8349619 : CollatzResearch.WordTrace tailWord_8349619 prefixEnd_8349619 1429122609637690936987769 := by
  unfold tailWord_8349619
  simp only [CollatzResearch.WordTrace]
  refine ⟨304535623537763839240539911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203023749025175892827026607 304535623537763839240539911)
  ·
    refine ⟨456803435306645758860809867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304535623537763839240539911 456803435306645758860809867)
    ·
      refine ⟨685205152959968638291214801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456803435306645758860809867 685205152959968638291214801)
      ·
        refine ⟨513903864719976478718411101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 685205152959968638291214801 513903864719976478718411101)
        ·
          refine ⟨192713949269991179519404163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 513903864719976478718411101 192713949269991179519404163)
          ·
            refine ⟨289070923904986769279106245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192713949269991179519404163 289070923904986769279106245)
            ·
              refine ⟨54200798232185019239832421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 289070923904986769279106245 54200798232185019239832421)
              ·
                refine ⟨10162649668534691107468579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54200798232185019239832421 10162649668534691107468579)
                ·
                  refine ⟨15243974502802036661202869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10162649668534691107468579 15243974502802036661202869)
                  ·
                    refine ⟨1429122609637690936987769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15243974502802036661202869 1429122609637690936987769)
                    ·
                      rfl

theorem cell23_8349619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 5].length) (baseStart_8349619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349619 prefixEnd_8349619 := by exact prefixLift 8349619
  have htrace : WordTrace (prefixWord ++ tailWord_8349619) baseStart_8349619 baseEnd_8349619 := by
    simpa [prefixWord, tailWord_8349619, baseEnd_8349619] using wordTrace_append hprefix tailTrace_8349619
  have hstable : (prefixWord ++ tailWord_8349619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349619).length < 2 ^ (prefixWord ++ tailWord_8349619).sum := by decide
  have hdescent : baseEnd_8349619 < baseStart_8349619 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349626 : List Nat := [3, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2]
def baseStart_8349626 : Nat := 118140960795 + 8349626 * 2 ^ 59
def prefixEnd_8349626 : Nat := 4983230072969 + 3 ^ 40 * 8349626 * 2
def baseEnd_8349626 : Nat := 4287371423277654283575775

theorem tailTrace_8349626 : CollatzResearch.WordTrace tailWord_8349626 prefixEnd_8349626 4287371423277654283575775 := by
  unfold tailWord_8349626
  simp only [CollatzResearch.WordTrace]
  refine ⟨76133969712184619859011183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203023919232492319624029821 76133969712184619859011183)
  ·
    refine ⟨114200954568276929788516775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76133969712184619859011183 114200954568276929788516775)
    ·
      refine ⟨171301431852415394682775163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114200954568276929788516775 171301431852415394682775163)
      ·
        refine ⟨256952147778623092024162745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171301431852415394682775163 256952147778623092024162745)
        ·
          refine ⟨192714110833967319018122059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256952147778623092024162745 192714110833967319018122059)
          ·
            refine ⟨289071166250950978527183089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192714110833967319018122059 289071166250950978527183089)
            ·
              refine ⟨216803374688213233895387317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289071166250950978527183089 216803374688213233895387317)
              ·
                refine ⟨20325316377019990677692561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 216803374688213233895387317 20325316377019990677692561)
                ·
                  refine ⟨15243987282764993008269421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20325316377019990677692561 15243987282764993008269421)
                  ·
                    refine ⟨5716495231036872378101033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15243987282764993008269421 5716495231036872378101033)
                    ·
                      refine ⟨4287371423277654283575775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5716495231036872378101033 4287371423277654283575775)
                      ·
                        rfl

theorem cell23_8349626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2].length) (baseStart_8349626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349626 prefixEnd_8349626 := by exact prefixLift 8349626
  have htrace : WordTrace (prefixWord ++ tailWord_8349626) baseStart_8349626 baseEnd_8349626 := by
    simpa [prefixWord, tailWord_8349626, baseEnd_8349626] using wordTrace_append hprefix tailTrace_8349626
  have hstable : (prefixWord ++ tailWord_8349626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349626).length < 2 ^ (prefixWord ++ tailWord_8349626).sum := by decide
  have hdescent : baseEnd_8349626 < baseStart_8349626 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349650 : List Nat := [3, 2, 2, 3, 2, 1, 2, 1, 3, 1, 3]
def baseStart_8349650 : Nat := 118140960795 + 8349650 * 2 ^ 59
def prefixEnd_8349650 : Nat := 4983230072969 + 3 ^ 40 * 8349650 * 2
def baseEnd_8349650 : Nat := 4287383746813362189675665

theorem tailTrace_8349650 : CollatzResearch.WordTrace tailWord_8349650 prefixEnd_8349650 4287383746813362189675665 := by
  unfold tailWord_8349650
  simp only [CollatzResearch.WordTrace]
  refine ⟨76134188550162882883729601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203024502800434354356612269 76134188550162882883729601)
  ·
    refine ⟨57100641412622162162797201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76134188550162882883729601 57100641412622162162797201)
    ·
      refine ⟨42825481059466621622097901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57100641412622162162797201 42825481059466621622097901)
      ·
        refine ⟨16059555397299983108286713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42825481059466621622097901 16059555397299983108286713)
        ·
          refine ⟨12044666547974987331215035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16059555397299983108286713 12044666547974987331215035)
          ·
            refine ⟨18066999821962480996822553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12044666547974987331215035 18066999821962480996822553)
            ·
              refine ⟨13550249866471860747616915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18066999821962480996822553 13550249866471860747616915)
              ·
                refine ⟨20325374799707791121425373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13550249866471860747616915 20325374799707791121425373)
                ·
                  refine ⟨7622015549890421670534515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20325374799707791121425373 7622015549890421670534515)
                  ·
                    refine ⟨11433023324835632505801773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7622015549890421670534515 11433023324835632505801773)
                    ·
                      refine ⟨4287383746813362189675665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11433023324835632505801773 4287383746813362189675665)
                      ·
                        rfl

theorem cell23_8349650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_8349650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349650 prefixEnd_8349650 := by exact prefixLift 8349650
  have htrace : WordTrace (prefixWord ++ tailWord_8349650) baseStart_8349650 baseEnd_8349650 := by
    simpa [prefixWord, tailWord_8349650, baseEnd_8349650] using wordTrace_append hprefix tailTrace_8349650
  have hstable : (prefixWord ++ tailWord_8349650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349650).length < 2 ^ (prefixWord ++ tailWord_8349650).sum := by decide
  have hdescent : baseEnd_8349650 < baseStart_8349650 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349707 : List Nat := [1, 1, 1, 1, 6, 1, 5, 2, 1, 2, 2]
def baseStart_8349707 : Nat := 118140960795 + 8349707 * 2 ^ 59
def prefixEnd_8349707 : Nat := 4983230072969 + 3 ^ 40 * 8349707 * 2
def baseEnd_8349707 : Nat := 4287413015210668466662903

theorem tailTrace_8349707 : CollatzResearch.WordTrace tailWord_8349707 prefixEnd_8349707 4287413015210668466662903 := by
  unfold tailWord_8349707
  simp only [CollatzResearch.WordTrace]
  refine ⟨304538833161445030269743375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203025888774296686846495583 304538833161445030269743375)
  ·
    refine ⟨456808249742167545404615063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304538833161445030269743375 456808249742167545404615063)
    ·
      refine ⟨685212374613251318106922595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456808249742167545404615063 685212374613251318106922595)
      ·
        refine ⟨1027818561919876977160383893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685212374613251318106922595 1027818561919876977160383893)
        ·
          refine ⟨48178995089994233304392995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1027818561919876977160383893 48178995089994233304392995)
          ·
            refine ⟨72268492634991349956589493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48178995089994233304392995 72268492634991349956589493)
            ·
              refine ⟨6775171184530439058430265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72268492634991349956589493 6775171184530439058430265)
              ·
                refine ⟨5081378388397829293822699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6775171184530439058430265 5081378388397829293822699)
                ·
                  refine ⟨7622067582596743940734049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5081378388397829293822699 7622067582596743940734049)
                  ·
                    refine ⟨5716550686947557955550537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7622067582596743940734049 5716550686947557955550537)
                    ·
                      refine ⟨4287413015210668466662903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5716550686947557955550537 4287413015210668466662903)
                      ·
                        rfl

theorem cell23_8349707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2, 1, 2, 2].length) (baseStart_8349707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349707 prefixEnd_8349707 := by exact prefixLift 8349707
  have htrace : WordTrace (prefixWord ++ tailWord_8349707) baseStart_8349707 baseEnd_8349707 := by
    simpa [prefixWord, tailWord_8349707, baseEnd_8349707] using wordTrace_append hprefix tailTrace_8349707
  have hstable : (prefixWord ++ tailWord_8349707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349707).length < 2 ^ (prefixWord ++ tailWord_8349707).sum := by decide
  have hdescent : baseEnd_8349707 < baseStart_8349707 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349717 : List Nat := [1, 3, 2, 1, 6, 1, 2, 1, 2, 4]
def baseStart_8349717 : Nat := 118140960795 + 8349717 * 2 ^ 59
def prefixEnd_8349717 : Nat := 4983230072969 + 3 ^ 40 * 8349717 * 2
def baseEnd_8349717 : Nat := 1429139383339071142512619

theorem tailTrace_8349717 : CollatzResearch.WordTrace tailWord_8349717 prefixEnd_8349717 1429139383339071142512619 := by
  unfold tailWord_8349717
  simp only [CollatzResearch.WordTrace]
  refine ⟨304539197891408801977607405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203026131927605867985071603 304539197891408801977607405)
  ·
    refine ⟨114202199209278300741602777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304539197891408801977607405 114202199209278300741602777)
    ·
      refine ⟨85651649406958725556202083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114202199209278300741602777 85651649406958725556202083)
      ·
        refine ⟨128477474110438088334303125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85651649406958725556202083 128477474110438088334303125)
        ·
          refine ⟨6022381598926785390670459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 128477474110438088334303125 6022381598926785390670459)
          ·
            refine ⟨9033572398390178086005689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6022381598926785390670459 9033572398390178086005689)
            ·
              refine ⟨6775179298792633564504267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9033572398390178086005689 6775179298792633564504267)
              ·
                refine ⟨10162768948188950346756401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6775179298792633564504267 10162768948188950346756401)
                ·
                  refine ⟨7622076711141712760067301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10162768948188950346756401 7622076711141712760067301)
                  ·
                    refine ⟨1429139383339071142512619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7622076711141712760067301 1429139383339071142512619)
                    ·
                      rfl

theorem cell23_8349717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_8349717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349717 prefixEnd_8349717 := by exact prefixLift 8349717
  have htrace : WordTrace (prefixWord ++ tailWord_8349717) baseStart_8349717 baseEnd_8349717 := by
    simpa [prefixWord, tailWord_8349717, baseEnd_8349717] using wordTrace_append hprefix tailTrace_8349717
  have hstable : (prefixWord ++ tailWord_8349717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349717).length < 2 ^ (prefixWord ++ tailWord_8349717).sum := by decide
  have hdescent : baseEnd_8349717 < baseStart_8349717 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349733 : List Nat := [1, 3, 1, 2, 2, 4, 1, 1, 3, 3, 2]
def baseStart_8349733 : Nat := 118140960795 + 8349733 * 2 ^ 59
def prefixEnd_8349733 : Nat := 4983230072969 + 3 ^ 40 * 8349733 * 2
def baseEnd_8349733 : Nat := 4287426365707685364937783

theorem tailTrace_8349733 : CollatzResearch.WordTrace tailWord_8349733 prefixEnd_8349733 4287426365707685364937783 := by
  unfold tailWord_8349733
  simp only [CollatzResearch.WordTrace]
  refine ⟨304539781459350836710189853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203026520972900557806793235 304539781459350836710189853)
  ·
    refine ⟨114202418047256563766321195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304539781459350836710189853 114202418047256563766321195)
    ·
      refine ⟨171303627070884845649481793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114202418047256563766321195 171303627070884845649481793)
      ·
        refine ⟨128477720303163634237111345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171303627070884845649481793 128477720303163634237111345)
        ·
          refine ⟨96358290227372725677833509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128477720303163634237111345 96358290227372725677833509)
          ·
            refine ⟨18067179417632386064593783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96358290227372725677833509 18067179417632386064593783)
            ·
              refine ⟨27100769126448579096890675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18067179417632386064593783 27100769126448579096890675)
              ·
                refine ⟨40651153689672868645336013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27100769126448579096890675 40651153689672868645336013)
                ·
                  refine ⟨15244182633627325742001005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40651153689672868645336013 15244182633627325742001005)
                  ·
                    refine ⟨5716568487610247153250377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15244182633627325742001005 5716568487610247153250377)
                    ·
                      refine ⟨4287426365707685364937783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5716568487610247153250377 4287426365707685364937783)
                      ·
                        rfl

theorem cell23_8349733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 3, 2].length) (baseStart_8349733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349733 prefixEnd_8349733 := by exact prefixLift 8349733
  have htrace : WordTrace (prefixWord ++ tailWord_8349733) baseStart_8349733 baseEnd_8349733 := by
    simpa [prefixWord, tailWord_8349733, baseEnd_8349733] using wordTrace_append hprefix tailTrace_8349733
  have hstable : (prefixWord ++ tailWord_8349733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349733).length < 2 ^ (prefixWord ++ tailWord_8349733).sum := by decide
  have hdescent : baseEnd_8349733 < baseStart_8349733 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349758 : List Nat := [4, 2, 1, 3, 3, 1, 2, 2, 1, 2, 2]
def baseStart_8349758 : Nat := 118140960795 + 8349758 * 2 ^ 59
def prefixEnd_8349758 : Nat := 4983230072969 + 3 ^ 40 * 8349758 * 2
def baseEnd_8349758 : Nat := 4287439202724047767125169

theorem tailTrace_8349758 : CollatzResearch.WordTrace tailWord_8349758 prefixEnd_8349758 4287439202724047767125169 := by
  unfold tailWord_8349758
  simp only [CollatzResearch.WordTrace]
  refine ⟨38067586660532533247481241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203027128856173510653233285 38067586660532533247481241)
  ·
    refine ⟨28550689995399399935610931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38067586660532533247481241 28550689995399399935610931)
    ·
      refine ⟨42826034993099099903416397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28550689995399399935610931 42826034993099099903416397)
      ·
        refine ⟨16059763122412162463781149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42826034993099099903416397 16059763122412162463781149)
        ·
          refine ⟨6022411170904560923917931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16059763122412162463781149 6022411170904560923917931)
          ·
            refine ⟨9033616756356841385876897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6022411170904560923917931 9033616756356841385876897)
            ·
              refine ⟨6775212567267631039407673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9033616756356841385876897 6775212567267631039407673)
              ·
                refine ⟨5081409425450723279555755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6775212567267631039407673 5081409425450723279555755)
                ·
                  refine ⟨7622114138176084919333633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5081409425450723279555755 7622114138176084919333633)
                  ·
                    refine ⟨5716585603632063689500225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7622114138176084919333633 5716585603632063689500225)
                    ·
                      refine ⟨4287439202724047767125169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5716585603632063689500225 4287439202724047767125169)
                      ·
                        rfl

theorem cell23_8349758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_8349758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349758 prefixEnd_8349758 := by exact prefixLift 8349758
  have htrace : WordTrace (prefixWord ++ tailWord_8349758) baseStart_8349758 baseEnd_8349758 := by
    simpa [prefixWord, tailWord_8349758, baseEnd_8349758] using wordTrace_append hprefix tailTrace_8349758
  have hstable : (prefixWord ++ tailWord_8349758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349758).length < 2 ^ (prefixWord ++ tailWord_8349758).sum := by decide
  have hdescent : baseEnd_8349758 < baseStart_8349758 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349769 : List Nat := [1, 2, 1, 1, 2, 2, 4, 3, 7]
def baseStart_8349769 : Nat := 118140960795 + 8349769 * 2 ^ 59
def prefixEnd_8349769 : Nat := 4983230072969 + 3 ^ 40 * 8349769 * 2
def baseEnd_8349769 : Nat := 476382761223471913787513

theorem tailTrace_8349769 : CollatzResearch.WordTrace tailWord_8349769 prefixEnd_8349769 476382761223471913787513 := by
  unfold tailWord_8349769
  simp only [CollatzResearch.WordTrace]
  refine ⟨304541094487220414858500361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203027396324813609905666907 304541094487220414858500361)
  ·
    refine ⟨228405820865415311143875271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304541094487220414858500361 228405820865415311143875271)
    ·
      refine ⟨342608731298122966715812907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228405820865415311143875271 342608731298122966715812907)
      ·
        refine ⟨513913096947184450073719361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342608731298122966715812907 513913096947184450073719361)
        ·
          refine ⟨385434822710388337555289521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513913096947184450073719361 385434822710388337555289521)
          ·
            refine ⟨289076117032791253166467141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385434822710388337555289521 289076117032791253166467141)
            ·
              refine ⟨54201771943648359968712589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 289076117032791253166467141 54201771943648359968712589)
              ·
                refine ⟨20325664478868134988267221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54201771943648359968712589 20325664478868134988267221)
                ·
                  refine ⟨476382761223471913787513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20325664478868134988267221 476382761223471913787513)
                  ·
                    rfl

theorem cell23_8349769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 7].length) (baseStart_8349769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349769 prefixEnd_8349769 := by exact prefixLift 8349769
  have htrace : WordTrace (prefixWord ++ tailWord_8349769) baseStart_8349769 baseEnd_8349769 := by
    simpa [prefixWord, tailWord_8349769, baseEnd_8349769] using wordTrace_append hprefix tailTrace_8349769
  have hstable : (prefixWord ++ tailWord_8349769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349769).length < 2 ^ (prefixWord ++ tailWord_8349769).sum := by decide
  have hdescent : baseEnd_8349769 < baseStart_8349769 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349814 : List Nat := [5, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2]
def baseStart_8349814 : Nat := 118140960795 + 8349814 * 2 ^ 59
def prefixEnd_8349814 : Nat := 4983230072969 + 3 ^ 40 * 8349814 * 2
def baseEnd_8349814 : Nat := 4287467957640699548024911

theorem tailTrace_8349814 : CollatzResearch.WordTrace tailWord_8349814 prefixEnd_8349814 4287467957640699548024911 := by
  unfold tailWord_8349814
  simp only [CollatzResearch.WordTrace]
  refine ⟨19033920985753586721493031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203028490514704925029258997 19033920985753586721493031)
  ·
    refine ⟨28550881478630380082239547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19033920985753586721493031 28550881478630380082239547)
    ·
      refine ⟨42826322217945570123359321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28550881478630380082239547 42826322217945570123359321)
      ·
        refine ⟨32119741663459177592519491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42826322217945570123359321 32119741663459177592519491)
        ·
          refine ⟨48179612495188766388779237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32119741663459177592519491 48179612495188766388779237)
          ·
            refine ⟨9033677342847893697896107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48179612495188766388779237 9033677342847893697896107)
            ·
              refine ⟨13550516014271840546844161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9033677342847893697896107 13550516014271840546844161)
              ·
                refine ⟨10162887010703880410133121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13550516014271840546844161 10162887010703880410133121)
                ·
                  refine ⟨7622165258027910307599841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10162887010703880410133121 7622165258027910307599841)
                  ·
                    refine ⟨5716623943520932730699881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7622165258027910307599841 5716623943520932730699881)
                    ·
                      refine ⟨4287467957640699548024911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5716623943520932730699881 4287467957640699548024911)
                      ·
                        rfl

theorem cell23_8349814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_8349814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349814 prefixEnd_8349814 := by exact prefixLift 8349814
  have htrace : WordTrace (prefixWord ++ tailWord_8349814) baseStart_8349814 baseEnd_8349814 := by
    simpa [prefixWord, tailWord_8349814, baseEnd_8349814] using wordTrace_append hprefix tailTrace_8349814
  have hstable : (prefixWord ++ tailWord_8349814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349814).length < 2 ^ (prefixWord ++ tailWord_8349814).sum := by decide
  have hdescent : baseEnd_8349814 < baseStart_8349814 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349854 : List Nat := [4, 3, 1, 1, 4, 1, 1, 3, 5]
def baseStart_8349854 : Nat := 118140960795 + 8349854 * 2 ^ 59
def prefixEnd_8349854 : Nat := 4983230072969 + 3 ^ 40 * 8349854 * 2
def baseEnd_8349854 : Nat := 476387610762986599058303

theorem tailTrace_8349854 : CollatzResearch.WordTrace tailWord_8349854 prefixEnd_8349854 476387610762986599058303 := by
  unfold tailWord_8349854
  simp only [CollatzResearch.WordTrace]
  refine ⟨38068024336489059296918077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203029463127941649583563077 38068024336489059296918077)
  ·
    refine ⟨14275509126183397236344279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38068024336489059296918077 14275509126183397236344279)
    ·
      refine ⟨21413263689275095854516419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14275509126183397236344279 21413263689275095854516419)
      ·
        refine ⟨32119895533912643781774629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21413263689275095854516419 32119895533912643781774629)
        ·
          refine ⟨6022480412608620709082743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32119895533912643781774629 6022480412608620709082743)
          ·
            refine ⟨9033720618912931063624115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6022480412608620709082743 9033720618912931063624115)
            ·
              refine ⟨13550580928369396595436173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9033720618912931063624115 13550580928369396595436173)
              ·
                refine ⟨5081467848138523723288565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13550580928369396595436173 5081467848138523723288565)
                ·
                  refine ⟨476387610762986599058303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5081467848138523723288565 476387610762986599058303)
                  ·
                    rfl

theorem cell23_8349854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_8349854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349854 prefixEnd_8349854 := by exact prefixLift 8349854
  have htrace : WordTrace (prefixWord ++ tailWord_8349854) baseStart_8349854 baseEnd_8349854 := by
    simpa [prefixWord, tailWord_8349854, baseEnd_8349854] using wordTrace_append hprefix tailTrace_8349854
  have hstable : (prefixWord ++ tailWord_8349854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349854).length < 2 ^ (prefixWord ++ tailWord_8349854).sum := by decide
  have hdescent : baseEnd_8349854 < baseStart_8349854 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349893 : List Nat := [1, 3, 1, 1, 1, 1, 8, 1, 6]
def baseStart_8349893 : Nat := 118140960795 + 8349893 * 2 ^ 59
def prefixEnd_8349893 : Nat := 4983230072969 + 3 ^ 40 * 8349893 * 2
def baseEnd_8349893 : Nat := 476389835845822748770783

theorem tailTrace_8349893 : CollatzResearch.WordTrace tailWord_8349893 prefixEnd_8349893 476389835845822748770783 := by
  unfold tailWord_8349893
  simp only [CollatzResearch.WordTrace]
  refine ⟨304545617138771184036014333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203030411425847456024009555 304545617138771184036014333)
  ·
    refine ⟨114204606427039194013505375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304545617138771184036014333 114204606427039194013505375)
    ·
      refine ⟨171306909640558791020258063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114204606427039194013505375 171306909640558791020258063)
      ·
        refine ⟨256960364460838186530387095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171306909640558791020258063 256960364460838186530387095)
        ·
          refine ⟨385440546691257279795580643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256960364460838186530387095 385440546691257279795580643)
          ·
            refine ⟨578160820036885919693370965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385440546691257279795580643 578160820036885919693370965)
            ·
              refine ⟨6775322109807256871406691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 578160820036885919693370965 6775322109807256871406691)
              ·
                refine ⟨10162983164710885307110037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6775322109807256871406691 10162983164710885307110037)
                ·
                  refine ⟨476389835845822748770783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10162983164710885307110037 476389835845822748770783)
                  ·
                    rfl

theorem cell23_8349893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 6].length) (baseStart_8349893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349893 prefixEnd_8349893 := by exact prefixLift 8349893
  have htrace : WordTrace (prefixWord ++ tailWord_8349893) baseStart_8349893 baseEnd_8349893 := by
    simpa [prefixWord, tailWord_8349893, baseEnd_8349893] using wordTrace_append hprefix tailTrace_8349893
  have hstable : (prefixWord ++ tailWord_8349893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349893).length < 2 ^ (prefixWord ++ tailWord_8349893).sum := by decide
  have hdescent : baseEnd_8349893 < baseStart_8349893 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349903 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 5, 1, 3]
def baseStart_8349903 : Nat := 118140960795 + 8349903 * 2 ^ 59
def prefixEnd_8349903 : Nat := 4983230072969 + 3 ^ 40 * 8349903 * 2
def baseEnd_8349903 : Nat := 4287513657418949699812001

theorem tailTrace_8349903 : CollatzResearch.WordTrace tailWord_8349903 prefixEnd_8349903 4287513657418949699812001 := by
  unfold tailWord_8349903
  simp only [CollatzResearch.WordTrace]
  refine ⟨304545981868734955743878363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203030654579156637162585575 304545981868734955743878363)
  ·
    refine ⟨456818972803102433615817545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304545981868734955743878363 456818972803102433615817545)
    ·
      refine ⟨342614229602326825211863159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456818972803102433615817545 342614229602326825211863159)
      ·
        refine ⟨513921344403490237817794739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342614229602326825211863159 513921344403490237817794739)
        ·
          refine ⟨770882016605235356726692109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513921344403490237817794739 770882016605235356726692109)
          ·
            refine ⟨289080756226963258772509541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 770882016605235356726692109 289080756226963258772509541)
            ·
              refine ⟨54202641792555611019845539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 289080756226963258772509541 54202641792555611019845539)
              ·
                refine ⟨81303962688833416529768309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54202641792555611019845539 81303962688833416529768309)
                ·
                  refine ⟨7622246502078132799665779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81303962688833416529768309 7622246502078132799665779)
                  ·
                    refine ⟨11433369753117199199498669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7622246502078132799665779 11433369753117199199498669)
                    ·
                      refine ⟨4287513657418949699812001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11433369753117199199498669 4287513657418949699812001)
                      ·
                        rfl

theorem cell23_8349903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5, 1, 3].length) (baseStart_8349903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349903 prefixEnd_8349903 := by exact prefixLift 8349903
  have htrace : WordTrace (prefixWord ++ tailWord_8349903) baseStart_8349903 baseEnd_8349903 := by
    simpa [prefixWord, tailWord_8349903, baseEnd_8349903] using wordTrace_append hprefix tailTrace_8349903
  have hstable : (prefixWord ++ tailWord_8349903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349903).length < 2 ^ (prefixWord ++ tailWord_8349903).sum := by decide
  have hdescent : baseEnd_8349903 < baseStart_8349903 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349913 : List Nat := [1, 2, 1, 2, 3, 1, 2, 3, 1, 5, 2]
def baseStart_8349913 : Nat := 118140960795 + 8349913 * 2 ^ 59
def prefixEnd_8349913 : Nat := 4983230072969 + 3 ^ 40 * 8349913 * 2
def baseEnd_8349913 : Nat := 4287518792225494660686955

theorem tailTrace_8349913 : CollatzResearch.WordTrace tailWord_8349913 prefixEnd_8349913 4287518792225494660686955 := by
  unfold tailWord_8349913
  simp only [CollatzResearch.WordTrace]
  refine ⟨304546346598698727451742393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203030897732465818301161595 304546346598698727451742393)
  ·
    refine ⟨228409759949024045588806795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304546346598698727451742393 228409759949024045588806795)
    ·
      refine ⟨342614639923536068383210193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228409759949024045588806795 342614639923536068383210193)
      ·
        refine ⟨256960979942652051287407645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342614639923536068383210193 256960979942652051287407645)
        ·
          refine ⟨96360367478494519232777867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256960979942652051287407645 96360367478494519232777867)
          ·
            refine ⟨144540551217741778849166801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96360367478494519232777867 144540551217741778849166801)
            ·
              refine ⟨108405413413306334136875101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144540551217741778849166801 108405413413306334136875101)
              ·
                refine ⟨40652030029989875301328163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108405413413306334136875101 40652030029989875301328163)
                ·
                  refine ⟨60978045044984812951992245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40652030029989875301328163 60978045044984812951992245)
                  ·
                    refine ⟨5716691722967326214249273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60978045044984812951992245 5716691722967326214249273)
                    ·
                      refine ⟨4287518792225494660686955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5716691722967326214249273 4287518792225494660686955)
                      ·
                        rfl

theorem cell23_8349913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 5, 2].length) (baseStart_8349913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349913 prefixEnd_8349913 := by exact prefixLift 8349913
  have htrace : WordTrace (prefixWord ++ tailWord_8349913) baseStart_8349913 baseEnd_8349913 := by
    simpa [prefixWord, tailWord_8349913, baseEnd_8349913] using wordTrace_append hprefix tailTrace_8349913
  have hstable : (prefixWord ++ tailWord_8349913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349913).length < 2 ^ (prefixWord ++ tailWord_8349913).sum := by decide
  have hdescent : baseEnd_8349913 < baseStart_8349913 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349930 : List Nat := [3, 1, 3, 1, 1, 2, 1, 4, 2, 3, 2]
def baseStart_8349930 : Nat := 118140960795 + 8349930 * 2 ^ 59
def prefixEnd_8349930 : Nat := 4983230072969 + 3 ^ 40 * 8349930 * 2
def baseEnd_8349930 : Nat := 4287527521396621094174377

theorem tailTrace_8349930 : CollatzResearch.WordTrace tailWord_8349930 prefixEnd_8349930 4287527521396621094174377 := by
  unfold tailWord_8349930
  simp only [CollatzResearch.WordTrace]
  refine ⟨76136741659909284838777811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203031311093091426236740829 76136741659909284838777811)
  ·
    refine ⟨114205112489863927258166717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76136741659909284838777811 114205112489863927258166717)
    ·
      refine ⟨42826917183698972721812519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114205112489863927258166717 42826917183698972721812519)
      ·
        refine ⟨64240375775548459082718779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42826917183698972721812519 64240375775548459082718779)
        ·
          refine ⟨96360563663322688624078169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64240375775548459082718779 96360563663322688624078169)
          ·
            refine ⟨72270422747492016468058627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96360563663322688624078169 72270422747492016468058627)
            ·
              refine ⟨108405634121238024702087941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72270422747492016468058627 108405634121238024702087941)
              ·
                refine ⟨20326056397732129631641489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108405634121238024702087941 20326056397732129631641489)
                ·
                  refine ⟨15244542298299097223731117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20326056397732129631641489 15244542298299097223731117)
                  ·
                    refine ⟨5716703361862161458899169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15244542298299097223731117 5716703361862161458899169)
                    ·
                      refine ⟨4287527521396621094174377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5716703361862161458899169 4287527521396621094174377)
                      ·
                        rfl

theorem cell23_8349930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_8349930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349930 prefixEnd_8349930 := by exact prefixLift 8349930
  have htrace : WordTrace (prefixWord ++ tailWord_8349930) baseStart_8349930 baseEnd_8349930 := by
    simpa [prefixWord, tailWord_8349930, baseEnd_8349930] using wordTrace_append hprefix tailTrace_8349930
  have hstable : (prefixWord ++ tailWord_8349930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349930).length < 2 ^ (prefixWord ++ tailWord_8349930).sum := by decide
  have hdescent : baseEnd_8349930 < baseStart_8349930 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349953 : List Nat := [1, 2, 4, 1, 1, 2, 4, 1, 1, 6]
def baseStart_8349953 : Nat := 118140960795 + 8349953 * 2 ^ 59
def prefixEnd_8349953 : Nat := 4983230072969 + 3 ^ 40 * 8349953 * 2
def baseEnd_8349953 : Nat := 1429179777150558168062257

theorem tailTrace_8349953 : CollatzResearch.WordTrace tailWord_8349953 prefixEnd_8349953 1429179777150558168062257 := by
  unfold tailWord_8349953
  simp only [CollatzResearch.WordTrace]
  refine ⟨304547805518553814283198513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203031870345702542855465675 304547805518553814283198513)
  ·
    refine ⟨228410854138915360712398885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304547805518553814283198513 228410854138915360712398885)
    ·
      refine ⟨42827035151046630133574791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228410854138915360712398885 42827035151046630133574791)
      ·
        refine ⟨64240552726569945200362187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42827035151046630133574791 64240552726569945200362187)
        ·
          refine ⟨96360829089854917800543281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64240552726569945200362187 96360829089854917800543281)
          ·
            refine ⟨72270621817391188350407461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96360829089854917800543281 72270621817391188350407461)
            ·
              refine ⟨13550741590760847815701399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72270621817391188350407461 13550741590760847815701399)
              ·
                refine ⟨20326112386141271723552099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13550741590760847815701399 20326112386141271723552099)
                ·
                  refine ⟨30489168579211907585328149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20326112386141271723552099 30489168579211907585328149)
                  ·
                    refine ⟨1429179777150558168062257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30489168579211907585328149 1429179777150558168062257)
                    ·
                      rfl

theorem cell23_8349953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_8349953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349953 prefixEnd_8349953 := by exact prefixLift 8349953
  have htrace : WordTrace (prefixWord ++ tailWord_8349953) baseStart_8349953 baseEnd_8349953 := by
    simpa [prefixWord, tailWord_8349953, baseEnd_8349953] using wordTrace_append hprefix tailTrace_8349953
  have hstable : (prefixWord ++ tailWord_8349953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349953).length < 2 ^ (prefixWord ++ tailWord_8349953).sum := by decide
  have hdescent : baseEnd_8349953 < baseStart_8349953 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349963 : List Nat := [1, 1, 1, 1, 5, 2, 1, 3, 3, 2, 3]
def baseStart_8349963 : Nat := 118140960795 + 8349963 * 2 ^ 59
def prefixEnd_8349963 : Nat := 4983230072969 + 3 ^ 40 * 8349963 * 2
def baseEnd_8349963 : Nat := 4287544466258219465061725

theorem tailTrace_8349963 : CollatzResearch.WordTrace tailWord_8349963 prefixEnd_8349963 4287544466258219465061725 := by
  unfold tailWord_8349963
  simp only [CollatzResearch.WordTrace]
  refine ⟨304548170248517585991062543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203032113499011723994041695 304548170248517585991062543)
  ·
    refine ⟨456822255372776378986593815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304548170248517585991062543 456822255372776378986593815)
    ·
      refine ⟨685233383059164568479890723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456822255372776378986593815 685233383059164568479890723)
      ·
        refine ⟨1027850074588746852719836085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685233383059164568479890723 1027850074588746852719836085)
        ·
          refine ⟨96360944492695017442484633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1027850074588746852719836085 96360944492695017442484633)
          ·
            refine ⟨72270708369521263081863475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96360944492695017442484633 72270708369521263081863475)
            ·
              refine ⟨108406062554281894622795213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72270708369521263081863475 108406062554281894622795213)
              ·
                refine ⟨40652273457855710483548205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108406062554281894622795213 40652273457855710483548205)
                ·
                  refine ⟨15244602546695891431330577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40652273457855710483548205 15244602546695891431330577)
                  ·
                    refine ⟨11433451910021918573497933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15244602546695891431330577 11433451910021918573497933)
                    ·
                      refine ⟨4287544466258219465061725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11433451910021918573497933 4287544466258219465061725)
                      ·
                        rfl

theorem cell23_8349963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2, 3].length) (baseStart_8349963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349963 prefixEnd_8349963 := by exact prefixLift 8349963
  have htrace : WordTrace (prefixWord ++ tailWord_8349963) baseStart_8349963 baseEnd_8349963 := by
    simpa [prefixWord, tailWord_8349963, baseEnd_8349963] using wordTrace_append hprefix tailTrace_8349963
  have hstable : (prefixWord ++ tailWord_8349963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349963).length < 2 ^ (prefixWord ++ tailWord_8349963).sum := by decide
  have hdescent : baseEnd_8349963 < baseStart_8349963 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349973 : List Nat := [1, 3, 2, 1, 2, 1, 4, 2, 1, 2, 4]
def baseStart_8349973 : Nat := 118140960795 + 8349973 * 2 ^ 59
def prefixEnd_8349973 : Nat := 4983230072969 + 3 ^ 40 * 8349973 * 2
def baseEnd_8349973 : Nat := 4287549601064764425936679

theorem tailTrace_8349973 : CollatzResearch.WordTrace tailWord_8349973 prefixEnd_8349973 4287549601064764425936679 := by
  unfold tailWord_8349973
  simp only [CollatzResearch.WordTrace]
  refine ⟨304548534978481357698926573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203032356652320905132617715 304548534978481357698926573)
  ·
    refine ⟨114205700616930509137097465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304548534978481357698926573 114205700616930509137097465)
    ·
      refine ⟨85654275462697881852823099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114205700616930509137097465 85654275462697881852823099)
      ·
        refine ⟨128481413194046822779234649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85654275462697881852823099 128481413194046822779234649)
        ·
          refine ⟨96361059895535117084425987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128481413194046822779234649 96361059895535117084425987)
          ·
            refine ⟨144541589843302675626638981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96361059895535117084425987 144541589843302675626638981)
            ·
              refine ⟨27101548095619251679994809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144541589843302675626638981 27101548095619251679994809)
              ·
                refine ⟨20326161071714438759996107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27101548095619251679994809 20326161071714438759996107)
                ·
                  refine ⟨30489241607571658139994161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20326161071714438759996107 30489241607571658139994161)
                  ·
                    refine ⟨22866931205678743604995621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30489241607571658139994161 22866931205678743604995621)
                    ·
                      refine ⟨4287549601064764425936679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22866931205678743604995621 4287549601064764425936679)
                      ·
                        rfl

theorem cell23_8349973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_8349973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349973 prefixEnd_8349973 := by exact prefixLift 8349973
  have htrace : WordTrace (prefixWord ++ tailWord_8349973) baseStart_8349973 baseEnd_8349973 := by
    simpa [prefixWord, tailWord_8349973, baseEnd_8349973] using wordTrace_append hprefix tailTrace_8349973
  have hstable : (prefixWord ++ tailWord_8349973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349973).length < 2 ^ (prefixWord ++ tailWord_8349973).sum := by decide
  have hdescent : baseEnd_8349973 < baseStart_8349973 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349996 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 1, 9]
def baseStart_8349996 : Nat := 118140960795 + 8349996 * 2 ^ 59
def prefixEnd_8349996 : Nat := 4983230072969 + 3 ^ 40 * 8349996 * 2
def baseEnd_8349996 : Nat := 1429187137039939278649691

theorem tailTrace_8349996 : CollatzResearch.WordTrace tailWord_8349996 prefixEnd_8349996 1429187137039939278649691 := by
  unfold tailWord_8349996
  simp only [CollatzResearch.WordTrace]
  refine ⟨152274686928699016313506921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203032915904932021751342561 152274686928699016313506921)
  ·
    refine ⟨114206015196524262235130191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152274686928699016313506921 114206015196524262235130191)
    ·
      refine ⟨171309022794786393352695287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114206015196524262235130191 171309022794786393352695287)
      ·
        refine ⟨256963534192179590029042931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171309022794786393352695287 256963534192179590029042931)
        ·
          refine ⟨385445301288269385043564397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256963534192179590029042931 385445301288269385043564397)
          ·
            refine ⟨144541987983101019391336649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 385445301288269385043564397 144541987983101019391336649)
            ·
              refine ⟨108406490987325764543502487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144541987983101019391336649 108406490987325764543502487)
              ·
                refine ⟨162609736480988646815253731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108406490987325764543502487 162609736480988646815253731)
                ·
                  refine ⟨243914604721482970222880597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162609736480988646815253731 243914604721482970222880597)
                  ·
                    refine ⟨1429187137039939278649691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 243914604721482970222880597 1429187137039939278649691)
                    ·
                      rfl

theorem cell23_8349996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 9].length) (baseStart_8349996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349996 prefixEnd_8349996 := by exact prefixLift 8349996
  have htrace : WordTrace (prefixWord ++ tailWord_8349996) baseStart_8349996 baseEnd_8349996 := by
    simpa [prefixWord, tailWord_8349996, baseEnd_8349996] using wordTrace_append hprefix tailTrace_8349996
  have hstable : (prefixWord ++ tailWord_8349996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349996).length < 2 ^ (prefixWord ++ tailWord_8349996).sum := by decide
  have hdescent : baseEnd_8349996 < baseStart_8349996 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8349997 : List Nat := [1, 5, 3, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_8349997 : Nat := 118140960795 + 8349997 * 2 ^ 59
def prefixEnd_8349997 : Nat := 4983230072969 + 3 ^ 40 * 8349997 * 2
def baseEnd_8349997 : Nat := 4287561924600472332036569

theorem tailTrace_8349997 : CollatzResearch.WordTrace tailWord_8349997 prefixEnd_8349997 4287561924600472332036569 := by
  unfold tailWord_8349997
  simp only [CollatzResearch.WordTrace]
  refine ⟨304549410330394409797800245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203032940220262939865200163 304549410330394409797800245)
  ·
    refine ⟨28551507218474475918543773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 304549410330394409797800245 28551507218474475918543773)
    ·
      refine ⟨10706815206927928469453915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28551507218474475918543773 10706815206927928469453915)
      ·
        refine ⟨16060222810391892704180873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10706815206927928469453915 16060222810391892704180873)
        ·
          refine ⟨12045167107793919528135655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16060222810391892704180873 12045167107793919528135655)
          ·
            refine ⟨18067750661690879292203483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12045167107793919528135655 18067750661690879292203483)
            ·
              refine ⟨27101625992536318938305225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18067750661690879292203483 27101625992536318938305225)
              ·
                refine ⟨20326219494402239203728919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27101625992536318938305225 20326219494402239203728919)
                ·
                  refine ⟨30489329241603358805593379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20326219494402239203728919 30489329241603358805593379)
                  ·
                    refine ⟨45733993862405038208390069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30489329241603358805593379 45733993862405038208390069)
                    ·
                      refine ⟨4287561924600472332036569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45733993862405038208390069 4287561924600472332036569)
                      ·
                        rfl

theorem cell23_8349997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_8349997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8349997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8349997 prefixEnd_8349997 := by exact prefixLift 8349997
  have htrace : WordTrace (prefixWord ++ tailWord_8349997) baseStart_8349997 baseEnd_8349997 := by
    simpa [prefixWord, tailWord_8349997, baseEnd_8349997] using wordTrace_append hprefix tailTrace_8349997
  have hstable : (prefixWord ++ tailWord_8349997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8349997).length < 2 ^ (prefixWord ++ tailWord_8349997).sum := by decide
  have hdescent : baseEnd_8349997 < baseStart_8349997 := by decide
  rcases family_descends (prefixWord ++ tailWord_8349997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350004 : List Nat := [2, 5, 1, 1, 1, 3, 3, 1, 2, 4]
def baseStart_8350004 : Nat := 118140960795 + 8350004 * 2 ^ 59
def prefixEnd_8350004 : Nat := 4983230072969 + 3 ^ 40 * 8350004 * 2
def baseEnd_8350004 : Nat := 1429188506321684601549679

theorem tailTrace_8350004 : CollatzResearch.WordTrace tailWord_8350004 prefixEnd_8350004 1429188506321684601549679 := by
  unfold tailWord_8350004
  simp only [CollatzResearch.WordTrace]
  refine ⟨152274832820684524996652533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203033110427579366662203377 152274832820684524996652533)
  ·
    refine ⟨14275765576939174218436175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152274832820684524996652533 14275765576939174218436175)
    ·
      refine ⟨21413648365408761327654263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14275765576939174218436175 21413648365408761327654263)
      ·
        refine ⟨32120472548113141991481395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21413648365408761327654263 32120472548113141991481395)
        ·
          refine ⟨48180708822169712987222093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32120472548113141991481395 48180708822169712987222093)
          ·
            refine ⟨18067765808313642370208285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48180708822169712987222093 18067765808313642370208285)
            ·
              refine ⟨6775412178117615888828107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18067765808313642370208285 6775412178117615888828107)
              ·
                refine ⟨10163118267176423833242161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6775412178117615888828107 10163118267176423833242161)
                ·
                  refine ⟨7622338700382317874931621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10163118267176423833242161 7622338700382317874931621)
                  ·
                    refine ⟨1429188506321684601549679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7622338700382317874931621 1429188506321684601549679)
                    ·
                      rfl

theorem cell23_8350004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_8350004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350004 prefixEnd_8350004 := by exact prefixLift 8350004
  have htrace : WordTrace (prefixWord ++ tailWord_8350004) baseStart_8350004 baseEnd_8350004 := by
    simpa [prefixWord, tailWord_8350004, baseEnd_8350004] using wordTrace_append hprefix tailTrace_8350004
  have hstable : (prefixWord ++ tailWord_8350004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350004).length < 2 ^ (prefixWord ++ tailWord_8350004).sum := by decide
  have hdescent : baseEnd_8350004 < baseStart_8350004 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350010 : List Nat := [3, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3]
def baseStart_8350010 : Nat := 118140960795 + 8350010 * 2 ^ 59
def prefixEnd_8350010 : Nat := 4983230072969 + 3 ^ 40 * 8350010 * 2
def baseEnd_8350010 : Nat := 4287568599848980781174009

theorem tailTrace_8350010 : CollatzResearch.WordTrace tailWord_8350010 prefixEnd_8350010 4287568599848980781174009 := by
  unfold tailWord_8350010
  simp only [CollatzResearch.WordTrace]
  refine ⟨76137471119836828254505871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203033256319564875345348989 76137471119836828254505871)
  ·
    refine ⟨114206206679755242381758807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76137471119836828254505871 114206206679755242381758807)
    ·
      refine ⟨171309310019632863572638211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114206206679755242381758807 171309310019632863572638211)
      ·
        refine ⟨256963965029449295358957317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171309310019632863572638211 256963965029449295358957317)
        ·
          refine ⟨48180743443021742879804497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256963965029449295358957317 48180743443021742879804497)
          ·
            refine ⟨36135557582266307159853373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48180743443021742879804497 36135557582266307159853373)
            ·
              refine ⟨13550834093349865184945015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36135557582266307159853373 13550834093349865184945015)
              ·
                refine ⟨20326251140024797777417523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13550834093349865184945015 20326251140024797777417523)
                ·
                  refine ⟨30489376710037196666126285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20326251140024797777417523 30489376710037196666126285)
                  ·
                    refine ⟨11433516266263948749797357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30489376710037196666126285 11433516266263948749797357)
                    ·
                      refine ⟨4287568599848980781174009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11433516266263948749797357 4287568599848980781174009)
                      ·
                        rfl

theorem cell23_8350010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3].length) (baseStart_8350010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350010 prefixEnd_8350010 := by exact prefixLift 8350010
  have htrace : WordTrace (prefixWord ++ tailWord_8350010) baseStart_8350010 baseEnd_8350010 := by
    simpa [prefixWord, tailWord_8350010, baseEnd_8350010] using wordTrace_append hprefix tailTrace_8350010
  have hstable : (prefixWord ++ tailWord_8350010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350010).length < 2 ^ (prefixWord ++ tailWord_8350010).sum := by decide
  have hdescent : baseEnd_8350010 < baseStart_8350010 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350016 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 8]
def baseStart_8350016 : Nat := 118140960795 + 8350016 * 2 ^ 59
def prefixEnd_8350016 : Nat := 4983230072969 + 3 ^ 40 * 8350016 * 2
def baseEnd_8350016 : Nat := 4287571680732907757698981

theorem tailTrace_8350016 : CollatzResearch.WordTrace tailWord_8350016 prefixEnd_8350016 4287571680732907757698981 := by
  unfold tailWord_8350016
  simp only [CollatzResearch.WordTrace]
  refine ⟨152275051658662788021370951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203033402211550384028494601 152275051658662788021370951)
  ·
    refine ⟨228412577487994182032056427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152275051658662788021370951 228412577487994182032056427)
    ·
      refine ⟨342618866231991273048084641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228412577487994182032056427 342618866231991273048084641)
      ·
        refine ⟨256964149673993454786063481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342618866231991273048084641 256964149673993454786063481)
        ·
          refine ⟨192723112255495091089547611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256964149673993454786063481 192723112255495091089547611)
          ·
            refine ⟨289084668383242636634321417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192723112255495091089547611 289084668383242636634321417)
            ·
              refine ⟨216813501287431977475741063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289084668383242636634321417 216813501287431977475741063)
              ·
                refine ⟨325220251931147966213611595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216813501287431977475741063 325220251931147966213611595)
                ·
                  refine ⟨487830377896721949320417393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 325220251931147966213611595 487830377896721949320417393)
                  ·
                    refine ⟨365872783422541461990313045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 487830377896721949320417393 365872783422541461990313045)
                    ·
                      refine ⟨4287571680732907757698981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 365872783422541461990313045 4287571680732907757698981)
                      ·
                        rfl

theorem cell23_8350016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_8350016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350016 prefixEnd_8350016 := by exact prefixLift 8350016
  have htrace : WordTrace (prefixWord ++ tailWord_8350016) baseStart_8350016 baseEnd_8350016 := by
    simpa [prefixWord, tailWord_8350016, baseEnd_8350016] using wordTrace_append hprefix tailTrace_8350016
  have hstable : (prefixWord ++ tailWord_8350016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350016).length < 2 ^ (prefixWord ++ tailWord_8350016).sum := by decide
  have hdescent : baseEnd_8350016 < baseStart_8350016 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350017 : List Nat := [1, 2, 5, 2, 2, 2, 2, 7]
def baseStart_8350017 : Nat := 118140960795 + 8350017 * 2 ^ 59
def prefixEnd_8350017 : Nat := 4983230072969 + 3 ^ 40 * 8350017 * 2
def baseEnd_8350017 : Nat := 158798970156057861251351

theorem tailTrace_8350017 : CollatzResearch.WordTrace tailWord_8350017 prefixEnd_8350017 158798970156057861251351 := by
  unfold tailWord_8350017
  simp only [CollatzResearch.WordTrace]
  refine ⟨304550139790321953213528305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203033426526881302142352203 304550139790321953213528305)
  ·
    refine ⟨228412604842741464910146229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304550139790321953213528305 228412604842741464910146229)
    ·
      refine ⟨21413681704007012335326209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228412604842741464910146229 21413681704007012335326209)
      ·
        refine ⟨16060261278005259251494657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21413681704007012335326209 16060261278005259251494657)
        ·
          refine ⟨12045195958503944438620993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16060261278005259251494657 12045195958503944438620993)
          ·
            refine ⟨9033896968877958328965745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12045195958503944438620993 9033896968877958328965745)
            ·
              refine ⟨6775422726658468746724309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9033896968877958328965745 6775422726658468746724309)
              ·
                refine ⟨158798970156057861251351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6775422726658468746724309 158798970156057861251351)
                ·
                  rfl

theorem cell23_8350017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 7].length) (baseStart_8350017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350017 prefixEnd_8350017 := by exact prefixLift 8350017
  have htrace : WordTrace (prefixWord ++ tailWord_8350017) baseStart_8350017 baseEnd_8350017 := by
    simpa [prefixWord, tailWord_8350017, baseEnd_8350017] using wordTrace_append hprefix tailTrace_8350017
  have hstable : (prefixWord ++ tailWord_8350017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350017).length < 2 ^ (prefixWord ++ tailWord_8350017).sum := by decide
  have hdescent : baseEnd_8350017 < baseStart_8350017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350067 : List Nat := [1, 1, 1, 2, 2, 1, 2, 7, 2, 2, 2]
def baseStart_8350067 : Nat := 118140960795 + 8350067 * 2 ^ 59
def prefixEnd_8350067 : Nat := 4983230072969 + 3 ^ 40 * 8350067 * 2
def baseEnd_8350067 : Nat := 4287597868246287058161247

theorem tailTrace_8350067 : CollatzResearch.WordTrace tailWord_8350067 prefixEnd_8350067 4287597868246287058161247 := by
  unfold tailWord_8350067
  simp only [CollatzResearch.WordTrace]
  refine ⟨304551963440140811752848455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203034642293427207835232303 304551963440140811752848455)
  ·
    refine ⟨456827945160211217629272683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304551963440140811752848455 456827945160211217629272683)
    ·
      refine ⟨685241917740316826443909025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456827945160211217629272683 685241917740316826443909025)
      ·
        refine ⟨513931438305237619832931769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 685241917740316826443909025 513931438305237619832931769)
        ·
          refine ⟨385448578728928214874698827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513931438305237619832931769 385448578728928214874698827)
          ·
            refine ⟨578172868093392322312048241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385448578728928214874698827 578172868093392322312048241)
            ·
              refine ⟨433629651070044241734036181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 578172868093392322312048241 433629651070044241734036181)
              ·
                refine ⟨10163194946954161915641473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 433629651070044241734036181 10163194946954161915641473)
                ·
                  refine ⟨7622396210215621436731105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10163194946954161915641473 7622396210215621436731105)
                  ·
                    refine ⟨5716797157661716077548329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7622396210215621436731105 5716797157661716077548329)
                    ·
                      refine ⟨4287597868246287058161247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5716797157661716077548329 4287597868246287058161247)
                      ·
                        rfl

theorem cell23_8350067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2, 2, 2].length) (baseStart_8350067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350067 prefixEnd_8350067 := by exact prefixLift 8350067
  have htrace : WordTrace (prefixWord ++ tailWord_8350067) baseStart_8350067 baseEnd_8350067 := by
    simpa [prefixWord, tailWord_8350067, baseEnd_8350067] using wordTrace_append hprefix tailTrace_8350067
  have hstable : (prefixWord ++ tailWord_8350067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350067).length < 2 ^ (prefixWord ++ tailWord_8350067).sum := by decide
  have hdescent : baseEnd_8350067 < baseStart_8350067 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350137 : List Nat := [1, 2, 1, 4, 3, 3, 1, 1, 2, 5]
def baseStart_8350137 : Nat := 118140960795 + 8350137 * 2 ^ 59
def prefixEnd_8350137 : Nat := 4983230072969 + 3 ^ 40 * 8350137 * 2
def baseEnd_8350137 : Nat := 1429211270630700594761975

theorem tailTrace_8350137 : CollatzResearch.WordTrace tailWord_8350137 prefixEnd_8350137 1429211270630700594761975 := by
  unfold tailWord_8350137
  simp only [CollatzResearch.WordTrace]
  refine ⟨304554516549887213707896665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203036344366591475805264443 304554516549887213707896665)
  ·
    refine ⟨228415887412415410280922499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304554516549887213707896665 228415887412415410280922499)
    ·
      refine ⟨342623831118623115421383749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228415887412415410280922499 342623831118623115421383749)
      ·
        refine ⟨64241968334741834141509453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 342623831118623115421383749 64241968334741834141509453)
        ·
          refine ⟨24090738125528187803066045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64241968334741834141509453 24090738125528187803066045)
          ·
            refine ⟨9034026797073070426149767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24090738125528187803066045 9034026797073070426149767)
            ·
              refine ⟨13551040195609605639224651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9034026797073070426149767 13551040195609605639224651)
              ·
                refine ⟨20326560293414408458836977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13551040195609605639224651 20326560293414408458836977)
                ·
                  refine ⟨15244920220060806344127733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20326560293414408458836977 15244920220060806344127733)
                  ·
                    refine ⟨1429211270630700594761975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15244920220060806344127733 1429211270630700594761975)
                    ·
                      rfl

theorem cell23_8350137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 5].length) (baseStart_8350137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350137 prefixEnd_8350137 := by exact prefixLift 8350137
  have htrace : WordTrace (prefixWord ++ tailWord_8350137) baseStart_8350137 baseEnd_8350137 := by
    simpa [prefixWord, tailWord_8350137, baseEnd_8350137] using wordTrace_append hprefix tailTrace_8350137
  have hstable : (prefixWord ++ tailWord_8350137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350137).length < 2 ^ (prefixWord ++ tailWord_8350137).sum := by decide
  have hdescent : baseEnd_8350137 < baseStart_8350137 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350153 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 2, 1, 6]
def baseStart_8350153 : Nat := 118140960795 + 8350153 * 2 ^ 59
def prefixEnd_8350153 : Nat := 4983230072969 + 3 ^ 40 * 8350153 * 2
def baseEnd_8350153 : Nat := 4287642027582573721685851

theorem tailTrace_8350153 : CollatzResearch.WordTrace tailWord_8350153 prefixEnd_8350153 4287642027582573721685851 := by
  unfold tailWord_8350153
  simp only [CollatzResearch.WordTrace]
  refine ⟨304555100117829248440479113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203036733411886165626986075 304555100117829248440479113)
  ·
    refine ⟨228416325088371936330359335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304555100117829248440479113 228416325088371936330359335)
    ·
      refine ⟨342624487632557904495539003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228416325088371936330359335 342624487632557904495539003)
      ·
        refine ⟨513936731448836856743308505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342624487632557904495539003 513936731448836856743308505)
        ·
          refine ⟨385452548586627642557481379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513936731448836856743308505 385452548586627642557481379)
          ·
            refine ⟨578178822879941463836222069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385452548586627642557481379 578178822879941463836222069)
            ·
              refine ⟨54204264644994512234645819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 578178822879941463836222069 54204264644994512234645819)
              ·
                refine ⟨81306396967491768351968729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54204264644994512234645819 81306396967491768351968729)
                ·
                  refine ⟨60979797725618826263976547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81306396967491768351968729 60979797725618826263976547)
                  ·
                    refine ⟨91469696588428239395964821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60979797725618826263976547 91469696588428239395964821)
                    ·
                      refine ⟨4287642027582573721685851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91469696588428239395964821 4287642027582573721685851)
                      ·
                        rfl

theorem cell23_8350153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 1, 6].length) (baseStart_8350153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350153 prefixEnd_8350153 := by exact prefixLift 8350153
  have htrace : WordTrace (prefixWord ++ tailWord_8350153) baseStart_8350153 baseEnd_8350153 := by
    simpa [prefixWord, tailWord_8350153, baseEnd_8350153] using wordTrace_append hprefix tailTrace_8350153
  have hstable : (prefixWord ++ tailWord_8350153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350153).length < 2 ^ (prefixWord ++ tailWord_8350153).sum := by decide
  have hdescent : baseEnd_8350153 < baseStart_8350153 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350203 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 5]
def baseStart_8350203 : Nat := 118140960795 + 8350203 * 2 ^ 59
def prefixEnd_8350203 : Nat := 4983230072969 + 3 ^ 40 * 8350203 * 2
def baseEnd_8350203 : Nat := 4287667701615298526060621

theorem tailTrace_8350203 : CollatzResearch.WordTrace tailWord_8350203 prefixEnd_8350203 4287667701615298526060621 := by
  unfold tailWord_8350203
  simp only [CollatzResearch.WordTrace]
  refine ⟨304556923767648106979799263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203037949178432071319866175 304556923767648106979799263)
  ·
    refine ⟨456835385651472160469698895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304556923767648106979799263 456835385651472160469698895)
    ·
      refine ⟨685253078477208240704548343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456835385651472160469698895 685253078477208240704548343)
      ·
        refine ⟨1027879617715812361056822515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685253078477208240704548343 1027879617715812361056822515)
        ·
          refine ⟨1541819426573718541585233773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1027879617715812361056822515 1541819426573718541585233773)
          ·
            refine ⟨578182284965144453094462665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1541819426573718541585233773 578182284965144453094462665)
            ·
              refine ⟨433636713723858339820846999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 578182284965144453094462665 433636713723858339820846999)
              ·
                refine ⟨650455070585787509731270499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433636713723858339820846999 650455070585787509731270499)
                ·
                  refine ⟨975682605878681264596905749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 650455070585787509731270499 975682605878681264596905749)
                  ·
                    refine ⟨45735122150563184277979957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 975682605878681264596905749 45735122150563184277979957)
                    ·
                      refine ⟨4287667701615298526060621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45735122150563184277979957 4287667701615298526060621)
                      ·
                        rfl

theorem cell23_8350203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 5].length) (baseStart_8350203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350203 prefixEnd_8350203 := by exact prefixLift 8350203
  have htrace : WordTrace (prefixWord ++ tailWord_8350203) baseStart_8350203 baseEnd_8350203 := by
    simpa [prefixWord, tailWord_8350203, baseEnd_8350203] using wordTrace_append hprefix tailTrace_8350203
  have hstable : (prefixWord ++ tailWord_8350203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350203).length < 2 ^ (prefixWord ++ tailWord_8350203).sum := by decide
  have hdescent : baseEnd_8350203 < baseStart_8350203 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350231 : List Nat := [1, 1, 3, 6, 1, 2, 2, 1, 6]
def baseStart_8350231 : Nat := 118140960795 + 8350231 * 2 ^ 59
def prefixEnd_8350231 : Nat := 4983230072969 + 3 ^ 40 * 8350231 * 2
def baseEnd_8350231 : Nat := 476409119897069379612277

theorem tailTrace_8350231 : CollatzResearch.WordTrace tailWord_8350231 prefixEnd_8350231 476409119897069379612277 := by
  unfold tailWord_8350231
  simp only [CollatzResearch.WordTrace]
  refine ⟨304557945011546667761818547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203038630007697778507879031 304557945011546667761818547)
  ·
    refine ⟨456836917517320001642727821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304557945011546667761818547 456836917517320001642727821)
    ·
      refine ⟨171313844068995000616022933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456836917517320001642727821 171313844068995000616022933)
      ·
        refine ⟨8030336440734140653876075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 171313844068995000616022933 8030336440734140653876075)
        ·
          refine ⟨12045504661101210980814113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8030336440734140653876075 12045504661101210980814113)
          ·
            refine ⟨9034128495825908235610585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12045504661101210980814113 9034128495825908235610585)
            ·
              refine ⟨6775596371869431176707939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9034128495825908235610585 6775596371869431176707939)
              ·
                refine ⟨10163394557804146765061909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6775596371869431176707939 10163394557804146765061909)
                ·
                  refine ⟨476409119897069379612277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10163394557804146765061909 476409119897069379612277)
                  ·
                    rfl

theorem cell23_8350231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 6].length) (baseStart_8350231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350231 prefixEnd_8350231 := by exact prefixLift 8350231
  have htrace : WordTrace (prefixWord ++ tailWord_8350231) baseStart_8350231 baseEnd_8350231 := by
    simpa [prefixWord, tailWord_8350231, baseEnd_8350231] using wordTrace_append hprefix tailTrace_8350231
  have hstable : (prefixWord ++ tailWord_8350231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350231).length < 2 ^ (prefixWord ++ tailWord_8350231).sum := by decide
  have hdescent : baseEnd_8350231 < baseStart_8350231 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350244 : List Nat := [2, 3, 1, 5, 1, 1, 1, 1, 3, 5]
def baseStart_8350244 : Nat := 118140960795 + 8350244 * 2 ^ 59
def prefixEnd_8350244 : Nat := 4983230072969 + 3 ^ 40 * 8350244 * 2
def baseEnd_8350244 : Nat := 1429229584774044288549311

theorem tailTrace_8350244 : CollatzResearch.WordTrace tailWord_8350244 prefixEnd_8350244 1429229584774044288549311 := by
  unfold tailWord_8350244
  simp only [CollatzResearch.WordTrace]
  refine ⟨152279209580249785491020893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203038946106999713988027857 152279209580249785491020893)
  ·
    refine ⟨57104703592593669559132835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152279209580249785491020893 57104703592593669559132835)
    ·
      refine ⟨85657055388890504338699253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57104703592593669559132835 85657055388890504338699253)
      ·
        refine ⟨8030348942708484781753055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85657055388890504338699253 8030348942708484781753055)
        ·
          refine ⟨12045523414062727172629583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8030348942708484781753055 12045523414062727172629583)
          ·
            refine ⟨18068285121094090758944375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12045523414062727172629583 18068285121094090758944375)
            ·
              refine ⟨27102427681641136138416563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18068285121094090758944375 27102427681641136138416563)
              ·
                refine ⟨40653641522461704207624845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27102427681641136138416563 40653641522461704207624845)
                ·
                  refine ⟨15245115570923139077859317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40653641522461704207624845 15245115570923139077859317)
                  ·
                    refine ⟨1429229584774044288549311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15245115570923139077859317 1429229584774044288549311)
                    ·
                      rfl

theorem cell23_8350244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_8350244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350244 prefixEnd_8350244 := by exact prefixLift 8350244
  have htrace : WordTrace (prefixWord ++ tailWord_8350244) baseStart_8350244 baseEnd_8350244 := by
    simpa [prefixWord, tailWord_8350244, baseEnd_8350244] using wordTrace_append hprefix tailTrace_8350244
  have hstable : (prefixWord ++ tailWord_8350244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350244).length < 2 ^ (prefixWord ++ tailWord_8350244).sum := by decide
  have hdescent : baseEnd_8350244 < baseStart_8350244 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350264 : List Nat := [2, 1, 2, 1, 4, 1, 5, 1, 1, 1, 4]
def baseStart_8350264 : Nat := 118140960795 + 8350264 * 2 ^ 59
def prefixEnd_8350264 : Nat := 4983230072969 + 3 ^ 40 * 8350264 * 2
def baseEnd_8350264 : Nat := 4287699023935222787397841

theorem tailTrace_8350264 : CollatzResearch.WordTrace tailWord_8350264 prefixEnd_8350264 4287699023935222787397841 := by
  unfold tailWord_8350264
  simp only [CollatzResearch.WordTrace]
  refine ⟨152279574310213557198884923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203039432413618076265179897 152279574310213557198884923)
  ·
    refine ⟨228419361465320335798327385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152279574310213557198884923 228419361465320335798327385)
    ·
      refine ⟨171314521098990251848745539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228419361465320335798327385 171314521098990251848745539)
      ·
        refine ⟨256971781648485377773118309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171314521098990251848745539 256971781648485377773118309)
        ·
          refine ⟨48182209059091008332459683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256971781648485377773118309 48182209059091008332459683)
          ·
            refine ⟨72273313588636512498689525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48182209059091008332459683 72273313588636512498689525)
            ·
              refine ⟨6775623148934673046752143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72273313588636512498689525 6775623148934673046752143)
              ·
                refine ⟨10163434723402009570128215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6775623148934673046752143 10163434723402009570128215)
                ·
                  refine ⟨15245152085103014355192323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10163434723402009570128215 15245152085103014355192323)
                  ·
                    refine ⟨22867728127654521532788485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15245152085103014355192323 22867728127654521532788485)
                    ·
                      refine ⟨4287699023935222787397841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22867728127654521532788485 4287699023935222787397841)
                      ·
                        rfl

theorem cell23_8350264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 1, 1, 4].length) (baseStart_8350264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350264 prefixEnd_8350264 := by exact prefixLift 8350264
  have htrace : WordTrace (prefixWord ++ tailWord_8350264) baseStart_8350264 baseEnd_8350264 := by
    simpa [prefixWord, tailWord_8350264, baseEnd_8350264] using wordTrace_append hprefix tailTrace_8350264
  have hstable : (prefixWord ++ tailWord_8350264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350264).length < 2 ^ (prefixWord ++ tailWord_8350264).sum := by decide
  have hdescent : baseEnd_8350264 < baseStart_8350264 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350297 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 8, 1, 3]
def baseStart_8350297 : Nat := 118140960795 + 8350297 * 2 ^ 59
def prefixEnd_8350297 : Nat := 4983230072969 + 3 ^ 40 * 8350297 * 2
def baseEnd_8350297 : Nat := 4287715968796821158285189

theorem tailTrace_8350297 : CollatzResearch.WordTrace tailWord_8350297 prefixEnd_8350297 4287715968796821158285189 := by
  unfold tailWord_8350297
  simp only [CollatzResearch.WordTrace]
  refine ⟨304560352229307561033721145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203040234819538374022480763 304560352229307561033721145)
  ·
    refine ⟨228420264171980670775290859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304560352229307561033721145 228420264171980670775290859)
    ·
      refine ⟨342630396257971006162936289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228420264171980670775290859 342630396257971006162936289)
      ·
        refine ⟨256972797193478254622202217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342630396257971006162936289 256972797193478254622202217)
        ·
          refine ⟨192729597895108690966651663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256972797193478254622202217 192729597895108690966651663)
          ·
            refine ⟨289094396842663036449977495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192729597895108690966651663 289094396842663036449977495)
            ·
              refine ⟨433641595263994554674966243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289094396842663036449977495 433641595263994554674966243)
              ·
                refine ⟨650462392895991832012449365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433641595263994554674966243 650462392895991832012449365)
                ·
                  refine ⟨7622606166749904281395891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 650462392895991832012449365 7622606166749904281395891)
                  ·
                    refine ⟨11433909250124856422093837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7622606166749904281395891 11433909250124856422093837)
                    ·
                      refine ⟨4287715968796821158285189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11433909250124856422093837 4287715968796821158285189)
                      ·
                        rfl

theorem cell23_8350297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8, 1, 3].length) (baseStart_8350297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350297 prefixEnd_8350297 := by exact prefixLift 8350297
  have htrace : WordTrace (prefixWord ++ tailWord_8350297) baseStart_8350297 baseEnd_8350297 := by
    simpa [prefixWord, tailWord_8350297, baseEnd_8350297] using wordTrace_append hprefix tailTrace_8350297
  have hstable : (prefixWord ++ tailWord_8350297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350297).length < 2 ^ (prefixWord ++ tailWord_8350297).sum := by decide
  have hdescent : baseEnd_8350297 < baseStart_8350297 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350302 : List Nat := [4, 4, 1, 2, 1, 2, 1, 1, 2, 3, 2]
def baseStart_8350302 : Nat := 118140960795 + 8350302 * 2 ^ 59
def prefixEnd_8350302 : Nat := 4983230072969 + 3 ^ 40 * 8350302 * 2
def baseEnd_8350302 : Nat := 4287718536200093638722667

theorem tailTrace_8350302 : CollatzResearch.WordTrace tailWord_8350302 prefixEnd_8350302 4287718536200093638722667 := by
  unfold tailWord_8350302
  simp only [CollatzResearch.WordTrace]
  refine ⟨38070066824286180860956645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203040356396192964591768773 38070066824286180860956645)
  ·
    refine ⟨7138137529553658911429371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38070066824286180860956645 7138137529553658911429371)
    ·
      refine ⟨10707206294330488367144057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7138137529553658911429371 10707206294330488367144057)
      ·
        refine ⟨8030404720747866275358043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10707206294330488367144057 8030404720747866275358043)
        ·
          refine ⟨12045607081121799413037065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8030404720747866275358043 12045607081121799413037065)
          ·
            refine ⟨9034205310841349559777799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12045607081121799413037065 9034205310841349559777799)
            ·
              refine ⟨13551307966262024339666699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9034205310841349559777799 13551307966262024339666699)
              ·
                refine ⟨20326961949393036509500049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13551307966262024339666699 20326961949393036509500049)
                ·
                  refine ⟨15245221462044777382125037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20326961949393036509500049 15245221462044777382125037)
                  ·
                    refine ⟨5716958048266791518296889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15245221462044777382125037 5716958048266791518296889)
                    ·
                      refine ⟨4287718536200093638722667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5716958048266791518296889 4287718536200093638722667)
                      ·
                        rfl

theorem cell23_8350302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_8350302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350302 prefixEnd_8350302 := by exact prefixLift 8350302
  have htrace : WordTrace (prefixWord ++ tailWord_8350302) baseStart_8350302 baseEnd_8350302 := by
    simpa [prefixWord, tailWord_8350302, baseEnd_8350302] using wordTrace_append hprefix tailTrace_8350302
  have hstable : (prefixWord ++ tailWord_8350302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350302).length < 2 ^ (prefixWord ++ tailWord_8350302).sum := by decide
  have hdescent : baseEnd_8350302 < baseStart_8350302 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350314 : List Nat := [3, 1, 3, 2, 1, 1, 2, 2, 4, 1, 3]
def baseStart_8350314 : Nat := 118140960795 + 8350314 * 2 ^ 59
def prefixEnd_8350314 : Nat := 4983230072969 + 3 ^ 40 * 8350314 * 2
def baseEnd_8350314 : Nat := 4287724697967947591772611

theorem tailTrace_8350314 : CollatzResearch.WordTrace tailWord_8350314 prefixEnd_8350314 4287724697967947591772611 := by
  unfold tailWord_8350314
  simp only [CollatzResearch.WordTrace]
  refine ⟨76140243067561493234272499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203040648180163981958059997 76140243067561493234272499)
  ·
    refine ⟨114210364601342239851408749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76140243067561493234272499 114210364601342239851408749)
    ·
      refine ⟨42828886725503339944278281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114210364601342239851408749 42828886725503339944278281)
      ·
        refine ⟨32121665044127504958208711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42828886725503339944278281 32121665044127504958208711)
        ·
          refine ⟨48182497566191257437313067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32121665044127504958208711 48182497566191257437313067)
          ·
            refine ⟨72273746349286886155969601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48182497566191257437313067 72273746349286886155969601)
            ·
              refine ⟨54205309761965164616977201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72273746349286886155969601 54205309761965164616977201)
              ·
                refine ⟨40653982321473873462732901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54205309761965164616977201 40653982321473873462732901)
                ·
                  refine ⟨7622621685276351274262419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40653982321473873462732901 7622621685276351274262419)
                  ·
                    refine ⟨11433932527914526911393629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7622621685276351274262419 11433932527914526911393629)
                    ·
                      refine ⟨4287724697967947591772611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11433932527914526911393629 4287724697967947591772611)
                      ·
                        rfl

theorem cell23_8350314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_8350314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350314 prefixEnd_8350314 := by exact prefixLift 8350314
  have htrace : WordTrace (prefixWord ++ tailWord_8350314) baseStart_8350314 baseEnd_8350314 := by
    simpa [prefixWord, tailWord_8350314, baseEnd_8350314] using wordTrace_append hprefix tailTrace_8350314
  have hstable : (prefixWord ++ tailWord_8350314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350314).length < 2 ^ (prefixWord ++ tailWord_8350314).sum := by decide
  have hdescent : baseEnd_8350314 < baseStart_8350314 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350318 : List Nat := [4, 1, 2, 2, 2, 3, 2, 1, 1, 2, 3]
def baseStart_8350318 : Nat := 118140960795 + 8350318 * 2 ^ 59
def prefixEnd_8350318 : Nat := 4983230072969 + 3 ^ 40 * 8350318 * 2
def baseEnd_8350318 : Nat := 4287726751890565576122593

theorem tailTrace_8350318 : CollatzResearch.WordTrace tailWord_8350318 prefixEnd_8350318 4287726751890565576122593 := by
  unfold tailWord_8350318
  simp only [CollatzResearch.WordTrace]
  refine ⟨38070139770278935202529451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203040745441487654413490405 38070139770278935202529451)
  ·
    refine ⟨57105209655418402803794177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38070139770278935202529451 57105209655418402803794177)
    ·
      refine ⟨42828907241563802102845633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57105209655418402803794177 42828907241563802102845633)
      ·
        refine ⟨32121680431172851577134225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42828907241563802102845633 32121680431172851577134225)
        ·
          refine ⟨24091260323379638682850669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32121680431172851577134225 24091260323379638682850669)
          ·
            refine ⟨9034222621267364506069001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24091260323379638682850669 9034222621267364506069001)
            ·
              refine ⟨6775666965950523379551751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9034222621267364506069001 6775666965950523379551751)
              ·
                refine ⟨10163500448925785069327627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6775666965950523379551751 10163500448925785069327627)
                ·
                  refine ⟨15245250673388677603991441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10163500448925785069327627 15245250673388677603991441)
                  ·
                    refine ⟨11433938005041508202993581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15245250673388677603991441 11433938005041508202993581)
                    ·
                      refine ⟨4287726751890565576122593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11433938005041508202993581 4287726751890565576122593)
                      ·
                        rfl

theorem cell23_8350318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_8350318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350318 prefixEnd_8350318 := by exact prefixLift 8350318
  have htrace : WordTrace (prefixWord ++ tailWord_8350318) baseStart_8350318 baseEnd_8350318 := by
    simpa [prefixWord, tailWord_8350318, baseEnd_8350318] using wordTrace_append hprefix tailTrace_8350318
  have hstable : (prefixWord ++ tailWord_8350318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350318).length < 2 ^ (prefixWord ++ tailWord_8350318).sum := by decide
  have hdescent : baseEnd_8350318 < baseStart_8350318 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350380 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 6]
def baseStart_8350380 : Nat := 118140960795 + 8350380 * 2 ^ 59
def prefixEnd_8350380 : Nat := 4983230072969 + 3 ^ 40 * 8350380 * 2
def baseEnd_8350380 : Nat := 4287758587691144333547307

theorem tailTrace_8350380 : CollatzResearch.WordTrace tailWord_8350380 prefixEnd_8350380 4287758587691144333547307 := by
  unfold tailWord_8350380
  simp only [CollatzResearch.WordTrace]
  refine ⟨152281689744003433104496297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203042252992004577472661729 152281689744003433104496297)
  ·
    refine ⟨114211267308002574828372223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152281689744003433104496297 114211267308002574828372223)
    ·
      refine ⟨171316900962003862242558335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114211267308002574828372223 171316900962003862242558335)
      ·
        refine ⟨256975351443005793363837503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171316900962003862242558335 256975351443005793363837503)
        ·
          refine ⟨385463027164508690045756255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256975351443005793363837503 385463027164508690045756255)
          ·
            refine ⟨578194540746763035068634383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385463027164508690045756255 578194540746763035068634383)
            ·
              refine ⟨867291811120144552602951575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578194540746763035068634383 867291811120144552602951575)
              ·
                refine ⟨1300937716680216828904427363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 867291811120144552602951575 1300937716680216828904427363)
                ·
                  refine ⟨1951406575020325243356641045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1300937716680216828904427363 1951406575020325243356641045)
                  ·
                    refine ⟨91472183204077745782342549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1951406575020325243356641045 91472183204077745782342549)
                    ·
                      refine ⟨4287758587691144333547307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91472183204077745782342549 4287758587691144333547307)
                      ·
                        rfl

theorem cell23_8350380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_8350380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350380 prefixEnd_8350380 := by exact prefixLift 8350380
  have htrace : WordTrace (prefixWord ++ tailWord_8350380) baseStart_8350380 baseEnd_8350380 := by
    simpa [prefixWord, tailWord_8350380, baseEnd_8350380] using wordTrace_append hprefix tailTrace_8350380
  have hstable : (prefixWord ++ tailWord_8350380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350380).length < 2 ^ (prefixWord ++ tailWord_8350380).sum := by decide
  have hdescent : baseEnd_8350380 < baseStart_8350380 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350424 : List Nat := [2, 1, 2, 2, 3, 3, 2, 1, 2, 5]
def baseStart_8350424 : Nat := 118140960795 + 8350424 * 2 ^ 59
def prefixEnd_8350424 : Nat := 4983230072969 + 3 ^ 40 * 8350424 * 2
def baseEnd_8350424 : Nat := 1429260393613314053799035

theorem tailTrace_8350424 : CollatzResearch.WordTrace tailWord_8350424 prefixEnd_8350424 1429260393613314053799035 := by
  unfold tailWord_8350424
  simp only [CollatzResearch.WordTrace]
  refine ⟨152282492149923730861797163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203043322866564974482396217 152282492149923730861797163)
  ·
    refine ⟨228423738224885596292695745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152282492149923730861797163 228423738224885596292695745)
    ·
      refine ⟨171317803668664197219521809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228423738224885596292695745 171317803668664197219521809)
      ·
        refine ⟨128488352751498147914641357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171317803668664197219521809 128488352751498147914641357)
        ·
          refine ⟨48183132281811805467990509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128488352751498147914641357 48183132281811805467990509)
          ·
            refine ⟨18068674605679427050496441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48183132281811805467990509 18068674605679427050496441)
            ·
              refine ⟨13551505954259570287872331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18068674605679427050496441 13551505954259570287872331)
              ·
                refine ⟨20327258931389355431808497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13551505954259570287872331 20327258931389355431808497)
                ·
                  refine ⟨15245444198542016573856373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20327258931389355431808497 15245444198542016573856373)
                  ·
                    refine ⟨1429260393613314053799035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15245444198542016573856373 1429260393613314053799035)
                    ·
                      rfl

theorem cell23_8350424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 2, 5].length) (baseStart_8350424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350424 prefixEnd_8350424 := by exact prefixLift 8350424
  have htrace : WordTrace (prefixWord ++ tailWord_8350424) baseStart_8350424 baseEnd_8350424 := by
    simpa [prefixWord, tailWord_8350424, baseEnd_8350424] using wordTrace_append hprefix tailTrace_8350424
  have hstable : (prefixWord ++ tailWord_8350424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350424).length < 2 ^ (prefixWord ++ tailWord_8350424).sum := by decide
  have hdescent : baseEnd_8350424 < baseStart_8350424 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350444 : List Nat := [2, 2, 1, 1, 2, 2, 1, 4, 2, 4, 2]
def baseStart_8350444 : Nat := 118140960795 + 8350444 * 2 ^ 59
def prefixEnd_8350444 : Nat := 4983230072969 + 3 ^ 40 * 8350444 * 2
def baseEnd_8350444 : Nat := 4287791450453032083147013

theorem tailTrace_8350444 : CollatzResearch.WordTrace tailWord_8350444 prefixEnd_8350444 4287791450453032083147013 := by
  unfold tailWord_8350444
  simp only [CollatzResearch.WordTrace]
  refine ⟨152282856879887502569661193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203043809173183336759548257 152282856879887502569661193)
  ·
    refine ⟨114212142659915626927245895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152282856879887502569661193 114212142659915626927245895)
    ·
      refine ⟨171318213989873440390868843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114212142659915626927245895 171318213989873440390868843)
      ·
        refine ⟨256977320984810160586303265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171318213989873440390868843 256977320984810160586303265)
        ·
          refine ⟨192732990738607620439727449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256977320984810160586303265 192732990738607620439727449)
          ·
            refine ⟨144549743053955715329795587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192732990738607620439727449 144549743053955715329795587)
            ·
              refine ⟨216824614580933572994693381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144549743053955715329795587 216824614580933572994693381)
              ·
                refine ⟨40654615233925044936505009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216824614580933572994693381 40654615233925044936505009)
                ·
                  refine ⟨30490961425443783702378757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40654615233925044936505009 30490961425443783702378757)
                  ·
                    refine ⟨5717055267270709444196017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30490961425443783702378757 5717055267270709444196017)
                    ·
                      refine ⟨4287791450453032083147013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5717055267270709444196017 4287791450453032083147013)
                      ·
                        rfl

theorem cell23_8350444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 4, 2].length) (baseStart_8350444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350444 prefixEnd_8350444 := by exact prefixLift 8350444
  have htrace : WordTrace (prefixWord ++ tailWord_8350444) baseStart_8350444 baseEnd_8350444 := by
    simpa [prefixWord, tailWord_8350444, baseEnd_8350444] using wordTrace_append hprefix tailTrace_8350444
  have hstable : (prefixWord ++ tailWord_8350444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350444).length < 2 ^ (prefixWord ++ tailWord_8350444).sum := by decide
  have hdescent : baseEnd_8350444 < baseStart_8350444 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350471 : List Nat := [1, 1, 4, 4, 1, 2, 1, 2, 3, 4]
def baseStart_8350471 : Nat := 118140960795 + 8350471 * 2 ^ 59
def prefixEnd_8350471 : Nat := 4983230072969 + 3 ^ 40 * 8350471 * 2
def baseEnd_8350471 : Nat := 1429268438143567825836463

theorem tailTrace_8350471 : CollatzResearch.WordTrace tailWord_8350471 prefixEnd_8350471 1429268438143567825836463 := by
  unfold tailWord_8350471
  simp only [CollatzResearch.WordTrace]
  refine ⟨304566698530677188750555267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203044465687118125833703511 304566698530677188750555267)
  ·
    refine ⟨456850047796015783125832901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304566698530677188750555267 456850047796015783125832901)
    ·
      refine ⟨85659383961752959336093669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 456850047796015783125832901 85659383961752959336093669)
      ·
        refine ⟨16061134492828679875517563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85659383961752959336093669 16061134492828679875517563)
        ·
          refine ⟨24091701739243019813276345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16061134492828679875517563 24091701739243019813276345)
          ·
            refine ⟨18068776304432264859957259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24091701739243019813276345 18068776304432264859957259)
            ·
              refine ⟨27103164456648397289935889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18068776304432264859957259 27103164456648397289935889)
              ·
                refine ⟨20327373342486297967451917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27103164456648397289935889 20327373342486297967451917)
                ·
                  refine ⟨7622765003432361737794469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20327373342486297967451917 7622765003432361737794469)
                  ·
                    refine ⟨1429268438143567825836463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7622765003432361737794469 1429268438143567825836463)
                    ·
                      rfl

theorem cell23_8350471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_8350471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350471 prefixEnd_8350471 := by exact prefixLift 8350471
  have htrace : WordTrace (prefixWord ++ tailWord_8350471) baseStart_8350471 baseEnd_8350471 := by
    simpa [prefixWord, tailWord_8350471, baseEnd_8350471] using wordTrace_append hprefix tailTrace_8350471
  have hstable : (prefixWord ++ tailWord_8350471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350471).length < 2 ^ (prefixWord ++ tailWord_8350471).sum := by decide
  have hdescent : baseEnd_8350471 < baseStart_8350471 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350544 : List Nat := [2, 1, 1, 1, 1, 4, 3, 2, 4, 4]
def baseStart_8350544 : Nat := 118140960795 + 8350544 * 2 ^ 59
def prefixEnd_8350544 : Nat := 4983230072969 + 3 ^ 40 * 8350544 * 2
def baseEnd_8350544 : Nat := 1429280932839493897298851

theorem tailTrace_8350544 : CollatzResearch.WordTrace tailWord_8350544 prefixEnd_8350544 1429280932839493897298851 := by
  unfold tailWord_8350544
  simp only [CollatzResearch.WordTrace]
  refine ⟨152284680529706361108981343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203046240706275148145308457 152284680529706361108981343)
  ·
    refine ⟨228427020794559541663472015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152284680529706361108981343 228427020794559541663472015)
    ·
      refine ⟨342640531191839312495208023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228427020794559541663472015 342640531191839312495208023)
      ·
        refine ⟨513960796787758968742812035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342640531191839312495208023 513960796787758968742812035)
        ·
          refine ⟨770941195181638453114218053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513960796787758968742812035 770941195181638453114218053)
          ·
            refine ⟨144551474096557209958915885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 770941195181638453114218053 144551474096557209958915885)
            ·
              refine ⟨54206802786208953734593457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144551474096557209958915885 54206802786208953734593457)
              ·
                refine ⟨40655102089656715300945093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54206802786208953734593457 40655102089656715300945093)
                ·
                  refine ⟨7622831641810634118927205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40655102089656715300945093 7622831641810634118927205)
                  ·
                    refine ⟨1429280932839493897298851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7622831641810634118927205 1429280932839493897298851)
                    ·
                      rfl

theorem cell23_8350544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 4, 4].length) (baseStart_8350544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350544 prefixEnd_8350544 := by exact prefixLift 8350544
  have htrace : WordTrace (prefixWord ++ tailWord_8350544) baseStart_8350544 baseEnd_8350544 := by
    simpa [prefixWord, tailWord_8350544, baseEnd_8350544] using wordTrace_append hprefix tailTrace_8350544
  have hstable : (prefixWord ++ tailWord_8350544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350544).length < 2 ^ (prefixWord ++ tailWord_8350544).sum := by decide
  have hdescent : baseEnd_8350544 < baseStart_8350544 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350551 : List Nat := [1, 1, 3, 2, 4, 1, 2, 3, 1, 1, 4]
def baseStart_8350551 : Nat := 118140960795 + 8350551 * 2 ^ 59
def prefixEnd_8350551 : Nat := 4983230072969 + 3 ^ 40 * 8350551 * 2
def baseEnd_8350551 : Nat := 4287846392883063164509021

theorem tailTrace_8350551 : CollatzResearch.WordTrace tailWord_8350551 prefixEnd_8350551 4287846392883063164509021 := by
  unfold tailWord_8350551
  simp only [CollatzResearch.WordTrace]
  refine ⟨304569616370387362413467507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203046410913591574942311671 304569616370387362413467507)
  ·
    refine ⟨456854424555581043620201261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304569616370387362413467507 456854424555581043620201261)
    ·
      refine ⟨171320409208342891357575473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456854424555581043620201261 171320409208342891357575473)
      ·
        refine ⟨128490306906257168518181605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171320409208342891357575473 128490306906257168518181605)
        ·
          refine ⟨24091932544923219097159051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128490306906257168518181605 24091932544923219097159051)
          ·
            refine ⟨36137898817384828645738577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24091932544923219097159051 36137898817384828645738577)
            ·
              refine ⟨27103424113038621484303933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36137898817384828645738577 27103424113038621484303933)
              ·
                refine ⟨10163784042389483056613975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27103424113038621484303933 10163784042389483056613975)
                ·
                  refine ⟨15245676063584224584920963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10163784042389483056613975 15245676063584224584920963)
                  ·
                    refine ⟨22868514095376336877381445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15245676063584224584920963 22868514095376336877381445)
                    ·
                      refine ⟨4287846392883063164509021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22868514095376336877381445 4287846392883063164509021)
                      ·
                        rfl

theorem cell23_8350551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_8350551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350551 prefixEnd_8350551 := by exact prefixLift 8350551
  have htrace : WordTrace (prefixWord ++ tailWord_8350551) baseStart_8350551 baseEnd_8350551 := by
    simpa [prefixWord, tailWord_8350551, baseEnd_8350551] using wordTrace_append hprefix tailTrace_8350551
  have hstable : (prefixWord ++ tailWord_8350551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350551).length < 2 ^ (prefixWord ++ tailWord_8350551).sum := by decide
  have hdescent : baseEnd_8350551 < baseStart_8350551 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350554 : List Nat := [3, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5]
def baseStart_8350554 : Nat := 118140960795 + 8350554 * 2 ^ 59
def prefixEnd_8350554 : Nat := 4983230072969 + 3 ^ 40 * 8350554 * 2
def baseEnd_8350554 : Nat := 4287847933325026652771507

theorem tailTrace_8350554 : CollatzResearch.WordTrace tailWord_8350554 prefixEnd_8350554 4287847933325026652771507 := by
  unfold tailWord_8350554
  simp only [CollatzResearch.WordTrace]
  refine ⟨76142431447344123481456679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203046483859584329283884477 76142431447344123481456679)
  ·
    refine ⟨114213647171016185222185019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76142431447344123481456679 114213647171016185222185019)
    ·
      refine ⟨171320470756524277833277529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114213647171016185222185019 171320470756524277833277529)
      ·
        refine ⟨128490353067393208374958147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171320470756524277833277529 128490353067393208374958147)
        ·
          refine ⟨192735529601089812562437221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128490353067393208374958147 192735529601089812562437221)
          ·
            refine ⟨36137911800204339855456979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192735529601089812562437221 36137911800204339855456979)
            ·
              refine ⟨54206867700306509783185469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36137911800204339855456979 54206867700306509783185469)
              ·
                refine ⟨20327575387614941168694551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54206867700306509783185469 20327575387614941168694551)
                ·
                  refine ⟨30491363081422411753041827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20327575387614941168694551 30491363081422411753041827)
                  ·
                    refine ⟨45737044622133617629562741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30491363081422411753041827 45737044622133617629562741)
                    ·
                      refine ⟨4287847933325026652771507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45737044622133617629562741 4287847933325026652771507)
                      ·
                        rfl

theorem cell23_8350554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_8350554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350554 prefixEnd_8350554 := by exact prefixLift 8350554
  have htrace : WordTrace (prefixWord ++ tailWord_8350554) baseStart_8350554 baseEnd_8350554 := by
    simpa [prefixWord, tailWord_8350554, baseEnd_8350554] using wordTrace_append hprefix tailTrace_8350554
  have hstable : (prefixWord ++ tailWord_8350554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350554).length < 2 ^ (prefixWord ++ tailWord_8350554).sum := by decide
  have hdescent : baseEnd_8350554 < baseStart_8350554 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350562 : List Nat := [3, 3, 2, 1, 4, 1, 1, 1, 3, 1, 3]
def baseStart_8350562 : Nat := 118140960795 + 8350562 * 2 ^ 59
def prefixEnd_8350562 : Nat := 4983230072969 + 3 ^ 40 * 8350562 * 2
def baseEnd_8350562 : Nat := 4287852041170262621471471

theorem tailTrace_8350562 : CollatzResearch.WordTrace tailWord_8350562 prefixEnd_8350562 4287852041170262621471471 := by
  unfold tailWord_8350562
  simp only [CollatzResearch.WordTrace]
  refine ⟨76142504393336877823029485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203046678382231674194745293 76142504393336877823029485)
  ·
    refine ⟨28553439147501329183636057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76142504393336877823029485 28553439147501329183636057)
    ·
      refine ⟨21415079360625996887727043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28553439147501329183636057 21415079360625996887727043)
      ·
        refine ⟨32122619040938995331590565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21415079360625996887727043 32122619040938995331590565)
        ·
          refine ⟨6022991070176061624673231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32122619040938995331590565 6022991070176061624673231)
          ·
            refine ⟨9034486605264092437009847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6022991070176061624673231 9034486605264092437009847)
            ·
              refine ⟨13551729907896138655514771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9034486605264092437009847 13551729907896138655514771)
              ·
                refine ⟨20327594861844207983272157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13551729907896138655514771 20327594861844207983272157)
                ·
                  refine ⟨7622848073191577993727059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20327594861844207983272157 7622848073191577993727059)
                  ·
                    refine ⟨11434272109787366990590589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7622848073191577993727059 11434272109787366990590589)
                    ·
                      refine ⟨4287852041170262621471471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11434272109787366990590589 4287852041170262621471471)
                      ·
                        rfl

theorem cell23_8350562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_8350562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350562 prefixEnd_8350562 := by exact prefixLift 8350562
  have htrace : WordTrace (prefixWord ++ tailWord_8350562) baseStart_8350562 baseEnd_8350562 := by
    simpa [prefixWord, tailWord_8350562, baseEnd_8350562] using wordTrace_append hprefix tailTrace_8350562
  have hstable : (prefixWord ++ tailWord_8350562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350562).length < 2 ^ (prefixWord ++ tailWord_8350562).sum := by decide
  have hdescent : baseEnd_8350562 < baseStart_8350562 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350564 : List Nat := [2, 3, 1, 1, 4, 1, 1, 2, 1, 1, 6]
def baseStart_8350564 : Nat := 118140960795 + 8350564 * 2 ^ 59
def prefixEnd_8350564 : Nat := 4983230072969 + 3 ^ 40 * 8350564 * 2
def baseEnd_8350564 : Nat := 4287853068131571613646461

theorem tailTrace_8350564 : CollatzResearch.WordTrace tailWord_8350564 prefixEnd_8350564 4287853068131571613646461 := by
  unfold tailWord_8350564
  simp only [CollatzResearch.WordTrace]
  refine ⟨152285045259670132816845373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203046727012893510422460497 152285045259670132816845373)
  ·
    refine ⟨57106891972376299806317015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152285045259670132816845373 57106891972376299806317015)
    ·
      refine ⟨85660337958564449709475523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57106891972376299806317015 85660337958564449709475523)
      ·
        refine ⟨128490506937846674564213285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85660337958564449709475523 128490506937846674564213285)
        ·
          refine ⟨24091970050846251480789991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128490506937846674564213285 24091970050846251480789991)
          ·
            refine ⟨36137955076269377221184987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24091970050846251480789991 36137955076269377221184987)
            ·
              refine ⟨54206932614404065831777481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36137955076269377221184987 54206932614404065831777481)
              ·
                refine ⟨40655199460803049373833111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54206932614404065831777481 40655199460803049373833111)
                ·
                  refine ⟨60982799191204574060749667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40655199460803049373833111 60982799191204574060749667)
                  ·
                    refine ⟨91474198786806861091124501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60982799191204574060749667 91474198786806861091124501)
                    ·
                      refine ⟨4287853068131571613646461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91474198786806861091124501 4287853068131571613646461)
                      ·
                        rfl

theorem cell23_8350564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_8350564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350564 prefixEnd_8350564 := by exact prefixLift 8350564
  have htrace : WordTrace (prefixWord ++ tailWord_8350564) baseStart_8350564 baseEnd_8350564 := by
    simpa [prefixWord, tailWord_8350564, baseEnd_8350564] using wordTrace_append hprefix tailTrace_8350564
  have hstable : (prefixWord ++ tailWord_8350564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350564).length < 2 ^ (prefixWord ++ tailWord_8350564).sum := by decide
  have hdescent : baseEnd_8350564 < baseStart_8350564 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350578 : List Nat := [3, 2, 1, 2, 1, 1, 6, 1, 2, 4]
def baseStart_8350578 : Nat := 118140960795 + 8350578 * 2 ^ 59
def prefixEnd_8350578 : Nat := 4983230072969 + 3 ^ 40 * 8350578 * 2
def baseEnd_8350578 : Nat := 1429286752286911519623799

theorem tailTrace_8350578 : CollatzResearch.WordTrace tailWord_8350578 prefixEnd_8350578 1429286752286911519623799 := by
  unfold tailWord_8350578
  simp only [CollatzResearch.WordTrace]
  refine ⟨76142650285322386506175097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203047067427526364016466925 76142650285322386506175097)
  ·
    refine ⟨57106987713991789879631323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76142650285322386506175097 57106987713991789879631323)
    ·
      refine ⟨85660481570987684819446985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57106987713991789879631323 85660481570987684819446985)
      ·
        refine ⟨64245361178240763614585239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85660481570987684819446985 64245361178240763614585239)
        ·
          refine ⟨96368041767361145421877859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64245361178240763614585239 96368041767361145421877859)
          ·
            refine ⟨144552062651041718132816789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96368041767361145421877859 144552062651041718132816789)
            ·
              refine ⟨6775877936767580537475787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144552062651041718132816789 6775877936767580537475787)
              ·
                refine ⟨10163816905151370806213681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6775877936767580537475787 10163816905151370806213681)
                ·
                  refine ⟨7622862678863528104660261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10163816905151370806213681 7622862678863528104660261)
                  ·
                    refine ⟨1429286752286911519623799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7622862678863528104660261 1429286752286911519623799)
                    ·
                      rfl

theorem cell23_8350578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_8350578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350578 prefixEnd_8350578 := by exact prefixLift 8350578
  have htrace : WordTrace (prefixWord ++ tailWord_8350578) baseStart_8350578 baseEnd_8350578 := by
    simpa [prefixWord, tailWord_8350578, baseEnd_8350578] using wordTrace_append hprefix tailTrace_8350578
  have hstable : (prefixWord ++ tailWord_8350578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350578).length < 2 ^ (prefixWord ++ tailWord_8350578).sum := by decide
  have hdescent : baseEnd_8350578 < baseStart_8350578 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350601 : List Nat := [1, 2, 1, 1, 5, 3, 1, 2, 1, 3, 3]
def baseStart_8350601 : Nat := 118140960795 + 8350601 * 2 ^ 59
def prefixEnd_8350601 : Nat := 4983230072969 + 3 ^ 40 * 8350601 * 2
def baseEnd_8350601 : Nat := 4287872066915787968883791

theorem tailTrace_8350601 : CollatzResearch.WordTrace tailWord_8350601 prefixEnd_8350601 4287872066915787968883791 := by
  unfold tailWord_8350601
  simp only [CollatzResearch.WordTrace]
  refine ⟨304571440020206220952787657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203047626680137480635191771 304571440020206220952787657)
  ·
    refine ⟨228428580015154665714590743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304571440020206220952787657 228428580015154665714590743)
    ·
      refine ⟨342642870022731998571886115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228428580015154665714590743 342642870022731998571886115)
      ·
        refine ⟨513964305034097997857829173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342642870022731998571886115 513964305034097997857829173)
        ·
          refine ⟨48184153596946687299171485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 513964305034097997857829173 48184153596946687299171485)
          ·
            refine ⟨18069057598855007737189307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48184153596946687299171485 18069057598855007737189307)
            ·
              refine ⟨27103586398282511605783961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18069057598855007737189307 27103586398282511605783961)
              ·
                refine ⟨20327689798711883704337971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27103586398282511605783961 20327689798711883704337971)
                ·
                  refine ⟨30491534698067825556506957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20327689798711883704337971 30491534698067825556506957)
                  ·
                    refine ⟨11434325511775434583690109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30491534698067825556506957 11434325511775434583690109)
                    ·
                      refine ⟨4287872066915787968883791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11434325511775434583690109 4287872066915787968883791)
                      ·
                        rfl

theorem cell23_8350601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 3, 3].length) (baseStart_8350601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350601 prefixEnd_8350601 := by exact prefixLift 8350601
  have htrace : WordTrace (prefixWord ++ tailWord_8350601) baseStart_8350601 baseEnd_8350601 := by
    simpa [prefixWord, tailWord_8350601, baseEnd_8350601] using wordTrace_append hprefix tailTrace_8350601
  have hstable : (prefixWord ++ tailWord_8350601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350601).length < 2 ^ (prefixWord ++ tailWord_8350601).sum := by decide
  have hdescent : baseEnd_8350601 < baseStart_8350601 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350624 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 4]
def baseStart_8350624 : Nat := 118140960795 + 8350624 * 2 ^ 59
def prefixEnd_8350624 : Nat := 4983230072969 + 3 ^ 40 * 8350624 * 2
def baseEnd_8350624 : Nat := 4287883876970841378896185

theorem tailTrace_8350624 : CollatzResearch.WordTrace tailWord_8350624 prefixEnd_8350624 4287883876970841378896185 := by
  unfold tailWord_8350624
  simp only [CollatzResearch.WordTrace]
  refine ⟨152286139449561447940437463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203048185932748597253916617 152286139449561447940437463)
  ·
    refine ⟨228429209174342171910656195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152286139449561447940437463 228429209174342171910656195)
    ·
      refine ⟨342643813761513257865984293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228429209174342171910656195 342643813761513257865984293)
      ·
        refine ⟨64245715080283735849872055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 342643813761513257865984293 64245715080283735849872055)
        ·
          refine ⟨96368572620425603774808083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64245715080283735849872055 96368572620425603774808083)
          ·
            refine ⟨144552858930638405662212125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96368572620425603774808083 144552858930638405662212125)
            ·
              refine ⟨54207322098989402123329547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144552858930638405662212125 54207322098989402123329547)
              ·
                refine ⟨81310983148484103184994321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54207322098989402123329547 81310983148484103184994321)
                ·
                  refine ⟨60983237361363077388745741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81310983148484103184994321 60983237361363077388745741)
                  ·
                    refine ⟨22868714010511154020779653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60983237361363077388745741 22868714010511154020779653)
                    ·
                      refine ⟨4287883876970841378896185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22868714010511154020779653 4287883876970841378896185)
                      ·
                        rfl

theorem cell23_8350624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_8350624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350624 prefixEnd_8350624 := by exact prefixLift 8350624
  have htrace : WordTrace (prefixWord ++ tailWord_8350624) baseStart_8350624 baseEnd_8350624 := by
    simpa [prefixWord, tailWord_8350624, baseEnd_8350624] using wordTrace_append hprefix tailTrace_8350624
  have hstable : (prefixWord ++ tailWord_8350624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350624).length < 2 ^ (prefixWord ++ tailWord_8350624).sum := by decide
  have hdescent : baseEnd_8350624 < baseStart_8350624 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350669 : List Nat := [1, 6, 3, 1, 1, 1, 1, 1, 4, 1, 3]
def baseStart_8350669 : Nat := 118140960795 + 8350669 * 2 ^ 59
def prefixEnd_8350669 : Nat := 4983230072969 + 3 ^ 40 * 8350669 * 2
def baseEnd_8350669 : Nat := 4287906983600293702833479

theorem tailTrace_8350669 : CollatzResearch.WordTrace tailWord_8350669 prefixEnd_8350669 4287906983600293702833479 := by
  unfold tailWord_8350669
  simp only [CollatzResearch.WordTrace]
  refine ⟨304573920183959868566263061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203049280122639912377508707 304573920183959868566263061)
  ·
    refine ⟨14276902508623118839043581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 304573920183959868566263061 14276902508623118839043581)
    ·
      refine ⟨5353838440733669564641343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14276902508623118839043581 5353838440733669564641343)
      ·
        refine ⟨8030757661100504346962015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5353838440733669564641343 8030757661100504346962015)
        ·
          refine ⟨12046136491650756520443023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8030757661100504346962015 12046136491650756520443023)
          ·
            refine ⟨18069204737476134780664535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12046136491650756520443023 18069204737476134780664535)
            ·
              refine ⟨27103807106214202170996803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18069204737476134780664535 27103807106214202170996803)
              ·
                refine ⟨40655710659321303256495205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27103807106214202170996803 40655710659321303256495205)
                ·
                  refine ⟨7622945748622744360592851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40655710659321303256495205 7622945748622744360592851)
                  ·
                    refine ⟨11434418622934116540889277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7622945748622744360592851 11434418622934116540889277)
                    ·
                      refine ⟨4287906983600293702833479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11434418622934116540889277 4287906983600293702833479)
                      ·
                        rfl

theorem cell23_8350669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_8350669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350669 prefixEnd_8350669 := by exact prefixLift 8350669
  have htrace : WordTrace (prefixWord ++ tailWord_8350669) baseStart_8350669 baseEnd_8350669 := by
    simpa [prefixWord, tailWord_8350669, baseEnd_8350669] using wordTrace_append hprefix tailTrace_8350669
  have hstable : (prefixWord ++ tailWord_8350669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350669).length < 2 ^ (prefixWord ++ tailWord_8350669).sum := by decide
  have hdescent : baseEnd_8350669 < baseStart_8350669 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350681 : List Nat := [1, 2, 1, 2, 5, 2, 2, 1, 7]
def baseStart_8350681 : Nat := 118140960795 + 8350681 * 2 ^ 59
def prefixEnd_8350681 : Nat := 4983230072969 + 3 ^ 40 * 8350681 * 2
def baseEnd_8350681 : Nat := 476434793929794183987047

theorem tailTrace_8350681 : CollatzResearch.WordTrace tailWord_8350681 prefixEnd_8350681 476434793929794183987047 := by
  unfold tailWord_8350681
  simp only [CollatzResearch.WordTrace]
  refine ⟨304574357859916394615699897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203049571906610929743799931 304574357859916394615699897)
  ·
    refine ⟨228430768394937295961774923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304574357859916394615699897 228430768394937295961774923)
    ·
      refine ⟨342646152592405943942662385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228430768394937295961774923 342646152592405943942662385)
      ·
        refine ⟨256984614444304457956996789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342646152592405943942662385 256984614444304457956996789)
        ·
          refine ⟨24092307604153542933468449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 256984614444304457956996789 24092307604153542933468449)
          ·
            refine ⟨18069230703115157200101337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24092307604153542933468449 18069230703115157200101337)
            ·
              refine ⟨13551923027336367900076003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18069230703115157200101337 13551923027336367900076003)
              ·
                refine ⟨20327884541004551850114005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13551923027336367900076003 20327884541004551850114005)
                ·
                  refine ⟨476434793929794183987047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20327884541004551850114005 476434793929794183987047)
                  ·
                    rfl

theorem cell23_8350681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 7].length) (baseStart_8350681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350681 prefixEnd_8350681 := by exact prefixLift 8350681
  have htrace : WordTrace (prefixWord ++ tailWord_8350681) baseStart_8350681 baseEnd_8350681 := by
    simpa [prefixWord, tailWord_8350681, baseEnd_8350681] using wordTrace_append hprefix tailTrace_8350681
  have hstable : (prefixWord ++ tailWord_8350681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350681).length < 2 ^ (prefixWord ++ tailWord_8350681).sum := by decide
  have hdescent : baseEnd_8350681 < baseStart_8350681 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350691 : List Nat := [1, 1, 1, 6, 1, 1, 1, 3, 2, 3, 3]
def baseStart_8350691 : Nat := 118140960795 + 8350691 * 2 ^ 59
def prefixEnd_8350691 : Nat := 4983230072969 + 3 ^ 40 * 8350691 * 2
def baseEnd_8350691 : Nat := 4287918280174692616758377

theorem tailTrace_8350691 : CollatzResearch.WordTrace tailWord_8350691 prefixEnd_8350691 4287918280174692616758377 := by
  unfold tailWord_8350691
  simp only [CollatzResearch.WordTrace]
  refine ⟨304574722589880166323563927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203049815059920110882375951 304574722589880166323563927)
  ·
    refine ⟨456862083884820249485345891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304574722589880166323563927 456862083884820249485345891)
    ·
      refine ⟨685293125827230374228018837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456862083884820249485345891 685293125827230374228018837)
      ·
        refine ⟨32123115273151423791938383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 685293125827230374228018837 32123115273151423791938383)
        ·
          refine ⟨48184672909727135687907575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32123115273151423791938383 48184672909727135687907575)
          ·
            refine ⟨72277009364590703531861363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48184672909727135687907575 72277009364590703531861363)
            ·
              refine ⟨108415514046886055297792045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72277009364590703531861363 108415514046886055297792045)
              ·
                refine ⟨40655817767582270736672017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108415514046886055297792045 40655817767582270736672017)
                ·
                  refine ⟨30491863325686703052504013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40655817767582270736672017 30491863325686703052504013)
                  ·
                    refine ⟨11434448747132513644689005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30491863325686703052504013 11434448747132513644689005)
                    ·
                      refine ⟨4287918280174692616758377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11434448747132513644689005 4287918280174692616758377)
                      ·
                        rfl

theorem cell23_8350691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_8350691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350691 prefixEnd_8350691 := by exact prefixLift 8350691
  have htrace : WordTrace (prefixWord ++ tailWord_8350691) baseStart_8350691 baseEnd_8350691 := by
    simpa [prefixWord, tailWord_8350691, baseEnd_8350691] using wordTrace_append hprefix tailTrace_8350691
  have hstable : (prefixWord ++ tailWord_8350691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350691).length < 2 ^ (prefixWord ++ tailWord_8350691).sum := by decide
  have hdescent : baseEnd_8350691 < baseStart_8350691 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350704 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 5]
def baseStart_8350704 : Nat := 118140960795 + 8350704 * 2 ^ 59
def prefixEnd_8350704 : Nat := 4983230072969 + 3 ^ 40 * 8350704 * 2
def baseEnd_8350704 : Nat := 4287924955423201065895817

theorem tailTrace_8350704 : CollatzResearch.WordTrace tailWord_8350704 prefixEnd_8350704 4287924955423201065895817 := by
  unfold tailWord_8350704
  simp only [CollatzResearch.WordTrace]
  refine ⟨152287598369416534771893583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203050131159222046362524777 152287598369416534771893583)
  ·
    refine ⟨228431397554124802157840375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152287598369416534771893583 228431397554124802157840375)
    ·
      refine ⟨342647096331187203236760563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228431397554124802157840375 342647096331187203236760563)
      ·
        refine ⟨513970644496780804855140845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342647096331187203236760563 513970644496780804855140845)
        ·
          refine ⟨192738991686292801820677817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 513970644496780804855140845 192738991686292801820677817)
          ·
            refine ⟨144554243764719601365508363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192738991686292801820677817 144554243764719601365508363)
            ·
              refine ⟨216831365647079402048262545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144554243764719601365508363 216831365647079402048262545)
              ·
                refine ⟨162623524235309551536196909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216831365647079402048262545 162623524235309551536196909)
                ·
                  refine ⟨60983821588241081826073841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162623524235309551536196909 60983821588241081826073841)
                  ·
                    refine ⟨45737866191180811369555381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60983821588241081826073841 45737866191180811369555381)
                    ·
                      refine ⟨4287924955423201065895817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45737866191180811369555381 4287924955423201065895817)
                      ·
                        rfl

theorem cell23_8350704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 5].length) (baseStart_8350704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350704 prefixEnd_8350704 := by exact prefixLift 8350704
  have htrace : WordTrace (prefixWord ++ tailWord_8350704) baseStart_8350704 baseEnd_8350704 := by
    simpa [prefixWord, tailWord_8350704, baseEnd_8350704] using wordTrace_append hprefix tailTrace_8350704
  have hstable : (prefixWord ++ tailWord_8350704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350704).length < 2 ^ (prefixWord ++ tailWord_8350704).sum := by decide
  have hdescent : baseEnd_8350704 < baseStart_8350704 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350731 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 4]
def baseStart_8350731 : Nat := 118140960795 + 8350731 * 2 ^ 59
def prefixEnd_8350731 : Nat := 4983230072969 + 3 ^ 40 * 8350731 * 2
def baseEnd_8350731 : Nat := 4287938819400872460258193

theorem tailTrace_8350731 : CollatzResearch.WordTrace tailWord_8350731 prefixEnd_8350731 4287938819400872460258193 := by
  unfold tailWord_8350731
  simp only [CollatzResearch.WordTrace]
  refine ⟨304576181509735253155020047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203050787673156835436680031 304576181509735253155020047)
  ·
    refine ⟨456864272264602879732530071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304576181509735253155020047 456864272264602879732530071)
    ·
      refine ⟨685296408396904319598795107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456864272264602879732530071 685296408396904319598795107)
      ·
        refine ⟨1027944612595356479398192661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685296408396904319598795107 1027944612595356479398192661)
        ·
          refine ⟨48184903715407334971790281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1027944612595356479398192661 48184903715407334971790281)
          ·
            refine ⟨36138677786555501228842711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48184903715407334971790281 36138677786555501228842711)
            ·
              refine ⟨54208016679833251843264067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36138677786555501228842711 54208016679833251843264067)
              ·
                refine ⟨81312025019749877764896101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54208016679833251843264067 81312025019749877764896101)
                ·
                  refine ⟨15246004691203102080918019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81312025019749877764896101 15246004691203102080918019)
                  ·
                    refine ⟨22869007036804653121377029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15246004691203102080918019 22869007036804653121377029)
                    ·
                      refine ⟨4287938819400872460258193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22869007036804653121377029 4287938819400872460258193)
                      ·
                        rfl

theorem cell23_8350731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 4].length) (baseStart_8350731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350731 prefixEnd_8350731 := by exact prefixLift 8350731
  have htrace : WordTrace (prefixWord ++ tailWord_8350731) baseStart_8350731 baseEnd_8350731 := by
    simpa [prefixWord, tailWord_8350731, baseEnd_8350731] using wordTrace_append hprefix tailTrace_8350731
  have hstable : (prefixWord ++ tailWord_8350731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350731).length < 2 ^ (prefixWord ++ tailWord_8350731).sum := by decide
  have hdescent : baseEnd_8350731 < baseStart_8350731 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350768 : List Nat := [2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 3]
def baseStart_8350768 : Nat := 118140960795 + 8350768 * 2 ^ 59
def prefixEnd_8350768 : Nat := 4983230072969 + 3 ^ 40 * 8350768 * 2
def baseEnd_8350768 : Nat := 4287957818185088815495523

theorem tailTrace_8350768 : CollatzResearch.WordTrace tailWord_8350768 prefixEnd_8350768 4287957818185088815495523 := by
  unfold tailWord_8350768
  simp only [CollatzResearch.WordTrace]
  refine ⟨152288765505300604237058479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203051687340400805649411305 152288765505300604237058479)
  ·
    refine ⟨228433148257950906355587719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152288765505300604237058479 228433148257950906355587719)
    ·
      refine ⟨342649722386926359533381579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228433148257950906355587719 342649722386926359533381579)
      ·
        refine ⟨513974583580389539300072369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342649722386926359533381579 513974583580389539300072369)
        ·
          refine ⟨385480937685292154475054277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513974583580389539300072369 385480937685292154475054277)
          ·
            refine ⟨72277675815992278964072677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 385480937685292154475054277 72277675815992278964072677)
            ·
              refine ⟨13552064215498552305763627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72277675815992278964072677 13552064215498552305763627)
              ·
                refine ⟨20328096323247828458645441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13552064215498552305763627 20328096323247828458645441)
                ·
                  refine ⟨15246072242435871343984081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20328096323247828458645441 15246072242435871343984081)
                  ·
                    refine ⟨11434554181826903507988061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15246072242435871343984081 11434554181826903507988061)
                    ·
                      refine ⟨4287957818185088815495523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11434554181826903507988061 4287957818185088815495523)
                      ·
                        rfl

theorem cell23_8350768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 3].length) (baseStart_8350768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350768 prefixEnd_8350768 := by exact prefixLift 8350768
  have htrace : WordTrace (prefixWord ++ tailWord_8350768) baseStart_8350768 baseEnd_8350768 := by
    simpa [prefixWord, tailWord_8350768, baseEnd_8350768] using wordTrace_append hprefix tailTrace_8350768
  have hstable : (prefixWord ++ tailWord_8350768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350768).length < 2 ^ (prefixWord ++ tailWord_8350768).sum := by decide
  have hdescent : baseEnd_8350768 < baseStart_8350768 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350801 : List Nat := [1, 2, 2, 1, 3, 1, 3, 2, 3, 5]
def baseStart_8350801 : Nat := 118140960795 + 8350801 * 2 ^ 59
def prefixEnd_8350801 : Nat := 4983230072969 + 3 ^ 40 * 8350801 * 2
def baseEnd_8350801 : Nat := 1429324921015562395460957

theorem tailTrace_8350801 : CollatzResearch.WordTrace tailWord_8350801 prefixEnd_8350801 1429324921015562395460957 := by
  unfold tailWord_8350801
  simp only [CollatzResearch.WordTrace]
  refine ⟨304578734619481655110068257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203052489746321103406712171 304578734619481655110068257)
  ·
    refine ⟨228434050964611241332551193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304578734619481655110068257 228434050964611241332551193)
    ·
      refine ⟨171325538223458430999413395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228434050964611241332551193 171325538223458430999413395)
      ·
        refine ⟨256988307335187646499120093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171325538223458430999413395 256988307335187646499120093)
        ·
          refine ⟨96370615250695367437170035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256988307335187646499120093 96370615250695367437170035)
          ·
            refine ⟨144555922876043051155755053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96370615250695367437170035 144555922876043051155755053)
            ·
              refine ⟨54208471078516144183408145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144555922876043051155755053 54208471078516144183408145)
              ·
                refine ⟨40656353308887108137556109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54208471078516144183408145 40656353308887108137556109)
                ·
                  refine ⟨15246132490832665551583541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40656353308887108137556109 15246132490832665551583541)
                  ·
                    refine ⟨1429324921015562395460957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15246132490832665551583541 1429324921015562395460957)
                    ·
                      rfl

theorem cell23_8350801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 5].length) (baseStart_8350801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350801 prefixEnd_8350801 := by exact prefixLift 8350801
  have htrace : WordTrace (prefixWord ++ tailWord_8350801) baseStart_8350801 baseEnd_8350801 := by
    simpa [prefixWord, tailWord_8350801, baseEnd_8350801] using wordTrace_append hprefix tailTrace_8350801
  have hstable : (prefixWord ++ tailWord_8350801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350801).length < 2 ^ (prefixWord ++ tailWord_8350801).sum := by decide
  have hdescent : baseEnd_8350801 < baseStart_8350801 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350808 : List Nat := [2, 1, 2, 2, 1, 3, 2, 2, 1, 5, 2]
def baseStart_8350808 : Nat := 118140960795 + 8350808 * 2 ^ 59
def prefixEnd_8350808 : Nat := 4983230072969 + 3 ^ 40 * 8350808 * 2
def baseEnd_8350808 : Nat := 4287978357411268658995339

theorem tailTrace_8350808 : CollatzResearch.WordTrace tailWord_8350808 prefixEnd_8350808 4287978357411268658995339 := by
  unfold tailWord_8350808
  simp only [CollatzResearch.WordTrace]
  refine ⟨152289494965228147652786539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203052659953637530203715385 152289494965228147652786539)
  ·
    refine ⟨228434242447842221479179809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152289494965228147652786539 228434242447842221479179809)
    ·
      refine ⟨171325681835881666109384857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228434242447842221479179809 171325681835881666109384857)
      ·
        refine ⟨128494261376911249582038643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171325681835881666109384857 128494261376911249582038643)
        ·
          refine ⟨192741392065366874373057965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128494261376911249582038643 192741392065366874373057965)
          ·
            refine ⟨72278022024512577889896737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192741392065366874373057965 72278022024512577889896737)
            ·
              refine ⟨54208516518384433417422553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72278022024512577889896737 54208516518384433417422553)
              ·
                refine ⟨40656387388788325063066915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54208516518384433417422553 40656387388788325063066915)
                ·
                  refine ⟨60984581083182487594600373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40656387388788325063066915 60984581083182487594600373)
                  ·
                    refine ⟨5717304476548358211993785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60984581083182487594600373 5717304476548358211993785)
                    ·
                      refine ⟨4287978357411268658995339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5717304476548358211993785 4287978357411268658995339)
                      ·
                        rfl

theorem cell23_8350808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 1, 5, 2].length) (baseStart_8350808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350808 prefixEnd_8350808 := by exact prefixLift 8350808
  have htrace : WordTrace (prefixWord ++ tailWord_8350808) baseStart_8350808 baseEnd_8350808 := by
    simpa [prefixWord, tailWord_8350808, baseEnd_8350808] using wordTrace_append hprefix tailTrace_8350808
  have hstable : (prefixWord ++ tailWord_8350808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350808).length < 2 ^ (prefixWord ++ tailWord_8350808).sum := by decide
  have hdescent : baseEnd_8350808 < baseStart_8350808 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350825 : List Nat := [1, 2, 1, 1, 1, 6, 3, 1, 2, 3, 2]
def baseStart_8350825 : Nat := 118140960795 + 8350825 * 2 ^ 59
def prefixEnd_8350825 : Nat := 4983230072969 + 3 ^ 40 * 8350825 * 2
def baseEnd_8350825 : Nat := 4287987086582395092482761

theorem tailTrace_8350825 : CollatzResearch.WordTrace tailWord_8350825 prefixEnd_8350825 4287987086582395092482761 := by
  unfold tailWord_8350825
  simp only [CollatzResearch.WordTrace]
  refine ⟨304579609971394707208941929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203053073314263138139294619 304579609971394707208941929)
  ·
    refine ⟨228434707478546030406706447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304579609971394707208941929 228434707478546030406706447)
    ·
      refine ⟨342652061217819045610059671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228434707478546030406706447 342652061217819045610059671)
      ·
        refine ⟨513978091826728568415089507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342652061217819045610059671 513978091826728568415089507)
        ·
          refine ⟨770967137740092852622634261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513978091826728568415089507 770967137740092852622634261)
          ·
            refine ⟨36139084581566852466685981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 770967137740092852622634261 36139084581566852466685981)
            ·
              refine ⟨13552156718087569675007243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36139084581566852466685981 13552156718087569675007243)
              ·
                refine ⟨20328235077131354512510865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13552156718087569675007243 20328235077131354512510865)
                ·
                  refine ⟨15246176307848515884383149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20328235077131354512510865 15246176307848515884383149)
                  ·
                    refine ⟨5717316115443193456643681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15246176307848515884383149 5717316115443193456643681)
                    ·
                      refine ⟨4287987086582395092482761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5717316115443193456643681 4287987086582395092482761)
                      ·
                        rfl

theorem cell23_8350825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 3, 2].length) (baseStart_8350825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350825 prefixEnd_8350825 := by exact prefixLift 8350825
  have htrace : WordTrace (prefixWord ++ tailWord_8350825) baseStart_8350825 baseEnd_8350825 := by
    simpa [prefixWord, tailWord_8350825, baseEnd_8350825] using wordTrace_append hprefix tailTrace_8350825
  have hstable : (prefixWord ++ tailWord_8350825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350825).length < 2 ^ (prefixWord ++ tailWord_8350825).sum := by decide
  have hdescent : baseEnd_8350825 < baseStart_8350825 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350831 : List Nat := [1, 1, 2, 1, 3, 3, 1, 4, 1, 6]
def baseStart_8350831 : Nat := 118140960795 + 8350831 * 2 ^ 59
def prefixEnd_8350831 : Nat := 4983230072969 + 3 ^ 40 * 8350831 * 2
def baseEnd_8350831 : Nat := 1429330055822107356335911

theorem tailTrace_8350831 : CollatzResearch.WordTrace tailWord_8350831 prefixEnd_8350831 1429330055822107356335911 := by
  unfold tailWord_8350831
  simp only [CollatzResearch.WordTrace]
  refine ⟨304579828809372970233660347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203053219206248646822440231 304579828809372970233660347)
  ·
    refine ⟨456869743214059455350490521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304579828809372970233660347 456869743214059455350490521)
    ·
      refine ⟨342652307410544591512867891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456869743214059455350490521 342652307410544591512867891)
      ·
        refine ⟨513978461115816887269301837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342652307410544591512867891 513978461115816887269301837)
        ·
          refine ⟨192741922918431332725988189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 513978461115816887269301837 192741922918431332725988189)
          ·
            refine ⟨72278221094411749772245571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192741922918431332725988189 72278221094411749772245571)
            ·
              refine ⟨108417331641617624658368357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72278221094411749772245571 108417331641617624658368357)
              ·
                refine ⟨20328249682803304623444067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108417331641617624658368357 20328249682803304623444067)
                ·
                  refine ⟨30492374524204956935166101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20328249682803304623444067 30492374524204956935166101)
                  ·
                    refine ⟨1429330055822107356335911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30492374524204956935166101 1429330055822107356335911)
                    ·
                      rfl

theorem cell23_8350831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 6].length) (baseStart_8350831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350831 prefixEnd_8350831 := by exact prefixLift 8350831
  have htrace : WordTrace (prefixWord ++ tailWord_8350831) baseStart_8350831 baseEnd_8350831 := by
    simpa [prefixWord, tailWord_8350831, baseEnd_8350831] using wordTrace_append hprefix tailTrace_8350831
  have hstable : (prefixWord ++ tailWord_8350831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350831).length < 2 ^ (prefixWord ++ tailWord_8350831).sum := by decide
  have hdescent : baseEnd_8350831 < baseStart_8350831 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350832 : List Nat := [2, 1, 1, 1, 5, 1, 4, 3, 1, 1, 3]
def baseStart_8350832 : Nat := 118140960795 + 8350832 * 2 ^ 59
def prefixEnd_8350832 : Nat := 4983230072969 + 3 ^ 40 * 8350832 * 2
def baseEnd_8350832 : Nat := 4287990680946976565095229

theorem tailTrace_8350832 : CollatzResearch.WordTrace tailWord_8350832 prefixEnd_8350832 4287990680946976565095229 := by
  unfold tailWord_8350832
  simp only [CollatzResearch.WordTrace]
  refine ⟨152289932641184673702223375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203053243521579564936297833 152289932641184673702223375)
  ·
    refine ⟨228434898961777010553335063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152289932641184673702223375 228434898961777010553335063)
    ·
      refine ⟨342652348442665515830002595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228434898961777010553335063 342652348442665515830002595)
      ·
        refine ⟨513978522663998273745003893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342652348442665515830002595 513978522663998273745003893)
        ·
          refine ⟨48185486499749838163594115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 513978522663998273745003893 48185486499749838163594115)
          ·
            refine ⟨72278229749624757245391173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48185486499749838163594115 72278229749624757245391173)
            ·
              refine ⟨13552168078054641983510845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72278229749624757245391173 13552168078054641983510845)
              ·
                refine ⟨5082063029270490743816567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13552168078054641983510845 5082063029270490743816567)
                ·
                  refine ⟨7623094543905736115724851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5082063029270490743816567 7623094543905736115724851)
                  ·
                    refine ⟨11434641815858604173587277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7623094543905736115724851 11434641815858604173587277)
                    ·
                      refine ⟨4287990680946976565095229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11434641815858604173587277 4287990680946976565095229)
                      ·
                        rfl

theorem cell23_8350832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3, 1, 1, 3].length) (baseStart_8350832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350832 prefixEnd_8350832 := by exact prefixLift 8350832
  have htrace : WordTrace (prefixWord ++ tailWord_8350832) baseStart_8350832 baseEnd_8350832 := by
    simpa [prefixWord, tailWord_8350832, baseEnd_8350832] using wordTrace_append hprefix tailTrace_8350832
  have hstable : (prefixWord ++ tailWord_8350832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350832).length < 2 ^ (prefixWord ++ tailWord_8350832).sum := by decide
  have hdescent : baseEnd_8350832 < baseStart_8350832 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350851 : List Nat := [1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 6]
def baseStart_8350851 : Nat := 118140960795 + 8350851 * 2 ^ 59
def prefixEnd_8350851 : Nat := 4983230072969 + 3 ^ 40 * 8350851 * 2
def baseEnd_8350851 : Nat := 4288000437079411990757641

theorem tailTrace_8350851 : CollatzResearch.WordTrace tailWord_8350851 prefixEnd_8350851 4288000437079411990757641 := by
  unfold tailWord_8350851
  simp only [CollatzResearch.WordTrace]
  refine ⟨304580558269300513649388407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203053705512867009099592271 304580558269300513649388407)
  ·
    refine ⟨456870837403950770474082611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304580558269300513649388407 456870837403950770474082611)
    ·
      refine ⟨685306256105926155711123917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456870837403950770474082611 685306256105926155711123917)
      ·
        refine ⟨256989846039722308391671469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 685306256105926155711123917 256989846039722308391671469)
        ·
          refine ⟨96371192264895865646876801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256989846039722308391671469 96371192264895865646876801)
          ·
            refine ⟨72278394198671899235157601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96371192264895865646876801 72278394198671899235157601)
            ·
              refine ⟨54208795649003924426368201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72278394198671899235157601 54208795649003924426368201)
              ·
                refine ⟨40656596736752943319776151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54208795649003924426368201 40656596736752943319776151)
                ·
                  refine ⟨60984895105129414979664227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40656596736752943319776151 60984895105129414979664227)
                  ·
                    refine ⟨91477342657694122469496341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60984895105129414979664227 91477342657694122469496341)
                    ·
                      refine ⟨4288000437079411990757641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91477342657694122469496341 4288000437079411990757641)
                      ·
                        rfl

theorem cell23_8350851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_8350851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350851 prefixEnd_8350851 := by exact prefixLift 8350851
  have htrace : WordTrace (prefixWord ++ tailWord_8350851) baseStart_8350851 baseEnd_8350851 := by
    simpa [prefixWord, tailWord_8350851, baseEnd_8350851] using wordTrace_append hprefix tailTrace_8350851
  have hstable : (prefixWord ++ tailWord_8350851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350851).length < 2 ^ (prefixWord ++ tailWord_8350851).sum := by decide
  have hdescent : baseEnd_8350851 < baseStart_8350851 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350858 : List Nat := [3, 1, 2, 3, 1, 1, 3, 2, 1, 1, 5]
def baseStart_8350858 : Nat := 118140960795 + 8350858 * 2 ^ 59
def prefixEnd_8350858 : Nat := 4983230072969 + 3 ^ 40 * 8350858 * 2
def baseEnd_8350858 : Nat := 4288004031443993463370109

theorem tailTrace_8350858 : CollatzResearch.WordTrace tailWord_8350858 prefixEnd_8350858 4288004031443993463370109 := by
  unfold tailWord_8350858
  simp only [CollatzResearch.WordTrace]
  refine ⟨76145203395068788461223307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203053875720183435896595485 76145203395068788461223307)
  ·
    refine ⟨114217805092603182691834961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76145203395068788461223307 114217805092603182691834961)
    ·
      refine ⟨85663353819452387018876221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114217805092603182691834961 85663353819452387018876221)
      ·
        refine ⟨32123757682294645132078583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85663353819452387018876221 32123757682294645132078583)
        ·
          refine ⟨48185636523441967698117875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32123757682294645132078583 48185636523441967698117875)
          ·
            refine ⟨72278454785162951547176813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48185636523441967698117875 72278454785162951547176813)
            ·
              refine ⟨27104420544436106830191305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72278454785162951547176813 27104420544436106830191305)
              ·
                refine ⟨20328315408327080122643479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27104420544436106830191305 20328315408327080122643479)
                ·
                  refine ⟨30492473112490620183965219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20328315408327080122643479 30492473112490620183965219)
                  ·
                    refine ⟨45738709668735930275947829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30492473112490620183965219 45738709668735930275947829)
                    ·
                      refine ⟨4288004031443993463370109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45738709668735930275947829 4288004031443993463370109)
                      ·
                        rfl

theorem cell23_8350858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_8350858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350858 prefixEnd_8350858 := by exact prefixLift 8350858
  have htrace : WordTrace (prefixWord ++ tailWord_8350858) baseStart_8350858 baseEnd_8350858 := by
    simpa [prefixWord, tailWord_8350858, baseEnd_8350858] using wordTrace_append hprefix tailTrace_8350858
  have hstable : (prefixWord ++ tailWord_8350858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350858).length < 2 ^ (prefixWord ++ tailWord_8350858).sum := by decide
  have hdescent : baseEnd_8350858 < baseStart_8350858 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350872 : List Nat := [2, 1, 2, 4, 2, 1, 2, 2, 3, 2, 2]
def baseStart_8350872 : Nat := 118140960795 + 8350872 * 2 ^ 59
def prefixEnd_8350872 : Nat := 4983230072969 + 3 ^ 40 * 8350872 * 2
def baseEnd_8350872 : Nat := 4288011220173156408595045

theorem tailTrace_8350872 : CollatzResearch.WordTrace tailWord_8350872 prefixEnd_8350872 4288011220173156408595045 := by
  unfold tailWord_8350872
  simp only [CollatzResearch.WordTrace]
  refine ⟨152290662101112217117951435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203054216134816289490601913 152290662101112217117951435)
  ·
    refine ⟨228435993151668325676927153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152290662101112217117951435 228435993151668325676927153)
    ·
      refine ⟨171326994863751244257695365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228435993151668325676927153 171326994863751244257695365)
      ·
        refine ⟨32123811536953358298317881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171326994863751244257695365 32123811536953358298317881)
        ·
          refine ⟨24092858652715018723738411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32123811536953358298317881 24092858652715018723738411)
          ·
            refine ⟨36139287979072528085607617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24092858652715018723738411 36139287979072528085607617)
            ·
              refine ⟨27104465984304396064205713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36139287979072528085607617 27104465984304396064205713)
              ·
                refine ⟨20328349488228297048154285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27104465984304396064205713 20328349488228297048154285)
                ·
                  refine ⟨7623131058085611393057857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20328349488228297048154285 7623131058085611393057857)
                  ·
                    refine ⟨5717348293564208544793393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7623131058085611393057857 5717348293564208544793393)
                    ·
                      refine ⟨4288011220173156408595045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5717348293564208544793393 4288011220173156408595045)
                      ·
                        rfl

theorem cell23_8350872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_8350872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350872 prefixEnd_8350872 := by exact prefixLift 8350872
  have htrace : WordTrace (prefixWord ++ tailWord_8350872) baseStart_8350872 baseEnd_8350872 := by
    simpa [prefixWord, tailWord_8350872, baseEnd_8350872] using wordTrace_append hprefix tailTrace_8350872
  have hstable : (prefixWord ++ tailWord_8350872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350872).length < 2 ^ (prefixWord ++ tailWord_8350872).sum := by decide
  have hdescent : baseEnd_8350872 < baseStart_8350872 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350905 : List Nat := [1, 2, 1, 4, 1, 3, 2, 1, 4, 1, 3]
def baseStart_8350905 : Nat := 118140960795 + 8350905 * 2 ^ 59
def prefixEnd_8350905 : Nat := 4983230072969 + 3 ^ 40 * 8350905 * 2
def baseEnd_8350905 : Nat := 4288028165034754779482393

theorem tailTrace_8350905 : CollatzResearch.WordTrace tailWord_8350905 prefixEnd_8350905 4288028165034754779482393 := by
  unfold tailWord_8350905
  simp only [CollatzResearch.WordTrace]
  refine ⟨304582527811104880871854169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203055018540736587247902779 304582527811104880871854169)
  ·
    refine ⟨228436895858328660653890627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304582527811104880871854169 228436895858328660653890627)
    ·
      refine ⟨342655343787492990980835941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228436895858328660653890627 342655343787492990980835941)
      ·
        refine ⟨64247876960154935808906739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 342655343787492990980835941 64247876960154935808906739)
        ·
          refine ⟨96371815440232403713360109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64247876960154935808906739 96371815440232403713360109)
          ·
            refine ⟨36139430790087151392510041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96371815440232403713360109 36139430790087151392510041)
            ·
              refine ⟨27104573092565363544382531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36139430790087151392510041 27104573092565363544382531)
              ·
                refine ⟨40656859638848045316573797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27104573092565363544382531 40656859638848045316573797)
                ·
                  refine ⟨7623161182284008496857587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40656859638848045316573797 7623161182284008496857587)
                  ·
                    refine ⟨11434741773426012745286381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7623161182284008496857587 11434741773426012745286381)
                    ·
                      refine ⟨4288028165034754779482393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11434741773426012745286381 4288028165034754779482393)
                      ·
                        rfl

theorem cell23_8350905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_8350905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350905 prefixEnd_8350905 := by exact prefixLift 8350905
  have htrace : WordTrace (prefixWord ++ tailWord_8350905) baseStart_8350905 baseEnd_8350905 := by
    simpa [prefixWord, tailWord_8350905, baseEnd_8350905] using wordTrace_append hprefix tailTrace_8350905
  have hstable : (prefixWord ++ tailWord_8350905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350905).length < 2 ^ (prefixWord ++ tailWord_8350905).sum := by decide
  have hdescent : baseEnd_8350905 < baseStart_8350905 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350916 : List Nat := [2, 3, 3, 1, 4, 1, 2, 1, 2, 4]
def baseStart_8350916 : Nat := 118140960795 + 8350916 * 2 ^ 59
def prefixEnd_8350916 : Nat := 4983230072969 + 3 ^ 40 * 8350916 * 2
def baseEnd_8350916 : Nat := 1429344604440651412148281

theorem tailTrace_8350916 : CollatzResearch.WordTrace tailWord_8350916 prefixEnd_8350916 1429344604440651412148281 := by
  unfold tailWord_8350916
  simp only [CollatzResearch.WordTrace]
  refine ⟨152291464507032514875252301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203055286009376686500336401 152291464507032514875252301)
  ·
    refine ⟨57109299190137193078219613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152291464507032514875252301 57109299190137193078219613)
    ·
      refine ⟨21415987196301447404332355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57109299190137193078219613 21415987196301447404332355)
      ·
        refine ⟨32123980794452171106498533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21415987196301447404332355 32123980794452171106498533)
        ·
          refine ⟨6023246398959782082468475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32123980794452171106498533 6023246398959782082468475)
          ·
            refine ⟨9034869598439673123702713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6023246398959782082468475 9034869598439673123702713)
            ·
              refine ⟨6776152198829754842777035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9034869598439673123702713 6776152198829754842777035)
              ·
                refine ⟨10164228298244632264165553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6776152198829754842777035 10164228298244632264165553)
                ·
                  refine ⟨7623171223683474198124165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10164228298244632264165553 7623171223683474198124165)
                  ·
                    refine ⟨1429344604440651412148281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7623171223683474198124165 1429344604440651412148281)
                    ·
                      rfl

theorem cell23_8350916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_8350916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350916 prefixEnd_8350916 := by exact prefixLift 8350916
  have htrace : WordTrace (prefixWord ++ tailWord_8350916) baseStart_8350916 baseEnd_8350916 := by
    simpa [prefixWord, tailWord_8350916, baseEnd_8350916] using wordTrace_append hprefix tailTrace_8350916
  have hstable : (prefixWord ++ tailWord_8350916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350916).length < 2 ^ (prefixWord ++ tailWord_8350916).sum := by decide
  have hdescent : baseEnd_8350916 < baseStart_8350916 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350921 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 6, 6]
def baseStart_8350921 : Nat := 118140960795 + 8350921 * 2 ^ 59
def prefixEnd_8350921 : Nat := 4983230072969 + 3 ^ 40 * 8350921 * 2
def baseEnd_8350921 : Nat := 1429345460241742238960773

theorem tailTrace_8350921 : CollatzResearch.WordTrace tailWord_8350921 prefixEnd_8350921 1429345460241742238960773 := by
  unfold tailWord_8350921
  simp only [CollatzResearch.WordTrace]
  refine ⟨304583111379046915604436617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203055407586031277069624411 304583111379046915604436617)
  ·
    refine ⟨228437333534285186703327463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304583111379046915604436617 228437333534285186703327463)
    ·
      refine ⟨342656000301427780054991195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228437333534285186703327463 342656000301427780054991195)
      ·
        refine ⟨513984000452141670082486793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342656000301427780054991195 513984000452141670082486793)
        ·
          refine ⟨385488000339106252561865095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513984000452141670082486793 385488000339106252561865095)
          ·
            refine ⟨578232000508659378842797643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385488000339106252561865095 578232000508659378842797643)
            ·
              refine ⟨867348000762989068264196465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578232000508659378842797643 867348000762989068264196465)
              ·
                refine ⟨650511000572241801198147349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 867348000762989068264196465 650511000572241801198147349)
                ·
                  refine ⟨30492703151823834431163157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 650511000572241801198147349 30492703151823834431163157)
                  ·
                    refine ⟨1429345460241742238960773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30492703151823834431163157 1429345460241742238960773)
                    ·
                      rfl

theorem cell23_8350921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 6].length) (baseStart_8350921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350921 prefixEnd_8350921 := by exact prefixLift 8350921
  have htrace : WordTrace (prefixWord ++ tailWord_8350921) baseStart_8350921 baseEnd_8350921 := by
    simpa [prefixWord, tailWord_8350921, baseEnd_8350921] using wordTrace_append hprefix tailTrace_8350921
  have hstable : (prefixWord ++ tailWord_8350921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350921).length < 2 ^ (prefixWord ++ tailWord_8350921).sum := by decide
  have hdescent : baseEnd_8350921 < baseStart_8350921 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350922 : List Nat := [3, 1, 2, 1, 3, 3, 1, 3, 2, 1, 3]
def baseStart_8350922 : Nat := 118140960795 + 8350922 * 2 ^ 59
def prefixEnd_8350922 : Nat := 4983230072969 + 3 ^ 40 * 8350922 * 2
def baseEnd_8350922 : Nat := 4288036894205881212969815

theorem tailTrace_8350922 : CollatzResearch.WordTrace tailWord_8350922 prefixEnd_8350922 4288036894205881212969815 := by
  unfold tailWord_8350922
  simp only [CollatzResearch.WordTrace]
  refine ⟨76145786963010823193805755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203055431901362195183482013 76145786963010823193805755)
  ·
    refine ⟨114218680444516234790708633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76145786963010823193805755 114218680444516234790708633)
    ·
      refine ⟨85664010333387176093031475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114218680444516234790708633 85664010333387176093031475)
      ·
        refine ⟨128496015500080764139547213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85664010333387176093031475 128496015500080764139547213)
        ·
          refine ⟨48186005812530286552330205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128496015500080764139547213 48186005812530286552330205)
          ·
            refine ⟨18069752179698857457123827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48186005812530286552330205 18069752179698857457123827)
            ·
              refine ⟨27104628269548286185685741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18069752179698857457123827 27104628269548286185685741)
              ·
                refine ⟨10164235601080607319632153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27104628269548286185685741 10164235601080607319632153)
                ·
                  refine ⟨7623176700810455489724115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10164235601080607319632153 7623176700810455489724115)
                  ·
                    refine ⟨11434765051215683234586173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7623176700810455489724115 11434765051215683234586173)
                    ·
                      refine ⟨4288036894205881212969815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11434765051215683234586173 4288036894205881212969815)
                      ·
                        rfl

theorem cell23_8350922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_8350922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350922 prefixEnd_8350922 := by exact prefixLift 8350922
  have htrace : WordTrace (prefixWord ++ tailWord_8350922) baseStart_8350922 baseEnd_8350922 := by
    simpa [prefixWord, tailWord_8350922, baseEnd_8350922] using wordTrace_append hprefix tailTrace_8350922
  have hstable : (prefixWord ++ tailWord_8350922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350922).length < 2 ^ (prefixWord ++ tailWord_8350922).sum := by decide
  have hdescent : baseEnd_8350922 < baseStart_8350922 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350931 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 5]
def baseStart_8350931 : Nat := 118140960795 + 8350931 * 2 ^ 59
def prefixEnd_8350931 : Nat := 4983230072969 + 3 ^ 40 * 8350931 * 2
def baseEnd_8350931 : Nat := 4288041515531771677757273

theorem tailTrace_8350931 : CollatzResearch.WordTrace tailWord_8350931 prefixEnd_8350931 4288041515531771677757273 := by
  unfold tailWord_8350931
  simp only [CollatzResearch.WordTrace]
  refine ⟨304583476109010687312300647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203055650739340458208200431 304583476109010687312300647)
  ·
    refine ⟨456875214163516030968450971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304583476109010687312300647 456875214163516030968450971)
    ·
      refine ⟨685312821245274046452676457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456875214163516030968450971 685312821245274046452676457)
      ·
        refine ⟨513984615933955534839507343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 685312821245274046452676457 513984615933955534839507343)
        ·
          refine ⟨770976923900933302259261015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513984615933955534839507343 770976923900933302259261015)
          ·
            refine ⟨1156465385851399953388891523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770976923900933302259261015 1156465385851399953388891523)
            ·
              refine ⟨1734698078777099930083337285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1156465385851399953388891523 1734698078777099930083337285)
              ·
                refine ⟨325255889770706236890625741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1734698078777099930083337285 325255889770706236890625741)
                ·
                  refine ⟨121970958664014838833984653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 325255889770706236890625741 121970958664014838833984653)
                  ·
                    refine ⟨45739109499005564562744245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121970958664014838833984653 45739109499005564562744245)
                    ·
                      refine ⟨4288041515531771677757273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45739109499005564562744245 4288041515531771677757273)
                      ·
                        rfl

theorem cell23_8350931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 5].length) (baseStart_8350931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350931 prefixEnd_8350931 := by exact prefixLift 8350931
  have htrace : WordTrace (prefixWord ++ tailWord_8350931) baseStart_8350931 baseEnd_8350931 := by
    simpa [prefixWord, tailWord_8350931, baseEnd_8350931] using wordTrace_append hprefix tailTrace_8350931
  have hstable : (prefixWord ++ tailWord_8350931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350931).length < 2 ^ (prefixWord ++ tailWord_8350931).sum := by decide
  have hdescent : baseEnd_8350931 < baseStart_8350931 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350945 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 3, 4, 2]
def baseStart_8350945 : Nat := 118140960795 + 8350945 * 2 ^ 59
def prefixEnd_8350945 : Nat := 4983230072969 + 3 ^ 40 * 8350945 * 2
def baseEnd_8350945 : Nat := 4288048704260934622982209

theorem tailTrace_8350945 : CollatzResearch.WordTrace tailWord_8350945 prefixEnd_8350945 4288048704260934622982209 := by
  unfold tailWord_8350945
  simp only [CollatzResearch.WordTrace]
  refine ⟨304583986730959967703310289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203055991153973311802206859 304583986730959967703310289)
  ·
    refine ⟨228437990048219975777482717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304583986730959967703310289 228437990048219975777482717)
    ·
      refine ⟨85664246268082490916556019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228437990048219975777482717 85664246268082490916556019)
      ·
        refine ⟨128496369402123736374834029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85664246268082490916556019 128496369402123736374834029)
        ·
          refine ⟨48186138525796401140562761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128496369402123736374834029 48186138525796401140562761)
          ·
            refine ⟨36139603894347300855422071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48186138525796401140562761 36139603894347300855422071)
            ·
              refine ⟨54209405841520951283133107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36139603894347300855422071 54209405841520951283133107)
              ·
                refine ⟨81314108762281426924699661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54209405841520951283133107 81314108762281426924699661)
                ·
                  refine ⟨30492790785855535096762373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81314108762281426924699661 30492790785855535096762373)
                  ·
                    refine ⟨5717398272347912830642945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30492790785855535096762373 5717398272347912830642945)
                    ·
                      refine ⟨4288048704260934622982209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5717398272347912830642945 4288048704260934622982209)
                      ·
                        rfl

theorem cell23_8350945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 4, 2].length) (baseStart_8350945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350945 prefixEnd_8350945 := by exact prefixLift 8350945
  have htrace : WordTrace (prefixWord ++ tailWord_8350945) baseStart_8350945 baseEnd_8350945 := by
    simpa [prefixWord, tailWord_8350945, baseEnd_8350945] using wordTrace_append hprefix tailTrace_8350945
  have hstable : (prefixWord ++ tailWord_8350945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350945).length < 2 ^ (prefixWord ++ tailWord_8350945).sum := by decide
  have hdescent : baseEnd_8350945 < baseStart_8350945 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8350948 : List Nat := [2, 3, 1, 1, 1, 2, 4, 1, 2, 1, 5]
def baseStart_8350948 : Nat := 118140960795 + 8350948 * 2 ^ 59
def prefixEnd_8350948 : Nat := 4983230072969 + 3 ^ 40 * 8350948 * 2
def baseEnd_8350948 : Nat := 4288050244702898111244695

theorem tailTrace_8350948 : CollatzResearch.WordTrace tailWord_8350948 prefixEnd_8350948 4288050244702898111244695 := by
  unfold tailWord_8350948
  simp only [CollatzResearch.WordTrace]
  refine ⟨152292048074974549607834749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203056064099966066143779665 152292048074974549607834749)
  ·
    refine ⟨57109518028115456102938031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152292048074974549607834749 57109518028115456102938031)
    ·
      refine ⟨85664277042173184154407047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57109518028115456102938031 85664277042173184154407047)
      ·
        refine ⟨128496415563259776231610571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85664277042173184154407047 128496415563259776231610571)
        ·
          refine ⟨192744623344889664347415857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128496415563259776231610571 192744623344889664347415857)
          ·
            refine ⟨144558467508667248260561893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192744623344889664347415857 144558467508667248260561893)
            ·
              refine ⟨27104712657875109048855355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144558467508667248260561893 27104712657875109048855355)
              ·
                refine ⟨40657068986812663573283033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27104712657875109048855355 40657068986812663573283033)
                ·
                  refine ⟨30492801740109497679962275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40657068986812663573283033 30492801740109497679962275)
                  ·
                    refine ⟨45739202610164246519943413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30492801740109497679962275 45739202610164246519943413)
                    ·
                      refine ⟨4288050244702898111244695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45739202610164246519943413 4288050244702898111244695)
                      ·
                        rfl

theorem cell23_8350948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_8350948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8350948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8350948 prefixEnd_8350948 := by exact prefixLift 8350948
  have htrace : WordTrace (prefixWord ++ tailWord_8350948) baseStart_8350948 baseEnd_8350948 := by
    simpa [prefixWord, tailWord_8350948, baseEnd_8350948] using wordTrace_append hprefix tailTrace_8350948
  have hstable : (prefixWord ++ tailWord_8350948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8350948).length < 2 ^ (prefixWord ++ tailWord_8350948).sum := by decide
  have hdescent : baseEnd_8350948 < baseStart_8350948 := by decide
  rcases family_descends (prefixWord ++ tailWord_8350948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351002 : List Nat := [3, 1, 1, 3, 3, 2, 2, 3, 5]
def baseStart_8351002 : Nat := 118140960795 + 8351002 * 2 ^ 59
def prefixEnd_8351002 : Nat := 4983230072969 + 3 ^ 40 * 8351002 * 2
def baseEnd_8351002 : Nat := 476453108073137877774383

theorem tailTrace_8351002 : CollatzResearch.WordTrace tailWord_8351002 prefixEnd_8351002 476453108073137877774383 := by
  unfold tailWord_8351002
  simp only [CollatzResearch.WordTrace]
  refine ⟨76146516422938366609533815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203057377127835644292090173 76146516422938366609533815)
  ·
    refine ⟨114219774634407549914300723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76146516422938366609533815 114219774634407549914300723)
    ·
      refine ⟨171329661951611324871451085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114219774634407549914300723 171329661951611324871451085)
      ·
        refine ⟨64248623231854246826794157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171329661951611324871451085 64248623231854246826794157)
        ·
          refine ⟨24093233711945342560047809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64248623231854246826794157 24093233711945342560047809)
          ·
            refine ⟨18069925283959006920035857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24093233711945342560047809 18069925283959006920035857)
            ·
              refine ⟨13552443962969255190026893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18069925283959006920035857 13552443962969255190026893)
              ·
                refine ⟨5082166486113470696260085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13552443962969255190026893 5082166486113470696260085)
                ·
                  refine ⟨476453108073137877774383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5082166486113470696260085 476453108073137877774383)
                  ·
                    rfl

theorem cell23_8351002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3, 5].length) (baseStart_8351002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351002 prefixEnd_8351002 := by exact prefixLift 8351002
  have htrace : WordTrace (prefixWord ++ tailWord_8351002) baseStart_8351002 baseEnd_8351002 := by
    simpa [prefixWord, tailWord_8351002, baseEnd_8351002] using wordTrace_append hprefix tailTrace_8351002
  have hstable : (prefixWord ++ tailWord_8351002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351002).length < 2 ^ (prefixWord ++ tailWord_8351002).sum := by decide
  have hdescent : baseEnd_8351002 < baseStart_8351002 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351030 : List Nat := [5, 1, 2, 3, 1, 1, 3, 1, 2, 2, 2]
def baseStart_8351030 : Nat := 118140960795 + 8351030 * 2 ^ 59
def prefixEnd_8351030 : Nat := 4983230072969 + 3 ^ 40 * 8351030 * 2
def baseEnd_8351030 : Nat := 4288092350116566790419319

theorem tailTrace_8351030 : CollatzResearch.WordTrace tailWord_8351030 prefixEnd_8351030 4288092350116566790419319 := by
  unfold tailWord_8351030
  simp only [CollatzResearch.WordTrace]
  refine ⟨19036692933478251701259659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203058057957101351480103029 19036692933478251701259659)
  ·
    refine ⟨28555039400217377551889489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19036692933478251701259659 28555039400217377551889489)
    ·
      refine ⟨21416279550163033163917117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28555039400217377551889489 21416279550163033163917117)
      ·
        refine ⟨8031104831311137436468919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21416279550163033163917117 8031104831311137436468919)
        ·
          refine ⟨12046657246966706154703379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8031104831311137436468919 12046657246966706154703379)
          ·
            refine ⟨18069985870450059232055069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12046657246966706154703379 18069985870450059232055069)
            ·
              refine ⟨6776244701418772212020651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18069985870450059232055069 6776244701418772212020651)
              ·
                refine ⟨10164367052128158318030977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6776244701418772212020651 10164367052128158318030977)
                ·
                  refine ⟨7623275289096118738523233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10164367052128158318030977 7623275289096118738523233)
                  ·
                    refine ⟨5717456466822089053892425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7623275289096118738523233 5717456466822089053892425)
                    ·
                      refine ⟨4288092350116566790419319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5717456466822089053892425 4288092350116566790419319)
                      ·
                        rfl

theorem cell23_8351030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_8351030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351030 prefixEnd_8351030 := by exact prefixLift 8351030
  have htrace : WordTrace (prefixWord ++ tailWord_8351030) baseStart_8351030 baseEnd_8351030 := by
    simpa [prefixWord, tailWord_8351030, baseEnd_8351030] using wordTrace_append hprefix tailTrace_8351030
  have hstable : (prefixWord ++ tailWord_8351030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351030).length < 2 ^ (prefixWord ++ tailWord_8351030).sum := by decide
  have hdescent : baseEnd_8351030 < baseStart_8351030 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351048 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 1, 6, 4]
def baseStart_8351048 : Nat := 118140960795 + 8351048 * 2 ^ 59
def prefixEnd_8351048 : Nat := 4983230072969 + 3 ^ 40 * 8351048 * 2
def baseEnd_8351048 : Nat := 4288101592768347719994235

theorem tailTrace_8351048 : CollatzResearch.WordTrace tailWord_8351048 prefixEnd_8351048 4288101592768347719994235 := by
  unfold tailWord_8351048
  simp only [CollatzResearch.WordTrace]
  refine ⟨152293871724793408147154899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203058495633057877529539865 152293871724793408147154899)
  ·
    refine ⟨228440807587190112220732349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152293871724793408147154899 228440807587190112220732349)
    ·
      refine ⟨85665302845196292082774631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228440807587190112220732349 85665302845196292082774631)
      ·
        refine ⟨128497954267794438124161947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85665302845196292082774631 128497954267794438124161947)
        ·
          refine ⟨192746931401691657186242921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128497954267794438124161947 192746931401691657186242921)
          ·
            refine ⟨144560198551268742889682191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192746931401691657186242921 144560198551268742889682191)
            ·
              refine ⟨216840297826903114334523287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144560198551268742889682191 216840297826903114334523287)
              ·
                refine ⟨325260446740354671501784931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216840297826903114334523287 325260446740354671501784931)
                ·
                  refine ⟨487890670110532007252677397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 325260446740354671501784931 487890670110532007252677397)
                  ·
                    refine ⟨22869875161431187839969253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 487890670110532007252677397 22869875161431187839969253)
                    ·
                      refine ⟨4288101592768347719994235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22869875161431187839969253 4288101592768347719994235)
                      ·
                        rfl

theorem cell23_8351048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_8351048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351048 prefixEnd_8351048 := by exact prefixLift 8351048
  have htrace : WordTrace (prefixWord ++ tailWord_8351048) baseStart_8351048 baseEnd_8351048 := by
    simpa [prefixWord, tailWord_8351048, baseEnd_8351048] using wordTrace_append hprefix tailTrace_8351048
  have hstable : (prefixWord ++ tailWord_8351048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351048).length < 2 ^ (prefixWord ++ tailWord_8351048).sum := by decide
  have hdescent : baseEnd_8351048 < baseStart_8351048 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351053 : List Nat := [1, 6, 1, 3, 2, 1, 1, 3, 5]
def baseStart_8351053 : Nat := 118140960795 + 8351053 * 2 ^ 59
def prefixEnd_8351053 : Nat := 4983230072969 + 3 ^ 40 * 8351053 * 2
def baseEnd_8351053 : Nat := 476456017796846688936857

theorem tailTrace_8351053 : CollatzResearch.WordTrace tailWord_8351053 prefixEnd_8351053 476456017796846688936857 := by
  unfold tailWord_8351053
  simp only [CollatzResearch.WordTrace]
  refine ⟨304587925814568702148241813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203058617209712468098827875 304587925814568702148241813)
  ·
    refine ⟨14277559022557907913198835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 304587925814568702148241813 14277559022557907913198835)
    ·
      refine ⟨21416338533836861869798253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14277559022557907913198835 21416338533836861869798253)
      ·
        refine ⟨8031126950188823201174345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21416338533836861869798253 8031126950188823201174345)
        ·
          refine ⟨6023345212641617400880759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8031126950188823201174345 6023345212641617400880759)
          ·
            refine ⟨9035017818962426101321139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6023345212641617400880759 9035017818962426101321139)
            ·
              refine ⟨13552526728443639151981709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9035017818962426101321139 13552526728443639151981709)
              ·
                refine ⟨5082197523166364681993141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13552526728443639151981709 5082197523166364681993141)
                ·
                  refine ⟨476456017796846688936857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5082197523166364681993141 476456017796846688936857)
                  ·
                    rfl

theorem cell23_8351053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_8351053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351053 prefixEnd_8351053 := by exact prefixLift 8351053
  have htrace : WordTrace (prefixWord ++ tailWord_8351053) baseStart_8351053 baseEnd_8351053 := by
    simpa [prefixWord, tailWord_8351053, baseEnd_8351053] using wordTrace_append hprefix tailTrace_8351053
  have hstable : (prefixWord ++ tailWord_8351053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351053).length < 2 ^ (prefixWord ++ tailWord_8351053).sum := by decide
  have hdescent : baseEnd_8351053 < baseStart_8351053 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351072 : List Nat := [2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 3]
def baseStart_8351072 : Nat := 118140960795 + 8351072 * 2 ^ 59
def prefixEnd_8351072 : Nat := 4983230072969 + 3 ^ 40 * 8351072 * 2
def baseEnd_8351072 : Nat := 4288113916304055626094125

theorem tailTrace_8351072 : CollatzResearch.WordTrace tailWord_8351072 prefixEnd_8351072 4288113916304055626094125 := by
  unfold tailWord_8351072
  simp only [CollatzResearch.WordTrace]
  refine ⟨152294309400749934196591735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203059079200999912262122313 152294309400749934196591735)
  ·
    refine ⟨228441464101124901294887603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152294309400749934196591735 228441464101124901294887603)
    ·
      refine ⟨342662196151687351942331405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228441464101124901294887603 342662196151687351942331405)
      ·
        refine ⟨128498323556882756978374277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342662196151687351942331405 128498323556882756978374277)
        ·
          refine ⟨24093435666915516933445177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128498323556882756978374277 24093435666915516933445177)
          ·
            refine ⟨18070076750186637700083883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24093435666915516933445177 18070076750186637700083883)
            ·
              refine ⟨27105115125279956550125825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18070076750186637700083883 27105115125279956550125825)
              ·
                refine ⟨20328836343959967412594369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27105115125279956550125825 20328836343959967412594369)
                ·
                  refine ⟨15246627257969975559445777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20328836343959967412594369 15246627257969975559445777)
                  ·
                    refine ⟨11434970443477481669584333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15246627257969975559445777 11434970443477481669584333)
                    ·
                      refine ⟨4288113916304055626094125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11434970443477481669584333 4288113916304055626094125)
                      ·
                        rfl

theorem cell23_8351072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_8351072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351072 prefixEnd_8351072 := by exact prefixLift 8351072
  have htrace : WordTrace (prefixWord ++ tailWord_8351072) baseStart_8351072 baseEnd_8351072 := by
    simpa [prefixWord, tailWord_8351072, baseEnd_8351072] using wordTrace_append hprefix tailTrace_8351072
  have hstable : (prefixWord ++ tailWord_8351072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351072).length < 2 ^ (prefixWord ++ tailWord_8351072).sum := by decide
  have hdescent : baseEnd_8351072 < baseStart_8351072 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351079 : List Nat := [1, 1, 5, 1, 4, 2, 1, 1, 3, 4]
def baseStart_8351079 : Nat := 118140960795 + 8351079 * 2 ^ 59
def prefixEnd_8351079 : Nat := 4983230072969 + 3 ^ 40 * 8351079 * 2
def baseEnd_8351079 : Nat := 1429372503556212366235531

theorem tailTrace_8351079 : CollatzResearch.WordTrace tailWord_8351079 prefixEnd_8351079 1429372503556212366235531 := by
  unfold tailWord_8351079
  simp only [CollatzResearch.WordTrace]
  refine ⟨304588874112474508588688291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203059249408316339059125527 304588874112474508588688291)
  ·
    refine ⟨456883311168711762883032437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304588874112474508588688291 456883311168711762883032437)
    ·
      refine ⟨42832810422066727770284291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 456883311168711762883032437 42832810422066727770284291)
      ·
        refine ⟨64249215633100091655426437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42832810422066727770284291 64249215633100091655426437)
        ·
          refine ⟨12046727931206267185392457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64249215633100091655426437 12046727931206267185392457)
          ·
            refine ⟨9035045948404700389044343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12046727931206267185392457 9035045948404700389044343)
            ·
              refine ⟨13552568922607050583566515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9035045948404700389044343 13552568922607050583566515)
              ·
                refine ⟨20328853383910575875349773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13552568922607050583566515 20328853383910575875349773)
                ·
                  refine ⟨7623320018966465953256165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20328853383910575875349773 7623320018966465953256165)
                  ·
                    refine ⟨1429372503556212366235531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7623320018966465953256165 1429372503556212366235531)
                    ·
                      rfl

theorem cell23_8351079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_8351079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351079 prefixEnd_8351079 := by exact prefixLift 8351079
  have htrace : WordTrace (prefixWord ++ tailWord_8351079) baseStart_8351079 baseEnd_8351079 := by
    simpa [prefixWord, tailWord_8351079, baseEnd_8351079] using wordTrace_append hprefix tailTrace_8351079
  have hstable : (prefixWord ++ tailWord_8351079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351079).length < 2 ^ (prefixWord ++ tailWord_8351079).sum := by decide
  have hdescent : baseEnd_8351079 < baseStart_8351079 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351098 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7]
def baseStart_8351098 : Nat := 118140960795 + 8351098 * 2 ^ 59
def prefixEnd_8351098 : Nat := 4983230072969 + 3 ^ 40 * 8351098 * 2
def baseEnd_8351098 : Nat := 4288127266801072524369005

theorem tailTrace_8351098 : CollatzResearch.WordTrace tailWord_8351098 prefixEnd_8351098 4288127266801072524369005 := by
  unfold tailWord_8351098
  simp only [CollatzResearch.WordTrace]
  refine ⟨76147391774851418708407487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203059711399603783222419965 76147391774851418708407487)
  ·
    refine ⟨114221087662277128062611231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76147391774851418708407487 114221087662277128062611231)
    ·
      refine ⟨171331631493415692093916847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114221087662277128062611231 171331631493415692093916847)
      ·
        refine ⟨256997447240123538140875271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171331631493415692093916847 256997447240123538140875271)
        ·
          refine ⟨385496170860185307211312907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256997447240123538140875271 385496170860185307211312907)
          ·
            refine ⟨578244256290277960816969361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385496170860185307211312907 578244256290277960816969361)
            ·
              refine ⟨433683192217708470612727021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 578244256290277960816969361 433683192217708470612727021)
              ·
                refine ⟨162631197081640676479772633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 433683192217708470612727021 162631197081640676479772633)
                ·
                  refine ⟨121973397811230507359829475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162631197081640676479772633 121973397811230507359829475)
                  ·
                    refine ⟨182960096716845761039744213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121973397811230507359829475 182960096716845761039744213)
                    ·
                      refine ⟨4288127266801072524369005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182960096716845761039744213 4288127266801072524369005)
                      ·
                        rfl

theorem cell23_8351098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_8351098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351098 prefixEnd_8351098 := by exact prefixLift 8351098
  have htrace : WordTrace (prefixWord ++ tailWord_8351098) baseStart_8351098 baseEnd_8351098 := by
    simpa [prefixWord, tailWord_8351098, baseEnd_8351098] using wordTrace_append hprefix tailTrace_8351098
  have hstable : (prefixWord ++ tailWord_8351098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351098).length < 2 ^ (prefixWord ++ tailWord_8351098).sum := by decide
  have hdescent : baseEnd_8351098 < baseStart_8351098 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351106 : List Nat := [3, 4, 2, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_8351106 : Nat := 118140960795 + 8351106 * 2 ^ 59
def prefixEnd_8351106 : Nat := 4983230072969 + 3 ^ 40 * 8351106 * 2
def baseEnd_8351106 : Nat := 4288131374646308493068969

theorem tailTrace_8351106 : CollatzResearch.WordTrace tailWord_8351106 prefixEnd_8351106 4288131374646308493068969 := by
  unfold tailWord_8351106
  simp only [CollatzResearch.WordTrace]
  refine ⟨76147464720844173049980293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203059905922251128133280781 76147464720844173049980293)
  ·
    refine ⟨14277649635158282446871305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76147464720844173049980293 14277649635158282446871305)
    ·
      refine ⟨10708237226368711835153479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14277649635158282446871305 10708237226368711835153479)
      ·
        refine ⟨16062355839553067752730219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10708237226368711835153479 16062355839553067752730219)
        ·
          refine ⟨24093533759329601629095329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16062355839553067752730219 24093533759329601629095329)
          ·
            refine ⟨18070150319497201221821497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24093533759329601629095329 18070150319497201221821497)
            ·
              refine ⟨13552612739622900916366123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18070150319497201221821497 13552612739622900916366123)
              ·
                refine ⟨20328919109434351374549185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13552612739622900916366123 20328919109434351374549185)
                ·
                  refine ⟨15246689332075763530911889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20328919109434351374549185 15246689332075763530911889)
                  ·
                    refine ⟨11435016999056822648183917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15246689332075763530911889 11435016999056822648183917)
                    ·
                      refine ⟨4288131374646308493068969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11435016999056822648183917 4288131374646308493068969)
                      ·
                        rfl

theorem cell23_8351106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_8351106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351106 prefixEnd_8351106 := by exact prefixLift 8351106
  have htrace : WordTrace (prefixWord ++ tailWord_8351106) baseStart_8351106 baseEnd_8351106 := by
    simpa [prefixWord, tailWord_8351106, baseEnd_8351106] using wordTrace_append hprefix tailTrace_8351106
  have hstable : (prefixWord ++ tailWord_8351106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351106).length < 2 ^ (prefixWord ++ tailWord_8351106).sum := by decide
  have hdescent : baseEnd_8351106 < baseStart_8351106 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351159 : List Nat := [1, 1, 3, 1, 3, 2, 3, 2, 3, 2, 2]
def baseStart_8351159 : Nat := 118140960795 + 8351159 * 2 ^ 59
def prefixEnd_8351159 : Nat := 4983230072969 + 3 ^ 40 * 8351159 * 2
def baseEnd_8351159 : Nat := 4288158589120996785706225

theorem tailTrace_8351159 : CollatzResearch.WordTrace tailWord_8351159 prefixEnd_8351159 4288158589120996785706225 := by
  unfold tailWord_8351159
  simp only [CollatzResearch.WordTrace]
  refine ⟨304591791952184682251600531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203061194634789788167733687 304591791952184682251600531)
  ·
    refine ⟨456887687928277023377400797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304591791952184682251600531 456887687928277023377400797)
    ·
      refine ⟨171332882973103883766525299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456887687928277023377400797 171332882973103883766525299)
      ·
        refine ⟨256999324459655825649787949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171332882973103883766525299 256999324459655825649787949)
        ·
          refine ⟨96374746672370934618670481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256999324459655825649787949 96374746672370934618670481)
          ·
            refine ⟨72281060004278200964002861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96374746672370934618670481 72281060004278200964002861)
            ·
              refine ⟨27105397501604325361501073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72281060004278200964002861 27105397501604325361501073)
              ·
                refine ⟨20329048126203244021125805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27105397501604325361501073 20329048126203244021125805)
                ·
                  refine ⟨7623393047326216507922177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20329048126203244021125805 7623393047326216507922177)
                  ·
                    refine ⟨5717544785494662380941633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7623393047326216507922177 5717544785494662380941633)
                    ·
                      refine ⟨4288158589120996785706225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5717544785494662380941633 4288158589120996785706225)
                      ·
                        rfl

theorem cell23_8351159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 2, 2].length) (baseStart_8351159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351159 prefixEnd_8351159 := by exact prefixLift 8351159
  have htrace : WordTrace (prefixWord ++ tailWord_8351159) baseStart_8351159 baseEnd_8351159 := by
    simpa [prefixWord, tailWord_8351159, baseEnd_8351159] using wordTrace_append hprefix tailTrace_8351159
  have hstable : (prefixWord ++ tailWord_8351159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351159).length < 2 ^ (prefixWord ++ tailWord_8351159).sum := by decide
  have hdescent : baseEnd_8351159 < baseStart_8351159 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351179 : List Nat := [1, 1, 1, 1, 3, 3, 6, 1, 1, 2, 3]
def baseStart_8351179 : Nat := 118140960795 + 8351179 * 2 ^ 59
def prefixEnd_8351179 : Nat := 4983230072969 + 3 ^ 40 * 8351179 * 2
def baseEnd_8351179 : Nat := 4288168858734086707456133

theorem tailTrace_8351179 : CollatzResearch.WordTrace tailWord_8351179 prefixEnd_8351179 4288168858734086707456133 := by
  unfold tailWord_8351179
  simp only [CollatzResearch.WordTrace]
  refine ⟨304592521412112225667328591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203061680941408150444885727 304592521412112225667328591)
  ·
    refine ⟨456888782118168338500992887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304592521412112225667328591 456888782118168338500992887)
    ·
      refine ⟨685333173177252507751489331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456888782118168338500992887 685333173177252507751489331)
      ·
        refine ⟨1027999759765878761627233997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685333173177252507751489331 1027999759765878761627233997)
        ·
          refine ⟨385499909912204535610212749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1027999759765878761627233997 385499909912204535610212749)
          ·
            refine ⟨144562466217076700853829781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 385499909912204535610212749 144562466217076700853829781)
            ·
              refine ⟨6776365603925470352523271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144562466217076700853829781 6776365603925470352523271)
              ·
                refine ⟨10164548405888205528784907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6776365603925470352523271 10164548405888205528784907)
                ·
                  refine ⟨15246822608832308293177361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10164548405888205528784907 15246822608832308293177361)
                  ·
                    refine ⟨11435116956624231219883021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15246822608832308293177361 11435116956624231219883021)
                    ·
                      refine ⟨4288168858734086707456133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11435116956624231219883021 4288168858734086707456133)
                      ·
                        rfl

theorem cell23_8351179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 1, 2, 3].length) (baseStart_8351179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351179 prefixEnd_8351179 := by exact prefixLift 8351179
  have htrace : WordTrace (prefixWord ++ tailWord_8351179) baseStart_8351179 baseEnd_8351179 := by
    simpa [prefixWord, tailWord_8351179, baseEnd_8351179] using wordTrace_append hprefix tailTrace_8351179
  have hstable : (prefixWord ++ tailWord_8351179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351179).length < 2 ^ (prefixWord ++ tailWord_8351179).sum := by decide
  have hdescent : baseEnd_8351179 < baseStart_8351179 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351215 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 4]
def baseStart_8351215 : Nat := 118140960795 + 8351215 * 2 ^ 59
def prefixEnd_8351215 : Nat := 4983230072969 + 3 ^ 40 * 8351215 * 2
def baseEnd_8351215 : Nat := 4288187344037648566605967

theorem tailTrace_8351215 : CollatzResearch.WordTrace tailWord_8351215 prefixEnd_8351215 4288187344037648566605967 := by
  unfold tailWord_8351215
  simp only [CollatzResearch.WordTrace]
  refine ⟨304593834439981803815639099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203062556293321202543759399 304593834439981803815639099)
  ·
    refine ⟨456890751659972705723458649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304593834439981803815639099 456890751659972705723458649)
    ·
      refine ⟨342668063744979529292593987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456890751659972705723458649 342668063744979529292593987)
      ·
        refine ⟨514002095617469293938890981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342668063744979529292593987 514002095617469293938890981)
        ·
          refine ⟨96375392928275492613542059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 514002095617469293938890981 96375392928275492613542059)
          ·
            refine ⟨144563089392413238920313089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96375392928275492613542059 144563089392413238920313089)
            ·
              refine ⟨108422317044309929190234817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144563089392413238920313089 108422317044309929190234817)
              ·
                refine ⟨81316737783232446892676113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108422317044309929190234817 81316737783232446892676113)
                ·
                  refine ⟨60987553337424335169507085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81316737783232446892676113 60987553337424335169507085)
                  ·
                    refine ⟨22870332501534125688565157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60987553337424335169507085 22870332501534125688565157)
                    ·
                      refine ⟨4288187344037648566605967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22870332501534125688565157 4288187344037648566605967)
                      ·
                        rfl

theorem cell23_8351215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 4].length) (baseStart_8351215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351215 prefixEnd_8351215 := by exact prefixLift 8351215
  have htrace : WordTrace (prefixWord ++ tailWord_8351215) baseStart_8351215 baseEnd_8351215 := by
    simpa [prefixWord, tailWord_8351215, baseEnd_8351215] using wordTrace_append hprefix tailTrace_8351215
  have hstable : (prefixWord ++ tailWord_8351215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351215).length < 2 ^ (prefixWord ++ tailWord_8351215).sum := by decide
  have hdescent : baseEnd_8351215 < baseStart_8351215 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351222 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_8351222 : Nat := 118140960795 + 8351222 * 2 ^ 59
def prefixEnd_8351222 : Nat := 4983230072969 + 3 ^ 40 * 8351222 * 2
def baseEnd_8351222 : Nat := 4288190938402230039218435

theorem tailTrace_8351222 : CollatzResearch.WordTrace tailWord_8351222 prefixEnd_8351222 4288190938402230039218435 := by
  unfold tailWord_8351222
  simp only [CollatzResearch.WordTrace]
  refine ⟨19037130609434777750696495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203062726500637629340762613 19037130609434777750696495)
  ·
    refine ⟨28555695914152166626044743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19037130609434777750696495 28555695914152166626044743)
    ·
      refine ⟨42833543871228249939067115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28555695914152166626044743 42833543871228249939067115)
      ·
        refine ⟨64250315806842374908600673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42833543871228249939067115 64250315806842374908600673)
        ·
          refine ⟨48187736855131781181450505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64250315806842374908600673 48187736855131781181450505)
          ·
            refine ⟨36140802641348835886087879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48187736855131781181450505 36140802641348835886087879)
            ·
              refine ⟨54211203962023253829131819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36140802641348835886087879 54211203962023253829131819)
              ·
                refine ⟨81316805943034880743697729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54211203962023253829131819 81316805943034880743697729)
                ·
                  refine ⟨60987604457276160557773297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81316805943034880743697729 60987604457276160557773297)
                  ·
                    refine ⟨45740703342957120418329973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60987604457276160557773297 45740703342957120418329973)
                    ·
                      refine ⟨4288190938402230039218435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45740703342957120418329973 4288190938402230039218435)
                      ·
                        rfl

theorem cell23_8351222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_8351222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351222 prefixEnd_8351222 := by exact prefixLift 8351222
  have htrace : WordTrace (prefixWord ++ tailWord_8351222) baseStart_8351222 baseEnd_8351222 := by
    simpa [prefixWord, tailWord_8351222, baseEnd_8351222] using wordTrace_append hprefix tailTrace_8351222
  have hstable : (prefixWord ++ tailWord_8351222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351222).length < 2 ^ (prefixWord ++ tailWord_8351222).sum := by decide
  have hdescent : baseEnd_8351222 < baseStart_8351222 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351249 : List Nat := [1, 2, 2, 1, 1, 2, 3, 3, 4, 2, 2]
def baseStart_8351249 : Nat := 118140960795 + 8351249 * 2 ^ 59
def prefixEnd_8351249 : Nat := 4983230072969 + 3 ^ 40 * 8351249 * 2
def baseEnd_8351249 : Nat := 4288204802379901433580811

theorem tailTrace_8351249 : CollatzResearch.WordTrace tailWord_8351249 prefixEnd_8351249 4288204802379901433580811 := by
  unfold tailWord_8351249
  simp only [CollatzResearch.WordTrace]
  refine ⟨304595074521858627622376801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203063383014572418414917867 304595074521858627622376801)
  ·
    refine ⟨228446305891393970716782601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304595074521858627622376801 228446305891393970716782601)
    ·
      refine ⟨171334729418545478037586951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228446305891393970716782601 171334729418545478037586951)
      ·
        refine ⟨257002094127818217056380427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171334729418545478037586951 257002094127818217056380427)
        ·
          refine ⟨385503141191727325584570641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257002094127818217056380427 385503141191727325584570641)
          ·
            refine ⟨289127355893795494188427981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385503141191727325584570641 289127355893795494188427981)
            ·
              refine ⟨108422758460173310320660493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289127355893795494188427981 108422758460173310320660493)
              ·
                refine ⟨40658534422564991370247685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108422758460173310320660493 40658534422564991370247685)
                ·
                  refine ⟨7623475204230935881921441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40658534422564991370247685 7623475204230935881921441)
                  ·
                    refine ⟨5717606403173201911441081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7623475204230935881921441 5717606403173201911441081)
                    ·
                      refine ⟨4288204802379901433580811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5717606403173201911441081 4288204802379901433580811)
                      ·
                        rfl

theorem cell23_8351249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4, 2, 2].length) (baseStart_8351249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351249 prefixEnd_8351249 := by exact prefixLift 8351249
  have htrace : WordTrace (prefixWord ++ tailWord_8351249) baseStart_8351249 baseEnd_8351249 := by
    simpa [prefixWord, tailWord_8351249, baseEnd_8351249] using wordTrace_append hprefix tailTrace_8351249
  have hstable : (prefixWord ++ tailWord_8351249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351249).length < 2 ^ (prefixWord ++ tailWord_8351249).sum := by decide
  have hdescent : baseEnd_8351249 < baseStart_8351249 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351282 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3]
def baseStart_8351282 : Nat := 118140960795 + 8351282 * 2 ^ 59
def prefixEnd_8351282 : Nat := 4983230072969 + 3 ^ 40 * 8351282 * 2
def baseEnd_8351282 : Nat := 4288221747241499804468159

theorem tailTrace_8351282 : CollatzResearch.WordTrace tailWord_8351282 prefixEnd_8351282 4288221747241499804468159 := by
  unfold tailWord_8351282
  simp only [CollatzResearch.WordTrace]
  refine ⟨76149069532684768564582025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203064185420492716172218733 76149069532684768564582025)
  ·
    refine ⟨57111802149513576423436519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76149069532684768564582025 57111802149513576423436519)
    ·
      refine ⟨85667703224270364635154779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57111802149513576423436519 85667703224270364635154779)
      ·
        refine ⟨128501554836405546952732169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85667703224270364635154779 128501554836405546952732169)
        ·
          refine ⟨96376166127304160214549127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128501554836405546952732169 96376166127304160214549127)
          ·
            refine ⟨144564249190956240321823691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96376166127304160214549127 144564249190956240321823691)
            ·
              refine ⟨216846373786434360482735537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144564249190956240321823691 216846373786434360482735537)
              ·
                refine ⟨162634780339825770362051653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216846373786434360482735537 162634780339825770362051653)
                ·
                  refine ⟨30494021313717331942884685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162634780339825770362051653 30494021313717331942884685)
                  ·
                    refine ⟨11435257992643999478581757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30494021313717331942884685 11435257992643999478581757)
                    ·
                      refine ⟨4288221747241499804468159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11435257992643999478581757 4288221747241499804468159)
                      ·
                        rfl

theorem cell23_8351282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_8351282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351282 prefixEnd_8351282 := by exact prefixLift 8351282
  have htrace : WordTrace (prefixWord ++ tailWord_8351282) baseStart_8351282 baseEnd_8351282 := by
    simpa [prefixWord, tailWord_8351282, baseEnd_8351282] using wordTrace_append hprefix tailTrace_8351282
  have hstable : (prefixWord ++ tailWord_8351282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351282).length < 2 ^ (prefixWord ++ tailWord_8351282).sum := by decide
  have hdescent : baseEnd_8351282 < baseStart_8351282 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351322 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4]
def baseStart_8351322 : Nat := 118140960795 + 8351322 * 2 ^ 59
def prefixEnd_8351322 : Nat := 4983230072969 + 3 ^ 40 * 8351322 * 2
def baseEnd_8351322 : Nat := 4288242286467679647967975

theorem tailTrace_8351322 : CollatzResearch.WordTrace tailWord_8351322 prefixEnd_8351322 4288242286467679647967975 := by
  unfold tailWord_8351322
  simp only [CollatzResearch.WordTrace]
  refine ⟨76149434262648540272446055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203065158033729440726522813 76149434262648540272446055)
  ·
    refine ⟨114224151393972810408669083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76149434262648540272446055 114224151393972810408669083)
    ·
      refine ⟨171336227090959215613003625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114224151393972810408669083 171336227090959215613003625)
      ·
        refine ⟨128502170318219411709752719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171336227090959215613003625 128502170318219411709752719)
        ·
          refine ⟨192753255477329117564629079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128502170318219411709752719 192753255477329117564629079)
          ·
            refine ⟨289129883215993676346943619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192753255477329117564629079 289129883215993676346943619)
            ·
              refine ⟨433694824823990514520415429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289129883215993676346943619 433694824823990514520415429)
              ·
                refine ⟨81317779654498221472577893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 433694824823990514520415429 81317779654498221472577893)
                ·
                  refine ⟨15247083685218416526108355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81317779654498221472577893 15247083685218416526108355)
                  ·
                    refine ⟨22870625527827624789162533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15247083685218416526108355 22870625527827624789162533)
                    ·
                      refine ⟨4288242286467679647967975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22870625527827624789162533 4288242286467679647967975)
                      ·
                        rfl

theorem cell23_8351322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_8351322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351322 prefixEnd_8351322 := by exact prefixLift 8351322
  have htrace : WordTrace (prefixWord ++ tailWord_8351322) baseStart_8351322 baseEnd_8351322 := by
    simpa [prefixWord, tailWord_8351322, baseEnd_8351322] using wordTrace_append hprefix tailTrace_8351322
  have hstable : (prefixWord ++ tailWord_8351322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351322).length < 2 ^ (prefixWord ++ tailWord_8351322).sum := by decide
  have hdescent : baseEnd_8351322 < baseStart_8351322 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351336 : List Nat := [2, 1, 4, 3, 1, 3, 1, 1, 2, 5]
def baseStart_8351336 : Nat := 118140960795 + 8351336 * 2 ^ 59
def prefixEnd_8351336 : Nat := 4983230072969 + 3 ^ 40 * 8351336 * 2
def baseEnd_8351336 : Nat := 1429416491732280864397637

theorem tailTrace_8351336 : CollatzResearch.WordTrace tailWord_8351336 prefixEnd_8351336 1429416491732280864397637 := by
  unfold tailWord_8351336
  simp only [CollatzResearch.WordTrace]
  refine ⟨152299123836271720740396931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203065498448362294320529241 152299123836271720740396931)
  ·
    refine ⟨228448685754407581110595397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152299123836271720740396931 228448685754407581110595397)
    ·
      refine ⟨42834128578951421458236637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228448685754407581110595397 42834128578951421458236637)
      ·
        refine ⟨16062798217106783046838739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42834128578951421458236637 16062798217106783046838739)
        ·
          refine ⟨24094197325660174570258109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16062798217106783046838739 24094197325660174570258109)
          ·
            refine ⟨9035323997122565463846791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24094197325660174570258109 9035323997122565463846791)
            ·
              refine ⟨13552985995683848195770187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9035323997122565463846791 13552985995683848195770187)
              ·
                refine ⟨20329478993525772293655281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13552985995683848195770187 20329478993525772293655281)
                ·
                  refine ⟨15247109245144329220241461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20329478993525772293655281 15247109245144329220241461)
                  ·
                    refine ⟨1429416491732280864397637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15247109245144329220241461 1429416491732280864397637)
                    ·
                      rfl

theorem cell23_8351336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_8351336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351336 prefixEnd_8351336 := by exact prefixLift 8351336
  have htrace : WordTrace (prefixWord ++ tailWord_8351336) baseStart_8351336 baseEnd_8351336 := by
    simpa [prefixWord, tailWord_8351336, baseEnd_8351336] using wordTrace_append hprefix tailTrace_8351336
  have hstable : (prefixWord ++ tailWord_8351336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351336).length < 2 ^ (prefixWord ++ tailWord_8351336).sum := by decide
  have hdescent : baseEnd_8351336 < baseStart_8351336 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351430 : List Nat := [6, 1, 2, 1, 1, 1, 4, 1, 6]
def baseStart_8351430 : Nat := 118140960795 + 8351430 * 2 ^ 59
def prefixEnd_8351430 : Nat := 4983230072969 + 3 ^ 40 * 8351430 * 2
def baseEnd_8351430 : Nat := 476477526930929469490831

theorem tailTrace_8351430 : CollatzResearch.WordTrace tailWord_8351430 prefixEnd_8351430 476477526930929469490831 := by
  unfold tailWord_8351430
  simp only [CollatzResearch.WordTrace]
  refine ⟨9518802379193840485459867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 203067784089468597023143829 9518802379193840485459867)
  ·
    refine ⟨14278203568790760728189801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9518802379193840485459867 14278203568790760728189801)
    ·
      refine ⟨10708652676593070546142351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14278203568790760728189801 10708652676593070546142351)
      ·
        refine ⟨16062979014889605819213527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10708652676593070546142351 16062979014889605819213527)
        ·
          refine ⟨24094468522334408728820291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16062979014889605819213527 24094468522334408728820291)
          ·
            refine ⟨36141702783501613093230437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24094468522334408728820291 36141702783501613093230437)
            ·
              refine ⟨6776569271906552454980707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36141702783501613093230437 6776569271906552454980707)
              ·
                refine ⟨10164853907859828682471061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6776569271906552454980707 10164853907859828682471061)
                ·
                  refine ⟨476477526930929469490831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10164853907859828682471061 476477526930929469490831)
                  ·
                    rfl

theorem cell23_8351430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_8351430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351430 prefixEnd_8351430 := by exact prefixLift 8351430
  have htrace : WordTrace (prefixWord ++ tailWord_8351430) baseStart_8351430 baseEnd_8351430 := by
    simpa [prefixWord, tailWord_8351430, baseEnd_8351430] using wordTrace_append hprefix tailTrace_8351430
  have hstable : (prefixWord ++ tailWord_8351430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351430).length < 2 ^ (prefixWord ++ tailWord_8351430).sum := by decide
  have hdescent : baseEnd_8351430 < baseStart_8351430 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351466 : List Nat := [3, 1, 3, 1, 1, 1, 2, 5, 1, 2, 3]
def baseStart_8351466 : Nat := 118140960795 + 8351466 * 2 ^ 59
def prefixEnd_8351466 : Nat := 4983230072969 + 3 ^ 40 * 8351466 * 2
def baseEnd_8351466 : Nat := 4288316227681927084567313

theorem tailTrace_8351466 : CollatzResearch.WordTrace tailWord_8351466 prefixEnd_8351466 4288316227681927084567313 := by
  unfold tailWord_8351466
  simp only [CollatzResearch.WordTrace]
  refine ⟨76150747290518118420756563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203068659441381649122017501 76150747290518118420756563)
  ·
    refine ⟨114226120935777177631134845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76150747290518118420756563 114226120935777177631134845)
    ·
      refine ⟨42834795350916441611675567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114226120935777177631134845 42834795350916441611675567)
      ·
        refine ⟨64252193026374662417513351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42834795350916441611675567 64252193026374662417513351)
        ·
          refine ⟨96378289539561993626270027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64252193026374662417513351 96378289539561993626270027)
          ·
            refine ⟨144567434309342990439405041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96378289539561993626270027 144567434309342990439405041)
            ·
              refine ⟨108425575732007242829553781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144567434309342990439405041 108425575732007242829553781)
              ·
                refine ⟨10164897724875679015270667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108425575732007242829553781 10164897724875679015270667)
                ·
                  refine ⟨15247346587313518522906001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10164897724875679015270667 15247346587313518522906001)
                  ·
                    refine ⟨11435509940485138892179501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15247346587313518522906001 11435509940485138892179501)
                    ·
                      refine ⟨4288316227681927084567313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11435509940485138892179501 4288316227681927084567313)
                      ·
                        rfl

theorem cell23_8351466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_8351466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351466 prefixEnd_8351466 := by exact prefixLift 8351466
  have htrace : WordTrace (prefixWord ++ tailWord_8351466) baseStart_8351466 baseEnd_8351466 := by
    simpa [prefixWord, tailWord_8351466, baseEnd_8351466] using wordTrace_append hprefix tailTrace_8351466
  have hstable : (prefixWord ++ tailWord_8351466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351466).length < 2 ^ (prefixWord ++ tailWord_8351466).sum := by decide
  have hdescent : baseEnd_8351466 < baseStart_8351466 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351472 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 6]
def baseStart_8351472 : Nat := 118140960795 + 8351472 * 2 ^ 59
def prefixEnd_8351472 : Nat := 4983230072969 + 3 ^ 40 * 8351472 * 2
def baseEnd_8351472 : Nat := 4288319308565854061092285

theorem tailTrace_8351472 : CollatzResearch.WordTrace tailWord_8351472 prefixEnd_8351472 4288319308565854061092285 := by
  unfold tailWord_8351472
  simp only [CollatzResearch.WordTrace]
  refine ⟨152301604000025368353872335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203068805333367157805163113 152301604000025368353872335)
  ·
    refine ⟨228452406000038052530808503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152301604000025368353872335 228452406000038052530808503)
    ·
      refine ⟨342678609000057078796212755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228452406000038052530808503 342678609000057078796212755)
      ·
        refine ⟨514017913500085618194319133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342678609000057078796212755 514017913500085618194319133)
        ·
          refine ⟨192756717562532106822869675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 514017913500085618194319133 192756717562532106822869675)
          ·
            refine ⟨289135076343798160234304513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192756717562532106822869675 289135076343798160234304513)
            ·
              refine ⟨216851307257848620175728385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289135076343798160234304513 216851307257848620175728385)
              ·
                refine ⟨162638480443386465131796289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216851307257848620175728385 162638480443386465131796289)
                ·
                  refine ⟨121978860332539848848847217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162638480443386465131796289 121978860332539848848847217)
                  ·
                    refine ⟨91484145249404886636635413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121978860332539848848847217 91484145249404886636635413)
                    ·
                      refine ⟨4288319308565854061092285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91484145249404886636635413 4288319308565854061092285)
                      ·
                        rfl

theorem cell23_8351472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 6].length) (baseStart_8351472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351472 prefixEnd_8351472 := by exact prefixLift 8351472
  have htrace : WordTrace (prefixWord ++ tailWord_8351472) baseStart_8351472 baseEnd_8351472 := by
    simpa [prefixWord, tailWord_8351472, baseEnd_8351472] using wordTrace_append hprefix tailTrace_8351472
  have hstable : (prefixWord ++ tailWord_8351472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351472).length < 2 ^ (prefixWord ++ tailWord_8351472).sum := by decide
  have hdescent : baseEnd_8351472 < baseStart_8351472 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351496 : List Nat := [2, 1, 3, 2, 2, 1, 4, 1, 1, 3, 3]
def baseStart_8351496 : Nat := 118140960795 + 8351496 * 2 ^ 59
def prefixEnd_8351496 : Nat := 4983230072969 + 3 ^ 40 * 8351496 * 2
def baseEnd_8351496 : Nat := 4288331632101561967192175

theorem tailTrace_8351496 : CollatzResearch.WordTrace tailWord_8351496 prefixEnd_8351496 4288331632101561967192175 := by
  unfold tailWord_8351496
  simp only [CollatzResearch.WordTrace]
  refine ⟨152302041675981894403309171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203069388901309192537745561 152302041675981894403309171)
  ·
    refine ⟨228453062513972841604963757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152302041675981894403309171 228453062513972841604963757)
    ·
      refine ⟨85669898442739815601861409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228453062513972841604963757 85669898442739815601861409)
      ·
        refine ⟨64252423832054861701396057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85669898442739815601861409 64252423832054861701396057)
        ·
          refine ⟨48189317874041146276047043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64252423832054861701396057 48189317874041146276047043)
          ·
            refine ⟨72283976811061719414070565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48189317874041146276047043 72283976811061719414070565)
            ·
              refine ⟨13553245652074072390138231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72283976811061719414070565 13553245652074072390138231)
              ·
                refine ⟨20329868478111108585207347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13553245652074072390138231 20329868478111108585207347)
                ·
                  refine ⟨30494802717166662877811021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20329868478111108585207347 30494802717166662877811021)
                  ·
                    refine ⟨11435551018937498579179133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30494802717166662877811021 11435551018937498579179133)
                    ·
                      refine ⟨4288331632101561967192175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11435551018937498579179133 4288331632101561967192175)
                      ·
                        rfl

theorem cell23_8351496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_8351496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351496 prefixEnd_8351496 := by exact prefixLift 8351496
  have htrace : WordTrace (prefixWord ++ tailWord_8351496) baseStart_8351496 baseEnd_8351496 := by
    simpa [prefixWord, tailWord_8351496, baseEnd_8351496] using wordTrace_append hprefix tailTrace_8351496
  have hstable : (prefixWord ++ tailWord_8351496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351496).length < 2 ^ (prefixWord ++ tailWord_8351496).sum := by decide
  have hdescent : baseEnd_8351496 < baseStart_8351496 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351501 : List Nat := [1, 7, 2, 1, 1, 2, 1, 1, 2, 3, 2]
def baseStart_8351501 : Nat := 118140960795 + 8351501 * 2 ^ 59
def prefixEnd_8351501 : Nat := 4983230072969 + 3 ^ 40 * 8351501 * 2
def baseEnd_8351501 : Nat := 4288334199504834447629653

theorem tailTrace_8351501 : CollatzResearch.WordTrace tailWord_8351501 prefixEnd_8351501 4288334199504834447629653 := by
  unfold tailWord_8351501
  simp only [CollatzResearch.WordTrace]
  refine ⟨304604265716945674660550357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203069510477963783107033571 304604265716945674660550357)
  ·
    refine ⟨7139162477740914249856649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 304604265716945674660550357 7139162477740914249856649)
    ·
      refine ⟨5354371858305685687392487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7139162477740914249856649 5354371858305685687392487)
      ·
        refine ⟨8031557787458528531088731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5354371858305685687392487 8031557787458528531088731)
        ·
          refine ⟨12047336681187792796633097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8031557787458528531088731 12047336681187792796633097)
          ·
            refine ⟨9035502510890844597474823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12047336681187792796633097 9035502510890844597474823)
            ·
              refine ⟨13553253766336266896212235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9035502510890844597474823 13553253766336266896212235)
              ·
                refine ⟨20329880649504400344318353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13553253766336266896212235 20329880649504400344318353)
                ·
                  refine ⟨15247410487128300258238765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20329880649504400344318353 15247410487128300258238765)
                  ·
                    refine ⟨5717778932673112596839537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15247410487128300258238765 5717778932673112596839537)
                    ·
                      refine ⟨4288334199504834447629653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5717778932673112596839537 4288334199504834447629653)
                      ·
                        rfl

theorem cell23_8351501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_8351501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351501 prefixEnd_8351501 := by exact prefixLift 8351501
  have htrace : WordTrace (prefixWord ++ tailWord_8351501) baseStart_8351501 baseEnd_8351501 := by
    simpa [prefixWord, tailWord_8351501, baseEnd_8351501] using wordTrace_append hprefix tailTrace_8351501
  have hstable : (prefixWord ++ tailWord_8351501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351501).length < 2 ^ (prefixWord ++ tailWord_8351501).sum := by decide
  have hdescent : baseEnd_8351501 < baseStart_8351501 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351559 : List Nat := [1, 1, 4, 1, 2, 1, 4, 2, 7]
def baseStart_8351559 : Nat := 118140960795 + 8351559 * 2 ^ 59
def prefixEnd_8351559 : Nat := 4983230072969 + 3 ^ 40 * 8351559 * 2
def baseEnd_8351559 : Nat := 476484886820310580078265

theorem tailTrace_8351559 : CollatzResearch.WordTrace tailWord_8351559 prefixEnd_8351559 476484886820310580078265 := by
  unfold tailWord_8351559
  simp only [CollatzResearch.WordTrace]
  refine ⟨304606381150735550566161731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203070920767157033710774487 304606381150735550566161731)
  ·
    refine ⟨456909571726103325849242597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304606381150735550566161731 456909571726103325849242597)
    ·
      refine ⟨85670544698644373596732987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 456909571726103325849242597 85670544698644373596732987)
      ·
        refine ⟨128505817047966560395099481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85670544698644373596732987 128505817047966560395099481)
        ·
          refine ⟨96379362785974920296324611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128505817047966560395099481 96379362785974920296324611)
          ·
            refine ⟨144569044178962380444486917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96379362785974920296324611 144569044178962380444486917)
            ·
              refine ⟨27106695783555446333341297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144569044178962380444486917 27106695783555446333341297)
              ·
                refine ⟨20330021837666584750005973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27106695783555446333341297 20330021837666584750005973)
                ·
                  refine ⟨476484886820310580078265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20330021837666584750005973 476484886820310580078265)
                  ·
                    rfl

theorem cell23_8351559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 7].length) (baseStart_8351559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351559 prefixEnd_8351559 := by exact prefixLift 8351559
  have htrace : WordTrace (prefixWord ++ tailWord_8351559) baseStart_8351559 baseEnd_8351559 := by
    simpa [prefixWord, tailWord_8351559, baseEnd_8351559] using wordTrace_append hprefix tailTrace_8351559
  have hstable : (prefixWord ++ tailWord_8351559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351559).length < 2 ^ (prefixWord ++ tailWord_8351559).sum := by decide
  have hdescent : baseEnd_8351559 < baseStart_8351559 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351623 : List Nat := [1, 1, 4, 2, 4, 1, 2, 1, 2, 5]
def baseStart_8351623 : Nat := 118140960795 + 8351623 * 2 ^ 59
def prefixEnd_8351623 : Nat := 4983230072969 + 3 ^ 40 * 8351623 * 2
def baseEnd_8351623 : Nat := 1429465614714894323434697

theorem tailTrace_8351623 : CollatzResearch.WordTrace tailWord_8351623 prefixEnd_8351623 1429465614714894323434697 := by
  unfold tailWord_8351623
  simp only [CollatzResearch.WordTrace]
  refine ⟨304608715422503689496491523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203072476948335792997661015 304608715422503689496491523)
  ·
    refine ⟨456913073133755534244737285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304608715422503689496491523 456913073133755534244737285)
    ·
      refine ⟨85671201212579162670888241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 456913073133755534244737285 85671201212579162670888241)
      ·
        refine ⟨64253400909434372003166181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85671201212579162670888241 64253400909434372003166181)
        ·
          refine ⟨12047512670518944750593659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64253400909434372003166181 12047512670518944750593659)
          ·
            refine ⟨18071269005778417125890489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12047512670518944750593659 18071269005778417125890489)
            ·
              refine ⟨13553451754333812844417867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18071269005778417125890489 13553451754333812844417867)
              ·
                refine ⟨20330177631500719266626801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13553451754333812844417867 20330177631500719266626801)
                ·
                  refine ⟨15247633223625539449970101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20330177631500719266626801 15247633223625539449970101)
                  ·
                    refine ⟨1429465614714894323434697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15247633223625539449970101 1429465614714894323434697)
                    ·
                      rfl

theorem cell23_8351623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_8351623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351623 prefixEnd_8351623 := by exact prefixLift 8351623
  have htrace : WordTrace (prefixWord ++ tailWord_8351623) baseStart_8351623 baseEnd_8351623 := by
    simpa [prefixWord, tailWord_8351623, baseEnd_8351623] using wordTrace_append hprefix tailTrace_8351623
  have hstable : (prefixWord ++ tailWord_8351623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351623).length < 2 ^ (prefixWord ++ tailWord_8351623).sum := by decide
  have hdescent : baseEnd_8351623 < baseStart_8351623 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351689 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 1, 3, 7]
def baseStart_8351689 : Nat := 118140960795 + 8351689 * 2 ^ 59
def prefixEnd_8351689 : Nat := 4983230072969 + 3 ^ 40 * 8351689 * 2
def baseEnd_8351689 : Nat := 4288430733867879712078787

theorem tailTrace_8351689 : CollatzResearch.WordTrace tailWord_8351689 prefixEnd_8351689 4288430733867879712078787 := by
  unfold tailWord_8351689
  simp only [CollatzResearch.WordTrace]
  refine ⟨304611122640264582768394121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203074081760176388512262747 304611122640264582768394121)
  ·
    refine ⟨228458341980198437076295591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304611122640264582768394121 228458341980198437076295591)
    ·
      refine ⟨342687512970297655614443387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228458341980198437076295591 342687512970297655614443387)
      ·
        refine ⟨514031269455446483421665081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342687512970297655614443387 514031269455446483421665081)
        ·
          refine ⟨385523452091584862566248811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 514031269455446483421665081 385523452091584862566248811)
          ·
            refine ⟨578285178137377293849373217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385523452091584862566248811 578285178137377293849373217)
            ·
              refine ⟨433713883603032970387029913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 578285178137377293849373217 433713883603032970387029913)
              ·
                refine ⟨325285412702274727790272435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433713883603032970387029913 325285412702274727790272435)
                ·
                  refine ⟨487928119053412091685408653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 325285412702274727790272435 487928119053412091685408653)
                  ·
                    refine ⟨182973044645029534382028245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 487928119053412091685408653 182973044645029534382028245)
                    ·
                      refine ⟨4288430733867879712078787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182973044645029534382028245 4288430733867879712078787)
                      ·
                        rfl

theorem cell23_8351689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 3, 7].length) (baseStart_8351689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351689 prefixEnd_8351689 := by exact prefixLift 8351689
  have htrace : WordTrace (prefixWord ++ tailWord_8351689) baseStart_8351689 baseEnd_8351689 := by
    simpa [prefixWord, tailWord_8351689, baseEnd_8351689] using wordTrace_append hprefix tailTrace_8351689
  have hstable : (prefixWord ++ tailWord_8351689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351689).length < 2 ^ (prefixWord ++ tailWord_8351689).sum := by decide
  have hdescent : baseEnd_8351689 < baseStart_8351689 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351703 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 4, 3, 2]
def baseStart_8351703 : Nat := 118140960795 + 8351703 * 2 ^ 59
def prefixEnd_8351703 : Nat := 4983230072969 + 3 ^ 40 * 8351703 * 2
def baseEnd_8351703 : Nat := 4288437922597042657303723

theorem tailTrace_8351703 : CollatzResearch.WordTrace tailWord_8351703 prefixEnd_8351703 4288437922597042657303723 := by
  unfold tailWord_8351703
  simp only [CollatzResearch.WordTrace]
  refine ⟨304611633262213863159403763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203074422174809242106269175 304611633262213863159403763)
  ·
    refine ⟨456917449893320794739105645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304611633262213863159403763 456917449893320794739105645)
    ·
      refine ⟨171344043709995298027164617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456917449893320794739105645 171344043709995298027164617)
      ·
        refine ⟨128508032782496473520373463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171344043709995298027164617 128508032782496473520373463)
        ·
          refine ⟨192762049173744710280560195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128508032782496473520373463 192762049173744710280560195)
          ·
            refine ⟨289143073760617065420840293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192762049173744710280560195 289143073760617065420840293)
            ·
              refine ⟨54214326330115699766407555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 289143073760617065420840293 54214326330115699766407555)
              ·
                refine ⟨81321489495173549649611333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54214326330115699766407555 81321489495173549649611333)
                ·
                  refine ⟨15247779280345040559302125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81321489495173549649611333 15247779280345040559302125)
                  ·
                    refine ⟨5717917230129390209738297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15247779280345040559302125 5717917230129390209738297)
                    ·
                      refine ⟨4288437922597042657303723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5717917230129390209738297 4288437922597042657303723)
                      ·
                        rfl

theorem cell23_8351703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 3, 2].length) (baseStart_8351703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351703 prefixEnd_8351703 := by exact prefixLift 8351703
  have htrace : WordTrace (prefixWord ++ tailWord_8351703) baseStart_8351703 baseEnd_8351703 := by
    simpa [prefixWord, tailWord_8351703, baseEnd_8351703] using wordTrace_append hprefix tailTrace_8351703
  have hstable : (prefixWord ++ tailWord_8351703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351703).length < 2 ^ (prefixWord ++ tailWord_8351703).sum := by decide
  have hdescent : baseEnd_8351703 < baseStart_8351703 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351773 : List Nat := [1, 4, 2, 2, 2, 2, 2, 8]
def baseStart_8351773 : Nat := 118140960795 + 8351773 * 2 ^ 59
def prefixEnd_8351773 : Nat := 4983230072969 + 3 ^ 40 * 8351773 * 2
def baseEnd_8351773 : Nat := 158832365416402125312163

theorem tailTrace_8351773 : CollatzResearch.WordTrace tailWord_8351773 prefixEnd_8351773 158832365416402125312163 := by
  unfold tailWord_8351773
  simp only [CollatzResearch.WordTrace]
  refine ⟨304614186371960265114451973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203076124247973510076301315 304614186371960265114451973)
  ·
    refine ⟨57115159944742549708959745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304614186371960265114451973 57115159944742549708959745)
    ·
      refine ⟨42836369958556912281719809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57115159944742549708959745 42836369958556912281719809)
      ·
        refine ⟨32127277468917684211289857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42836369958556912281719809 32127277468917684211289857)
        ·
          refine ⟨24095458101688263158467393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32127277468917684211289857 24095458101688263158467393)
          ·
            refine ⟨18071593576266197368850545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24095458101688263158467393 18071593576266197368850545)
            ·
              refine ⟨13553695182199648026637909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18071593576266197368850545 13553695182199648026637909)
              ·
                refine ⟨158832365416402125312163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13553695182199648026637909 158832365416402125312163)
                ·
                  rfl

theorem cell23_8351773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 8].length) (baseStart_8351773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351773 prefixEnd_8351773 := by exact prefixLift 8351773
  have htrace : WordTrace (prefixWord ++ tailWord_8351773) baseStart_8351773 baseEnd_8351773 := by
    simpa [prefixWord, tailWord_8351773, baseEnd_8351773] using wordTrace_append hprefix tailTrace_8351773
  have hstable : (prefixWord ++ tailWord_8351773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351773).length < 2 ^ (prefixWord ++ tailWord_8351773).sum := by decide
  have hdescent : baseEnd_8351773 < baseStart_8351773 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351784 : List Nat := [2, 1, 5, 3, 1, 2, 1, 2, 1, 1, 4]
def baseStart_8351784 : Nat := 118140960795 + 8351784 * 2 ^ 59
def prefixEnd_8351784 : Nat := 4983230072969 + 3 ^ 40 * 8351784 * 2
def baseEnd_8351784 : Nat := 4288479514530056840390851

theorem tailTrace_8351784 : CollatzResearch.WordTrace tailWord_8351784 prefixEnd_8351784 4288479514530056840390851 := by
  unfold tailWord_8351784
  simp only [CollatzResearch.WordTrace]
  refine ⟨152307293787460206996551203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203076391716613609328734937 152307293787460206996551203)
  ·
    refine ⟨228460940681190310494826805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152307293787460206996551203 228460940681190310494826805)
    ·
      refine ⟨21418213188861591608890013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228460940681190310494826805 21418213188861591608890013)
      ·
        refine ⟨8031829945823096853333755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21418213188861591608890013 8031829945823096853333755)
        ·
          refine ⟨12047744918734645280000633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8031829945823096853333755 12047744918734645280000633)
          ·
            refine ⟨9035808689050983960000475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12047744918734645280000633 9035808689050983960000475)
            ·
              refine ⟨13553713033576475940000713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9035808689050983960000475 13553713033576475940000713)
              ·
                refine ⟨10165284775182356955000535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13553713033576475940000713 10165284775182356955000535)
                ·
                  refine ⟨15247927162773535432500803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10165284775182356955000535 15247927162773535432500803)
                  ·
                    refine ⟨22871890744160303148751205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15247927162773535432500803 22871890744160303148751205)
                    ·
                      refine ⟨4288479514530056840390851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22871890744160303148751205 4288479514530056840390851)
                      ·
                        rfl

theorem cell23_8351784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_8351784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351784 prefixEnd_8351784 := by exact prefixLift 8351784
  have htrace : WordTrace (prefixWord ++ tailWord_8351784) baseStart_8351784 baseEnd_8351784 := by
    simpa [prefixWord, tailWord_8351784, baseEnd_8351784] using wordTrace_append hprefix tailTrace_8351784
  have hstable : (prefixWord ++ tailWord_8351784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351784).length < 2 ^ (prefixWord ++ tailWord_8351784).sum := by decide
  have hdescent : baseEnd_8351784 < baseStart_8351784 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351800 : List Nat := [2, 1, 2, 1, 6, 1, 1, 2, 1, 3, 3]
def baseStart_8351800 : Nat := 118140960795 + 8351800 * 2 ^ 59
def prefixEnd_8351800 : Nat := 4983230072969 + 3 ^ 40 * 8351800 * 2
def baseEnd_8351800 : Nat := 4288487730220528777790777

theorem tailTrace_8351800 : CollatzResearch.WordTrace tailWord_8351800 prefixEnd_8351800 4288487730220528777790777 := by
  unfold tailWord_8351800
  simp only [CollatzResearch.WordTrace]
  refine ⟨152307585571431224362842427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203076780761908299150456569 152307585571431224362842427)
  ·
    refine ⟨228461378357146836544263641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152307585571431224362842427 228461378357146836544263641)
    ·
      refine ⟨171346033767860127408197731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228461378357146836544263641 171346033767860127408197731)
      ·
        refine ⟨257019050651790191112296597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171346033767860127408197731 257019050651790191112296597)
        ·
          refine ⟨12047767999302665208388903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 257019050651790191112296597 12047767999302665208388903)
          ·
            refine ⟨18071651998953997812583355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12047767999302665208388903 18071651998953997812583355)
            ·
              refine ⟨27107477998430996718875033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18071651998953997812583355 27107477998430996718875033)
              ·
                refine ⟨20330608498823247539156275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27107477998430996718875033 20330608498823247539156275)
                ·
                  refine ⟨30495912748234871308734413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20330608498823247539156275 30495912748234871308734413)
                  ·
                    refine ⟨11435967280588076740775405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30495912748234871308734413 11435967280588076740775405)
                    ·
                      refine ⟨4288487730220528777790777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11435967280588076740775405 4288487730220528777790777)
                      ·
                        rfl

theorem cell23_8351800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 1, 3, 3].length) (baseStart_8351800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351800 prefixEnd_8351800 := by exact prefixLift 8351800
  have htrace : WordTrace (prefixWord ++ tailWord_8351800) baseStart_8351800 baseEnd_8351800 := by
    simpa [prefixWord, tailWord_8351800, baseEnd_8351800] using wordTrace_append hprefix tailTrace_8351800
  have hstable : (prefixWord ++ tailWord_8351800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351800).length < 2 ^ (prefixWord ++ tailWord_8351800).sum := by decide
  have hdescent : baseEnd_8351800 < baseStart_8351800 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351840 : List Nat := [2, 1, 1, 3, 2, 3, 1, 3, 1, 4, 2]
def baseStart_8351840 : Nat := 118140960795 + 8351840 * 2 ^ 59
def prefixEnd_8351840 : Nat := 4983230072969 + 3 ^ 40 * 8351840 * 2
def baseEnd_8351840 : Nat := 4288508269446708621290593

theorem tailTrace_8351840 : CollatzResearch.WordTrace tailWord_8351840 prefixEnd_8351840 4288508269446708621290593 := by
  unfold tailWord_8351840
  simp only [CollatzResearch.WordTrace]
  refine ⟨152308315031358767778570487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203077753375145023704760649 152308315031358767778570487)
  ·
    refine ⟨228462472547038151667855731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152308315031358767778570487 228462472547038151667855731)
    ·
      refine ⟨342693708820557227501783597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228462472547038151667855731 342693708820557227501783597)
      ·
        refine ⟨128510140807708960313168849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342693708820557227501783597 128510140807708960313168849)
        ·
          refine ⟨96382605605781720234876637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128510140807708960313168849 96382605605781720234876637)
          ·
            refine ⟨36143477102168145088078739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96382605605781720234876637 36143477102168145088078739)
            ·
              refine ⟨54215215653252217632118109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36143477102168145088078739 54215215653252217632118109)
              ·
                refine ⟨20330705869969581612044291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54215215653252217632118109 20330705869969581612044291)
                ·
                  refine ⟨30496058804954372418066437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20330705869969581612044291 30496058804954372418066437)
                  ·
                    refine ⟨5718011025928944828387457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30496058804954372418066437 5718011025928944828387457)
                    ·
                      refine ⟨4288508269446708621290593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5718011025928944828387457 4288508269446708621290593)
                      ·
                        rfl

theorem cell23_8351840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 1, 4, 2].length) (baseStart_8351840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351840 prefixEnd_8351840 := by exact prefixLift 8351840
  have htrace : WordTrace (prefixWord ++ tailWord_8351840) baseStart_8351840 baseEnd_8351840 := by
    simpa [prefixWord, tailWord_8351840, baseEnd_8351840] using wordTrace_append hprefix tailTrace_8351840
  have hstable : (prefixWord ++ tailWord_8351840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351840).length < 2 ^ (prefixWord ++ tailWord_8351840).sum := by decide
  have hdescent : baseEnd_8351840 < baseStart_8351840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351853 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_8351853 : Nat := 118140960795 + 8351853 * 2 ^ 59
def prefixEnd_8351853 : Nat := 4983230072969 + 3 ^ 40 * 8351853 * 2
def baseEnd_8351853 : Nat := 4288514944695217070428033

theorem tailTrace_8351853 : CollatzResearch.WordTrace tailWord_8351853 prefixEnd_8351853 4288514944695217070428033 := by
  unfold tailWord_8351853
  simp only [CollatzResearch.WordTrace]
  refine ⟨304617104211670438777364213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203078069474446959184909475 304617104211670438777364213)
  ·
    refine ⟨28557853519844103635377895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 304617104211670438777364213 28557853519844103635377895)
    ·
      refine ⟨42836780279766155453066843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28557853519844103635377895 42836780279766155453066843)
      ·
        refine ⟨64255170419649233179600265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42836780279766155453066843 64255170419649233179600265)
        ·
          refine ⟨48191377814736924884700199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64255170419649233179600265 48191377814736924884700199)
          ·
            refine ⟨72287066722105387327050299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48191377814736924884700199 72287066722105387327050299)
            ·
              refine ⟨108430600083158080990575449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72287066722105387327050299 108430600083158080990575449)
              ·
                refine ⟨81322950062368560742931587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108430600083158080990575449 81322950062368560742931587)
                ·
                  refine ⟨121984425093552841114397381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81322950062368560742931587 121984425093552841114397381)
                  ·
                    refine ⟨22872079705041157708949509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121984425093552841114397381 22872079705041157708949509)
                    ·
                      refine ⟨4288514944695217070428033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22872079705041157708949509 4288514944695217070428033)
                      ·
                        rfl

theorem cell23_8351853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_8351853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351853 prefixEnd_8351853 := by exact prefixLift 8351853
  have htrace : WordTrace (prefixWord ++ tailWord_8351853) baseStart_8351853 baseEnd_8351853 := by
    simpa [prefixWord, tailWord_8351853, baseEnd_8351853] using wordTrace_append hprefix tailTrace_8351853
  have hstable : (prefixWord ++ tailWord_8351853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351853).length < 2 ^ (prefixWord ++ tailWord_8351853).sum := by decide
  have hdescent : baseEnd_8351853 < baseStart_8351853 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351880 : List Nat := [2, 1, 3, 4, 1, 2, 2, 1, 7]
def baseStart_8351880 : Nat := 118140960795 + 8351880 * 2 ^ 59
def prefixEnd_8351880 : Nat := 4983230072969 + 3 ^ 40 * 8351880 * 2
def baseEnd_8351880 : Nat := 476503200963654273865601

theorem tailTrace_8351880 : CollatzResearch.WordTrace tailWord_8351880 prefixEnd_8351880 476503200963654273865601 := by
  unfold tailWord_8351880
  simp only [CollatzResearch.WordTrace]
  refine ⟨152309044491286311194298547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203078725988381748259064729 152309044491286311194298547)
  ·
    refine ⟨228463566736929466791447821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152309044491286311194298547 228463566736929466791447821)
    ·
      refine ⟨85673837526348550046792933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228463566736929466791447821 85673837526348550046792933)
      ·
        refine ⟨16063844536190353133773675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85673837526348550046792933 16063844536190353133773675)
        ·
          refine ⟨24095766804285529700660513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16063844536190353133773675 24095766804285529700660513)
          ·
            refine ⟨18071825103214147275495385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24095766804285529700660513 18071825103214147275495385)
            ·
              refine ⟨13553868827410610456621539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18071825103214147275495385 13553868827410610456621539)
              ·
                refine ⟨20330803241115915684932309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13553868827410610456621539 20330803241115915684932309)
                ·
                  refine ⟨476503200963654273865601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20330803241115915684932309 476503200963654273865601)
                  ·
                    rfl

theorem cell23_8351880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 7].length) (baseStart_8351880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351880 prefixEnd_8351880 := by exact prefixLift 8351880
  have htrace : WordTrace (prefixWord ++ tailWord_8351880) baseStart_8351880 baseEnd_8351880 := by
    simpa [prefixWord, tailWord_8351880, baseEnd_8351880] using wordTrace_append hprefix tailTrace_8351880
  have hstable : (prefixWord ++ tailWord_8351880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351880).length < 2 ^ (prefixWord ++ tailWord_8351880).sum := by decide
  have hdescent : baseEnd_8351880 < baseStart_8351880 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351890 : List Nat := [3, 2, 3, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_8351890 : Nat := 118140960795 + 8351890 * 2 ^ 59
def prefixEnd_8351890 : Nat := 4983230072969 + 3 ^ 40 * 8351890 * 2
def baseEnd_8351890 : Nat := 4288533943479433425665363

theorem tailTrace_8351890 : CollatzResearch.WordTrace tailWord_8351890 prefixEnd_8351890 4288533943479433425665363 := by
  unfold tailWord_8351890
  simp only [CollatzResearch.WordTrace]
  refine ⟨76154613428134098524115281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203078969141690929397640749 76154613428134098524115281)
  ·
    refine ⟨57115960071100573893086461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76154613428134098524115281 57115960071100573893086461)
    ·
      refine ⟨21418485026662715209907423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57115960071100573893086461 21418485026662715209907423)
      ·
        refine ⟨32127727539994072814861135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21418485026662715209907423 32127727539994072814861135)
        ·
          refine ⟨48191591309991109222291703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32127727539994072814861135 48191591309991109222291703)
          ·
            refine ⟨72287386964986663833437555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48191591309991109222291703 72287386964986663833437555)
            ·
              refine ⟨108431080447479995750156333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72287386964986663833437555 108431080447479995750156333)
              ·
                refine ⟨40661655167804998406308625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108431080447479995750156333 40661655167804998406308625)
                ·
                  refine ⟨30496241375853748804731469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40661655167804998406308625 30496241375853748804731469)
                  ·
                    refine ⟨11436090515945155801774301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30496241375853748804731469 11436090515945155801774301)
                    ·
                      refine ⟨4288533943479433425665363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11436090515945155801774301 4288533943479433425665363)
                      ·
                        rfl

theorem cell23_8351890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_8351890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351890 prefixEnd_8351890 := by exact prefixLift 8351890
  have htrace : WordTrace (prefixWord ++ tailWord_8351890) baseStart_8351890 baseEnd_8351890 := by
    simpa [prefixWord, tailWord_8351890, baseEnd_8351890] using wordTrace_append hprefix tailTrace_8351890
  have hstable : (prefixWord ++ tailWord_8351890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351890).length < 2 ^ (prefixWord ++ tailWord_8351890).sum := by decide
  have hdescent : baseEnd_8351890 < baseStart_8351890 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351930 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2]
def baseStart_8351930 : Nat := 118140960795 + 8351930 * 2 ^ 59
def prefixEnd_8351930 : Nat := 4983230072969 + 3 ^ 40 * 8351930 * 2
def baseEnd_8351930 : Nat := 4288554482705613269165179

theorem tailTrace_8351930 : CollatzResearch.WordTrace tailWord_8351930 prefixEnd_8351930 4288554482705613269165179 := by
  unfold tailWord_8351930
  simp only [CollatzResearch.WordTrace]
  refine ⟨76154978158097870231979311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203079941754927653951944829 76154978158097870231979311)
  ·
    refine ⟨114232467237146805347968967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76154978158097870231979311 114232467237146805347968967)
    ·
      refine ⟨171348700855720208021953451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114232467237146805347968967 171348700855720208021953451)
      ·
        refine ⟨257023051283580312032930177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171348700855720208021953451 257023051283580312032930177)
        ·
          refine ⟨192767288462685234024697633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257023051283580312032930177 192767288462685234024697633)
          ·
            refine ⟨144575466347013925518523225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192767288462685234024697633 144575466347013925518523225)
            ·
              refine ⟨108431599760260444138892419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144575466347013925518523225 108431599760260444138892419)
              ·
                refine ⟨162647399640390666208338629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108431599760260444138892419 162647399640390666208338629)
                ·
                  refine ⟨30496387432573249914063493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162647399640390666208338629 30496387432573249914063493)
                  ·
                    refine ⟨5718072643607484358886905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30496387432573249914063493 5718072643607484358886905)
                    ·
                      refine ⟨4288554482705613269165179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5718072643607484358886905 4288554482705613269165179)
                      ·
                        rfl

theorem cell23_8351930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2].length) (baseStart_8351930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351930 prefixEnd_8351930 := by exact prefixLift 8351930
  have htrace : WordTrace (prefixWord ++ tailWord_8351930) baseStart_8351930 baseEnd_8351930 := by
    simpa [prefixWord, tailWord_8351930, baseEnd_8351930] using wordTrace_append hprefix tailTrace_8351930
  have hstable : (prefixWord ++ tailWord_8351930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351930).length < 2 ^ (prefixWord ++ tailWord_8351930).sum := by decide
  have hdescent : baseEnd_8351930 < baseStart_8351930 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351937 : List Nat := [1, 2, 6, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_8351937 : Nat := 118140960795 + 8351937 * 2 ^ 59
def prefixEnd_8351937 : Nat := 4983230072969 + 3 ^ 40 * 8351937 * 2
def baseEnd_8351937 : Nat := 4288558077070194741777647

theorem tailTrace_8351937 : CollatzResearch.WordTrace tailWord_8351937 prefixEnd_8351937 4288558077070194741777647 := by
  unfold tailWord_8351937
  simp only [CollatzResearch.WordTrace]
  refine ⟨304620167943366121123422065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203080111962244080748948043 304620167943366121123422065)
  ·
    refine ⟨228465125957524590842566549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304620167943366121123422065 228465125957524590842566549)
    ·
      refine ⟨10709302779258965195745307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 228465125957524590842566549 10709302779258965195745307)
      ·
        refine ⟨16063954168888447793617961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10709302779258965195745307 16063954168888447793617961)
        ·
          refine ⟨12047965626666335845213471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16063954168888447793617961 12047965626666335845213471)
          ·
            refine ⟨18071948439999503767820207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12047965626666335845213471 18071948439999503767820207)
            ·
              refine ⟨27107922659999255651730311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18071948439999503767820207 27107922659999255651730311)
              ·
                refine ⟨40661883989998883477595467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27107922659999255651730311 40661883989998883477595467)
                ·
                  refine ⟨60992825984998325216393201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40661883989998883477595467 60992825984998325216393201)
                  ·
                    refine ⟨45744619488748743912294901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60992825984998325216393201 45744619488748743912294901)
                    ·
                      refine ⟨4288558077070194741777647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45744619488748743912294901 4288558077070194741777647)
                      ·
                        rfl

theorem cell23_8351937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_8351937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351937 prefixEnd_8351937 := by exact prefixLift 8351937
  have htrace : WordTrace (prefixWord ++ tailWord_8351937) baseStart_8351937 baseEnd_8351937 := by
    simpa [prefixWord, tailWord_8351937, baseEnd_8351937] using wordTrace_append hprefix tailTrace_8351937
  have hstable : (prefixWord ++ tailWord_8351937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351937).length < 2 ^ (prefixWord ++ tailWord_8351937).sum := by decide
  have hdescent : baseEnd_8351937 < baseStart_8351937 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8351963 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 1, 7, 3]
def baseStart_8351963 : Nat := 118140960795 + 8351963 * 2 ^ 59
def prefixEnd_8351963 : Nat := 4983230072969 + 3 ^ 40 * 8351963 * 2
def baseEnd_8351963 : Nat := 4288571427567211640052527

theorem tailTrace_8351963 : CollatzResearch.WordTrace tailWord_8351963 prefixEnd_8351963 4288571427567211640052527 := by
  unfold tailWord_8351963
  simp only [CollatzResearch.WordTrace]
  refine ⟨304621116241271927563868543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203080744160847951709245695 304621116241271927563868543)
  ·
    refine ⟨456931674361907891345802815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304621116241271927563868543 456931674361907891345802815)
    ·
      refine ⟨685397511542861837018704223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456931674361907891345802815 685397511542861837018704223)
      ·
        refine ⟨1028096267314292755528056335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685397511542861837018704223 1028096267314292755528056335)
        ·
          refine ⟨1542144400971439133292084503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1028096267314292755528056335 1542144400971439133292084503)
          ·
            refine ⟨2313216601457158699938126755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1542144400971439133292084503 2313216601457158699938126755)
            ·
              refine ⟨3469824902185738049907190133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2313216601457158699938126755 3469824902185738049907190133)
              ·
                refine ⟨325296084579912942178799075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3469824902185738049907190133 325296084579912942178799075)
                ·
                  refine ⟨487944126869869413268198613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 325296084579912942178799075 487944126869869413268198613)
                  ·
                    refine ⟨11436190473512564373473405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 487944126869869413268198613 11436190473512564373473405)
                    ·
                      refine ⟨4288571427567211640052527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11436190473512564373473405 4288571427567211640052527)
                      ·
                        rfl

theorem cell23_8351963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7, 3].length) (baseStart_8351963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8351963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8351963 prefixEnd_8351963 := by exact prefixLift 8351963
  have htrace : WordTrace (prefixWord ++ tailWord_8351963) baseStart_8351963 baseEnd_8351963 := by
    simpa [prefixWord, tailWord_8351963, baseEnd_8351963] using wordTrace_append hprefix tailTrace_8351963
  have hstable : (prefixWord ++ tailWord_8351963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8351963).length < 2 ^ (prefixWord ++ tailWord_8351963).sum := by decide
  have hdescent : baseEnd_8351963 < baseStart_8351963 := by decide
  rcases family_descends (prefixWord ++ tailWord_8351963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352031 : List Nat := [1, 1, 2, 4, 3, 2, 2, 3, 1, 1, 3]
def baseStart_8352031 : Nat := 118140960795 + 8352031 * 2 ^ 59
def prefixEnd_8352031 : Nat := 4983230072969 + 3 ^ 40 * 8352031 * 2
def baseEnd_8352031 : Nat := 4288606344251717374002215

theorem tailTrace_8352031 : CollatzResearch.WordTrace tailWord_8352031 prefixEnd_8352031 4288606344251717374002215 := by
  unfold tailWord_8352031
  simp only [CollatzResearch.WordTrace]
  refine ⟨304623596405025575177343947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203082397603350383451562631 304623596405025575177343947)
  ·
    refine ⟨456935394607538362766015921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304623596405025575177343947 456935394607538362766015921)
    ·
      refine ⟨342701545955653772074511941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456935394607538362766015921 342701545955653772074511941)
      ·
        refine ⟨64256539866685082263970989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 342701545955653772074511941 64256539866685082263970989)
        ·
          refine ⟨24096202450006905848989121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64256539866685082263970989 24096202450006905848989121)
          ·
            refine ⟨18072151837505179386741841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24096202450006905848989121 18072151837505179386741841)
            ·
              refine ⟨13554113878128884540056381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18072151837505179386741841 13554113878128884540056381)
              ·
                refine ⟨5082792704298331702521143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13554113878128884540056381 5082792704298331702521143)
                ·
                  refine ⟨7624189056447497553781715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5082792704298331702521143 7624189056447497553781715)
                  ·
                    refine ⟨11436283584671246330672573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7624189056447497553781715 11436283584671246330672573)
                    ·
                      refine ⟨4288606344251717374002215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11436283584671246330672573 4288606344251717374002215)
                      ·
                        rfl

theorem cell23_8352031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_8352031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352031 prefixEnd_8352031 := by exact prefixLift 8352031
  have htrace : WordTrace (prefixWord ++ tailWord_8352031) baseStart_8352031 baseEnd_8352031 := by
    simpa [prefixWord, tailWord_8352031, baseEnd_8352031] using wordTrace_append hprefix tailTrace_8352031
  have hstable : (prefixWord ++ tailWord_8352031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352031).length < 2 ^ (prefixWord ++ tailWord_8352031).sum := by decide
  have hdescent : baseEnd_8352031 < baseStart_8352031 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352034 : List Nat := [3, 3, 1, 1, 3, 1, 4, 1, 1, 5]
def baseStart_8352034 : Nat := 118140960795 + 8352034 * 2 ^ 59
def prefixEnd_8352034 : Nat := 4983230072969 + 3 ^ 40 * 8352034 * 2
def baseEnd_8352034 : Nat := 1429535961564560287421567

theorem tailTrace_8352034 : CollatzResearch.WordTrace tailWord_8352034 prefixEnd_8352034 1429535961564560287421567 := by
  unfold tailWord_8352034
  simp only [CollatzResearch.WordTrace]
  refine ⟨76155926456003676672425789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203082470549343137793135437 76155926456003676672425789)
  ·
    refine ⟨28558472421001378752159671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76155926456003676672425789 28558472421001378752159671)
    ·
      refine ⟨42837708631502068128239507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28558472421001378752159671 42837708631502068128239507)
      ·
        refine ⟨64256562947253102192359261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42837708631502068128239507 64256562947253102192359261)
        ·
          refine ⟨24096211105219913322134723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64256562947253102192359261 24096211105219913322134723)
          ·
            refine ⟨36144316657829869983202085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24096211105219913322134723 36144316657829869983202085)
            ·
              refine ⟨6777059373343100621850391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36144316657829869983202085 6777059373343100621850391)
              ·
                refine ⟨10165589060014650932775587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6777059373343100621850391 10165589060014650932775587)
                ·
                  refine ⟨15248383590021976399163381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10165589060014650932775587 15248383590021976399163381)
                  ·
                    refine ⟨1429535961564560287421567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15248383590021976399163381 1429535961564560287421567)
                    ·
                      rfl

theorem cell23_8352034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_8352034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352034 prefixEnd_8352034 := by exact prefixLift 8352034
  have htrace : WordTrace (prefixWord ++ tailWord_8352034) baseStart_8352034 baseEnd_8352034 := by
    simpa [prefixWord, tailWord_8352034, baseEnd_8352034] using wordTrace_append hprefix tailTrace_8352034
  have hstable : (prefixWord ++ tailWord_8352034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352034).length < 2 ^ (prefixWord ++ tailWord_8352034).sum := by decide
  have hdescent : baseEnd_8352034 < baseStart_8352034 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352047 : List Nat := [1, 1, 2, 1, 2, 1, 7, 2, 2, 4]
def baseStart_8352047 : Nat := 118140960795 + 8352047 * 2 ^ 59
def prefixEnd_8352047 : Nat := 4983230072969 + 3 ^ 40 * 8352047 * 2
def baseEnd_8352047 : Nat := 1429538186647396437134047

theorem tailTrace_8352047 : CollatzResearch.WordTrace tailWord_8352047 prefixEnd_8352047 1429538186647396437134047 := by
  unfold tailWord_8352047
  simp only [CollatzResearch.WordTrace]
  refine ⟨304624179972967609909926395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203082786648645073273284263 304624179972967609909926395)
  ·
    refine ⟨456936269959451414864889593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304624179972967609909926395 456936269959451414864889593)
    ·
      refine ⟨342702202469588561148667195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456936269959451414864889593 342702202469588561148667195)
      ·
        refine ⟨514053303704382841723000793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342702202469588561148667195 514053303704382841723000793)
        ·
          refine ⟨385539977778287131292250595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 514053303704382841723000793 385539977778287131292250595)
          ·
            refine ⟨578309966667430696938375893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385539977778287131292250595 578309966667430696938375893)
            ·
              refine ⟨13554139843767906959493185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 578309966667430696938375893 13554139843767906959493185)
              ·
                refine ⟨10165604882825930219619889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13554139843767906959493185 10165604882825930219619889)
                ·
                  refine ⟨7624203662119447664714917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10165604882825930219619889 7624203662119447664714917)
                  ·
                    refine ⟨1429538186647396437134047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7624203662119447664714917 1429538186647396437134047)
                    ·
                      rfl

theorem cell23_8352047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2, 4].length) (baseStart_8352047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352047 prefixEnd_8352047 := by exact prefixLift 8352047
  have htrace : WordTrace (prefixWord ++ tailWord_8352047) baseStart_8352047 baseEnd_8352047 := by
    simpa [prefixWord, tailWord_8352047, baseEnd_8352047] using wordTrace_append hprefix tailTrace_8352047
  have hstable : (prefixWord ++ tailWord_8352047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352047).length < 2 ^ (prefixWord ++ tailWord_8352047).sum := by decide
  have hdescent : baseEnd_8352047 < baseStart_8352047 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352057 : List Nat := [1, 2, 1, 6, 1, 2, 1, 2, 1, 1, 5]
def baseStart_8352057 : Nat := 118140960795 + 8352057 * 2 ^ 59
def prefixEnd_8352057 : Nat := 4983230072969 + 3 ^ 40 * 8352057 * 2
def baseEnd_8352057 : Nat := 4288619694748734272277095

theorem tailTrace_8352057 : CollatzResearch.WordTrace tailWord_8352057 prefixEnd_8352057 4288619694748734272277095 := by
  unfold tailWord_8352057
  simp only [CollatzResearch.WordTrace]
  refine ⟨304624544702931381617790425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203083029801954254411860283 304624544702931381617790425)
  ·
    refine ⟨228468408527198536213342819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304624544702931381617790425 228468408527198536213342819)
    ·
      refine ⟨342702612790797804320014229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228468408527198536213342819 342702612790797804320014229)
      ·
        refine ⟨16064184974568647077500667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 342702612790797804320014229 16064184974568647077500667)
        ·
          refine ⟨24096277461852970616251001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16064184974568647077500667 24096277461852970616251001)
          ·
            refine ⟨18072208096389727962188251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24096277461852970616251001 18072208096389727962188251)
            ·
              refine ⟨27108312144584591943282377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18072208096389727962188251 27108312144584591943282377)
              ·
                refine ⟨20331234108438443957461783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27108312144584591943282377 20331234108438443957461783)
                ·
                  refine ⟨30496851162657665936192675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20331234108438443957461783 30496851162657665936192675)
                  ·
                    refine ⟨45745276743986498904289013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30496851162657665936192675 45745276743986498904289013)
                    ·
                      refine ⟨4288619694748734272277095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45745276743986498904289013 4288619694748734272277095)
                      ·
                        rfl

theorem cell23_8352057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_8352057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352057 prefixEnd_8352057 := by exact prefixLift 8352057
  have htrace : WordTrace (prefixWord ++ tailWord_8352057) baseStart_8352057 baseEnd_8352057 := by
    simpa [prefixWord, tailWord_8352057, baseEnd_8352057] using wordTrace_append hprefix tailTrace_8352057
  have hstable : (prefixWord ++ tailWord_8352057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352057).length < 2 ^ (prefixWord ++ tailWord_8352057).sum := by decide
  have hdescent : baseEnd_8352057 < baseStart_8352057 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352087 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 6, 1, 3]
def baseStart_8352087 : Nat := 118140960795 + 8352087 * 2 ^ 59
def prefixEnd_8352087 : Nat := 4983230072969 + 3 ^ 40 * 8352087 * 2
def baseEnd_8352087 : Nat := 4288635099168369154901957

theorem tailTrace_8352087 : CollatzResearch.WordTrace tailWord_8352087 prefixEnd_8352087 4288635099168369154901957 := by
  unfold tailWord_8352087
  simp only [CollatzResearch.WordTrace]
  refine ⟨304625638892822696741382515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203083759261881797827588343 304625638892822696741382515)
  ·
    refine ⟨456938458339234045112073773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304625638892822696741382515 456938458339234045112073773)
    ·
      refine ⟨171351921877212766917027665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456938458339234045112073773 171351921877212766917027665)
      ·
        refine ⟨128513941407909575187770749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171351921877212766917027665 128513941407909575187770749)
        ·
          refine ⟨48192728027966090695414031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128513941407909575187770749 48192728027966090695414031)
          ·
            refine ⟨72289092041949136043121047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48192728027966090695414031 72289092041949136043121047)
            ·
              refine ⟨108433638062923704064681571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72289092041949136043121047 108433638062923704064681571)
              ·
                refine ⟨162650457094385556097022357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108433638062923704064681571 162650457094385556097022357)
                ·
                  refine ⟨7624240176299322942047923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 162650457094385556097022357 7624240176299322942047923)
                  ·
                    refine ⟨11436360264448984413071885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7624240176299322942047923 11436360264448984413071885)
                    ·
                      refine ⟨4288635099168369154901957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11436360264448984413071885 4288635099168369154901957)
                      ·
                        rfl

theorem cell23_8352087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_8352087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352087 prefixEnd_8352087 := by exact prefixLift 8352087
  have htrace : WordTrace (prefixWord ++ tailWord_8352087) baseStart_8352087 baseEnd_8352087 := by
    simpa [prefixWord, tailWord_8352087, baseEnd_8352087] using wordTrace_append hprefix tailTrace_8352087
  have hstable : (prefixWord ++ tailWord_8352087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352087).length < 2 ^ (prefixWord ++ tailWord_8352087).sum := by decide
  have hdescent : baseEnd_8352087 < baseStart_8352087 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352097 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 7, 3, 2]
def baseStart_8352097 : Nat := 118140960795 + 8352097 * 2 ^ 59
def prefixEnd_8352097 : Nat := 4983230072969 + 3 ^ 40 * 8352097 * 2
def baseEnd_8352097 : Nat := 4288640233974914115776911

theorem tailTrace_8352097 : CollatzResearch.WordTrace tailWord_8352097 prefixEnd_8352097 4288640233974914115776911 := by
  unfold tailWord_8352097
  simp only [CollatzResearch.WordTrace]
  refine ⟨304626003622786468449246545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203084002415190978966164363 304626003622786468449246545)
  ·
    refine ⟨228469502717089851336934909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304626003622786468449246545 228469502717089851336934909)
    ·
      refine ⟨85676063518908694251350591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228469502717089851336934909 85676063518908694251350591)
      ·
        refine ⟨128514095278363041377025887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85676063518908694251350591 128514095278363041377025887)
        ·
          refine ⟨192771142917544562065538831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128514095278363041377025887 192771142917544562065538831)
          ·
            refine ⟨289156714376316843098308247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192771142917544562065538831 289156714376316843098308247)
            ·
              refine ⟨433735071564475264647462371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289156714376316843098308247 433735071564475264647462371)
              ·
                refine ⟨650602607346712896971193557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433735071564475264647462371 650602607346712896971193557)
                ·
                  refine ⟨15248498609688583522762349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 650602607346712896971193557 15248498609688583522762349)
                  ·
                    refine ⟨5718186978633218821035881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15248498609688583522762349 5718186978633218821035881)
                    ·
                      refine ⟨4288640233974914115776911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5718186978633218821035881 4288640233974914115776911)
                      ·
                        rfl

theorem cell23_8352097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 3, 2].length) (baseStart_8352097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352097 prefixEnd_8352097 := by exact prefixLift 8352097
  have htrace : WordTrace (prefixWord ++ tailWord_8352097) baseStart_8352097 baseEnd_8352097 := by
    simpa [prefixWord, tailWord_8352097, baseEnd_8352097] using wordTrace_append hprefix tailTrace_8352097
  have hstable : (prefixWord ++ tailWord_8352097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352097).length < 2 ^ (prefixWord ++ tailWord_8352097).sum := by decide
  have hdescent : baseEnd_8352097 < baseStart_8352097 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
