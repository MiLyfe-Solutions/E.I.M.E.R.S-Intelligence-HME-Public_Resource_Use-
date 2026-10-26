import V185TrunkScan23Chunk1274

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7553556 : List Nat := [2, 4, 3, 1, 1, 1, 4, 2, 1, 1, 3]
def baseStart_7553556 : Nat := 118140960795 + 7553556 * 2 ^ 59
def prefixEnd_7553556 : Nat := 4983230072969 + 3 ^ 40 * 7553556 * 2
def baseEnd_7553556 : Nat := 3878604878652953911111835

theorem tailTrace_7553556 : CollatzResearch.WordTrace tailWord_7553556 prefixEnd_7553556 3878604878652953911111835 := by
  unfold tailWord_7553556
  simp only [CollatzResearch.WordTrace]
  refine ⟨137750410311382065752104261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183667213748509421002805681 137750410311382065752104261)
  ·
    refine ⟨25828201933384137328519549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137750410311382065752104261 25828201933384137328519549)
    ·
      refine ⟨9685575725019051498194831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25828201933384137328519549 9685575725019051498194831)
      ·
        refine ⟨14528363587528577247292247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9685575725019051498194831 14528363587528577247292247)
        ·
          refine ⟨21792545381292865870938371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14528363587528577247292247 21792545381292865870938371)
          ·
            refine ⟨32688818071939298806407557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21792545381292865870938371 32688818071939298806407557)
            ·
              refine ⟨6129153388488618526201417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32688818071939298806407557 6129153388488618526201417)
              ·
                refine ⟨4596865041366463894651063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6129153388488618526201417 4596865041366463894651063)
                ·
                  refine ⟨6895297562049695841976595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4596865041366463894651063 6895297562049695841976595)
                  ·
                    refine ⟨10342946343074543762964893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6895297562049695841976595 10342946343074543762964893)
                    ·
                      refine ⟨3878604878652953911111835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10342946343074543762964893 3878604878652953911111835)
                      ·
                        rfl

theorem cell23_7553556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_7553556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553556 prefixEnd_7553556 := by exact prefixLift 7553556
  have htrace : WordTrace (prefixWord ++ tailWord_7553556) baseStart_7553556 baseEnd_7553556 := by
    simpa [prefixWord, tailWord_7553556, baseEnd_7553556] using wordTrace_append hprefix tailTrace_7553556
  have hstable : (prefixWord ++ tailWord_7553556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553556).length < 2 ^ (prefixWord ++ tailWord_7553556).sum := by decide
  have hdescent : baseEnd_7553556 < baseStart_7553556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553591 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 5]
def baseStart_7553591 : Nat := 118140960795 + 7553591 * 2 ^ 59
def prefixEnd_7553591 : Nat := 4983230072969 + 3 ^ 40 * 7553591 * 2
def baseEnd_7553591 : Nat := 3878622850475861274174173

theorem tailTrace_7553591 : CollatzResearch.WordTrace tailWord_7553591 prefixEnd_7553591 3878622850475861274174173 := by
  unfold tailWord_7553591
  simp only [CollatzResearch.WordTrace]
  refine ⟨275502097177637332481732627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183668064785091554987821751 275502097177637332481732627)
  ·
    refine ⟨413253145766455998722598941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275502097177637332481732627 413253145766455998722598941)
    ·
      refine ⟨154969929662420999520974603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413253145766455998722598941 154969929662420999520974603)
      ·
        refine ⟨232454894493631499281461905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154969929662420999520974603 232454894493631499281461905)
        ·
          refine ⟨174341170870223624461096429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232454894493631499281461905 174341170870223624461096429)
          ·
            refine ⟨65377939076333859172911161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174341170870223624461096429 65377939076333859172911161)
            ·
              refine ⟨49033454307250394379683371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65377939076333859172911161 49033454307250394379683371)
              ·
                refine ⟨73550181460875591569525057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49033454307250394379683371 73550181460875591569525057)
                ·
                  refine ⟨55162636095656693677143793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73550181460875591569525057 55162636095656693677143793)
                  ·
                    refine ⟨41371977071742520257857845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55162636095656693677143793 41371977071742520257857845)
                    ·
                      refine ⟨3878622850475861274174173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41371977071742520257857845 3878622850475861274174173)
                      ·
                        rfl

theorem cell23_7553591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_7553591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553591 prefixEnd_7553591 := by exact prefixLift 7553591
  have htrace : WordTrace (prefixWord ++ tailWord_7553591) baseStart_7553591 baseEnd_7553591 := by
    simpa [prefixWord, tailWord_7553591, baseEnd_7553591] using wordTrace_append hprefix tailTrace_7553591
  have hstable : (prefixWord ++ tailWord_7553591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553591).length < 2 ^ (prefixWord ++ tailWord_7553591).sum := by decide
  have hdescent : baseEnd_7553591 < baseStart_7553591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553611 : List Nat := [1, 1, 1, 1, 3, 1, 5, 2, 2, 6]
def baseStart_7553611 : Nat := 118140960795 + 7553611 * 2 ^ 59
def prefixEnd_7553611 : Nat := 4983230072969 + 3 ^ 40 * 7553611 * 2
def baseEnd_7553611 : Nat := 1292877706696317065308027

theorem tailTrace_7553611 : CollatzResearch.WordTrace tailWord_7553611 prefixEnd_7553611 1292877706696317065308027 := by
  unfold tailWord_7553611
  simp only [CollatzResearch.WordTrace]
  refine ⟨275502826637564875897460687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183668551091709917264973791 275502826637564875897460687)
  ·
    refine ⟨413254239956347313846191031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275502826637564875897460687 413254239956347313846191031)
    ·
      refine ⟨619881359934520970769286547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413254239956347313846191031 619881359934520970769286547)
      ·
        refine ⟨929822039901781456153929821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619881359934520970769286547 929822039901781456153929821)
        ·
          refine ⟨348683264963168046057723683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 929822039901781456153929821 348683264963168046057723683)
          ·
            refine ⟨523024897444752069086585525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348683264963168046057723683 523024897444752069086585525)
            ·
              refine ⟨49033584135445506476867393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 523024897444752069086585525 49033584135445506476867393)
              ·
                refine ⟨36775188101584129857650545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49033584135445506476867393 36775188101584129857650545)
                ·
                  refine ⟨27581391076188097393237909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36775188101584129857650545 27581391076188097393237909)
                  ·
                    refine ⟨1292877706696317065308027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27581391076188097393237909 1292877706696317065308027)
                    ·
                      rfl

theorem cell23_7553611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 6].length) (baseStart_7553611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553611 prefixEnd_7553611 := by exact prefixLift 7553611
  have htrace : WordTrace (prefixWord ++ tailWord_7553611) baseStart_7553611 baseEnd_7553611 := by
    simpa [prefixWord, tailWord_7553611, baseEnd_7553611] using wordTrace_append hprefix tailTrace_7553611
  have hstable : (prefixWord ++ tailWord_7553611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553611).length < 2 ^ (prefixWord ++ tailWord_7553611).sum := by decide
  have hdescent : baseEnd_7553611 < baseStart_7553611 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553688 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 4, 5]
def baseStart_7553688 : Nat := 118140960795 + 7553688 * 2 ^ 59
def prefixEnd_7553688 : Nat := 4983230072969 + 3 ^ 40 * 7553688 * 2
def baseEnd_7553688 : Nat := 1292890886033115798220409

theorem tailTrace_7553688 : CollatzResearch.WordTrace tailWord_7553688 prefixEnd_7553688 1292890886033115798220409 := by
  unfold tailWord_7553688
  simp only [CollatzResearch.WordTrace]
  refine ⟨137752817529142959024006859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183670423372190612032009145 137752817529142959024006859)
  ·
    refine ⟨206629226293714438536010289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137752817529142959024006859 206629226293714438536010289)
    ·
      refine ⟨154971919720285828902007717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206629226293714438536010289 154971919720285828902007717)
      ·
        refine ⟨29057234947553592919126447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154971919720285828902007717 29057234947553592919126447)
        ·
          refine ⟨43585852421330389378689671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29057234947553592919126447 43585852421330389378689671)
          ·
            refine ⟨65378778631995584068034507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43585852421330389378689671 65378778631995584068034507)
            ·
              refine ⟨98068167947993376102051761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65378778631995584068034507 98068167947993376102051761)
              ·
                refine ⟨73551125960995032076538821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98068167947993376102051761 73551125960995032076538821)
                ·
                  refine ⟨13790836117686568514351029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73551125960995032076538821 13790836117686568514351029)
                  ·
                    refine ⟨1292890886033115798220409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13790836117686568514351029 1292890886033115798220409)
                    ·
                      rfl

theorem cell23_7553688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 4, 5].length) (baseStart_7553688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553688 prefixEnd_7553688 := by exact prefixLift 7553688
  have htrace : WordTrace (prefixWord ++ tailWord_7553688) baseStart_7553688 baseEnd_7553688 := by
    simpa [prefixWord, tailWord_7553688, baseEnd_7553688] using wordTrace_append hprefix tailTrace_7553688
  have hstable : (prefixWord ++ tailWord_7553688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553688).length < 2 ^ (prefixWord ++ tailWord_7553688).sum := by decide
  have hdescent : baseEnd_7553688 < baseStart_7553688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553725 : List Nat := [1, 4, 1, 2, 1, 3, 2, 2, 2, 1, 4]
def baseStart_7553725 : Nat := 118140960795 + 7553725 * 2 ^ 59
def prefixEnd_7553725 : Nat := 4983230072969 + 3 ^ 40 * 7553725 * 2
def baseEnd_7553725 : Nat := 3878691656883563749898557

theorem tailTrace_7553725 : CollatzResearch.WordTrace tailWord_7553725 prefixEnd_7553725 3878691656883563749898557 := by
  unfold tailWord_7553725
  simp only [CollatzResearch.WordTrace]
  refine ⟨275506984559151873367110629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183671323039434582244740419 275506984559151873367110629)
  ·
    refine ⟨51657559604840976256333243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275506984559151873367110629 51657559604840976256333243)
    ·
      refine ⟨77486339407261464384499865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51657559604840976256333243 77486339407261464384499865)
      ·
        refine ⟨58114754555446098288374899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77486339407261464384499865 58114754555446098288374899)
        ·
          refine ⟨87172131833169147432562349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58114754555446098288374899 87172131833169147432562349)
          ·
            refine ⟨32689549437438430287210881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87172131833169147432562349 32689549437438430287210881)
            ·
              refine ⟨24517162078078822715408161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32689549437438430287210881 24517162078078822715408161)
              ·
                refine ⟨18387871558559117036556121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24517162078078822715408161 18387871558559117036556121)
                ·
                  refine ⟨13790903668919337777417091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18387871558559117036556121 13790903668919337777417091)
                  ·
                    refine ⟨20686355503379006666125637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13790903668919337777417091 20686355503379006666125637)
                    ·
                      refine ⟨3878691656883563749898557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20686355503379006666125637 3878691656883563749898557)
                      ·
                        rfl

theorem cell23_7553725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_7553725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553725 prefixEnd_7553725 := by exact prefixLift 7553725
  have htrace : WordTrace (prefixWord ++ tailWord_7553725) baseStart_7553725 baseEnd_7553725 := by
    simpa [prefixWord, tailWord_7553725, baseEnd_7553725] using wordTrace_append hprefix tailTrace_7553725
  have hstable : (prefixWord ++ tailWord_7553725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553725).length < 2 ^ (prefixWord ++ tailWord_7553725).sum := by decide
  have hdescent : baseEnd_7553725 < baseStart_7553725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553742 : List Nat := [4, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2]
def baseStart_7553742 : Nat := 118140960795 + 7553742 * 2 ^ 59
def prefixEnd_7553742 : Nat := 4983230072969 + 3 ^ 40 * 7553742 * 2
def baseEnd_7553742 : Nat := 3878700386054690183385979

theorem tailTrace_7553742 : CollatzResearch.WordTrace tailWord_7553742 prefixEnd_7553742 3878700386054690183385979 := by
  unfold tailWord_7553742
  simp only [CollatzResearch.WordTrace]
  refine ⟨34438450575011285658809935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183671736400060190180319653 34438450575011285658809935)
  ·
    refine ⟨51657675862516928488214903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34438450575011285658809935 51657675862516928488214903)
    ·
      refine ⟨77486513793775392732322355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51657675862516928488214903 77486513793775392732322355)
      ·
        refine ⟨116229770690663089098483533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77486513793775392732322355 116229770690663089098483533)
        ·
          refine ⟨43586164008998658411931325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116229770690663089098483533 43586164008998658411931325)
          ·
            refine ⟨16344811503374496904474247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43586164008998658411931325 16344811503374496904474247)
            ·
              refine ⟨24517217255061745356711371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16344811503374496904474247 24517217255061745356711371)
              ·
                refine ⟨36775825882592618035067057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24517217255061745356711371 36775825882592618035067057)
                ·
                  refine ⟨27581869411944463526300293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36775825882592618035067057 27581869411944463526300293)
                  ·
                    refine ⟨5171600514739586911181305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27581869411944463526300293 5171600514739586911181305)
                    ·
                      refine ⟨3878700386054690183385979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5171600514739586911181305 3878700386054690183385979)
                      ·
                        rfl

theorem cell23_7553742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2].length) (baseStart_7553742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553742 prefixEnd_7553742 := by exact prefixLift 7553742
  have htrace : WordTrace (prefixWord ++ tailWord_7553742) baseStart_7553742 baseEnd_7553742 := by
    simpa [prefixWord, tailWord_7553742, baseEnd_7553742] using wordTrace_append hprefix tailTrace_7553742
  have hstable : (prefixWord ++ tailWord_7553742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553742).length < 2 ^ (prefixWord ++ tailWord_7553742).sum := by decide
  have hdescent : baseEnd_7553742 < baseStart_7553742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553825 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 6, 4]
def baseStart_7553825 : Nat := 118140960795 + 7553825 * 2 ^ 59
def prefixEnd_7553825 : Nat := 4983230072969 + 3 ^ 40 * 7553825 * 2
def baseEnd_7553825 : Nat := 1292914334983004452882699

theorem tailTrace_7553825 : CollatzResearch.WordTrace tailWord_7553825 prefixEnd_7553825 1292914334983004452882699 := by
  unfold tailWord_7553825
  simp only [CollatzResearch.WordTrace]
  refine ⟨275510631858789590445750929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183673754572526393630500619 275510631858789590445750929)
  ·
    refine ⟨206632973894092192834313197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275510631858789590445750929 206632973894092192834313197)
    ·
      refine ⟨77487365210284572312867449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206632973894092192834313197 77487365210284572312867449)
      ·
        refine ⟨58115523907713429234650587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77487365210284572312867449 58115523907713429234650587)
        ·
          refine ⟨87173285861570143851975881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58115523907713429234650587 87173285861570143851975881)
          ·
            refine ⟨65379964396177607888981911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87173285861570143851975881 65379964396177607888981911)
            ·
              refine ⟨98069946594266411833472867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65379964396177607888981911 98069946594266411833472867)
              ·
                refine ⟨147104919891399617750209301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98069946594266411833472867 147104919891399617750209301)
                ·
                  refine ⟨6895543119909357082041061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147104919891399617750209301 6895543119909357082041061)
                  ·
                    refine ⟨1292914334983004452882699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6895543119909357082041061 1292914334983004452882699)
                    ·
                      rfl

theorem cell23_7553825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_7553825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553825 prefixEnd_7553825 := by exact prefixLift 7553825
  have htrace : WordTrace (prefixWord ++ tailWord_7553825) baseStart_7553825 baseEnd_7553825 := by
    simpa [prefixWord, tailWord_7553825, baseEnd_7553825] using wordTrace_append hprefix tailTrace_7553825
  have hstable : (prefixWord ++ tailWord_7553825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553825).length < 2 ^ (prefixWord ++ tailWord_7553825).sum := by decide
  have hdescent : baseEnd_7553825 < baseStart_7553825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553826 : List Nat := [3, 3, 1, 1, 2, 2, 3, 3, 1, 1, 3]
def baseStart_7553826 : Nat := 118140960795 + 7553826 * 2 ^ 59
def prefixEnd_7553826 : Nat := 4983230072969 + 3 ^ 40 * 7553826 * 2
def baseEnd_7553826 : Nat := 3878743518429667854735593

theorem tailTrace_7553826 : CollatzResearch.WordTrace tailWord_7553826 prefixEnd_7553826 3878743518429667854735593 := by
  unfold tailWord_7553826
  simp only [CollatzResearch.WordTrace]
  refine ⟨68877667082946491904134333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183673778887857311744358221 68877667082946491904134333)
  ·
    refine ⟨25829125156104934464050375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68877667082946491904134333 25829125156104934464050375)
    ·
      refine ⟨38743687734157401696075563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25829125156104934464050375 38743687734157401696075563)
      ·
        refine ⟨58115531601236102544113345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38743687734157401696075563 58115531601236102544113345)
        ·
          refine ⟨43586648700927076908085009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58115531601236102544113345 43586648700927076908085009)
          ·
            refine ⟨32689986525695307681063757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43586648700927076908085009 32689986525695307681063757)
            ·
              refine ⟨12258744947135740380398909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32689986525695307681063757 12258744947135740380398909)
              ·
                refine ⟨4597029355175902642649591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12258744947135740380398909 4597029355175902642649591)
                ·
                  refine ⟨6895544032763853963974387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4597029355175902642649591 6895544032763853963974387)
                  ·
                    refine ⟨10343316049145780945961581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6895544032763853963974387 10343316049145780945961581)
                    ·
                      refine ⟨3878743518429667854735593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10343316049145780945961581 3878743518429667854735593)
                      ·
                        rfl

theorem cell23_7553826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_7553826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553826 prefixEnd_7553826 := by exact prefixLift 7553826
  have htrace : WordTrace (prefixWord ++ tailWord_7553826) baseStart_7553826 baseEnd_7553826 := by
    simpa [prefixWord, tailWord_7553826, baseEnd_7553826] using wordTrace_append hprefix tailTrace_7553826
  have hstable : (prefixWord ++ tailWord_7553826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553826).length < 2 ^ (prefixWord ++ tailWord_7553826).sum := by decide
  have hdescent : baseEnd_7553826 < baseStart_7553826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553832 : List Nat := [2, 1, 5, 1, 1, 1, 1, 5, 1, 1, 4]
def baseStart_7553832 : Nat := 118140960795 + 7553832 * 2 ^ 59
def prefixEnd_7553832 : Nat := 4983230072969 + 3 ^ 40 * 7553832 * 2
def baseEnd_7553832 : Nat := 3878746599313594831260565

theorem tailTrace_7553832 : CollatzResearch.WordTrace tailWord_7553832 prefixEnd_7553832 3878746599313594831260565 := by
  unfold tailWord_7553832
  simp only [CollatzResearch.WordTrace]
  refine ⟨137755443584882115320627875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183673924779842820427503833 137755443584882115320627875)
  ·
    refine ⟨206633165377323172980941813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137755443584882115320627875 206633165377323172980941813)
    ·
      refine ⟨19371859254124047466963295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206633165377323172980941813 19371859254124047466963295)
      ·
        refine ⟨29057788881186071200444943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19371859254124047466963295 29057788881186071200444943)
        ·
          refine ⟨43586683321779106800667415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29057788881186071200444943 43586683321779106800667415)
          ·
            refine ⟨65380024982668660201001123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43586683321779106800667415 65380024982668660201001123)
            ·
              refine ⟨98070037474002990301501685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65380024982668660201001123 98070037474002990301501685)
              ·
                refine ⟨9194066013187780340765783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98070037474002990301501685 9194066013187780340765783)
                ·
                  refine ⟨13791099019781670511148675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9194066013187780340765783 13791099019781670511148675)
                  ·
                    refine ⟨20686648529672505766723013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13791099019781670511148675 20686648529672505766723013)
                    ·
                      refine ⟨3878746599313594831260565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20686648529672505766723013 3878746599313594831260565)
                      ·
                        rfl

theorem cell23_7553832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_7553832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553832 prefixEnd_7553832 := by exact prefixLift 7553832
  have htrace : WordTrace (prefixWord ++ tailWord_7553832) baseStart_7553832 baseEnd_7553832 := by
    simpa [prefixWord, tailWord_7553832, baseEnd_7553832] using wordTrace_append hprefix tailTrace_7553832
  have hstable : (prefixWord ++ tailWord_7553832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553832).length < 2 ^ (prefixWord ++ tailWord_7553832).sum := by decide
  have hdescent : baseEnd_7553832 < baseStart_7553832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553842 : List Nat := [3, 2, 1, 1, 3, 1, 2, 4, 2, 4]
def baseStart_7553842 : Nat := 118140960795 + 7553842 * 2 ^ 59
def prefixEnd_7553842 : Nat := 4983230072969 + 3 ^ 40 * 7553842 * 2
def baseEnd_7553842 : Nat := 1292917244706713264045173

theorem tailTrace_7553842 : CollatzResearch.WordTrace tailWord_7553842 prefixEnd_7553842 1292917244706713264045173 := by
  unfold tailWord_7553842
  simp only [CollatzResearch.WordTrace]
  refine ⟨68877812974932000587279945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183674167933152001566079853 68877812974932000587279945)
  ·
    refine ⟨51658359731199000440459959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68877812974932000587279945 51658359731199000440459959)
    ·
      refine ⟨77487539596798500660689939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51658359731199000440459959 77487539596798500660689939)
      ·
        refine ⟨116231309395197750991034909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77487539596798500660689939 116231309395197750991034909)
        ·
          refine ⟨43586741023199156621638091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116231309395197750991034909 43586741023199156621638091)
          ·
            refine ⟨65380111534798734932457137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43586741023199156621638091 65380111534798734932457137)
            ·
              refine ⟨49035083651099051199342853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65380111534798734932457137 49035083651099051199342853)
              ·
                refine ⟨9194078184581072099876785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49035083651099051199342853 9194078184581072099876785)
                ·
                  refine ⟨6895558638435804074907589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9194078184581072099876785 6895558638435804074907589)
                  ·
                    refine ⟨1292917244706713264045173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6895558638435804074907589 1292917244706713264045173)
                    ·
                      rfl

theorem cell23_7553842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_7553842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553842 prefixEnd_7553842 := by exact prefixLift 7553842
  have htrace : WordTrace (prefixWord ++ tailWord_7553842) baseStart_7553842 baseEnd_7553842 := by
    simpa [prefixWord, tailWord_7553842, baseEnd_7553842] using wordTrace_append hprefix tailTrace_7553842
  have hstable : (prefixWord ++ tailWord_7553842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553842).length < 2 ^ (prefixWord ++ tailWord_7553842).sum := by decide
  have hdescent : baseEnd_7553842 < baseStart_7553842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553845 : List Nat := [1, 3, 3, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_7553845 : Nat := 118140960795 + 7553845 * 2 ^ 59
def prefixEnd_7553845 : Nat := 4983230072969 + 3 ^ 40 * 7553845 * 2
def baseEnd_7553845 : Nat := 3878753274562103280398005

theorem tailTrace_7553845 : CollatzResearch.WordTrace tailWord_7553845 prefixEnd_7553845 3878753274562103280398005 := by
  unfold tailWord_7553845
  simp only [CollatzResearch.WordTrace]
  refine ⟨275511361318717133861478989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183674240879144755907652659 275511361318717133861478989)
  ·
    refine ⟨103316760494518925198054621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275511361318717133861478989 103316760494518925198054621)
    ·
      refine ⟨38743785185444596949270483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103316760494518925198054621 38743785185444596949270483)
      ·
        refine ⟨58115677778166895423905725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38743785185444596949270483 58115677778166895423905725)
        ·
          refine ⟨21793379166812585783964647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58115677778166895423905725 21793379166812585783964647)
          ·
            refine ⟨32690068750218878675946971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21793379166812585783964647 32690068750218878675946971)
            ·
              refine ⟨49035103125328318013920457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32690068750218878675946971 49035103125328318013920457)
              ·
                refine ⟨36776327343996238510440343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49035103125328318013920457 36776327343996238510440343)
                ·
                  refine ⟨55164491015994357765660515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36776327343996238510440343 55164491015994357765660515)
                  ·
                    refine ⟨82746736523991536648490773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55164491015994357765660515 82746736523991536648490773)
                    ·
                      refine ⟨3878753274562103280398005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82746736523991536648490773 3878753274562103280398005)
                      ·
                        rfl

theorem cell23_7553845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_7553845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553845 prefixEnd_7553845 := by exact prefixLift 7553845
  have htrace : WordTrace (prefixWord ++ tailWord_7553845) baseStart_7553845 baseEnd_7553845 := by
    simpa [prefixWord, tailWord_7553845, baseEnd_7553845] using wordTrace_append hprefix tailTrace_7553845
  have hstable : (prefixWord ++ tailWord_7553845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553845).length < 2 ^ (prefixWord ++ tailWord_7553845).sum := by decide
  have hdescent : baseEnd_7553845 < baseStart_7553845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553855 : List Nat := [1, 1, 2, 2, 5, 2, 2, 8]
def baseStart_7553855 : Nat := 118140960795 + 7553855 * 2 ^ 59
def prefixEnd_7553855 : Nat := 4983230072969 + 3 ^ 40 * 7553855 * 2
def baseEnd_7553855 : Nat := 143657718865505490417517

theorem tailTrace_7553855 : CollatzResearch.WordTrace tailWord_7553855 prefixEnd_7553855 143657718865505490417517 := by
  unfold tailWord_7553855
  simp only [CollatzResearch.WordTrace]
  refine ⟨275511726048680905569343019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183674484032453937046228679 275511726048680905569343019)
  ·
    refine ⟨413267589073021358354014529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275511726048680905569343019 413267589073021358354014529)
    ·
      refine ⟨309950691804766018765510897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413267589073021358354014529 309950691804766018765510897)
      ·
        refine ⟨232463018853574514074133173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309950691804766018765510897 232463018853574514074133173)
        ·
          refine ⟨21793408017522610694449985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 232463018853574514074133173 21793408017522610694449985)
          ·
            refine ⟨16345056013141958020837489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21793408017522610694449985 16345056013141958020837489)
            ·
              refine ⟨12258792009856468515628117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16345056013141958020837489 12258792009856468515628117)
              ·
                refine ⟨143657718865505490417517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12258792009856468515628117 143657718865505490417517)
                ·
                  rfl

theorem cell23_7553855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 8].length) (baseStart_7553855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553855 prefixEnd_7553855 := by exact prefixLift 7553855
  have htrace : WordTrace (prefixWord ++ tailWord_7553855) baseStart_7553855 baseEnd_7553855 := by
    simpa [prefixWord, tailWord_7553855, baseEnd_7553855] using wordTrace_append hprefix tailTrace_7553855
  have hstable : (prefixWord ++ tailWord_7553855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553855).length < 2 ^ (prefixWord ++ tailWord_7553855).sum := by decide
  have hdescent : baseEnd_7553855 < baseStart_7553855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553882 : List Nat := [3, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3]
def baseStart_7553882 : Nat := 118140960795 + 7553882 * 2 ^ 59
def prefixEnd_7553882 : Nat := 4983230072969 + 3 ^ 40 * 7553882 * 2
def baseEnd_7553882 : Nat := 3878772273346319635635335

theorem tailTrace_7553882 : CollatzResearch.WordTrace tailWord_7553882 prefixEnd_7553882 3878772273346319635635335 := by
  unfold tailWord_7553882
  simp only [CollatzResearch.WordTrace]
  refine ⟨68878177704895772295143975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183675140546388726120383933 68878177704895772295143975)
  ·
    refine ⟨103317266557343658442715963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68878177704895772295143975 103317266557343658442715963)
    ·
      refine ⟨154975899836015487664073945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103317266557343658442715963 154975899836015487664073945)
      ·
        refine ⟨116231924877011615748055459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154975899836015487664073945 116231924877011615748055459)
        ·
          refine ⟨174347887315517423622083189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116231924877011615748055459 174347887315517423622083189)
          ·
            refine ⟨16345114435829758464570299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174347887315517423622083189 16345114435829758464570299)
            ·
              refine ⟨24517671653744637696855449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16345114435829758464570299 24517671653744637696855449)
              ·
                refine ⟨18388253740308478272641587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24517671653744637696855449 18388253740308478272641587)
                ·
                  refine ⟨27582380610462717408962381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18388253740308478272641587 27582380610462717408962381)
                  ·
                    refine ⟨10343392728923519028360893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27582380610462717408962381 10343392728923519028360893)
                    ·
                      refine ⟨3878772273346319635635335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10343392728923519028360893 3878772273346319635635335)
                      ·
                        rfl

theorem cell23_7553882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_7553882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553882 prefixEnd_7553882 := by exact prefixLift 7553882
  have htrace : WordTrace (prefixWord ++ tailWord_7553882) baseStart_7553882 baseEnd_7553882 := by
    simpa [prefixWord, tailWord_7553882, baseEnd_7553882] using wordTrace_append hprefix tailTrace_7553882
  have hstable : (prefixWord ++ tailWord_7553882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553882).length < 2 ^ (prefixWord ++ tailWord_7553882).sum := by decide
  have hdescent : baseEnd_7553882 < baseStart_7553882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553905 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 2, 3, 4]
def baseStart_7553905 : Nat := 118140960795 + 7553905 * 2 ^ 59
def prefixEnd_7553905 : Nat := 4983230072969 + 3 ^ 40 * 7553905 * 2
def baseEnd_7553905 : Nat := 3878784083401373045647729

theorem tailTrace_7553905 : CollatzResearch.WordTrace tailWord_7553905 prefixEnd_7553905 3878784083401373045647729 := by
  unfold tailWord_7553905
  simp only [CollatzResearch.WordTrace]
  refine ⟨275513549698499764108663169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183675699798999842739108779 275513549698499764108663169)
  ·
    refine ⟨206635162273874823081497377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275513549698499764108663169 206635162273874823081497377)
    ·
      refine ⟨154976371705406117311123033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206635162273874823081497377 154976371705406117311123033)
      ·
        refine ⟨116232278779054587983342275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154976371705406117311123033 116232278779054587983342275)
        ·
          refine ⟨174348418168581881975013413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116232278779054587983342275 174348418168581881975013413)
          ·
            refine ⟨32690328406609102870315015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174348418168581881975013413 32690328406609102870315015)
            ·
              refine ⟨49035492609913654305472523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32690328406609102870315015 49035492609913654305472523)
              ·
                refine ⟨73553238914870481458208785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49035492609913654305472523 73553238914870481458208785)
                ·
                  refine ⟨55164929186152861093656589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73553238914870481458208785 55164929186152861093656589)
                  ·
                    refine ⟨20686848444807322910121221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55164929186152861093656589 20686848444807322910121221)
                    ·
                      refine ⟨3878784083401373045647729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20686848444807322910121221 3878784083401373045647729)
                      ·
                        rfl

theorem cell23_7553905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_7553905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553905 prefixEnd_7553905 := by exact prefixLift 7553905
  have htrace : WordTrace (prefixWord ++ tailWord_7553905) baseStart_7553905 baseEnd_7553905 := by
    simpa [prefixWord, tailWord_7553905, baseEnd_7553905] using wordTrace_append hprefix tailTrace_7553905
  have hstable : (prefixWord ++ tailWord_7553905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553905).length < 2 ^ (prefixWord ++ tailWord_7553905).sum := by decide
  have hdescent : baseEnd_7553905 < baseStart_7553905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553909 : List Nat := [1, 3, 4, 1, 1, 2, 1, 2, 3, 3, 2]
def baseStart_7553909 : Nat := 118140960795 + 7553909 * 2 ^ 59
def prefixEnd_7553909 : Nat := 4983230072969 + 3 ^ 40 * 7553909 * 2
def baseEnd_7553909 : Nat := 3878786137323991029997711

theorem tailTrace_7553909 : CollatzResearch.WordTrace tailWord_7553909 prefixEnd_7553909 3878786137323991029997711 := by
  unfold tailWord_7553909
  simp only [CollatzResearch.WordTrace]
  refine ⟨275513695590485272791808781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183675797060323515194539187 275513695590485272791808781)
  ·
    refine ⟨103317635846431977296928293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275513695590485272791808781 103317635846431977296928293)
    ·
      refine ⟨19372056721205995743174055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103317635846431977296928293 19372056721205995743174055)
      ·
        refine ⟨29058085081808993614761083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19372056721205995743174055 29058085081808993614761083)
        ·
          refine ⟨43587127622713490422141625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29058085081808993614761083 43587127622713490422141625)
          ·
            refine ⟨32690345717035117816606219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43587127622713490422141625 32690345717035117816606219)
            ·
              refine ⟨49035518575552676724909329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32690345717035117816606219 49035518575552676724909329)
              ·
                refine ⟨36776638931664507543681997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49035518575552676724909329 36776638931664507543681997)
                ·
                  refine ⟨13791239599374190328880749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36776638931664507543681997 13791239599374190328880749)
                  ·
                    refine ⟨5171714849765321373330281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13791239599374190328880749 5171714849765321373330281)
                    ·
                      refine ⟨3878786137323991029997711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5171714849765321373330281 3878786137323991029997711)
                      ·
                        rfl

theorem cell23_7553909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_7553909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553909 prefixEnd_7553909 := by exact prefixLift 7553909
  have htrace : WordTrace (prefixWord ++ tailWord_7553909) baseStart_7553909 baseEnd_7553909 := by
    simpa [prefixWord, tailWord_7553909, baseEnd_7553909] using wordTrace_append hprefix tailTrace_7553909
  have hstable : (prefixWord ++ tailWord_7553909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553909).length < 2 ^ (prefixWord ++ tailWord_7553909).sum := by decide
  have hdescent : baseEnd_7553909 < baseStart_7553909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553973 : List Nat := [1, 3, 3, 2, 1, 1, 5, 1, 2, 2, 2]
def baseStart_7553973 : Nat := 118140960795 + 7553973 * 2 ^ 59
def prefixEnd_7553973 : Nat := 4983230072969 + 3 ^ 40 * 7553973 * 2
def baseEnd_7553973 : Nat := 3878819000085878779597417

theorem tailTrace_7553973 : CollatzResearch.WordTrace tailWord_7553973 prefixEnd_7553973 3878819000085878779597417 := by
  unfold tailWord_7553973
  simp only [CollatzResearch.WordTrace]
  refine ⟨275516029862253411722138573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183677353241502274481425715 275516029862253411722138573)
  ·
    refine ⟨103318511198345029395801965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275516029862253411722138573 103318511198345029395801965)
    ·
      refine ⟨38744441699379386023425737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103318511198345029395801965 38744441699379386023425737)
      ·
        refine ⟨29058331274534539517569303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38744441699379386023425737 29058331274534539517569303)
        ·
          refine ⟨43587496911801809276353955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29058331274534539517569303 43587496911801809276353955)
          ·
            refine ⟨65381245367702713914530933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43587496911801809276353955 65381245367702713914530933)
            ·
              refine ⟨6129491753222129429487275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65381245367702713914530933 6129491753222129429487275)
              ·
                refine ⟨9194237629833194144230913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6129491753222129429487275 9194237629833194144230913)
                ·
                  refine ⟨6895678222374895608173185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9194237629833194144230913 6895678222374895608173185)
                  ·
                    refine ⟨5171758666781171706129889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6895678222374895608173185 5171758666781171706129889)
                    ·
                      refine ⟨3878819000085878779597417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5171758666781171706129889 3878819000085878779597417)
                      ·
                        rfl

theorem cell23_7553973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_7553973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553973 prefixEnd_7553973 := by exact prefixLift 7553973
  have htrace : WordTrace (prefixWord ++ tailWord_7553973) baseStart_7553973 baseEnd_7553973 := by
    simpa [prefixWord, tailWord_7553973, baseEnd_7553973] using wordTrace_append hprefix tailTrace_7553973
  have hstable : (prefixWord ++ tailWord_7553973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553973).length < 2 ^ (prefixWord ++ tailWord_7553973).sum := by decide
  have hdescent : baseEnd_7553973 < baseStart_7553973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553975 : List Nat := [1, 1, 3, 1, 3, 1, 3, 2, 1, 7]
def baseStart_7553975 : Nat := 118140960795 + 7553975 * 2 ^ 59
def prefixEnd_7553975 : Nat := 4983230072969 + 3 ^ 40 * 7553975 * 2
def baseEnd_7553975 : Nat := 1292940009015729257257469

theorem tailTrace_7553975 : CollatzResearch.WordTrace tailWord_7553975 prefixEnd_7553975 1292940009015729257257469 := by
  unfold tailWord_7553975
  simp only [CollatzResearch.WordTrace]
  refine ⟨275516102808246166063711379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183677401872164110709140919 275516102808246166063711379)
  ·
    refine ⟨413274154212369249095567069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275516102808246166063711379 413274154212369249095567069)
    ·
      refine ⟨154977807829638468410837651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413274154212369249095567069 154977807829638468410837651)
      ·
        refine ⟨232466711744457702616256477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154977807829638468410837651 232466711744457702616256477)
        ·
          refine ⟨87175016904171638481096179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232466711744457702616256477 87175016904171638481096179)
          ·
            refine ⟨130762525356257457721644269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87175016904171638481096179 130762525356257457721644269)
            ·
              refine ⟨49035947008596546645616601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130762525356257457721644269 49035947008596546645616601)
              ·
                refine ⟨36776960256447409984212451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49035947008596546645616601 36776960256447409984212451)
                ·
                  refine ⟨55165440384671114976318677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36776960256447409984212451 55165440384671114976318677)
                  ·
                    refine ⟨1292940009015729257257469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55165440384671114976318677 1292940009015729257257469)
                    ·
                      rfl

theorem cell23_7553975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 7].length) (baseStart_7553975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553975 prefixEnd_7553975 := by exact prefixLift 7553975
  have htrace : WordTrace (prefixWord ++ tailWord_7553975) baseStart_7553975 baseEnd_7553975 := by
    simpa [prefixWord, tailWord_7553975, baseEnd_7553975] using wordTrace_append hprefix tailTrace_7553975
  have hstable : (prefixWord ++ tailWord_7553975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553975).length < 2 ^ (prefixWord ++ tailWord_7553975).sum := by decide
  have hdescent : baseEnd_7553975 < baseStart_7553975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554032 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 3]
def baseStart_7554032 : Nat := 118140960795 + 7554032 * 2 ^ 59
def prefixEnd_7554032 : Nat := 4983230072969 + 3 ^ 40 * 7554032 * 2
def baseEnd_7554032 : Nat := 3878849295444494048759645

theorem tailTrace_7554032 : CollatzResearch.WordTrace tailWord_7554032 prefixEnd_7554032 3878849295444494048759645 := by
  unfold tailWord_7554032
  simp only [CollatzResearch.WordTrace]
  refine ⟨137759090884519832399268175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183678787846026443199024233 137759090884519832399268175)
  ·
    refine ⟨206638636326779748598902263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137759090884519832399268175 206638636326779748598902263)
    ·
      refine ⟨309957954490169622898353395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206638636326779748598902263 309957954490169622898353395)
      ·
        refine ⟨464936931735254434347530093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309957954490169622898353395 464936931735254434347530093)
        ·
          refine ⟨174351349400720412880323785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 464936931735254434347530093 174351349400720412880323785)
          ·
            refine ⟨130763512050540309660242839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174351349400720412880323785 130763512050540309660242839)
            ·
              refine ⟨196145268075810464490364259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130763512050540309660242839 196145268075810464490364259)
              ·
                refine ⟨294217902113715696735546389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196145268075810464490364259 294217902113715696735546389)
                ·
                  refine ⟨13791464161580423284478737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 294217902113715696735546389 13791464161580423284478737)
                  ·
                    refine ⟨10343598121185317463359053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13791464161580423284478737 10343598121185317463359053)
                    ·
                      refine ⟨3878849295444494048759645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10343598121185317463359053 3878849295444494048759645)
                      ·
                        rfl

theorem cell23_7554032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 3].length) (baseStart_7554032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554032 prefixEnd_7554032 := by exact prefixLift 7554032
  have htrace : WordTrace (prefixWord ++ tailWord_7554032) baseStart_7554032 baseEnd_7554032 := by
    simpa [prefixWord, tailWord_7554032, baseEnd_7554032] using wordTrace_append hprefix tailTrace_7554032
  have hstable : (prefixWord ++ tailWord_7554032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554032).length < 2 ^ (prefixWord ++ tailWord_7554032).sum := by decide
  have hdescent : baseEnd_7554032 < baseStart_7554032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554049 : List Nat := [1, 2, 4, 1, 2, 2, 1, 3, 2, 2, 3]
def baseStart_7554049 : Nat := 118140960795 + 7554049 * 2 ^ 59
def prefixEnd_7554049 : Nat := 4983230072969 + 3 ^ 40 * 7554049 * 2
def baseEnd_7554049 : Nat := 3878858024615620482247067

theorem tailTrace_7554049 : CollatzResearch.WordTrace tailWord_7554049 prefixEnd_7554049 3878858024615620482247067 := by
  unfold tailWord_7554049
  simp only [CollatzResearch.WordTrace]
  refine ⟨275518801809978076701905201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183679201206652051134603467 275518801809978076701905201)
  ·
    refine ⟨206639101357483557526428901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275518801809978076701905201 206639101357483557526428901)
    ·
      refine ⟨38744831504528167036205419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206639101357483557526428901 38744831504528167036205419)
      ·
        refine ⟨58117247256792250554308129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38744831504528167036205419 58117247256792250554308129)
        ·
          refine ⟨43587935442594187915731097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58117247256792250554308129 43587935442594187915731097)
          ·
            refine ⟨32690951581945640936798323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43587935442594187915731097 32690951581945640936798323)
            ·
              refine ⟨49036427372918461405197485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32690951581945640936798323 49036427372918461405197485)
              ·
                refine ⟨18388660264844423026949057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49036427372918461405197485 18388660264844423026949057)
                ·
                  refine ⟨13791495198633317270211793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18388660264844423026949057 13791495198633317270211793)
                  ·
                    refine ⟨10343621398974987952658845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13791495198633317270211793 10343621398974987952658845)
                    ·
                      refine ⟨3878858024615620482247067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10343621398974987952658845 3878858024615620482247067)
                      ·
                        rfl

theorem cell23_7554049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_7554049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554049 prefixEnd_7554049 := by exact prefixLift 7554049
  have htrace : WordTrace (prefixWord ++ tailWord_7554049) baseStart_7554049 baseEnd_7554049 := by
    simpa [prefixWord, tailWord_7554049, baseEnd_7554049] using wordTrace_append hprefix tailTrace_7554049
  have hstable : (prefixWord ++ tailWord_7554049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554049).length < 2 ^ (prefixWord ++ tailWord_7554049).sum := by decide
  have hdescent : baseEnd_7554049 < baseStart_7554049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554069 : List Nat := [1, 3, 2, 1, 4, 2, 2, 2, 6]
def baseStart_7554069 : Nat := 118140960795 + 7554069 * 2 ^ 59
def prefixEnd_7554069 : Nat := 4983230072969 + 3 ^ 40 * 7554069 * 2
def baseEnd_7554069 : Nat := 430985366025412267110775

theorem tailTrace_7554069 : CollatzResearch.WordTrace tailWord_7554069 prefixEnd_7554069 430985366025412267110775 := by
  unfold tailWord_7554069
  simp only [CollatzResearch.WordTrace]
  refine ⟨275519531269905620117633261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183679687513270413411755507 275519531269905620117633261)
  ·
    refine ⟨103319824226214607544112473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275519531269905620117633261 103319824226214607544112473)
    ·
      refine ⟨77489868169660955658084355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103319824226214607544112473 77489868169660955658084355)
      ·
        refine ⟨116234802254491433487126533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77489868169660955658084355 116234802254491433487126533)
        ·
          refine ⟨21794025422717143778836225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116234802254491433487126533 21794025422717143778836225)
          ·
            refine ⟨16345519067037857834127169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21794025422717143778836225 16345519067037857834127169)
            ·
              refine ⟨12259139300278393375595377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16345519067037857834127169 12259139300278393375595377)
              ·
                refine ⟨9194354475208795031696533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12259139300278393375595377 9194354475208795031696533)
                ·
                  refine ⟨430985366025412267110775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9194354475208795031696533 430985366025412267110775)
                  ·
                    rfl

theorem cell23_7554069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 6].length) (baseStart_7554069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554069 prefixEnd_7554069 := by exact prefixLift 7554069
  have htrace : WordTrace (prefixWord ++ tailWord_7554069) baseStart_7554069 baseEnd_7554069 := by
    simpa [prefixWord, tailWord_7554069, baseEnd_7554069] using wordTrace_append hprefix tailTrace_7554069
  have hstable : (prefixWord ++ tailWord_7554069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554069).length < 2 ^ (prefixWord ++ tailWord_7554069).sum := by decide
  have hdescent : baseEnd_7554069 < baseStart_7554069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554106 : List Nat := [3, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2]
def baseStart_7554106 : Nat := 118140960795 + 7554106 * 2 ^ 59
def prefixEnd_7554106 : Nat := 4983230072969 + 3 ^ 40 * 7554106 * 2
def baseEnd_7554106 : Nat := 3878887293012926759234305

theorem tailTrace_7554106 : CollatzResearch.WordTrace tailWord_7554106 prefixEnd_7554106 3878887293012926759234305 := by
  unfold tailWord_7554106
  simp only [CollatzResearch.WordTrace]
  refine ⟨68880220192692893859182543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183680587180514383624486781 68880220192692893859182543)
  ·
    refine ⟨103320330289039340788773815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68880220192692893859182543 103320330289039340788773815)
    ·
      refine ⟨154980495433559011183160723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103320330289039340788773815 154980495433559011183160723)
      ·
        refine ⟨232470743150338516774741085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154980495433559011183160723 232470743150338516774741085)
        ·
          refine ⟨87176528681376943790527907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232470743150338516774741085 87176528681376943790527907)
          ·
            refine ⟨130764793022065415685791861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87176528681376943790527907 130764793022065415685791861)
            ·
              refine ⟨12259199345818632720542987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130764793022065415685791861 12259199345818632720542987)
              ·
                refine ⟨18388799018727949080814481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12259199345818632720542987 18388799018727949080814481)
                ·
                  refine ⟨13791599264045961810610861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18388799018727949080814481 13791599264045961810610861)
                  ·
                    refine ⟨5171849724017235678979073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13791599264045961810610861 5171849724017235678979073)
                    ·
                      refine ⟨3878887293012926759234305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5171849724017235678979073 3878887293012926759234305)
                      ·
                        rfl

theorem cell23_7554106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2].length) (baseStart_7554106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554106 prefixEnd_7554106 := by exact prefixLift 7554106
  have htrace : WordTrace (prefixWord ++ tailWord_7554106) baseStart_7554106 baseEnd_7554106 := by
    simpa [prefixWord, tailWord_7554106, baseEnd_7554106] using wordTrace_append hprefix tailTrace_7554106
  have hstable : (prefixWord ++ tailWord_7554106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554106).length < 2 ^ (prefixWord ++ tailWord_7554106).sum := by decide
  have hdescent : baseEnd_7554106 < baseStart_7554106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554112 : List Nat := [2, 1, 1, 2, 2, 3, 1, 4, 1, 6]
def baseStart_7554112 : Nat := 118140960795 + 7554112 * 2 ^ 59
def prefixEnd_7554112 : Nat := 4983230072969 + 3 ^ 40 * 7554112 * 2
def baseEnd_7554112 : Nat := 1292963457965617911919759

theorem tailTrace_7554112 : CollatzResearch.WordTrace tailWord_7554112 prefixEnd_7554112 1292963457965617911919759 := by
  unfold tailWord_7554112
  simp only [CollatzResearch.WordTrace]
  refine ⟨137760549804374919230724295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183680733072499892307632393 137760549804374919230724295)
  ·
    refine ⟨206640824706562378846086443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137760549804374919230724295 206640824706562378846086443)
    ·
      refine ⟨309961237059843568269129665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206640824706562378846086443 309961237059843568269129665)
      ·
        refine ⟨232470927794882676201847249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309961237059843568269129665 232470927794882676201847249)
        ·
          refine ⟨174353195846162007151385437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232470927794882676201847249 174353195846162007151385437)
          ·
            refine ⟨65382448442310752681769539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174353195846162007151385437 65382448442310752681769539)
            ·
              refine ⟨98073672663466129022654309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65382448442310752681769539 98073672663466129022654309)
              ·
                refine ⟨18388813624399899191747683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98073672663466129022654309 18388813624399899191747683)
                ·
                  refine ⟨27583220436599848787621525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18388813624399899191747683 27583220436599848787621525)
                  ·
                    refine ⟨1292963457965617911919759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27583220436599848787621525 1292963457965617911919759)
                    ·
                      rfl

theorem cell23_7554112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 1, 6].length) (baseStart_7554112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554112 prefixEnd_7554112 := by exact prefixLift 7554112
  have htrace : WordTrace (prefixWord ++ tailWord_7554112) baseStart_7554112 baseEnd_7554112 := by
    simpa [prefixWord, tailWord_7554112, baseEnd_7554112] using wordTrace_append hprefix tailTrace_7554112
  have hstable : (prefixWord ++ tailWord_7554112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554112).length < 2 ^ (prefixWord ++ tailWord_7554112).sum := by decide
  have hdescent : baseEnd_7554112 < baseStart_7554112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554146 : List Nat := [3, 3, 2, 2, 1, 1, 3, 1, 1, 6]
def baseStart_7554146 : Nat := 118140960795 + 7554146 * 2 ^ 59
def prefixEnd_7554146 : Nat := 4983230072969 + 3 ^ 40 * 7554146 * 2
def baseEnd_7554146 : Nat := 1292969277413035534244707

theorem tailTrace_7554146 : CollatzResearch.WordTrace tailWord_7554146 prefixEnd_7554146 1292969277413035534244707 := by
  unfold tailWord_7554146
  simp only [CollatzResearch.WordTrace]
  refine ⟨68880584922656665567046573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183681559793751108178790861 68880584922656665567046573)
  ·
    refine ⟨25830219345996249587642465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68880584922656665567046573 25830219345996249587642465)
    ·
      refine ⟨19372664509497187190731849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25830219345996249587642465 19372664509497187190731849)
      ·
        refine ⟨14529498382122890393048887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19372664509497187190731849 14529498382122890393048887)
        ·
          refine ⟨21794247573184335589573331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14529498382122890393048887 21794247573184335589573331)
          ·
            refine ⟨32691371359776503384359997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21794247573184335589573331 32691371359776503384359997)
            ·
              refine ⟨12259264259916188769134999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32691371359776503384359997 12259264259916188769134999)
              ·
                refine ⟨18388896389874283153702499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12259264259916188769134999 18388896389874283153702499)
                ·
                  refine ⟨27583344584811424730553749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18388896389874283153702499 27583344584811424730553749)
                  ·
                    refine ⟨1292969277413035534244707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27583344584811424730553749 1292969277413035534244707)
                    ·
                      rfl

theorem cell23_7554146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_7554146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554146 prefixEnd_7554146 := by exact prefixLift 7554146
  have htrace : WordTrace (prefixWord ++ tailWord_7554146) baseStart_7554146 baseEnd_7554146 := by
    simpa [prefixWord, tailWord_7554146, baseEnd_7554146] using wordTrace_append hprefix tailTrace_7554146
  have hstable : (prefixWord ++ tailWord_7554146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554146).length < 2 ^ (prefixWord ++ tailWord_7554146).sum := by decide
  have hdescent : baseEnd_7554146 < baseStart_7554146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554156 : List Nat := [2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 3]
def baseStart_7554156 : Nat := 118140960795 + 7554156 * 2 ^ 59
def prefixEnd_7554156 : Nat := 4983230072969 + 3 ^ 40 * 7554156 * 2
def baseEnd_7554156 : Nat := 3878912967045651563609075

theorem tailTrace_7554156 : CollatzResearch.WordTrace tailWord_7554156 prefixEnd_7554156 3878912967045651563609075 := by
  unfold tailWord_7554156
  simp only [CollatzResearch.WordTrace]
  refine ⟨137761352210295216988025161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183681802947060289317366881 137761352210295216988025161)
  ·
    refine ⟨103321014157721412741018871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137761352210295216988025161 103321014157721412741018871)
    ·
      refine ⟨154981521236582119111528307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103321014157721412741018871 154981521236582119111528307)
      ·
        refine ⟨232472281854873178667292461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154981521236582119111528307 232472281854873178667292461)
        ·
          refine ⟨87177105695577442000234673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232472281854873178667292461 87177105695577442000234673)
          ·
            refine ⟨65382829271683081500176005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87177105695577442000234673 65382829271683081500176005)
            ·
              refine ⟨12259280488440577781283001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65382829271683081500176005 12259280488440577781283001)
              ·
                refine ⟨9194460366330433335962251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12259280488440577781283001 9194460366330433335962251)
                ·
                  refine ⟨13791690549495650003943377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9194460366330433335962251 13791690549495650003943377)
                  ·
                    refine ⟨10343767912121737502957533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13791690549495650003943377 10343767912121737502957533)
                    ·
                      refine ⟨3878912967045651563609075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10343767912121737502957533 3878912967045651563609075)
                      ·
                        rfl

theorem cell23_7554156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 3].length) (baseStart_7554156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554156 prefixEnd_7554156 := by exact prefixLift 7554156
  have htrace : WordTrace (prefixWord ++ tailWord_7554156) baseStart_7554156 baseEnd_7554156 := by
    simpa [prefixWord, tailWord_7554156, baseEnd_7554156] using wordTrace_append hprefix tailTrace_7554156
  have hstable : (prefixWord ++ tailWord_7554156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554156).length < 2 ^ (prefixWord ++ tailWord_7554156).sum := by decide
  have hdescent : baseEnd_7554156 < baseStart_7554156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554186 : List Nat := [3, 1, 2, 3, 1, 1, 1, 3, 4, 1, 3]
def baseStart_7554186 : Nat := 118140960795 + 7554186 * 2 ^ 59
def prefixEnd_7554186 : Nat := 4983230072969 + 3 ^ 40 * 7554186 * 2
def baseEnd_7554186 : Nat := 3878928371465286446233937

theorem tailTrace_7554186 : CollatzResearch.WordTrace tailWord_7554186 prefixEnd_7554186 3878928371465286446233937 := by
  unfold tailWord_7554186
  simp only [CollatzResearch.WordTrace]
  refine ⟨68880949652620437274910603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183682532406987832733094941 68880949652620437274910603)
  ·
    refine ⟨103321424478930655912365905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68880949652620437274910603 103321424478930655912365905)
    ·
      refine ⟨77491068359197991934274429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103321424478930655912365905 77491068359197991934274429)
      ·
        refine ⟨29059150634699246975352911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77491068359197991934274429 29059150634699246975352911)
        ·
          refine ⟨43588725952048870463029367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29059150634699246975352911 43588725952048870463029367)
          ·
            refine ⟨65383088928073305694544051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43588725952048870463029367 65383088928073305694544051)
            ·
              refine ⟨98074633392109958541816077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65383088928073305694544051 98074633392109958541816077)
              ·
                refine ⟨36777987522041234453181029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98074633392109958541816077 36777987522041234453181029)
                ·
                  refine ⟨6895872660382731459971443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36777987522041234453181029 6895872660382731459971443)
                  ·
                    refine ⟨10343808990574097189957165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6895872660382731459971443 10343808990574097189957165)
                    ·
                      refine ⟨3878928371465286446233937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10343808990574097189957165 3878928371465286446233937)
                      ·
                        rfl

theorem cell23_7554186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_7554186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554186 prefixEnd_7554186 := by exact prefixLift 7554186
  have htrace : WordTrace (prefixWord ++ tailWord_7554186) baseStart_7554186 baseEnd_7554186 := by
    simpa [prefixWord, tailWord_7554186, baseEnd_7554186] using wordTrace_append hprefix tailTrace_7554186
  have hstable : (prefixWord ++ tailWord_7554186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554186).length < 2 ^ (prefixWord ++ tailWord_7554186).sum := by decide
  have hdescent : baseEnd_7554186 < baseStart_7554186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554213 : List Nat := [1, 3, 1, 2, 1, 4, 3, 2, 1, 3, 2]
def baseStart_7554213 : Nat := 118140960795 + 7554213 * 2 ^ 59
def prefixEnd_7554213 : Nat := 4983230072969 + 3 ^ 40 * 7554213 * 2
def baseEnd_7554213 : Nat := 3878942235442957840596313

theorem tailTrace_7554213 : CollatzResearch.WordTrace tailWord_7554213 prefixEnd_7554213 3878942235442957840596313 := by
  unfold tailWord_7554213
  simp only [CollatzResearch.WordTrace]
  refine ⟨275524783381383932710875293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183683188920922621807250195 275524783381383932710875293)
  ·
    refine ⟨103321793768018974766578235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275524783381383932710875293 103321793768018974766578235)
    ·
      refine ⟨154982690652028462149867353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103321793768018974766578235 154982690652028462149867353)
      ·
        refine ⟨116237017989021346612400515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154982690652028462149867353 116237017989021346612400515)
        ·
          refine ⟨174355526983532019918600773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116237017989021346612400515 174355526983532019918600773)
          ·
            refine ⟨32691661309412253734737645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174355526983532019918600773 32691661309412253734737645)
            ·
              refine ⟨12259372991029595150526617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32691661309412253734737645 12259372991029595150526617)
              ·
                refine ⟨9194529743272196362894963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12259372991029595150526617 9194529743272196362894963)
                ·
                  refine ⟨13791794614908294544342445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9194529743272196362894963 13791794614908294544342445)
                  ·
                    refine ⟨5171922980590610454128417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13791794614908294544342445 5171922980590610454128417)
                    ·
                      refine ⟨3878942235442957840596313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5171922980590610454128417 3878942235442957840596313)
                      ·
                        rfl

theorem cell23_7554213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 3, 2].length) (baseStart_7554213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554213 prefixEnd_7554213 := by exact prefixLift 7554213
  have htrace : WordTrace (prefixWord ++ tailWord_7554213) baseStart_7554213 baseEnd_7554213 := by
    simpa [prefixWord, tailWord_7554213, baseEnd_7554213] using wordTrace_append hprefix tailTrace_7554213
  have hstable : (prefixWord ++ tailWord_7554213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554213).length < 2 ^ (prefixWord ++ tailWord_7554213).sum := by decide
  have hdescent : baseEnd_7554213 < baseStart_7554213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554226 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2]
def baseStart_7554226 : Nat := 118140960795 + 7554226 * 2 ^ 59
def prefixEnd_7554226 : Nat := 4983230072969 + 3 ^ 40 * 7554226 * 2
def baseEnd_7554226 : Nat := 3878948910691466289733753

theorem tailTrace_7554226 : CollatzResearch.WordTrace tailWord_7554226 prefixEnd_7554226 3878948910691466289733753 := by
  unfold tailWord_7554226
  simp only [CollatzResearch.WordTrace]
  refine ⟨68881314382584208982774633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183683505020224557287399021 68881314382584208982774633)
  ·
    refine ⟨51660985786938156737080975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68881314382584208982774633 51660985786938156737080975)
    ·
      refine ⟨77491478680407235105621463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51660985786938156737080975 77491478680407235105621463)
      ·
        refine ⟨116237218020610852658432195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77491478680407235105621463 116237218020610852658432195)
        ·
          refine ⟨174355827030916278987648293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116237218020610852658432195 174355827030916278987648293)
          ·
            refine ⟨32691717568296802310184055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174355827030916278987648293 32691717568296802310184055)
            ·
              refine ⟨49037576352445203465276083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32691717568296802310184055 49037576352445203465276083)
              ·
                refine ⟨73556364528667805197914125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49037576352445203465276083 73556364528667805197914125)
                ·
                  refine ⟨27583636698250426949217797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73556364528667805197914125 27583636698250426949217797)
                  ·
                    refine ⟨5171931880921955052978337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27583636698250426949217797 5171931880921955052978337)
                    ·
                      refine ⟨3878948910691466289733753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5171931880921955052978337 3878948910691466289733753)
                      ·
                        rfl

theorem cell23_7554226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2].length) (baseStart_7554226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554226 prefixEnd_7554226 := by exact prefixLift 7554226
  have htrace : WordTrace (prefixWord ++ tailWord_7554226) baseStart_7554226 baseEnd_7554226 := by
    simpa [prefixWord, tailWord_7554226, baseEnd_7554226] using wordTrace_append hprefix tailTrace_7554226
  have hstable : (prefixWord ++ tailWord_7554226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554226).length < 2 ^ (prefixWord ++ tailWord_7554226).sum := by decide
  have hdescent : baseEnd_7554226 < baseStart_7554226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554232 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 11]
def baseStart_7554232 : Nat := 118140960795 + 7554232 * 2 ^ 59
def prefixEnd_7554232 : Nat := 4983230072969 + 3 ^ 40 * 7554232 * 2
def baseEnd_7554232 : Nat := 430994665730599251806525

theorem tailTrace_7554232 : CollatzResearch.WordTrace tailWord_7554232 prefixEnd_7554232 430994665730599251806525 := by
  unfold tailWord_7554232
  simp only [CollatzResearch.WordTrace]
  refine ⟨137762738184157549477908475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183683650912210065970544633 137762738184157549477908475)
  ·
    refine ⟨206644107276236324216862713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137762738184157549477908475 206644107276236324216862713)
    ·
      refine ⟨154983080457177243162647035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206644107276236324216862713 154983080457177243162647035)
      ·
        refine ⟨232474620685765864743970553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154983080457177243162647035 232474620685765864743970553)
        ·
          refine ⟨174355965514324398557977915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232474620685765864743970553 174355965514324398557977915)
          ·
            refine ⟨261533948271486597836966873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174355965514324398557977915 261533948271486597836966873)
            ·
              refine ⟨196150461203614948377725155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261533948271486597836966873 196150461203614948377725155)
              ·
                refine ⟨294225691805422422566587733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196150461203614948377725155 294225691805422422566587733)
                ·
                  refine ⟨430994665730599251806525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 294225691805422422566587733 430994665730599251806525)
                  ·
                    rfl

theorem cell23_7554232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 11].length) (baseStart_7554232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554232 prefixEnd_7554232 := by exact prefixLift 7554232
  have htrace : WordTrace (prefixWord ++ tailWord_7554232) baseStart_7554232 baseEnd_7554232 := by
    simpa [prefixWord, tailWord_7554232, baseEnd_7554232] using wordTrace_append hprefix tailTrace_7554232
  have hstable : (prefixWord ++ tailWord_7554232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554232).length < 2 ^ (prefixWord ++ tailWord_7554232).sum := by decide
  have hdescent : baseEnd_7554232 < baseStart_7554232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554259 : List Nat := [1, 1, 1, 2, 1, 1, 1, 7, 2, 3, 3]
def baseStart_7554259 : Nat := 118140960795 + 7554259 * 2 ^ 59
def prefixEnd_7554259 : Nat := 4983230072969 + 3 ^ 40 * 7554259 * 2
def baseEnd_7554259 : Nat := 3878965855553064660621101

theorem tailTrace_7554259 : CollatzResearch.WordTrace tailWord_7554259 prefixEnd_7554259 3878965855553064660621101 := by
  unfold tailWord_7554259
  simp only [CollatzResearch.WordTrace]
  refine ⟨275526461139217282567049831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183684307426144855044699887 275526461139217282567049831)
  ·
    refine ⟨413289691708825923850574747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275526461139217282567049831 413289691708825923850574747)
    ·
      refine ⟨619934537563238885775862121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413289691708825923850574747 619934537563238885775862121)
      ·
        refine ⟨464950903172429164331896591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 619934537563238885775862121 464950903172429164331896591)
        ·
          refine ⟨697426354758643746497844887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464950903172429164331896591 697426354758643746497844887)
          ·
            refine ⟨1046139532137965619746767331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697426354758643746497844887 1046139532137965619746767331)
            ·
              refine ⟨1569209298206948429620150997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1046139532137965619746767331 1569209298206948429620150997)
              ·
                refine ⟨36778342926725353819222289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1569209298206948429620150997 36778342926725353819222289)
                ·
                  refine ⟨27583757195044015364416717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36778342926725353819222289 27583757195044015364416717)
                  ·
                    refine ⟨10343908948141505761656269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27583757195044015364416717 10343908948141505761656269)
                    ·
                      refine ⟨3878965855553064660621101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10343908948141505761656269 3878965855553064660621101)
                      ·
                        rfl

theorem cell23_7554259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3, 3].length) (baseStart_7554259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554259 prefixEnd_7554259 := by exact prefixLift 7554259
  have htrace : WordTrace (prefixWord ++ tailWord_7554259) baseStart_7554259 baseEnd_7554259 := by
    simpa [prefixWord, tailWord_7554259, baseEnd_7554259] using wordTrace_append hprefix tailTrace_7554259
  have hstable : (prefixWord ++ tailWord_7554259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554259).length < 2 ^ (prefixWord ++ tailWord_7554259).sum := by decide
  have hdescent : baseEnd_7554259 < baseStart_7554259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554334 : List Nat := [4, 3, 2, 1, 3, 1, 1, 3, 5]
def baseStart_7554334 : Nat := 118140960795 + 7554334 * 2 ^ 59
def prefixEnd_7554334 : Nat := 4983230072969 + 3 ^ 40 * 7554334 * 2
def baseEnd_7554334 : Nat := 431000485178016874131473

theorem tailTrace_7554334 : CollatzResearch.WordTrace tailWord_7554334 prefixEnd_7554334 431000485178016874131473 := by
  unfold tailWord_7554334
  simp only [CollatzResearch.WordTrace]
  refine ⟨34441149576743196297003757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183686131075963713584020037 34441149576743196297003757)
  ·
    refine ⟨12915431091278698611376409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34441149576743196297003757 12915431091278698611376409)
    ·
      refine ⟨9686573318459023958532307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12915431091278698611376409 9686573318459023958532307)
      ·
        refine ⟨14529859977688535937798461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9686573318459023958532307 14529859977688535937798461)
        ·
          refine ⟨5448697491633200976674423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14529859977688535937798461 5448697491633200976674423)
          ·
            refine ⟨8173046237449801465011635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5448697491633200976674423 8173046237449801465011635)
            ·
              refine ⟨12259569356174702197517453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8173046237449801465011635 12259569356174702197517453)
              ·
                refine ⟨4597338508565513324069045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12259569356174702197517453 4597338508565513324069045)
                ·
                  refine ⟨431000485178016874131473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4597338508565513324069045 431000485178016874131473)
                  ·
                    rfl

theorem cell23_7554334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_7554334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554334 prefixEnd_7554334 := by exact prefixLift 7554334
  have htrace : WordTrace (prefixWord ++ tailWord_7554334) baseStart_7554334 baseEnd_7554334 := by
    simpa [prefixWord, tailWord_7554334, baseEnd_7554334] using wordTrace_append hprefix tailTrace_7554334
  have hstable : (prefixWord ++ tailWord_7554334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554334).length < 2 ^ (prefixWord ++ tailWord_7554334).sum := by decide
  have hdescent : baseEnd_7554334 < baseStart_7554334 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554339 : List Nat := [1, 1, 1, 4, 2, 3, 1, 2, 8]
def baseStart_7554339 : Nat := 118140960795 + 7554339 * 2 ^ 59
def prefixEnd_7554339 : Nat := 4983230072969 + 3 ^ 40 * 7554339 * 2
def baseEnd_7554339 : Nat := 431000770445047149735637

theorem tailTrace_7554339 : CollatzResearch.WordTrace tailWord_7554339 prefixEnd_7554339 431000770445047149735637 := by
  unfold tailWord_7554339
  simp only [CollatzResearch.WordTrace]
  refine ⟨275529378978927456229962071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183686252652618304153308047 275529378978927456229962071)
  ·
    refine ⟨413294068468391184344943107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275529378978927456229962071 413294068468391184344943107)
    ·
      refine ⟨619941102702586776517414661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413294068468391184344943107 619941102702586776517414661)
      ·
        refine ⟨116238956756735020597015249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 619941102702586776517414661 116238956756735020597015249)
        ·
          refine ⟨87179217567551265447761437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116238956756735020597015249 87179217567551265447761437)
          ·
            refine ⟨32692206587831724542910539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87179217567551265447761437 32692206587831724542910539)
            ·
              refine ⟨49038309881747586814365809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32692206587831724542910539 49038309881747586814365809)
              ·
                refine ⟨36778732411310690110774357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49038309881747586814365809 36778732411310690110774357)
                ·
                  refine ⟨431000770445047149735637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36778732411310690110774357 431000770445047149735637)
                  ·
                    rfl

theorem cell23_7554339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 8].length) (baseStart_7554339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554339 prefixEnd_7554339 := by exact prefixLift 7554339
  have htrace : WordTrace (prefixWord ++ tailWord_7554339) baseStart_7554339 baseEnd_7554339 := by
    simpa [prefixWord, tailWord_7554339, baseEnd_7554339] using wordTrace_append hprefix tailTrace_7554339
  have hstable : (prefixWord ++ tailWord_7554339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554339).length < 2 ^ (prefixWord ++ tailWord_7554339).sum := by decide
  have hdescent : baseEnd_7554339 < baseStart_7554339 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554353 : List Nat := [1, 2, 2, 3, 3, 2, 1, 2, 2, 2, 3]
def baseStart_7554353 : Nat := 118140960795 + 7554353 * 2 ^ 59
def prefixEnd_7554353 : Nat := 4983230072969 + 3 ^ 40 * 7554353 * 2
def baseEnd_7554353 : Nat := 3879014122734587292845669

theorem tailTrace_7554353 : CollatzResearch.WordTrace tailWord_7554353 prefixEnd_7554353 3879014122734587292845669 := by
  unfold tailWord_7554353
  simp only [CollatzResearch.WordTrace]
  refine ⟨275529889600876736620971713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183686593067251157747314475 275529889600876736620971713)
  ·
    refine ⟨206647417200657552465728785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275529889600876736620971713 206647417200657552465728785)
    ·
      refine ⟨154985562900493164349296589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206647417200657552465728785 154985562900493164349296589)
      ·
        refine ⟨58119586087684936630986221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154985562900493164349296589 58119586087684936630986221)
        ·
          refine ⟨21794844782881851236619833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58119586087684936630986221 21794844782881851236619833)
          ·
            refine ⟨16346133587161388427464875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21794844782881851236619833 16346133587161388427464875)
            ·
              refine ⟨24519200380742082641197313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16346133587161388427464875 24519200380742082641197313)
              ·
                refine ⟨18389400285556561980897985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24519200380742082641197313 18389400285556561980897985)
                ·
                  refine ⟨13792050214167421485673489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18389400285556561980897985 13792050214167421485673489)
                  ·
                    refine ⟨10344037660625566114255117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13792050214167421485673489 10344037660625566114255117)
                    ·
                      refine ⟨3879014122734587292845669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10344037660625566114255117 3879014122734587292845669)
                      ·
                        rfl

theorem cell23_7554353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_7554353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554353 prefixEnd_7554353 := by exact prefixLift 7554353
  have htrace : WordTrace (prefixWord ++ tailWord_7554353) baseStart_7554353 baseEnd_7554353 := by
    simpa [prefixWord, tailWord_7554353, baseEnd_7554353] using wordTrace_append hprefix tailTrace_7554353
  have hstable : (prefixWord ++ tailWord_7554353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554353).length < 2 ^ (prefixWord ++ tailWord_7554353).sum := by decide
  have hdescent : baseEnd_7554353 < baseStart_7554353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554356 : List Nat := [2, 5, 1, 1, 1, 1, 1, 3, 8]
def baseStart_7554356 : Nat := 118140960795 + 7554356 * 2 ^ 59
def prefixEnd_7554356 : Nat := 4983230072969 + 3 ^ 40 * 7554356 * 2
def baseEnd_7554356 : Nat := 431001740352950086789795

theorem tailTrace_7554356 : CollatzResearch.WordTrace tailWord_7554356 prefixEnd_7554356 431001740352950086789795 := by
  unfold tailWord_7554356
  simp only [CollatzResearch.WordTrace]
  refine ⟨137764999509932934066665461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183686666013243912088887281 137764999509932934066665461)
  ·
    refine ⟨12915468704056212568749887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137764999509932934066665461 12915468704056212568749887)
    ·
      refine ⟨19373203056084318853124831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12915468704056212568749887 19373203056084318853124831)
      ·
        refine ⟨29059804584126478279687247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19373203056084318853124831 29059804584126478279687247)
        ·
          refine ⟨43589706876189717419530871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29059804584126478279687247 43589706876189717419530871)
          ·
            refine ⟨65384560314284576129296307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43589706876189717419530871 65384560314284576129296307)
            ·
              refine ⟨98076840471426864193944461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65384560314284576129296307 98076840471426864193944461)
              ·
                refine ⟨36778815176785074072729173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98076840471426864193944461 36778815176785074072729173)
                ·
                  refine ⟨431001740352950086789795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36778815176785074072729173 431001740352950086789795)
                  ·
                    rfl

theorem cell23_7554356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_7554356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554356 prefixEnd_7554356 := by exact prefixLift 7554356
  have htrace : WordTrace (prefixWord ++ tailWord_7554356) baseStart_7554356 baseEnd_7554356 := by
    simpa [prefixWord, tailWord_7554356, baseEnd_7554356] using wordTrace_append hprefix tailTrace_7554356
  have hstable : (prefixWord ++ tailWord_7554356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554356).length < 2 ^ (prefixWord ++ tailWord_7554356).sum := by decide
  have hdescent : baseEnd_7554356 < baseStart_7554356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554393 : List Nat := [1, 2, 1, 2, 2, 2, 3, 3, 2, 3, 2]
def baseStart_7554393 : Nat := 118140960795 + 7554393 * 2 ^ 59
def prefixEnd_7554393 : Nat := 4983230072969 + 3 ^ 40 * 7554393 * 2
def baseEnd_7554393 : Nat := 3879034661960767136345485

theorem tailTrace_7554393 : CollatzResearch.WordTrace tailWord_7554393 prefixEnd_7554393 3879034661960767136345485 := by
  unfold tailWord_7554393
  simp only [CollatzResearch.WordTrace]
  refine ⟨275531348520731823452427833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183687565680487882301618555 275531348520731823452427833)
  ·
    refine ⟨206648511390548867589320875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275531348520731823452427833 206648511390548867589320875)
    ·
      refine ⟨309972767085823301383981313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206648511390548867589320875 309972767085823301383981313)
      ·
        refine ⟨232479575314367476037985985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309972767085823301383981313 232479575314367476037985985)
        ·
          refine ⟨174359681485775607028489489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232479575314367476037985985 174359681485775607028489489)
          ·
            refine ⟨130769761114331705271367117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174359681485775607028489489 130769761114331705271367117)
            ·
              refine ⟨49038660417874389476762669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130769761114331705271367117 49038660417874389476762669)
              ·
                refine ⟨18389497656702896053786001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49038660417874389476762669 18389497656702896053786001)
                ·
                  refine ⟨13792123242527172040339501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18389497656702896053786001 13792123242527172040339501)
                  ·
                    refine ⟨5172046215947689515127313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13792123242527172040339501 5172046215947689515127313)
                    ·
                      refine ⟨3879034661960767136345485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5172046215947689515127313 3879034661960767136345485)
                      ·
                        rfl

theorem cell23_7554393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 3, 2].length) (baseStart_7554393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554393 prefixEnd_7554393 := by exact prefixLift 7554393
  have htrace : WordTrace (prefixWord ++ tailWord_7554393) baseStart_7554393 baseEnd_7554393 := by
    simpa [prefixWord, tailWord_7554393, baseEnd_7554393] using wordTrace_append hprefix tailTrace_7554393
  have hstable : (prefixWord ++ tailWord_7554393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554393).length < 2 ^ (prefixWord ++ tailWord_7554393).sum := by decide
  have hdescent : baseEnd_7554393 < baseStart_7554393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554417 : List Nat := [1, 2, 2, 2, 1, 2, 6, 2, 1, 1, 3]
def baseStart_7554417 : Nat := 118140960795 + 7554417 * 2 ^ 59
def prefixEnd_7554417 : Nat := 4983230072969 + 3 ^ 40 * 7554417 * 2
def baseEnd_7554417 : Nat := 3879046985496475042445375

theorem tailTrace_7554417 : CollatzResearch.WordTrace tailWord_7554417 prefixEnd_7554417 3879046985496475042445375 := by
  unfold tailWord_7554417
  simp only [CollatzResearch.WordTrace]
  refine ⟨275532223872644875551301505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183688149248429917034201003 275532223872644875551301505)
  ·
    refine ⟨206649167904483656663476129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275532223872644875551301505 206649167904483656663476129)
    ·
      refine ⟨154986875928362742497607097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206649167904483656663476129 154986875928362742497607097)
      ·
        refine ⟨116240156946272056873205323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154986875928362742497607097 116240156946272056873205323)
        ·
          refine ⟨174360235419408085309807985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116240156946272056873205323 174360235419408085309807985)
          ·
            refine ⟨130770176564556063982355989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174360235419408085309807985 130770176564556063982355989)
            ·
              refine ⟨6129852026463565499172937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130770176564556063982355989 6129852026463565499172937)
              ·
                refine ⟨4597389019847674124379703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6129852026463565499172937 4597389019847674124379703)
                ·
                  refine ⟨6896083529771511186569555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4597389019847674124379703 6896083529771511186569555)
                  ·
                    refine ⟨10344125294657266779854333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6896083529771511186569555 10344125294657266779854333)
                    ·
                      refine ⟨3879046985496475042445375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10344125294657266779854333 3879046985496475042445375)
                      ·
                        rfl

theorem cell23_7554417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2, 1, 1, 3].length) (baseStart_7554417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554417 prefixEnd_7554417 := by exact prefixLift 7554417
  have htrace : WordTrace (prefixWord ++ tailWord_7554417) baseStart_7554417 baseEnd_7554417 := by
    simpa [prefixWord, tailWord_7554417, baseEnd_7554417] using wordTrace_append hprefix tailTrace_7554417
  have hstable : (prefixWord ++ tailWord_7554417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554417).length < 2 ^ (prefixWord ++ tailWord_7554417).sum := by decide
  have hdescent : baseEnd_7554417 < baseStart_7554417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554440 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 5, 2, 2]
def baseStart_7554440 : Nat := 118140960795 + 7554440 * 2 ^ 59
def prefixEnd_7554440 : Nat := 4983230072969 + 3 ^ 40 * 7554440 * 2
def baseEnd_7554440 : Nat := 3879058795551528452457769

theorem tailTrace_7554440 : CollatzResearch.WordTrace tailWord_7554440 prefixEnd_7554440 3879058795551528452457769 := by
  unfold tailWord_7554440
  simp only [CollatzResearch.WordTrace]
  refine ⟨137766531375780775239694387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183688708501041033652925849 137766531375780775239694387)
  ·
    refine ⟨206649797063671162859541581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137766531375780775239694387 206649797063671162859541581)
    ·
      refine ⟨77493673898876686072328093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206649797063671162859541581 77493673898876686072328093)
      ·
        refine ⟨29060127712078757277123035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77493673898876686072328093 29060127712078757277123035)
        ·
          refine ⟨43590191568118135915684553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29060127712078757277123035 43590191568118135915684553)
          ·
            refine ⟨32692643676088601936763415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43590191568118135915684553 32692643676088601936763415)
            ·
              refine ⟨49038965514132902905145123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32692643676088601936763415 49038965514132902905145123)
              ·
                refine ⟨73558448271199354357717685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49038965514132902905145123 73558448271199354357717685)
                ·
                  refine ⟨6896104525424939471036033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73558448271199354357717685 6896104525424939471036033)
                  ·
                    refine ⟨5172078394068704603277025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6896104525424939471036033 5172078394068704603277025)
                    ·
                      refine ⟨3879058795551528452457769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5172078394068704603277025 3879058795551528452457769)
                      ·
                        rfl

theorem cell23_7554440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_7554440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554440 prefixEnd_7554440 := by exact prefixLift 7554440
  have htrace : WordTrace (prefixWord ++ tailWord_7554440) baseStart_7554440 baseEnd_7554440 := by
    simpa [prefixWord, tailWord_7554440, baseEnd_7554440] using wordTrace_append hprefix tailTrace_7554440
  have hstable : (prefixWord ++ tailWord_7554440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554440).length < 2 ^ (prefixWord ++ tailWord_7554440).sum := by decide
  have hdescent : baseEnd_7554440 < baseStart_7554440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554443 : List Nat := [1, 1, 1, 1, 4, 3, 2, 4, 1, 2, 3]
def baseStart_7554443 : Nat := 118140960795 + 7554443 * 2 ^ 59
def prefixEnd_7554443 : Nat := 4983230072969 + 3 ^ 40 * 7554443 * 2
def baseEnd_7554443 : Nat := 3879060335993491940720255

theorem tailTrace_7554443 : CollatzResearch.WordTrace tailWord_7554443 prefixEnd_7554443 3879060335993491940720255 := by
  unfold tailWord_7554443
  simp only [CollatzResearch.WordTrace]
  refine ⟨275533172170550681991747983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183688781447033787994498655 275533172170550681991747983)
  ·
    refine ⟨413299758255826022987621975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275533172170550681991747983 413299758255826022987621975)
    ·
      refine ⟨619949637383739034481432963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413299758255826022987621975 619949637383739034481432963)
      ·
        refine ⟨929924456075608551722149445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619949637383739034481432963 929924456075608551722149445)
        ·
          refine ⟨174360835514176603447903021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 929924456075608551722149445 174360835514176603447903021)
          ·
            refine ⟨65385313317816226292963633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174360835514176603447903021 65385313317816226292963633)
            ·
              refine ⟨49038984988362169719722725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65385313317816226292963633 49038984988362169719722725)
              ·
                refine ⟨9194809685317906822448011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49038984988362169719722725 9194809685317906822448011)
                ·
                  refine ⟨13792214527976860233672017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9194809685317906822448011 13792214527976860233672017)
                  ·
                    refine ⟨10344160895982645175254013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13792214527976860233672017 10344160895982645175254013)
                    ·
                      refine ⟨3879060335993491940720255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10344160895982645175254013 3879060335993491940720255)
                      ·
                        rfl

theorem cell23_7554443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 2, 3].length) (baseStart_7554443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554443 prefixEnd_7554443 := by exact prefixLift 7554443
  have htrace : WordTrace (prefixWord ++ tailWord_7554443) baseStart_7554443 baseEnd_7554443 := by
    simpa [prefixWord, tailWord_7554443, baseEnd_7554443] using wordTrace_append hprefix tailTrace_7554443
  have hstable : (prefixWord ++ tailWord_7554443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554443).length < 2 ^ (prefixWord ++ tailWord_7554443).sum := by decide
  have hdescent : baseEnd_7554443 < baseStart_7554443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554457 : List Nat := [1, 2, 1, 2, 1, 5, 1, 5, 1, 2, 2]
def baseStart_7554457 : Nat := 118140960795 + 7554457 * 2 ^ 59
def prefixEnd_7554457 : Nat := 4983230072969 + 3 ^ 40 * 7554457 * 2
def baseEnd_7554457 : Nat := 3879067524722654885945191

theorem tailTrace_7554457 : CollatzResearch.WordTrace tailWord_7554457 prefixEnd_7554457 3879067524722654885945191 := by
  unfold tailWord_7554457
  simp only [CollatzResearch.WordTrace]
  refine ⟨275533682792499962382757625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183689121861666641588505083 275533682792499962382757625)
  ·
    refine ⟨206650262094374971787068219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275533682792499962382757625 206650262094374971787068219)
    ·
      refine ⟨309975393141562457680602329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206650262094374971787068219 309975393141562457680602329)
      ·
        refine ⟨232481544856171843260451747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309975393141562457680602329 232481544856171843260451747)
        ·
          refine ⟨348722317284257764890677621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232481544856171843260451747 348722317284257764890677621)
          ·
            refine ⟨32692717245399165458501027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 348722317284257764890677621 32692717245399165458501027)
            ·
              refine ⟨49039075868098748187751541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32692717245399165458501027 49039075868098748187751541)
              ·
                refine ⟨4597413362634257642601707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49039075868098748187751541 4597413362634257642601707)
                ·
                  refine ⟨6896120043951386463902561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4597413362634257642601707 6896120043951386463902561)
                  ·
                    refine ⟨5172090032963539847926921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6896120043951386463902561 5172090032963539847926921)
                    ·
                      refine ⟨3879067524722654885945191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5172090032963539847926921 3879067524722654885945191)
                      ·
                        rfl

theorem cell23_7554457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5, 1, 2, 2].length) (baseStart_7554457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554457 prefixEnd_7554457 := by exact prefixLift 7554457
  have htrace : WordTrace (prefixWord ++ tailWord_7554457) baseStart_7554457 baseEnd_7554457 := by
    simpa [prefixWord, tailWord_7554457, baseEnd_7554457] using wordTrace_append hprefix tailTrace_7554457
  have hstable : (prefixWord ++ tailWord_7554457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554457).length < 2 ^ (prefixWord ++ tailWord_7554457).sum := by decide
  have hdescent : baseEnd_7554457 < baseStart_7554457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554483 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 5, 3, 2]
def baseStart_7554483 : Nat := 118140960795 + 7554483 * 2 ^ 59
def prefixEnd_7554483 : Nat := 4983230072969 + 3 ^ 40 * 7554483 * 2
def baseEnd_7554483 : Nat := 3879080875219671784220071

theorem tailTrace_7554483 : CollatzResearch.WordTrace tailWord_7554483 prefixEnd_7554483 3879080875219671784220071 := by
  unfold tailWord_7554483
  simp only [CollatzResearch.WordTrace]
  refine ⟨275534631090405768823204103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183689754060270512548802735 275534631090405768823204103)
  ·
    refine ⟨413301946635608653234806155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275534631090405768823204103 413301946635608653234806155)
    ·
      refine ⟨619952919953412979852209233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413301946635608653234806155 619952919953412979852209233)
      ·
        refine ⟨464964689965059734889156925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 619952919953412979852209233 464964689965059734889156925)
        ·
          refine ⟨174361758736897400583433847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 464964689965059734889156925 174361758736897400583433847)
          ·
            refine ⟨261542638105346100875150771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174361758736897400583433847 261542638105346100875150771)
            ·
              refine ⟨392313957158019151312726157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261542638105346100875150771 392313957158019151312726157)
              ·
                refine ⟨147117733934257181742272309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 392313957158019151312726157 147117733934257181742272309)
                ·
                  refine ⟨13792287556336610788338029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147117733934257181742272309 13792287556336610788338029)
                  ·
                    refine ⟨5172107833626229045626761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13792287556336610788338029 5172107833626229045626761)
                    ·
                      refine ⟨3879080875219671784220071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5172107833626229045626761 3879080875219671784220071)
                      ·
                        rfl

theorem cell23_7554483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 3, 2].length) (baseStart_7554483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554483 prefixEnd_7554483 := by exact prefixLift 7554483
  have htrace : WordTrace (prefixWord ++ tailWord_7554483) baseStart_7554483 baseEnd_7554483 := by
    simpa [prefixWord, tailWord_7554483, baseEnd_7554483] using wordTrace_append hprefix tailTrace_7554483
  have hstable : (prefixWord ++ tailWord_7554483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554483).length < 2 ^ (prefixWord ++ tailWord_7554483).sum := by decide
  have hdescent : baseEnd_7554483 < baseStart_7554483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554496 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 4]
def baseStart_7554496 : Nat := 118140960795 + 7554496 * 2 ^ 59
def prefixEnd_7554496 : Nat := 4983230072969 + 3 ^ 40 * 7554496 * 2
def baseEnd_7554496 : Nat := 3879087550468180233357511

theorem tailTrace_7554496 : CollatzResearch.WordTrace tailWord_7554496 prefixEnd_7554496 3879087550468180233357511 := by
  unfold tailWord_7554496
  simp only [CollatzResearch.WordTrace]
  refine ⟨137767552619679336021713671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183690070159572448028951561 137767552619679336021713671)
  ·
    refine ⟨206651328929519004032570507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137767552619679336021713671 206651328929519004032570507)
    ·
      refine ⟨309976993394278506048855761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206651328929519004032570507 309976993394278506048855761)
      ·
        refine ⟨232482745045708879536641821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309976993394278506048855761 232482745045708879536641821)
        ·
          refine ⟨87181029392140829826240683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232482745045708879536641821 87181029392140829826240683)
          ·
            refine ⟨130771544088211244739361025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87181029392140829826240683 130771544088211244739361025)
            ·
              refine ⟨98078658066158433554520769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130771544088211244739361025 98078658066158433554520769)
              ·
                refine ⟨73558993549618825165890577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98078658066158433554520769 73558993549618825165890577)
                ·
                  refine ⟨55169245162214118874417933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73558993549618825165890577 55169245162214118874417933)
                  ·
                    refine ⟨20688466935830294577906725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55169245162214118874417933 20688466935830294577906725)
                    ·
                      refine ⟨3879087550468180233357511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20688466935830294577906725 3879087550468180233357511)
                      ·
                        rfl

theorem cell23_7554496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_7554496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554496 prefixEnd_7554496 := by exact prefixLift 7554496
  have htrace : WordTrace (prefixWord ++ tailWord_7554496) baseStart_7554496 baseEnd_7554496 := by
    simpa [prefixWord, tailWord_7554496, baseEnd_7554496] using wordTrace_append hprefix tailTrace_7554496
  have hstable : (prefixWord ++ tailWord_7554496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554496).length < 2 ^ (prefixWord ++ tailWord_7554496).sum := by decide
  have hdescent : baseEnd_7554496 < baseStart_7554496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554541 : List Nat := [1, 5, 1, 3, 2, 2, 2, 1, 2, 1, 3]
def baseStart_7554541 : Nat := 118140960795 + 7554541 * 2 ^ 59
def prefixEnd_7554541 : Nat := 4983230072969 + 3 ^ 40 * 7554541 * 2
def baseEnd_7554541 : Nat := 3879110657097632557294805

theorem tailTrace_7554541 : CollatzResearch.WordTrace tailWord_7554541 prefixEnd_7554541 3879110657097632557294805 := by
  unfold tailWord_7554541
  simp only [CollatzResearch.WordTrace]
  refine ⟨275536746524195644728815477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183691164349463763152543651 275536746524195644728815477)
  ·
    refine ⟨25831569986643341693326451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 275536746524195644728815477 25831569986643341693326451)
    ·
      refine ⟨38747354979965012539989677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25831569986643341693326451 38747354979965012539989677)
      ·
        refine ⟨14530258117486879702496129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38747354979965012539989677 14530258117486879702496129)
        ·
          refine ⟨10897693588115159776872097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14530258117486879702496129 10897693588115159776872097)
          ·
            refine ⟨8173270191086369832654073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10897693588115159776872097 8173270191086369832654073)
            ·
              refine ⟨6129952643314777374490555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8173270191086369832654073 6129952643314777374490555)
              ·
                refine ⟨9194928964972166061735833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6129952643314777374490555 9194928964972166061735833)
                ·
                  refine ⟨6896196723729124546301875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9194928964972166061735833 6896196723729124546301875)
                  ·
                    refine ⟨10344295085593686819452813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6896196723729124546301875 10344295085593686819452813)
                    ·
                      refine ⟨3879110657097632557294805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10344295085593686819452813 3879110657097632557294805)
                      ·
                        rfl

theorem cell23_7554541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_7554541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554541 prefixEnd_7554541 := by exact prefixLift 7554541
  have htrace : WordTrace (prefixWord ++ tailWord_7554541) baseStart_7554541 baseEnd_7554541 := by
    simpa [prefixWord, tailWord_7554541, baseEnd_7554541] using wordTrace_append hprefix tailTrace_7554541
  have hstable : (prefixWord ++ tailWord_7554541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554541).length < 2 ^ (prefixWord ++ tailWord_7554541).sum := by decide
  have hdescent : baseEnd_7554541 < baseStart_7554541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554593 : List Nat := [1, 2, 3, 2, 2, 2, 2, 1, 1, 2, 5]
def baseStart_7554593 : Nat := 118140960795 + 7554593 * 2 ^ 59
def prefixEnd_7554593 : Nat := 4983230072969 + 3 ^ 40 * 7554593 * 2
def baseEnd_7554593 : Nat := 3879137358091666353844565

theorem tailTrace_7554593 : CollatzResearch.WordTrace tailWord_7554593 prefixEnd_7554593 3879137358091666353844565 := by
  unfold tailWord_7554593
  simp only [CollatzResearch.WordTrace]
  refine ⟨275538643120007257609708433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183692428746671505073138955 275538643120007257609708433)
  ·
    refine ⟨206653982340005443207281325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275538643120007257609708433 206653982340005443207281325)
    ·
      refine ⟨77495243377502041202730497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206653982340005443207281325 77495243377502041202730497)
      ·
        refine ⟨58121432533126530902047873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77495243377502041202730497 58121432533126530902047873)
        ·
          refine ⟨43591074399844898176535905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58121432533126530902047873 43591074399844898176535905)
          ·
            refine ⟨32693305799883673632401929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43591074399844898176535905 32693305799883673632401929)
            ·
              refine ⟨24519979349912755224301447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32693305799883673632401929 24519979349912755224301447)
              ·
                refine ⟨36779969024869132836452171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24519979349912755224301447 36779969024869132836452171)
                ·
                  refine ⟨55169953537303699254678257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36779969024869132836452171 55169953537303699254678257)
                  ·
                    refine ⟨41377465152977774441008693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55169953537303699254678257 41377465152977774441008693)
                    ·
                      refine ⟨3879137358091666353844565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41377465152977774441008693 3879137358091666353844565)
                      ·
                        rfl

theorem cell23_7554593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_7554593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554593 prefixEnd_7554593 := by exact prefixLift 7554593
  have htrace : WordTrace (prefixWord ++ tailWord_7554593) baseStart_7554593 baseEnd_7554593 := by
    simpa [prefixWord, tailWord_7554593, baseEnd_7554593] using wordTrace_append hprefix tailTrace_7554593
  have hstable : (prefixWord ++ tailWord_7554593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554593).length < 2 ^ (prefixWord ++ tailWord_7554593).sum := by decide
  have hdescent : baseEnd_7554593 < baseStart_7554593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554620 : List Nat := [2, 2, 2, 2, 4, 1, 1, 1, 1, 3, 4]
def baseStart_7554620 : Nat := 118140960795 + 7554620 * 2 ^ 59
def prefixEnd_7554620 : Nat := 4983230072969 + 3 ^ 40 * 7554620 * 2
def baseEnd_7554620 : Nat := 3879151222069337748206941

theorem tailTrace_7554620 : CollatzResearch.WordTrace tailWord_7554620 prefixEnd_7554620 3879151222069337748206941 := by
  unfold tailWord_7554620
  simp only [CollatzResearch.WordTrace]
  refine ⟨137769813945454720610470657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183693085260606294147294209 137769813945454720610470657)
  ·
    refine ⟨103327360459091040457852993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137769813945454720610470657 103327360459091040457852993)
    ·
      refine ⟨77495520344318280343389745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103327360459091040457852993 77495520344318280343389745)
      ·
        refine ⟨58121640258238710257542309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77495520344318280343389745 58121640258238710257542309)
        ·
          refine ⟨10897807548419758173289183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58121640258238710257542309 10897807548419758173289183)
          ·
            refine ⟨16346711322629637259933775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10897807548419758173289183 16346711322629637259933775)
            ·
              refine ⟨24520066983944455889900663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16346711322629637259933775 24520066983944455889900663)
              ·
                refine ⟨36780100475916683834850995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24520066983944455889900663 36780100475916683834850995)
                ·
                  refine ⟨55170150713875025752276493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36780100475916683834850995 55170150713875025752276493)
                  ·
                    refine ⟨20688806517703134657103685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55170150713875025752276493 20688806517703134657103685)
                    ·
                      refine ⟨3879151222069337748206941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20688806517703134657103685 3879151222069337748206941)
                      ·
                        rfl

theorem cell23_7554620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_7554620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554620 prefixEnd_7554620 := by exact prefixLift 7554620
  have htrace : WordTrace (prefixWord ++ tailWord_7554620) baseStart_7554620 baseEnd_7554620 := by
    simpa [prefixWord, tailWord_7554620, baseEnd_7554620] using wordTrace_append hprefix tailTrace_7554620
  have hstable : (prefixWord ++ tailWord_7554620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554620).length < 2 ^ (prefixWord ++ tailWord_7554620).sum := by decide
  have hdescent : baseEnd_7554620 < baseStart_7554620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554647 : List Nat := [1, 1, 3, 2, 2, 3, 2, 4, 1, 4]
def baseStart_7554647 : Nat := 118140960795 + 7554647 * 2 ^ 59
def prefixEnd_7554647 : Nat := 4983230072969 + 3 ^ 40 * 7554647 * 2
def baseEnd_7554647 : Nat := 1293055028682336380856439

theorem tailTrace_7554647 : CollatzResearch.WordTrace tailWord_7554647 prefixEnd_7554647 1293055028682336380856439 := by
  unfold tailWord_7554647
  simp only [CollatzResearch.WordTrace]
  refine ⟨275540612661811624832174195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183693741774541083221449463 275540612661811624832174195)
  ·
    refine ⟨413310918992717437248261293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275540612661811624832174195 413310918992717437248261293)
    ·
      refine ⟨154991594622269038968097985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413310918992717437248261293 154991594622269038968097985)
      ·
        refine ⟨116243695966701779226073489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154991594622269038968097985 116243695966701779226073489)
        ·
          refine ⟨87182771975026334419555117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116243695966701779226073489 87182771975026334419555117)
          ·
            refine ⟨32693539490634875407333169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87182771975026334419555117 32693539490634875407333169)
            ·
              refine ⟨24520154617976156555499877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32693539490634875407333169 24520154617976156555499877)
              ·
                refine ⟨4597528990870529354156227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24520154617976156555499877 4597528990870529354156227)
                ·
                  refine ⟨6896293486305794031234341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4597528990870529354156227 6896293486305794031234341)
                  ·
                    refine ⟨1293055028682336380856439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6896293486305794031234341 1293055028682336380856439)
                    ·
                      rfl

theorem cell23_7554647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4, 1, 4].length) (baseStart_7554647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554647 prefixEnd_7554647 := by exact prefixLift 7554647
  have htrace : WordTrace (prefixWord ++ tailWord_7554647) baseStart_7554647 baseEnd_7554647 := by
    simpa [prefixWord, tailWord_7554647, baseEnd_7554647] using wordTrace_append hprefix tailTrace_7554647
  have hstable : (prefixWord ++ tailWord_7554647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554647).length < 2 ^ (prefixWord ++ tailWord_7554647).sum := by decide
  have hdescent : baseEnd_7554647 < baseStart_7554647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554673 : List Nat := [1, 2, 2, 2, 1, 1, 1, 5, 3, 5]
def baseStart_7554673 : Nat := 118140960795 + 7554673 * 2 ^ 59
def prefixEnd_7554673 : Nat := 4983230072969 + 3 ^ 40 * 7554673 * 2
def baseEnd_7554673 : Nat := 1293059478848008680281399

theorem tailTrace_7554673 : CollatzResearch.WordTrace tailWord_7554673 prefixEnd_7554673 1293059478848008680281399 := by
  unfold tailWord_7554673
  simp only [CollatzResearch.WordTrace]
  refine ⟨275541560959717431272620673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183694373973144954181747115 275541560959717431272620673)
  ·
    refine ⟨206656170719788073454465505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275541560959717431272620673 206656170719788073454465505)
    ·
      refine ⟨154992128039841055090849129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206656170719788073454465505 154992128039841055090849129)
      ·
        refine ⟨116244096029880791318136847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154992128039841055090849129 116244096029880791318136847)
        ·
          refine ⟨174366144044821186977205271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116244096029880791318136847 174366144044821186977205271)
          ·
            refine ⟨261549216067231780465807907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174366144044821186977205271 261549216067231780465807907)
            ·
              refine ⟨392323824100847670698711861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261549216067231780465807907 392323824100847670698711861)
              ·
                refine ⟨36780358509454469128004237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 392323824100847670698711861 36780358509454469128004237)
                ·
                  refine ⟨13792634441045425923001589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36780358509454469128004237 13792634441045425923001589)
                  ·
                    refine ⟨1293059478848008680281399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13792634441045425923001589 1293059478848008680281399)
                    ·
                      rfl

theorem cell23_7554673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 5].length) (baseStart_7554673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554673 prefixEnd_7554673 := by exact prefixLift 7554673
  have htrace : WordTrace (prefixWord ++ tailWord_7554673) baseStart_7554673 baseEnd_7554673 := by
    simpa [prefixWord, tailWord_7554673, baseEnd_7554673] using wordTrace_append hprefix tailTrace_7554673
  have hstable : (prefixWord ++ tailWord_7554673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554673).length < 2 ^ (prefixWord ++ tailWord_7554673).sum := by decide
  have hdescent : baseEnd_7554673 < baseStart_7554673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554713 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 3, 1, 5]
def baseStart_7554713 : Nat := 118140960795 + 7554713 * 2 ^ 59
def prefixEnd_7554713 : Nat := 4983230072969 + 3 ^ 40 * 7554713 * 2
def baseEnd_7554713 : Nat := 3879198975770205884344013

theorem tailTrace_7554713 : CollatzResearch.WordTrace tailWord_7554713 prefixEnd_7554713 3879198975770205884344013 := by
  unfold tailWord_7554713
  simp only [CollatzResearch.WordTrace]
  refine ⟨275543019879572518104076793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183695346586381678736051195 275543019879572518104076793)
  ·
    refine ⟨206657264909679388578057595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275543019879572518104076793 206657264909679388578057595)
    ·
      refine ⟨309985897364519082867086393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206657264909679388578057595 309985897364519082867086393)
      ·
        refine ⟨232489423023389312150314795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309985897364519082867086393 232489423023389312150314795)
        ·
          refine ⟨348734134535083968225472193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232489423023389312150314795 348734134535083968225472193)
          ·
            refine ⟨261550600901312976169104145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348734134535083968225472193 261550600901312976169104145)
            ·
              refine ⟨196162950675984732126828109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261550600901312976169104145 196162950675984732126828109)
              ·
                refine ⟨73561106503494274547560541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196162950675984732126828109 73561106503494274547560541)
                ·
                  refine ⟨27585414938810352955335203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73561106503494274547560541 27585414938810352955335203)
                  ·
                    refine ⟨41378122408215529433002805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27585414938810352955335203 41378122408215529433002805)
                    ·
                      refine ⟨3879198975770205884344013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41378122408215529433002805 3879198975770205884344013)
                      ·
                        rfl

theorem cell23_7554713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_7554713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554713 prefixEnd_7554713 := by exact prefixLift 7554713
  have htrace : WordTrace (prefixWord ++ tailWord_7554713) baseStart_7554713 baseEnd_7554713 := by
    simpa [prefixWord, tailWord_7554713, baseEnd_7554713] using wordTrace_append hprefix tailTrace_7554713
  have hstable : (prefixWord ++ tailWord_7554713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554713).length < 2 ^ (prefixWord ++ tailWord_7554713).sum := by decide
  have hdescent : baseEnd_7554713 < baseStart_7554713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554723 : List Nat := [1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 6]
def baseStart_7554723 : Nat := 118140960795 + 7554723 * 2 ^ 59
def prefixEnd_7554723 : Nat := 4983230072969 + 3 ^ 40 * 7554723 * 2
def baseEnd_7554723 : Nat := 3879204110576750845218967

theorem tailTrace_7554723 : CollatzResearch.WordTrace tailWord_7554723 prefixEnd_7554723 3879204110576750845218967 := by
  unfold tailWord_7554723
  simp only [CollatzResearch.WordTrace]
  refine ⟨275543384609536289811940823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183695589739690859874627215 275543384609536289811940823)
  ·
    refine ⟨413315076914304434717911235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275543384609536289811940823 413315076914304434717911235)
    ·
      refine ⟨619972615371456652076866853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413315076914304434717911235 619972615371456652076866853)
      ·
        refine ⟨116244865382148122264412535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 619972615371456652076866853 116244865382148122264412535)
        ·
          refine ⟨174367298073222183396618803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116244865382148122264412535 174367298073222183396618803)
          ·
            refine ⟨261550947109833275094928205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174367298073222183396618803 261550947109833275094928205)
            ·
              refine ⟨98081605166187478160598077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261550947109833275094928205 98081605166187478160598077)
              ·
                refine ⟨36780601937320304310224279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98081605166187478160598077 36780601937320304310224279)
                ·
                  refine ⟨55170902905980456465336419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36780601937320304310224279 55170902905980456465336419)
                  ·
                    refine ⟨82756354358970684698004629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55170902905980456465336419 82756354358970684698004629)
                    ·
                      refine ⟨3879204110576750845218967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82756354358970684698004629 3879204110576750845218967)
                      ·
                        rfl

theorem cell23_7554723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_7554723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554723 prefixEnd_7554723 := by exact prefixLift 7554723
  have htrace : WordTrace (prefixWord ++ tailWord_7554723) baseStart_7554723 baseEnd_7554723 := by
    simpa [prefixWord, tailWord_7554723, baseEnd_7554723] using wordTrace_append hprefix tailTrace_7554723
  have hstable : (prefixWord ++ tailWord_7554723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554723).length < 2 ^ (prefixWord ++ tailWord_7554723).sum := by decide
  have hdescent : baseEnd_7554723 < baseStart_7554723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554760 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 3, 3, 3]
def baseStart_7554760 : Nat := 118140960795 + 7554760 * 2 ^ 59
def prefixEnd_7554760 : Nat := 4983230072969 + 3 ^ 40 * 7554760 * 2
def baseEnd_7554760 : Nat := 3879223109360967200456297

theorem tailTrace_7554760 : CollatzResearch.WordTrace tailWord_7554760 prefixEnd_7554760 3879223109360967200456297 := by
  unfold tailWord_7554760
  simp only [CollatzResearch.WordTrace]
  refine ⟨137772367055201122565518867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183696489406934830087358489 137772367055201122565518867)
  ·
    refine ⟨206658550582801683848278301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137772367055201122565518867 206658550582801683848278301)
    ·
      refine ⟨77496956468550631443104363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206658550582801683848278301 77496956468550631443104363)
      ·
        refine ⟨116245434702825947164656545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77496956468550631443104363 116245434702825947164656545)
        ·
          refine ⟨87184076027119460373492409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116245434702825947164656545 87184076027119460373492409)
          ·
            refine ⟨65388057020339595280119307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87184076027119460373492409 65388057020339595280119307)
            ·
              refine ⟨98082085530509392920178961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65388057020339595280119307 98082085530509392920178961)
              ·
                refine ⟨73561564147882044690134221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98082085530509392920178961 73561564147882044690134221)
                ·
                  refine ⟨27585586555455766758800333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73561564147882044690134221 27585586555455766758800333)
                  ·
                    refine ⟨10344594958295912534550125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27585586555455766758800333 10344594958295912534550125)
                    ·
                      refine ⟨3879223109360967200456297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10344594958295912534550125 3879223109360967200456297)
                      ·
                        rfl

theorem cell23_7554760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_7554760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554760 prefixEnd_7554760 := by exact prefixLift 7554760
  have htrace : WordTrace (prefixWord ++ tailWord_7554760) baseStart_7554760 baseEnd_7554760 := by
    simpa [prefixWord, tailWord_7554760, baseEnd_7554760] using wordTrace_append hprefix tailTrace_7554760
  have hstable : (prefixWord ++ tailWord_7554760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554760).length < 2 ^ (prefixWord ++ tailWord_7554760).sum := by decide
  have hdescent : baseEnd_7554760 < baseStart_7554760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554777 : List Nat := [1, 2, 1, 2, 3, 4, 2, 1, 1, 3, 3]
def baseStart_7554777 : Nat := 118140960795 + 7554777 * 2 ^ 59
def prefixEnd_7554777 : Nat := 4983230072969 + 3 ^ 40 * 7554777 * 2
def baseEnd_7554777 : Nat := 3879231838532093633943719

theorem tailTrace_7554777 : CollatzResearch.WordTrace tailWord_7554777 prefixEnd_7554777 3879231838532093633943719 := by
  unfold tailWord_7554777
  simp only [CollatzResearch.WordTrace]
  refine ⟨275545354151340657034406585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183696902767560438022937723 275545354151340657034406585)
  ·
    refine ⟨206659015613505492775804939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275545354151340657034406585 206659015613505492775804939)
    ·
      refine ⟨309988523420258239163707409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206659015613505492775804939 309988523420258239163707409)
      ·
        refine ⟨232491392565193679372780557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309988523420258239163707409 232491392565193679372780557)
        ·
          refine ⟨87184272211947629764792709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232491392565193679372780557 87184272211947629764792709)
          ·
            refine ⟨16347051039740180580898633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87184272211947629764792709 16347051039740180580898633)
            ·
              refine ⟨12260288279805135435673975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16347051039740180580898633 12260288279805135435673975)
              ·
                refine ⟨18390432419707703153510963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12260288279805135435673975 18390432419707703153510963)
                ·
                  refine ⟨27585648629561554730266445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18390432419707703153510963 27585648629561554730266445)
                  ·
                    refine ⟨10344618236085583023849917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27585648629561554730266445 10344618236085583023849917)
                    ·
                      refine ⟨3879231838532093633943719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10344618236085583023849917 3879231838532093633943719)
                      ·
                        rfl

theorem cell23_7554777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 3, 3].length) (baseStart_7554777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554777 prefixEnd_7554777 := by exact prefixLift 7554777
  have htrace : WordTrace (prefixWord ++ tailWord_7554777) baseStart_7554777 baseEnd_7554777 := by
    simpa [prefixWord, tailWord_7554777, baseEnd_7554777] using wordTrace_append hprefix tailTrace_7554777
  have hstable : (prefixWord ++ tailWord_7554777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554777).length < 2 ^ (prefixWord ++ tailWord_7554777).sum := by decide
  have hdescent : baseEnd_7554777 < baseStart_7554777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554793 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 3, 8]
def baseStart_7554793 : Nat := 118140960795 + 7554793 * 2 ^ 59
def prefixEnd_7554793 : Nat := 4983230072969 + 3 ^ 40 * 7554793 * 2
def baseEnd_7554793 : Nat := 1293080018074188523781215

theorem tailTrace_7554793 : CollatzResearch.WordTrace tailWord_7554793 prefixEnd_7554793 1293080018074188523781215 := by
  unfold tailWord_7554793
  simp only [CollatzResearch.WordTrace]
  refine ⟨275545937719282691766989033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183697291812855127844659355 275545937719282691766989033)
  ·
    refine ⟨206659453289462018825241775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275545937719282691766989033 206659453289462018825241775)
    ·
      refine ⟨309989179934193028237862663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206659453289462018825241775 309989179934193028237862663)
      ·
        refine ⟨464983769901289542356793995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309989179934193028237862663 464983769901289542356793995)
        ·
          refine ⟨697475654851934313535190993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464983769901289542356793995 697475654851934313535190993)
          ·
            refine ⟨523106741138950735151393245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 697475654851934313535190993 523106741138950735151393245)
            ·
              refine ⟨196165027927106525681772467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 523106741138950735151393245 196165027927106525681772467)
              ·
                refine ⟨294247541890659788522658701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196165027927106525681772467 294247541890659788522658701)
                ·
                  refine ⟨110342828208997420695997013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294247541890659788522658701 110342828208997420695997013)
                  ·
                    refine ⟨1293080018074188523781215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110342828208997420695997013 1293080018074188523781215)
                    ·
                      rfl

theorem cell23_7554793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 8].length) (baseStart_7554793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554793 prefixEnd_7554793 := by exact prefixLift 7554793
  have htrace : WordTrace (prefixWord ++ tailWord_7554793) baseStart_7554793 baseEnd_7554793 := by
    simpa [prefixWord, tailWord_7554793, baseEnd_7554793] using wordTrace_append hprefix tailTrace_7554793
  have hstable : (prefixWord ++ tailWord_7554793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554793).length < 2 ^ (prefixWord ++ tailWord_7554793).sum := by decide
  have hdescent : baseEnd_7554793 < baseStart_7554793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554817 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 3, 4, 2]
def baseStart_7554817 : Nat := 118140960795 + 7554817 * 2 ^ 59
def prefixEnd_7554817 : Nat := 4983230072969 + 3 ^ 40 * 7554817 * 2
def baseEnd_7554817 : Nat := 3879252377758273477443535

theorem tailTrace_7554817 : CollatzResearch.WordTrace tailWord_7554817 prefixEnd_7554817 3879252377758273477443535 := by
  unfold tailWord_7554817
  simp only [CollatzResearch.WordTrace]
  refine ⟨275546813071195743865862705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183697875380797162577241803 275546813071195743865862705)
  ·
    refine ⟨206660109803396807899397029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275546813071195743865862705 206660109803396807899397029)
    ·
      refine ⟨38748770588136901481136943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206660109803396807899397029 38748770588136901481136943)
      ·
        refine ⟨58123155882205352221705415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38748770588136901481136943 58123155882205352221705415)
        ·
          refine ⟨87184733823308028332558123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58123155882205352221705415 87184733823308028332558123)
          ·
            refine ⟨130777100734962042498837185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87184733823308028332558123 130777100734962042498837185)
            ·
              refine ⟨98082825551221531874127889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130777100734962042498837185 98082825551221531874127889)
              ·
                refine ⟨73562119163416148905595917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98082825551221531874127889 73562119163416148905595917)
                ·
                  refine ⟨27585794686281055839598469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73562119163416148905595917 27585794686281055839598469)
                  ·
                    refine ⟨5172336503677697969924713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27585794686281055839598469 5172336503677697969924713)
                    ·
                      refine ⟨3879252377758273477443535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5172336503677697969924713 3879252377758273477443535)
                      ·
                        rfl

theorem cell23_7554817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_7554817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554817 prefixEnd_7554817 := by exact prefixLift 7554817
  have htrace : WordTrace (prefixWord ++ tailWord_7554817) baseStart_7554817 baseEnd_7554817 := by
    simpa [prefixWord, tailWord_7554817, baseEnd_7554817] using wordTrace_append hprefix tailTrace_7554817
  have hstable : (prefixWord ++ tailWord_7554817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554817).length < 2 ^ (prefixWord ++ tailWord_7554817).sum := by decide
  have hdescent : baseEnd_7554817 < baseStart_7554817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554822 : List Nat := [6, 2, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_7554822 : Nat := 118140960795 + 7554822 * 2 ^ 59
def prefixEnd_7554822 : Nat := 4983230072969 + 3 ^ 40 * 7554822 * 2
def baseEnd_7554822 : Nat := 1293084981720515319293671

theorem tailTrace_7554822 : CollatzResearch.WordTrace tailWord_7554822 prefixEnd_7554822 1293084981720515319293671 := by
  unfold tailWord_7554822
  simp only [CollatzResearch.WordTrace]
  refine ⟨8610843607380550928743585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 183697996957451753146529813 8610843607380550928743585)
  ·
    refine ⟨6458132705535413196557689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8610843607380550928743585 6458132705535413196557689)
    ·
      refine ⟨4843599529151559897418267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6458132705535413196557689 4843599529151559897418267)
      ·
        refine ⟨7265399293727339846127401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4843599529151559897418267 7265399293727339846127401)
        ·
          refine ⟨5449049470295504884595551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7265399293727339846127401 5449049470295504884595551)
          ·
            refine ⟨8173574205443257326893327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5449049470295504884595551 8173574205443257326893327)
            ·
              refine ⟨12260361308164885990339991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8173574205443257326893327 12260361308164885990339991)
              ·
                refine ⟨18390541962247328985509987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12260361308164885990339991 18390541962247328985509987)
                ·
                  refine ⟨27585812943370993478264981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18390541962247328985509987 27585812943370993478264981)
                  ·
                    refine ⟨1293084981720515319293671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27585812943370993478264981 1293084981720515319293671)
                    ·
                      rfl

theorem cell23_7554822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_7554822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554822 prefixEnd_7554822 := by exact prefixLift 7554822
  have htrace : WordTrace (prefixWord ++ tailWord_7554822) baseStart_7554822 baseEnd_7554822 := by
    simpa [prefixWord, tailWord_7554822, baseEnd_7554822] using wordTrace_append hprefix tailTrace_7554822
  have hstable : (prefixWord ++ tailWord_7554822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554822).length < 2 ^ (prefixWord ++ tailWord_7554822).sum := by decide
  have hdescent : baseEnd_7554822 < baseStart_7554822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554840 : List Nat := [2, 1, 2, 3, 1, 1, 4, 2, 7]
def baseStart_7554840 : Nat := 118140960795 + 7554840 * 2 ^ 59
def prefixEnd_7554840 : Nat := 4983230072969 + 3 ^ 40 * 7554840 * 2
def baseEnd_7554840 : Nat := 431029354201480765272881

theorem tailTrace_7554840 : CollatzResearch.WordTrace tailWord_7554840 prefixEnd_7554840 431029354201480765272881 := by
  unfold tailWord_7554840
  simp only [CollatzResearch.WordTrace]
  refine ⟨137773825975056209396974987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183698434633408279195966649 137773825975056209396974987)
  ·
    refine ⟨206660738962584314095462481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137773825975056209396974987 206660738962584314095462481)
    ·
      refine ⟨154995554221938235571596861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206660738962584314095462481 154995554221938235571596861)
      ·
        refine ⟨58123332833226838339348823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154995554221938235571596861 58123332833226838339348823)
        ·
          refine ⟨87184999249840257509023235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58123332833226838339348823 87184999249840257509023235)
          ·
            refine ⟨130777498874760386263534853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87184999249840257509023235 130777498874760386263534853)
            ·
              refine ⟨24520781039017572424412785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130777498874760386263534853 24520781039017572424412785)
              ·
                refine ⟨18390585779263179318309589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24520781039017572424412785 18390585779263179318309589)
                ·
                  refine ⟨431029354201480765272881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18390585779263179318309589 431029354201480765272881)
                  ·
                    rfl

theorem cell23_7554840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 7].length) (baseStart_7554840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554840 prefixEnd_7554840 := by exact prefixLift 7554840
  have htrace : WordTrace (prefixWord ++ tailWord_7554840) baseStart_7554840 baseEnd_7554840 := by
    simpa [prefixWord, tailWord_7554840, baseEnd_7554840] using wordTrace_append hprefix tailTrace_7554840
  have hstable : (prefixWord ++ tailWord_7554840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554840).length < 2 ^ (prefixWord ++ tailWord_7554840).sum := by decide
  have hdescent : baseEnd_7554840 < baseStart_7554840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554947 : List Nat := [1, 1, 1, 3, 4, 2, 2, 3, 6]
def baseStart_7554947 : Nat := 118140960795 + 7554947 * 2 ^ 59
def prefixEnd_7554947 : Nat := 4983230072969 + 3 ^ 40 * 7554947 * 2
def baseEnd_7554947 : Nat := 431035458915928663201993

theorem tailTrace_7554947 : CollatzResearch.WordTrace tailWord_7554947 prefixEnd_7554947 431035458915928663201993 := by
  unfold tailWord_7554947
  simp only [CollatzResearch.WordTrace]
  refine ⟨275551554560724776068095095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183701036373816517378730063 275551554560724776068095095)
  ·
    refine ⟨413327331841087164102142643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275551554560724776068095095 413327331841087164102142643)
    ·
      refine ⟨619990997761630746153213965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413327331841087164102142643 619990997761630746153213965)
      ·
        refine ⟨232496624160611529807455237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 619990997761630746153213965 232496624160611529807455237)
        ·
          refine ⟨43593117030114661838897857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232496624160611529807455237 43593117030114661838897857)
          ·
            refine ⟨32694837772585996379173393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43593117030114661838897857 32694837772585996379173393)
            ·
              refine ⟨24521128329439497284380045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32694837772585996379173393 24521128329439497284380045)
              ·
                refine ⟨9195423123539811481642517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24521128329439497284380045 9195423123539811481642517)
                ·
                  refine ⟨431035458915928663201993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9195423123539811481642517 431035458915928663201993)
                  ·
                    rfl

theorem cell23_7554947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 6].length) (baseStart_7554947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554947 prefixEnd_7554947 := by exact prefixLift 7554947
  have htrace : WordTrace (prefixWord ++ tailWord_7554947) baseStart_7554947 baseEnd_7554947 := by
    simpa [prefixWord, tailWord_7554947, baseEnd_7554947] using wordTrace_append hprefix tailTrace_7554947
  have hstable : (prefixWord ++ tailWord_7554947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554947).length < 2 ^ (prefixWord ++ tailWord_7554947).sum := by decide
  have hdescent : baseEnd_7554947 < baseStart_7554947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554958 : List Nat := [4, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4]
def baseStart_7554958 : Nat := 118140960795 + 7554958 * 2 ^ 59
def prefixEnd_7554958 : Nat := 4983230072969 + 3 ^ 40 * 7554958 * 2
def baseEnd_7554958 : Nat := 3879324778530557425780387

theorem tailTrace_7554958 : CollatzResearch.WordTrace tailWord_7554958 prefixEnd_7554958 3879324778530557425780387 := by
  unfold tailWord_7554958
  simp only [CollatzResearch.WordTrace]
  refine ⟨34443994470460615618343191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183701303842456616631163685 34443994470460615618343191)
  ·
    refine ⟨51665991705690923427514787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34443994470460615618343191 51665991705690923427514787)
    ·
      refine ⟨77498987558536385141272181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51665991705690923427514787 77498987558536385141272181)
      ·
        refine ⟨7265530083612786106994267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77498987558536385141272181 7265530083612786106994267)
        ·
          refine ⟨10898295125419179160491401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7265530083612786106994267 10898295125419179160491401)
          ·
            refine ⟨8173721344064384370368551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10898295125419179160491401 8173721344064384370368551)
            ·
              refine ⟨12260582016096576555552827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8173721344064384370368551 12260582016096576555552827)
              ·
                refine ⟨18390873024144864833329241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12260582016096576555552827 18390873024144864833329241)
                ·
                  refine ⟨13793154768108648624996931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18390873024144864833329241 13793154768108648624996931)
                  ·
                    refine ⟨20689732152162972937495397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13793154768108648624996931 20689732152162972937495397)
                    ·
                      refine ⟨3879324778530557425780387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20689732152162972937495397 3879324778530557425780387)
                      ·
                        rfl

theorem cell23_7554958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_7554958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554958 prefixEnd_7554958 := by exact prefixLift 7554958
  have htrace : WordTrace (prefixWord ++ tailWord_7554958) baseStart_7554958 baseEnd_7554958 := by
    simpa [prefixWord, tailWord_7554958, baseEnd_7554958] using wordTrace_append hprefix tailTrace_7554958
  have hstable : (prefixWord ++ tailWord_7554958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554958).length < 2 ^ (prefixWord ++ tailWord_7554958).sum := by decide
  have hdescent : baseEnd_7554958 < baseStart_7554958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7554991 : List Nat := [1, 1, 2, 1, 2, 2, 3, 6, 1, 1, 3]
def baseStart_7554991 : Nat := 118140960795 + 7554991 * 2 ^ 59
def prefixEnd_7554991 : Nat := 4983230072969 + 3 ^ 40 * 7554991 * 2
def baseEnd_7554991 : Nat := 3879341723392155796667735

theorem tailTrace_7554991 : CollatzResearch.WordTrace tailWord_7554991 prefixEnd_7554991 3879341723392155796667735 := by
  unfold tailWord_7554991
  simp only [CollatzResearch.WordTrace]
  refine ⟨275553159372565371582696827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183702106248376914388464551 275553159372565371582696827)
  ·
    refine ⟨413329739058848057374045241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275553159372565371582696827 413329739058848057374045241)
    ·
      refine ⟨309997304294136043030533931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413329739058848057374045241 309997304294136043030533931)
      ·
        refine ⟨464995956441204064545800897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309997304294136043030533931 464995956441204064545800897)
        ·
          refine ⟨348746967330903048409350673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464995956441204064545800897 348746967330903048409350673)
          ·
            refine ⟨261560225498177286307013005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348746967330903048409350673 261560225498177286307013005)
            ·
              refine ⟨98085084561816482365129877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261560225498177286307013005 98085084561816482365129877)
              ·
                refine ⟨4597738338835147610865463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98085084561816482365129877 4597738338835147610865463)
                ·
                  refine ⟨6896607508252721416298195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4597738338835147610865463 6896607508252721416298195)
                  ·
                    refine ⟨10344911262379082124447293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6896607508252721416298195 10344911262379082124447293)
                    ·
                      refine ⟨3879341723392155796667735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10344911262379082124447293 3879341723392155796667735)
                      ·
                        rfl

theorem cell23_7554991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6, 1, 1, 3].length) (baseStart_7554991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7554991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7554991 prefixEnd_7554991 := by exact prefixLift 7554991
  have htrace : WordTrace (prefixWord ++ tailWord_7554991) baseStart_7554991 baseEnd_7554991 := by
    simpa [prefixWord, tailWord_7554991, baseEnd_7554991] using wordTrace_append hprefix tailTrace_7554991
  have hstable : (prefixWord ++ tailWord_7554991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7554991).length < 2 ^ (prefixWord ++ tailWord_7554991).sum := by decide
  have hdescent : baseEnd_7554991 < baseStart_7554991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7554991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555042 : List Nat := [3, 3, 3, 1, 3, 1, 1, 1, 3, 1, 3]
def baseStart_7555042 : Nat := 118140960795 + 7555042 * 2 ^ 59
def prefixEnd_7555042 : Nat := 4983230072969 + 3 ^ 40 * 7555042 * 2
def baseEnd_7555042 : Nat := 3879367910905535097130001

theorem tailTrace_7555042 : CollatzResearch.WordTrace tailWord_7555042 prefixEnd_7555042 3879367910905535097130001 := by
  unfold tailWord_7555042
  simp only [CollatzResearch.WordTrace]
  refine ⟨68888754873845151823200845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183703346330253738195202253 68888754873845151823200845)
  ·
    refine ⟨25833283077691931933700317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68888754873845151823200845 25833283077691931933700317)
    ·
      refine ⟨9687481154134474475137619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25833283077691931933700317 9687481154134474475137619)
      ·
        refine ⟨14531221731201711712706429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9687481154134474475137619 14531221731201711712706429)
        ·
          refine ⟨5449208149200641892264911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14531221731201711712706429 5449208149200641892264911)
          ·
            refine ⟨8173812223800962838397367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5449208149200641892264911 8173812223800962838397367)
            ·
              refine ⟨12260718335701444257596051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8173812223800962838397367 12260718335701444257596051)
              ·
                refine ⟨18391077503552166386394077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12260718335701444257596051 18391077503552166386394077)
                ·
                  refine ⟨6896654063832062394897779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18391077503552166386394077 6896654063832062394897779)
                  ·
                    refine ⟨10344981095748093592346669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6896654063832062394897779 10344981095748093592346669)
                    ·
                      refine ⟨3879367910905535097130001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10344981095748093592346669 3879367910905535097130001)
                      ·
                        rfl

theorem cell23_7555042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_7555042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555042 prefixEnd_7555042 := by exact prefixLift 7555042
  have htrace : WordTrace (prefixWord ++ tailWord_7555042) baseStart_7555042 baseEnd_7555042 := by
    simpa [prefixWord, tailWord_7555042, baseEnd_7555042] using wordTrace_append hprefix tailTrace_7555042
  have hstable : (prefixWord ++ tailWord_7555042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555042).length < 2 ^ (prefixWord ++ tailWord_7555042).sum := by decide
  have hdescent : baseEnd_7555042 < baseStart_7555042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555054 : List Nat := [4, 1, 2, 1, 3, 2, 2, 8]
def baseStart_7555054 : Nat := 118140960795 + 7555054 * 2 ^ 59
def prefixEnd_7555054 : Nat := 4983230072969 + 3 ^ 40 * 7555054 * 2
def baseEnd_7555054 : Nat := 143680521210125520377035

theorem tailTrace_7555054 : CollatzResearch.WordTrace tailWord_7555054 prefixEnd_7555054 143680521210125520377035 := by
  unfold tailWord_7555054
  simp only [CollatzResearch.WordTrace]
  refine ⟨34444432146417141667780027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183703638114224755561493477 34444432146417141667780027)
  ·
    refine ⟨51666648219625712501670041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34444432146417141667780027 51666648219625712501670041)
    ·
      refine ⟨38749986164719284376252531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51666648219625712501670041 38749986164719284376252531)
      ·
        refine ⟨58124979247078926564378797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38749986164719284376252531 58124979247078926564378797)
        ·
          refine ⟨21796867217654597461642049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58124979247078926564378797 21796867217654597461642049)
          ·
            refine ⟨16347650413240948096231537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21796867217654597461642049 16347650413240948096231537)
            ·
              refine ⟨12260737809930711072173653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16347650413240948096231537 12260737809930711072173653)
              ·
                refine ⟨143680521210125520377035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12260737809930711072173653 143680521210125520377035)
                ·
                  rfl

theorem cell23_7555054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 8].length) (baseStart_7555054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555054 prefixEnd_7555054 := by exact prefixLift 7555054
  have htrace : WordTrace (prefixWord ++ tailWord_7555054) baseStart_7555054 baseEnd_7555054 := by
    simpa [prefixWord, tailWord_7555054, baseEnd_7555054] using wordTrace_append hprefix tailTrace_7555054
  have hstable : (prefixWord ++ tailWord_7555054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555054).length < 2 ^ (prefixWord ++ tailWord_7555054).sum := by decide
  have hdescent : baseEnd_7555054 < baseStart_7555054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555091 : List Nat := [1, 1, 1, 2, 1, 4, 2, 5, 1, 3, 2]
def baseStart_7555091 : Nat := 118140960795 + 7555091 * 2 ^ 59
def prefixEnd_7555091 : Nat := 4983230072969 + 3 ^ 40 * 7555091 * 2
def baseEnd_7555091 : Nat := 3879393071457605405417275

theorem tailTrace_7555091 : CollatzResearch.WordTrace tailWord_7555091 prefixEnd_7555091 3879393071457605405417275 := by
  unfold tailWord_7555091
  simp only [CollatzResearch.WordTrace]
  refine ⟨275556806672203088661337127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183704537781468725774224751 275556806672203088661337127)
  ·
    refine ⟨413335210008304632992005691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275556806672203088661337127 413335210008304632992005691)
    ·
      refine ⟨620002815012456949488008537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413335210008304632992005691 620002815012456949488008537)
      ·
        refine ⟨465002111259342712116006403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 620002815012456949488008537 465002111259342712116006403)
        ·
          refine ⟨697503166889014068174009605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465002111259342712116006403 697503166889014068174009605)
          ·
            refine ⟨130781843791690137782626801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 697503166889014068174009605 130781843791690137782626801)
            ·
              refine ⟨98086382843767603336970101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130781843791690137782626801 98086382843767603336970101)
              ·
                refine ⟨9195598391603212812840947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98086382843767603336970101 9195598391603212812840947)
                ·
                  refine ⟨13793397587404819219261421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9195598391603212812840947 13793397587404819219261421)
                  ·
                    refine ⟨5172524095276807207223033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13793397587404819219261421 5172524095276807207223033)
                    ·
                      refine ⟨3879393071457605405417275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5172524095276807207223033 3879393071457605405417275)
                      ·
                        rfl

theorem cell23_7555091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 3, 2].length) (baseStart_7555091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555091 prefixEnd_7555091 := by exact prefixLift 7555091
  have htrace : WordTrace (prefixWord ++ tailWord_7555091) baseStart_7555091 baseEnd_7555091 := by
    simpa [prefixWord, tailWord_7555091, baseEnd_7555091] using wordTrace_append hprefix tailTrace_7555091
  have hstable : (prefixWord ++ tailWord_7555091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555091).length < 2 ^ (prefixWord ++ tailWord_7555091).sum := by decide
  have hdescent : baseEnd_7555091 < baseStart_7555091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555097 : List Nat := [1, 2, 1, 2, 1, 1, 3, 4, 2, 6]
def baseStart_7555097 : Nat := 118140960795 + 7555097 * 2 ^ 59
def prefixEnd_7555097 : Nat := 4983230072969 + 3 ^ 40 * 7555097 * 2
def baseEnd_7555097 : Nat := 1293132050780510793980749

theorem tailTrace_7555097 : CollatzResearch.WordTrace tailWord_7555097 prefixEnd_7555097 1293132050780510793980749 := by
  unfold tailWord_7555097
  simp only [CollatzResearch.WordTrace]
  refine ⟨275557025510181351686055545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183704683673454234457370363 275557025510181351686055545)
  ·
    refine ⟨206667769132636013764541659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275557025510181351686055545 206667769132636013764541659)
    ·
      refine ⟨310001653698954020646812489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206667769132636013764541659 310001653698954020646812489)
      ·
        refine ⟨232501240274215515485109367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310001653698954020646812489 232501240274215515485109367)
        ·
          refine ⟨348751860411323273227664051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232501240274215515485109367 348751860411323273227664051)
          ·
            refine ⟨523127790616984909841496077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348751860411323273227664051 523127790616984909841496077)
            ·
              refine ⟨196172921481369341190561029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 523127790616984909841496077 196172921481369341190561029)
              ·
                refine ⟨36782422777756751473230193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196172921481369341190561029 36782422777756751473230193)
                ·
                  refine ⟨27586817083317563604922645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36782422777756751473230193 27586817083317563604922645)
                  ·
                    refine ⟨1293132050780510793980749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27586817083317563604922645 1293132050780510793980749)
                    ·
                      rfl

theorem cell23_7555097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 6].length) (baseStart_7555097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555097 prefixEnd_7555097 := by exact prefixLift 7555097
  have htrace : WordTrace (prefixWord ++ tailWord_7555097) baseStart_7555097 baseEnd_7555097 := by
    simpa [prefixWord, tailWord_7555097, baseEnd_7555097] using wordTrace_append hprefix tailTrace_7555097
  have hstable : (prefixWord ++ tailWord_7555097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555097).length < 2 ^ (prefixWord ++ tailWord_7555097).sum := by decide
  have hdescent : baseEnd_7555097 < baseStart_7555097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555098 : List Nat := [3, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3]
def baseStart_7555098 : Nat := 118140960795 + 7555098 * 2 ^ 59
def prefixEnd_7555098 : Nat := 4983230072969 + 3 ^ 40 * 7555098 * 2
def baseEnd_7555098 : Nat := 3879396665822186878029743

theorem tailTrace_7555098 : CollatzResearch.WordTrace tailWord_7555098 prefixEnd_7555098 3879396665822186878029743 := by
  unfold tailWord_7555098
  simp only [CollatzResearch.WordTrace]
  refine ⟨68889265495794432214210487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183704707988785152571227965 68889265495794432214210487)
  ·
    refine ⟨103333898243691648321315731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68889265495794432214210487 103333898243691648321315731)
    ·
      refine ⟨155000847365537472481973597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103333898243691648321315731 155000847365537472481973597)
      ·
        refine ⟨58125317762076552180740099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155000847365537472481973597 58125317762076552180740099)
        ·
          refine ⟨87187976643114828271110149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58125317762076552180740099 87187976643114828271110149)
          ·
            refine ⟨16347745620584030300833153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87187976643114828271110149 16347745620584030300833153)
            ·
              refine ⟨12260809215438022725624865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16347745620584030300833153 12260809215438022725624865)
              ·
                refine ⟨9195606911578517044218649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12260809215438022725624865 9195606911578517044218649)
                ·
                  refine ⟨6896705183683887783163987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9195606911578517044218649 6896705183683887783163987)
                  ·
                    refine ⟨10345057775525831674745981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6896705183683887783163987 10345057775525831674745981)
                    ·
                      refine ⟨3879396665822186878029743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10345057775525831674745981 3879396665822186878029743)
                      ·
                        rfl

theorem cell23_7555098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_7555098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555098 prefixEnd_7555098 := by exact prefixLift 7555098
  have htrace : WordTrace (prefixWord ++ tailWord_7555098) baseStart_7555098 baseEnd_7555098 := by
    simpa [prefixWord, tailWord_7555098, baseEnd_7555098] using wordTrace_append hprefix tailTrace_7555098
  have hstable : (prefixWord ++ tailWord_7555098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555098).length < 2 ^ (prefixWord ++ tailWord_7555098).sum := by decide
  have hdescent : baseEnd_7555098 < baseStart_7555098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555114 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 1, 8]
def baseStart_7555114 : Nat := 118140960795 + 7555114 * 2 ^ 59
def prefixEnd_7555114 : Nat := 4983230072969 + 3 ^ 40 * 7555114 * 2
def baseEnd_7555114 : Nat := 1293134960504219605143223

theorem tailTrace_7555114 : CollatzResearch.WordTrace tailWord_7555114 prefixEnd_7555114 1293134960504219605143223 := by
  unfold tailWord_7555114
  simp only [CollatzResearch.WordTrace]
  refine ⟨68889411387779940897356099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183705097034079842392949597 68889411387779940897356099)
  ·
    refine ⟨103334117081669911346034149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68889411387779940897356099 103334117081669911346034149)
    ·
      refine ⟨19375146952813108377381403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103334117081669911346034149 19375146952813108377381403)
      ·
        refine ⟨29062720429219662566072105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19375146952813108377381403 29062720429219662566072105)
        ·
          refine ⟨21797040321914746924554079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29062720429219662566072105 21797040321914746924554079)
          ·
            refine ⟨32695560482872120386831119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21797040321914746924554079 32695560482872120386831119)
            ·
              refine ⟨49043340724308180580246679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32695560482872120386831119 49043340724308180580246679)
              ·
                refine ⟨73565011086462270870370019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49043340724308180580246679 73565011086462270870370019)
                ·
                  refine ⟨110347516629693406305555029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73565011086462270870370019 110347516629693406305555029)
                  ·
                    refine ⟨1293134960504219605143223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110347516629693406305555029 1293134960504219605143223)
                    ·
                      rfl

theorem cell23_7555114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_7555114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555114 prefixEnd_7555114 := by exact prefixLift 7555114
  have htrace : WordTrace (prefixWord ++ tailWord_7555114) baseStart_7555114 baseEnd_7555114 := by
    simpa [prefixWord, tailWord_7555114, baseEnd_7555114] using wordTrace_append hprefix tailTrace_7555114
  have hstable : (prefixWord ++ tailWord_7555114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555114).length < 2 ^ (prefixWord ++ tailWord_7555114).sum := by decide
  have hdescent : baseEnd_7555114 < baseStart_7555114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555121 : List Nat := [1, 2, 2, 3, 1, 3, 1, 3, 1, 4, 2]
def baseStart_7555121 : Nat := 118140960795 + 7555121 * 2 ^ 59
def prefixEnd_7555121 : Nat := 4983230072969 + 3 ^ 40 * 7555121 * 2
def baseEnd_7555121 : Nat := 3879408475877240288042137

theorem tailTrace_7555121 : CollatzResearch.WordTrace tailWord_7555121 prefixEnd_7555121 3879408475877240288042137 := by
  unfold tailWord_7555121
  simp only [CollatzResearch.WordTrace]
  refine ⟨275557900862094403784929217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183705267241396269189952811 275557900862094403784929217)
  ·
    refine ⟨206668425646570802838696913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275557900862094403784929217 206668425646570802838696913)
    ·
      refine ⟨155001319234928102129022685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206668425646570802838696913 155001319234928102129022685)
      ·
        refine ⟨58125494713098038298383507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155001319234928102129022685 58125494713098038298383507)
        ·
          refine ⟨87188242069647057447575261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58125494713098038298383507 87188242069647057447575261)
          ·
            refine ⟨32695590776117646542840723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87188242069647057447575261 32695590776117646542840723)
            ·
              refine ⟨49043386164176469814261085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32695590776117646542840723 49043386164176469814261085)
              ·
                refine ⟨18391269811566176180347907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49043386164176469814261085 18391269811566176180347907)
                ·
                  refine ⟨27586904717349264270521861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18391269811566176180347907 27586904717349264270521861)
                  ·
                    refine ⟨5172544634502987050722849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27586904717349264270521861 5172544634502987050722849)
                    ·
                      refine ⟨3879408475877240288042137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5172544634502987050722849 3879408475877240288042137)
                      ·
                        rfl

theorem cell23_7555121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_7555121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555121 prefixEnd_7555121 := by exact prefixLift 7555121
  have htrace : WordTrace (prefixWord ++ tailWord_7555121) baseStart_7555121 baseEnd_7555121 := by
    simpa [prefixWord, tailWord_7555121, baseEnd_7555121] using wordTrace_append hprefix tailTrace_7555121
  have hstable : (prefixWord ++ tailWord_7555121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555121).length < 2 ^ (prefixWord ++ tailWord_7555121).sum := by decide
  have hdescent : baseEnd_7555121 < baseStart_7555121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555127 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 9]
def baseStart_7555127 : Nat := 118140960795 + 7555127 * 2 ^ 59
def prefixEnd_7555127 : Nat := 4983230072969 + 3 ^ 40 * 7555127 * 2
def baseEnd_7555127 : Nat := 431045728529018584951901

theorem tailTrace_7555127 : CollatzResearch.WordTrace tailWord_7555127 prefixEnd_7555127 431045728529018584951901 := by
  unfold tailWord_7555127
  simp only [CollatzResearch.WordTrace]
  refine ⟨275558119700072666809647635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183705413133381777873098423 275558119700072666809647635)
  ·
    refine ⟨413337179550109000214471453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275558119700072666809647635 413337179550109000214471453)
    ·
      refine ⟨155001442331290875080426795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413337179550109000214471453 155001442331290875080426795)
      ·
        refine ⟨232502163496936312620640193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155001442331290875080426795 232502163496936312620640193)
        ·
          refine ⟨174376622622702234465480145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232502163496936312620640193 174376622622702234465480145)
          ·
            refine ⟨130782466967026675849110109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174376622622702234465480145 130782466967026675849110109)
            ·
              refine ⟨49043425112635003443416291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130782466967026675849110109 49043425112635003443416291)
              ·
                refine ⟨73565137668952505165124437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49043425112635003443416291 73565137668952505165124437)
                ·
                  refine ⟨431045728529018584951901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73565137668952505165124437 431045728529018584951901)
                  ·
                    rfl

theorem cell23_7555127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 9].length) (baseStart_7555127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555127 prefixEnd_7555127 := by exact prefixLift 7555127
  have htrace : WordTrace (prefixWord ++ tailWord_7555127) baseStart_7555127 baseEnd_7555127 := by
    simpa [prefixWord, tailWord_7555127, baseEnd_7555127] using wordTrace_append hprefix tailTrace_7555127
  have hstable : (prefixWord ++ tailWord_7555127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555127).length < 2 ^ (prefixWord ++ tailWord_7555127).sum := by decide
  have hdescent : baseEnd_7555127 < baseStart_7555127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555194 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4]
def baseStart_7555194 : Nat := 118140960795 + 7555194 * 2 ^ 59
def prefixEnd_7555194 : Nat := 4983230072969 + 3 ^ 40 * 7555194 * 2
def baseEnd_7555194 : Nat := 3879445959965018502429301

theorem tailTrace_7555194 : CollatzResearch.WordTrace tailWord_7555194 prefixEnd_7555194 3879445959965018502429301 := by
  unfold tailWord_7555194
  simp only [CollatzResearch.WordTrace]
  refine ⟨68890140847707484313084159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183707042260553291501557757 68890140847707484313084159)
  ·
    refine ⟨103335211271561226469626239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68890140847707484313084159 103335211271561226469626239)
    ·
      refine ⟨155002816907341839704439359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103335211271561226469626239 155002816907341839704439359)
      ·
        refine ⟨232504225361012759556659039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155002816907341839704439359 232504225361012759556659039)
        ·
          refine ⟨348756338041519139334988559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232504225361012759556659039 348756338041519139334988559)
          ·
            refine ⟨523134507062278709002482839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348756338041519139334988559 523134507062278709002482839)
            ·
              refine ⟨784701760593418063503724259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523134507062278709002482839 784701760593418063503724259)
              ·
                refine ⟨1177052640890127095255586389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 784701760593418063503724259 1177052640890127095255586389)
                ·
                  refine ⟨13793585635431176897526403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1177052640890127095255586389 13793585635431176897526403)
                  ·
                    refine ⟨20690378453146765346289605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13793585635431176897526403 20690378453146765346289605)
                    ·
                      refine ⟨3879445959965018502429301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20690378453146765346289605 3879445959965018502429301)
                      ·
                        rfl

theorem cell23_7555194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_7555194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555194 prefixEnd_7555194 := by exact prefixLift 7555194
  have htrace : WordTrace (prefixWord ++ tailWord_7555194) baseStart_7555194 baseEnd_7555194 := by
    simpa [prefixWord, tailWord_7555194, baseEnd_7555194] using wordTrace_append hprefix tailTrace_7555194
  have hstable : (prefixWord ++ tailWord_7555194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555194).length < 2 ^ (prefixWord ++ tailWord_7555194).sum := by decide
  have hdescent : baseEnd_7555194 < baseStart_7555194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555268 : List Nat := [2, 3, 3, 1, 2, 2, 2, 2, 6]
def baseStart_7555268 : Nat := 118140960795 + 7555268 * 2 ^ 59
def prefixEnd_7555268 : Nat := 4983230072969 + 3 ^ 40 * 7555268 * 2
def baseEnd_7555268 : Nat := 431053773059272356989329

theorem tailTrace_7555268 : CollatzResearch.WordTrace tailWord_7555268 prefixEnd_7555268 431053773059272356989329 := by
  unfold tailWord_7555268
  simp only [CollatzResearch.WordTrace]
  refine ⟨137781631196280923945265229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183708841595041231927020305 137781631196280923945265229)
  ·
    refine ⟨51668111698605346479474461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137781631196280923945265229 51668111698605346479474461)
    ·
      refine ⟨19375541886977004929802923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51668111698605346479474461 19375541886977004929802923)
      ·
        refine ⟨29063312830465507394704385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19375541886977004929802923 29063312830465507394704385)
        ·
          refine ⟨21797484622849130546028289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29063312830465507394704385 21797484622849130546028289)
          ·
            refine ⟨16348113467136847909521217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21797484622849130546028289 16348113467136847909521217)
            ·
              refine ⟨12261085100352635932140913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16348113467136847909521217 12261085100352635932140913)
              ·
                refine ⟨9195813825264476949105685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12261085100352635932140913 9195813825264476949105685)
                ·
                  refine ⟨431053773059272356989329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9195813825264476949105685 431053773059272356989329)
                  ·
                    rfl

theorem cell23_7555268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 6].length) (baseStart_7555268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555268 prefixEnd_7555268 := by exact prefixLift 7555268
  have htrace : WordTrace (prefixWord ++ tailWord_7555268) baseStart_7555268 baseEnd_7555268 := by
    simpa [prefixWord, tailWord_7555268, baseEnd_7555268] using wordTrace_append hprefix tailTrace_7555268
  have hstable : (prefixWord ++ tailWord_7555268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555268).length < 2 ^ (prefixWord ++ tailWord_7555268).sum := by decide
  have hdescent : baseEnd_7555268 < baseStart_7555268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555271 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 5, 5, 2]
def baseStart_7555271 : Nat := 118140960795 + 7555271 * 2 ^ 59
def prefixEnd_7555271 : Nat := 4983230072969 + 3 ^ 40 * 7555271 * 2
def baseEnd_7555271 : Nat := 3879485497975414701166447

theorem tailTrace_7555271 : CollatzResearch.WordTrace tailWord_7555271 prefixEnd_7555271 3879485497975414701166447 := by
  unfold tailWord_7555271
  simp only [CollatzResearch.WordTrace]
  refine ⟨275563371811550979402889667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183708914541033986268593111 275563371811550979402889667)
  ·
    refine ⟨413345057717326469104334501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275563371811550979402889667 413345057717326469104334501)
    ·
      refine ⟨77502198321998712957062719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 413345057717326469104334501 77502198321998712957062719)
      ·
        refine ⟨116253297482998069435594079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77502198321998712957062719 116253297482998069435594079)
        ·
          refine ⟨174379946224497104153391119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116253297482998069435594079 174379946224497104153391119)
          ·
            refine ⟨261569919336745656230086679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174379946224497104153391119 261569919336745656230086679)
            ·
              refine ⟨392354879005118484345130019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261569919336745656230086679 392354879005118484345130019)
              ·
                refine ⟨588532318507677726517695029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392354879005118484345130019 588532318507677726517695029)
                ·
                  refine ⟨55174904860094786861033909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 588532318507677726517695029 55174904860094786861033909)
                  ·
                    refine ⟨5172647330633886268221929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55174904860094786861033909 5172647330633886268221929)
                    ·
                      refine ⟨3879485497975414701166447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5172647330633886268221929 3879485497975414701166447)
                      ·
                        rfl

theorem cell23_7555271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 5, 2].length) (baseStart_7555271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555271 prefixEnd_7555271 := by exact prefixLift 7555271
  have htrace : WordTrace (prefixWord ++ tailWord_7555271) baseStart_7555271 baseEnd_7555271 := by
    simpa [prefixWord, tailWord_7555271, baseEnd_7555271] using wordTrace_append hprefix tailTrace_7555271
  have hstable : (prefixWord ++ tailWord_7555271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555271).length < 2 ^ (prefixWord ++ tailWord_7555271).sum := by decide
  have hdescent : baseEnd_7555271 < baseStart_7555271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555311 : List Nat := [1, 1, 2, 1, 6, 1, 2, 2, 1, 6]
def baseStart_7555311 : Nat := 118140960795 + 7555311 * 2 ^ 59
def prefixEnd_7555311 : Nat := 4983230072969 + 3 ^ 40 * 7555311 * 2
def baseEnd_7555311 : Nat := 1293168679067198181555421

theorem tailTrace_7555311 : CollatzResearch.WordTrace tailWord_7555311 prefixEnd_7555311 1293168679067198181555421 := by
  unfold tailWord_7555311
  simp only [CollatzResearch.WordTrace]
  refine ⟨275564830731406066234345787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183709887154270710822897191 275564830731406066234345787)
  ·
    refine ⟨413347246097109099351518681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275564830731406066234345787 413347246097109099351518681)
    ·
      refine ⟨310010434572831824513639011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413347246097109099351518681 310010434572831824513639011)
      ·
        refine ⟨465015651859247736770458517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310010434572831824513639011 465015651859247736770458517)
        ·
          refine ⟨21797608680902237661115243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 465015651859247736770458517 21797608680902237661115243)
          ·
            refine ⟨32696413021353356491672865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21797608680902237661115243 32696413021353356491672865)
            ·
              refine ⟨24522309766015017368754649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32696413021353356491672865 24522309766015017368754649)
              ·
                refine ⟨18391732324511263026565987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24522309766015017368754649 18391732324511263026565987)
                ·
                  refine ⟨27587598486766894539848981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18391732324511263026565987 27587598486766894539848981)
                  ·
                    refine ⟨1293168679067198181555421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27587598486766894539848981 1293168679067198181555421)
                    ·
                      rfl

theorem cell23_7555311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 6].length) (baseStart_7555311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555311 prefixEnd_7555311 := by exact prefixLift 7555311
  have htrace : WordTrace (prefixWord ++ tailWord_7555311) baseStart_7555311 baseEnd_7555311 := by
    simpa [prefixWord, tailWord_7555311, baseEnd_7555311] using wordTrace_append hprefix tailTrace_7555311
  have hstable : (prefixWord ++ tailWord_7555311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555311).length < 2 ^ (prefixWord ++ tailWord_7555311).sum := by decide
  have hdescent : baseEnd_7555311 < baseStart_7555311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555321 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 5, 2, 3]
def baseStart_7555321 : Nat := 118140960795 + 7555321 * 2 ^ 59
def prefixEnd_7555321 : Nat := 4983230072969 + 3 ^ 40 * 7555321 * 2
def baseEnd_7555321 : Nat := 3879511172008139505541217

theorem tailTrace_7555321 : CollatzResearch.WordTrace tailWord_7555321 prefixEnd_7555321 3879511172008139505541217 := by
  unfold tailWord_7555321
  simp only [CollatzResearch.WordTrace]
  refine ⟨275565195461369837942209817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183710130307579891961473211 275565195461369837942209817)
  ·
    refine ⟨206673896596027378456657363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275565195461369837942209817 206673896596027378456657363)
    ·
      refine ⟨310010844894041067684986045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206673896596027378456657363 310010844894041067684986045)
      ·
        refine ⟨116254066835265400381869767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310010844894041067684986045 116254066835265400381869767)
        ·
          refine ⟨174381100252898100572804651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116254066835265400381869767 174381100252898100572804651)
          ·
            refine ⟨261571650379347150859206977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174381100252898100572804651 261571650379347150859206977)
            ·
              refine ⟨196178737784510363144405233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261571650379347150859206977 196178737784510363144405233)
              ·
                refine ⟨147134053338382772358303925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196178737784510363144405233 147134053338382772358303925)
                ·
                  refine ⟨13793817500473384908590993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147134053338382772358303925 13793817500473384908590993)
                  ·
                    refine ⟨10345363125355038681443245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13793817500473384908590993 10345363125355038681443245)
                    ·
                      refine ⟨3879511172008139505541217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10345363125355038681443245 3879511172008139505541217)
                      ·
                        rfl

theorem cell23_7555321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_7555321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555321 prefixEnd_7555321 := by exact prefixLift 7555321
  have htrace : WordTrace (prefixWord ++ tailWord_7555321) baseStart_7555321 baseEnd_7555321 := by
    simpa [prefixWord, tailWord_7555321, baseEnd_7555321] using wordTrace_append hprefix tailTrace_7555321
  have hstable : (prefixWord ++ tailWord_7555321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555321).length < 2 ^ (prefixWord ++ tailWord_7555321).sum := by decide
  have hdescent : baseEnd_7555321 < baseStart_7555321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555328 : List Nat := [2, 1, 1, 2, 1, 1, 7, 2, 2, 4]
def baseStart_7555328 : Nat := 118140960795 + 7555328 * 2 ^ 59
def prefixEnd_7555328 : Nat := 4983230072969 + 3 ^ 40 * 7555328 * 2
def baseEnd_7555328 : Nat := 1293171588790906992717895

theorem tailTrace_7555328 : CollatzResearch.WordTrace tailWord_7555328 prefixEnd_7555328 1293171588790906992717895 := by
  unfold tailWord_7555328
  simp only [CollatzResearch.WordTrace]
  refine ⟨137782725386172239068857319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183710300514896318758476425 137782725386172239068857319)
  ·
    refine ⟨206674088079258358603285979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137782725386172239068857319 206674088079258358603285979)
    ·
      refine ⟨310011132118887537904928969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206674088079258358603285979 310011132118887537904928969)
      ·
        refine ⟨232508349089165653428696727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310011132118887537904928969 232508349089165653428696727)
        ·
          refine ⟨348762523633748480143045091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232508349089165653428696727 348762523633748480143045091)
          ·
            refine ⟨523143785450622720214567637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348762523633748480143045091 523143785450622720214567637)
            ·
              refine ⟨12261182471498970005028929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 523143785450622720214567637 12261182471498970005028929)
              ·
                refine ⟨9195886853624227503771697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12261182471498970005028929 9195886853624227503771697)
                ·
                  refine ⟨6896915140218170627828773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9195886853624227503771697 6896915140218170627828773)
                  ·
                    refine ⟨1293171588790906992717895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6896915140218170627828773 1293171588790906992717895)
                    ·
                      rfl

theorem cell23_7555328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 2, 4].length) (baseStart_7555328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555328 prefixEnd_7555328 := by exact prefixLift 7555328
  have htrace : WordTrace (prefixWord ++ tailWord_7555328) baseStart_7555328 baseEnd_7555328 := by
    simpa [prefixWord, tailWord_7555328, baseEnd_7555328] using wordTrace_append hprefix tailTrace_7555328
  have hstable : (prefixWord ++ tailWord_7555328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555328).length < 2 ^ (prefixWord ++ tailWord_7555328).sum := by decide
  have hdescent : baseEnd_7555328 < baseStart_7555328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555345 : List Nat := [1, 2, 2, 1, 1, 6, 3, 1, 2, 4]
def baseStart_7555345 : Nat := 118140960795 + 7555345 * 2 ^ 59
def prefixEnd_7555345 : Nat := 4983230072969 + 3 ^ 40 * 7555345 * 2
def baseEnd_7555345 : Nat := 1293174498514615803880369

theorem tailTrace_7555345 : CollatzResearch.WordTrace tailWord_7555345 prefixEnd_7555345 1293174498514615803880369 := by
  unfold tailWord_7555345
  simp only [CollatzResearch.WordTrace]
  refine ⟨275566070813282890041083489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183710713875521926694055659 275566070813282890041083489)
  ·
    refine ⟨206674553109962167530812617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275566070813282890041083489 206674553109962167530812617)
    ·
      refine ⟨155005914832471625648109463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206674553109962167530812617 155005914832471625648109463)
      ·
        refine ⟨232508872248707438472164195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155005914832471625648109463 232508872248707438472164195)
        ·
          refine ⟨348763308373061157708246293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232508872248707438472164195 348763308373061157708246293)
          ·
            refine ⟨16348280079987241767574045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 348763308373061157708246293 16348280079987241767574045)
            ·
              refine ⟨6130605029995215662840267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16348280079987241767574045 6130605029995215662840267)
              ·
                refine ⟨9195907544992823494260401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6130605029995215662840267 9195907544992823494260401)
                ·
                  refine ⟨6896930658744617620695301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9195907544992823494260401 6896930658744617620695301)
                  ·
                    refine ⟨1293174498514615803880369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6896930658744617620695301 1293174498514615803880369)
                    ·
                      rfl

theorem cell23_7555345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 2, 4].length) (baseStart_7555345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555345 prefixEnd_7555345 := by exact prefixLift 7555345
  have htrace : WordTrace (prefixWord ++ tailWord_7555345) baseStart_7555345 baseEnd_7555345 := by
    simpa [prefixWord, tailWord_7555345, baseEnd_7555345] using wordTrace_append hprefix tailTrace_7555345
  have hstable : (prefixWord ++ tailWord_7555345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555345).length < 2 ^ (prefixWord ++ tailWord_7555345).sum := by decide
  have hdescent : baseEnd_7555345 < baseStart_7555345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555381 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_7555381 : Nat := 118140960795 + 7555381 * 2 ^ 59
def prefixEnd_7555381 : Nat := 4983230072969 + 3 ^ 40 * 7555381 * 2
def baseEnd_7555381 : Nat := 3879541980847409270790941

theorem tailTrace_7555381 : CollatzResearch.WordTrace tailWord_7555381 prefixEnd_7555381 3879541980847409270790941 := by
  unfold tailWord_7555381
  simp only [CollatzResearch.WordTrace]
  refine ⟨275567383841152468189393997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183711589227434978792929331 275567383841152468189393997)
  ·
    refine ⟨103337768940432175571022749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275567383841152468189393997 103337768940432175571022749)
    ·
      refine ⟨38751663352662065839133531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103337768940432175571022749 38751663352662065839133531)
      ·
        refine ⟨58127495028993098758700297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38751663352662065839133531 58127495028993098758700297)
        ·
          refine ⟨43595621271744824069025223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58127495028993098758700297 43595621271744824069025223)
          ·
            refine ⟨65393431907617236103537835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43595621271744824069025223 65393431907617236103537835)
            ·
              refine ⟨98090147861425854155306753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65393431907617236103537835 98090147861425854155306753)
              ·
                refine ⟨73567610896069390616480065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98090147861425854155306753 73567610896069390616480065)
                ·
                  refine ⟨55175708172052042962360049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73567610896069390616480065 55175708172052042962360049)
                  ·
                    refine ⟨41381781129039032221770037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55175708172052042962360049 41381781129039032221770037)
                    ·
                      refine ⟨3879541980847409270790941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41381781129039032221770037 3879541980847409270790941)
                      ·
                        rfl

theorem cell23_7555381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_7555381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555381 prefixEnd_7555381 := by exact prefixLift 7555381
  have htrace : WordTrace (prefixWord ++ tailWord_7555381) baseStart_7555381 baseEnd_7555381 := by
    simpa [prefixWord, tailWord_7555381, baseEnd_7555381] using wordTrace_append hprefix tailTrace_7555381
  have hstable : (prefixWord ++ tailWord_7555381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555381).length < 2 ^ (prefixWord ++ tailWord_7555381).sum := by decide
  have hdescent : baseEnd_7555381 < baseStart_7555381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555385 : List Nat := [1, 2, 1, 6, 1, 1, 2, 1, 4, 1, 3]
def baseStart_7555385 : Nat := 118140960795 + 7555385 * 2 ^ 59
def prefixEnd_7555385 : Nat := 4983230072969 + 3 ^ 40 * 7555385 * 2
def baseEnd_7555385 : Nat := 3879544034770027255140923

theorem tailTrace_7555385 : CollatzResearch.WordTrace tailWord_7555385 prefixEnd_7555385 3879544034770027255140923 := by
  unfold tailWord_7555385
  simp only [CollatzResearch.WordTrace]
  refine ⟨275567529733137976872539609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183711686488758651248359739 275567529733137976872539609)
  ·
    refine ⟨206675647299853482654404707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275567529733137976872539609 206675647299853482654404707)
    ·
      refine ⟨310013470949780223981607061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206675647299853482654404707 310013470949780223981607061)
      ·
        refine ⟨14531881450770947999137831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 310013470949780223981607061 14531881450770947999137831)
        ·
          refine ⟨21797822176156421998706747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14531881450770947999137831 21797822176156421998706747)
          ·
            refine ⟨32696733264234632998060121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21797822176156421998706747 32696733264234632998060121)
            ·
              refine ⟨24522549948175974748545091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32696733264234632998060121 24522549948175974748545091)
              ·
                refine ⟨36783824922263962122817637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24522549948175974748545091 36783824922263962122817637)
                ·
                  refine ⟨6896967172924492898028307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36783824922263962122817637 6896967172924492898028307)
                  ·
                    refine ⟨10345450759386739347042461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6896967172924492898028307 10345450759386739347042461)
                    ·
                      refine ⟨3879544034770027255140923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10345450759386739347042461 3879544034770027255140923)
                      ·
                        rfl

theorem cell23_7555385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_7555385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555385 prefixEnd_7555385 := by exact prefixLift 7555385
  have htrace : WordTrace (prefixWord ++ tailWord_7555385) baseStart_7555385 baseEnd_7555385 := by
    simpa [prefixWord, tailWord_7555385, baseEnd_7555385] using wordTrace_append hprefix tailTrace_7555385
  have hstable : (prefixWord ++ tailWord_7555385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555385).length < 2 ^ (prefixWord ++ tailWord_7555385).sum := by decide
  have hdescent : baseEnd_7555385 < baseStart_7555385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555391 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 4]
def baseStart_7555391 : Nat := 118140960795 + 7555391 * 2 ^ 59
def prefixEnd_7555391 : Nat := 4983230072969 + 3 ^ 40 * 7555391 * 2
def baseEnd_7555391 : Nat := 3879547115653954231665895

theorem tailTrace_7555391 : CollatzResearch.WordTrace tailWord_7555391 prefixEnd_7555391 3879547115653954231665895 := by
  unfold tailWord_7555391
  simp only [CollatzResearch.WordTrace]
  refine ⟨275567748571116239897258027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183711832380744159931505351 275567748571116239897258027)
  ·
    refine ⟨413351622856674359845887041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275567748571116239897258027 413351622856674359845887041)
    ·
      refine ⟨310013717142505769884415281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413351622856674359845887041 310013717142505769884415281)
      ·
        refine ⟨232510287856879327413311461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310013717142505769884415281 232510287856879327413311461)
        ·
          refine ⟨43595678973164873889995899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232510287856879327413311461 43595678973164873889995899)
          ·
            refine ⟨65393518459747310834993849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43595678973164873889995899 65393518459747310834993849)
            ·
              refine ⟨49045138844810483126245387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65393518459747310834993849 49045138844810483126245387)
              ·
                refine ⟨73567708267215724689368081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49045138844810483126245387 73567708267215724689368081)
                ·
                  refine ⟨55175781200411793517026061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73567708267215724689368081 55175781200411793517026061)
                  ·
                    refine ⟨20690917950154422568884773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55175781200411793517026061 20690917950154422568884773)
                    ·
                      refine ⟨3879547115653954231665895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20690917950154422568884773 3879547115653954231665895)
                      ·
                        rfl

theorem cell23_7555391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_7555391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555391 prefixEnd_7555391 := by exact prefixLift 7555391
  have htrace : WordTrace (prefixWord ++ tailWord_7555391) baseStart_7555391 baseEnd_7555391 := by
    simpa [prefixWord, tailWord_7555391, baseEnd_7555391] using wordTrace_append hprefix tailTrace_7555391
  have hstable : (prefixWord ++ tailWord_7555391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555391).length < 2 ^ (prefixWord ++ tailWord_7555391).sum := by decide
  have hdescent : baseEnd_7555391 < baseStart_7555391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555396 : List Nat := [2, 3, 4, 1, 3, 1, 2, 1, 2, 4]
def baseStart_7555396 : Nat := 118140960795 + 7555396 * 2 ^ 59
def prefixEnd_7555396 : Nat := 4983230072969 + 3 ^ 40 * 7555396 * 2
def baseEnd_7555396 : Nat := 1293183227685742237367791

theorem tailTrace_7555396 : CollatzResearch.WordTrace tailWord_7555396 prefixEnd_7555396 1293183227685742237367791 := by
  unfold tailWord_7555396
  simp only [CollatzResearch.WordTrace]
  refine ⟨137783965468049062875595021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183711953957398750500793361 137783965468049062875595021)
  ·
    refine ⟨51668987050518398578348133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137783965468049062875595021 51668987050518398578348133)
    ·
      refine ⟨9687935071972199733440275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51668987050518398578348133 9687935071972199733440275)
      ·
        refine ⟨14531902607958299600160413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9687935071972199733440275 14531902607958299600160413)
        ·
          refine ⟨5449463477984362350060155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14531902607958299600160413 5449463477984362350060155)
          ·
            refine ⟨8174195216976543525090233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5449463477984362350060155 8174195216976543525090233)
            ·
              refine ⟨6130646412732407643817675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8174195216976543525090233 6130646412732407643817675)
              ·
                refine ⟨9195969619098611465726513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6130646412732407643817675 9195969619098611465726513)
                ·
                  refine ⟨6896977214323958599294885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9195969619098611465726513 6896977214323958599294885)
                  ·
                    refine ⟨1293183227685742237367791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6896977214323958599294885 1293183227685742237367791)
                    ·
                      rfl

theorem cell23_7555396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_7555396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555396 prefixEnd_7555396 := by exact prefixLift 7555396
  have htrace : WordTrace (prefixWord ++ tailWord_7555396) baseStart_7555396 baseEnd_7555396 := by
    simpa [prefixWord, tailWord_7555396, baseEnd_7555396] using wordTrace_append hprefix tailTrace_7555396
  have hstable : (prefixWord ++ tailWord_7555396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555396).length < 2 ^ (prefixWord ++ tailWord_7555396).sum := by decide
  have hdescent : baseEnd_7555396 < baseStart_7555396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555411 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 4, 4, 3]
def baseStart_7555411 : Nat := 118140960795 + 7555411 * 2 ^ 59
def prefixEnd_7555411 : Nat := 4983230072969 + 3 ^ 40 * 7555411 * 2
def baseEnd_7555411 : Nat := 3879557385267044153415803

theorem tailTrace_7555411 : CollatzResearch.WordTrace tailWord_7555411 prefixEnd_7555411 3879557385267044153415803 := by
  unfold tailWord_7555411
  simp only [CollatzResearch.WordTrace]
  refine ⟨275568478031043783312986087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183712318687362522208657391 275568478031043783312986087)
  ·
    refine ⟨413352717046565674969479131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275568478031043783312986087 413352717046565674969479131)
    ·
      refine ⟨620029075569848512454218697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413352717046565674969479131 620029075569848512454218697)
      ·
        refine ⟨465021806677386384340664023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 620029075569848512454218697 465021806677386384340664023)
        ·
          refine ⟨697532710016079576510996035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465021806677386384340664023 697532710016079576510996035)
          ·
            refine ⟨1046299065024119364766494053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697532710016079576510996035 1046299065024119364766494053)
            ·
              refine ⟨196181074692022380893717635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1046299065024119364766494053 196181074692022380893717635)
              ·
                refine ⟨294271612038033571340576453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196181074692022380893717635 294271612038033571340576453)
                ·
                  refine ⟨55175927257131294626358085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 294271612038033571340576453 55175927257131294626358085)
                  ·
                    refine ⟨10345486360712117742442141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55175927257131294626358085 10345486360712117742442141)
                    ·
                      refine ⟨3879557385267044153415803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10345486360712117742442141 3879557385267044153415803)
                      ·
                        rfl

theorem cell23_7555411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4, 3].length) (baseStart_7555411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555411 prefixEnd_7555411 := by exact prefixLift 7555411
  have htrace : WordTrace (prefixWord ++ tailWord_7555411) baseStart_7555411 baseEnd_7555411 := by
    simpa [prefixWord, tailWord_7555411, baseEnd_7555411] using wordTrace_append hprefix tailTrace_7555411
  have hstable : (prefixWord ++ tailWord_7555411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555411).length < 2 ^ (prefixWord ++ tailWord_7555411).sum := by decide
  have hdescent : baseEnd_7555411 < baseStart_7555411 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555412 : List Nat := [2, 4, 1, 1, 2, 2, 3, 2, 1, 3, 2]
def baseStart_7555412 : Nat := 118140960795 + 7555412 * 2 ^ 59
def prefixEnd_7555412 : Nat := 4983230072969 + 3 ^ 40 * 7555412 * 2
def baseEnd_7555412 : Nat := 3879557898747698649503299

theorem tailTrace_7555412 : CollatzResearch.WordTrace tailWord_7555412 prefixEnd_7555412 3879557898747698649503299 := by
  unfold tailWord_7555412
  simp only [CollatzResearch.WordTrace]
  refine ⟨137784257252020080241886245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183712343002693440322514993 137784257252020080241886245)
  ·
    refine ⟨25834548234753765045353671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137784257252020080241886245 25834548234753765045353671)
    ·
      refine ⟨38751822352130647568030507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25834548234753765045353671 38751822352130647568030507)
      ·
        refine ⟨58127733528195971352045761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38751822352130647568030507 58127733528195971352045761)
        ·
          refine ⟨43595800146146978514034321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58127733528195971352045761 43595800146146978514034321)
          ·
            refine ⟨32696850109610233885525741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43595800146146978514034321 32696850109610233885525741)
            ·
              refine ⟨12261318791103837707072153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32696850109610233885525741 12261318791103837707072153)
              ·
                refine ⟨9195989093327878280304115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12261318791103837707072153 9195989093327878280304115)
                ·
                  refine ⟨13793983639991817420456173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9195989093327878280304115 13793983639991817420456173)
                  ·
                    refine ⟨5172743864996931532671065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13793983639991817420456173 5172743864996931532671065)
                    ·
                      refine ⟨3879557898747698649503299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5172743864996931532671065 3879557898747698649503299)
                      ·
                        rfl

theorem cell23_7555412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_7555412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555412 prefixEnd_7555412 := by exact prefixLift 7555412
  have htrace : WordTrace (prefixWord ++ tailWord_7555412) baseStart_7555412 baseEnd_7555412 := by
    simpa [prefixWord, tailWord_7555412, baseEnd_7555412] using wordTrace_append hprefix tailTrace_7555412
  have hstable : (prefixWord ++ tailWord_7555412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555412).length < 2 ^ (prefixWord ++ tailWord_7555412).sum := by decide
  have hdescent : baseEnd_7555412 < baseStart_7555412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555442 : List Nat := [3, 2, 1, 2, 1, 3, 1, 4, 2, 2, 2]
def baseStart_7555442 : Nat := 118140960795 + 7555442 * 2 ^ 59
def prefixEnd_7555442 : Nat := 4983230072969 + 3 ^ 40 * 7555442 * 2
def baseEnd_7555442 : Nat := 3879573303167333532128161

theorem tailTrace_7555442 : CollatzResearch.WordTrace tailWord_7555442 prefixEnd_7555442 3879573303167333532128161 := by
  unfold tailWord_7555442
  simp only [CollatzResearch.WordTrace]
  refine ⟨68892402173482868901841145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183713072462620983738243053 68892402173482868901841145)
  ·
    refine ⟨51669301630112151676380859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68892402173482868901841145 51669301630112151676380859)
    ·
      refine ⟨77503952445168227514571289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51669301630112151676380859 77503952445168227514571289)
      ·
        refine ⟨58127964333876170635928467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77503952445168227514571289 58127964333876170635928467)
        ·
          refine ⟨87191946500814255953892701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58127964333876170635928467 87191946500814255953892701)
          ·
            refine ⟨32696979937805345982709763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87191946500814255953892701 32696979937805345982709763)
            ·
              refine ⟨49045469906708018974064645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32696979937805345982709763 49045469906708018974064645)
              ·
                refine ⟨9196025607507753557637121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49045469906708018974064645 9196025607507753557637121)
                ·
                  refine ⟨6897019205630815168227841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9196025607507753557637121 6897019205630815168227841)
                  ·
                    refine ⟨5172764404223111376170881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6897019205630815168227841 5172764404223111376170881)
                    ·
                      refine ⟨3879573303167333532128161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5172764404223111376170881 3879573303167333532128161)
                      ·
                        rfl

theorem cell23_7555442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_7555442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555442 prefixEnd_7555442 := by exact prefixLift 7555442
  have htrace : WordTrace (prefixWord ++ tailWord_7555442) baseStart_7555442 baseEnd_7555442 := by
    simpa [prefixWord, tailWord_7555442, baseEnd_7555442] using wordTrace_append hprefix tailTrace_7555442
  have hstable : (prefixWord ++ tailWord_7555442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555442).length < 2 ^ (prefixWord ++ tailWord_7555442).sum := by decide
  have hdescent : baseEnd_7555442 < baseStart_7555442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555461 : List Nat := [1, 3, 1, 1, 3, 1, 1, 4, 1, 7]
def baseStart_7555461 : Nat := 118140960795 + 7555461 * 2 ^ 59
def prefixEnd_7555461 : Nat := 4983230072969 + 3 ^ 40 * 7555461 * 2
def baseEnd_7555461 : Nat := 1293194353099922985930191

theorem tailTrace_7555461 : CollatzResearch.WordTrace tailWord_7555461 prefixEnd_7555461 1293194353099922985930191 := by
  unfold tailWord_7555461
  simp only [CollatzResearch.WordTrace]
  refine ⟨275570301680862641852306237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183713534453908427901537491 275570301680862641852306237)
  ·
    refine ⟨103338863130323490694614839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275570301680862641852306237 103338863130323490694614839)
    ·
      refine ⟨155008294695485236041922259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103338863130323490694614839 155008294695485236041922259)
      ·
        refine ⟨232512442043227854062883389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155008294695485236041922259 232512442043227854062883389)
        ·
          refine ⟨87192165766210445273581271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232512442043227854062883389 87192165766210445273581271)
          ·
            refine ⟨130788248649315667910371907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87192165766210445273581271 130788248649315667910371907)
            ·
              refine ⟨196182372973973501865557861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130788248649315667910371907 196182372973973501865557861)
              ·
                refine ⟨36784194932620031599792099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196182372973973501865557861 36784194932620031599792099)
                ·
                  refine ⟨55176292398930047399688149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36784194932620031599792099 55176292398930047399688149)
                  ·
                    refine ⟨1293194353099922985930191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55176292398930047399688149 1293194353099922985930191)
                    ·
                      rfl

theorem cell23_7555461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 7].length) (baseStart_7555461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555461 prefixEnd_7555461 := by exact prefixLift 7555461
  have htrace : WordTrace (prefixWord ++ tailWord_7555461) baseStart_7555461 baseEnd_7555461 := by
    simpa [prefixWord, tailWord_7555461, baseEnd_7555461] using wordTrace_append hprefix tailTrace_7555461
  have hstable : (prefixWord ++ tailWord_7555461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555461).length < 2 ^ (prefixWord ++ tailWord_7555461).sum := by decide
  have hdescent : baseEnd_7555461 < baseStart_7555461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555559 : List Nat := [1, 1, 5, 2, 1, 1, 5, 2, 1, 4]
def baseStart_7555559 : Nat := 118140960795 + 7555559 * 2 ^ 59
def prefixEnd_7555559 : Nat := 4983230072969 + 3 ^ 40 * 7555559 * 2
def baseEnd_7555559 : Nat := 1293211126801303191455041

theorem tailTrace_7555559 : CollatzResearch.WordTrace tailWord_7555559 prefixEnd_7555559 1293211126801303191455041 := by
  unfold tailWord_7555559
  simp only [CollatzResearch.WordTrace]
  refine ⟨275573876034507604589373731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183715917356338403059582487 275573876034507604589373731)
  ·
    refine ⟨413360814051761406884060597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275573876034507604589373731 413360814051761406884060597)
    ·
      refine ⟨38752576317352631895380681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 413360814051761406884060597 38752576317352631895380681)
      ·
        refine ⟨29064432238014473921535511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38752576317352631895380681 29064432238014473921535511)
        ·
          refine ⟨43596648357021710882303267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29064432238014473921535511 43596648357021710882303267)
          ·
            refine ⟨65394972535532566323454901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43596648357021710882303267 65394972535532566323454901)
            ·
              refine ⟨6130778675206178092823897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65394972535532566323454901 6130778675206178092823897)
              ·
                refine ⟨4598084006404633569617923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6130778675206178092823897 4598084006404633569617923)
                ·
                  refine ⟨6897126009606950354426885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4598084006404633569617923 6897126009606950354426885)
                  ·
                    refine ⟨1293211126801303191455041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6897126009606950354426885 1293211126801303191455041)
                    ·
                      rfl

theorem cell23_7555559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_7555559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555559 prefixEnd_7555559 := by exact prefixLift 7555559
  have htrace : WordTrace (prefixWord ++ tailWord_7555559) baseStart_7555559 baseEnd_7555559 := by
    simpa [prefixWord, tailWord_7555559, baseEnd_7555559] using wordTrace_append hprefix tailTrace_7555559
  have hstable : (prefixWord ++ tailWord_7555559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555559).length < 2 ^ (prefixWord ++ tailWord_7555559).sum := by decide
  have hdescent : baseEnd_7555559 < baseStart_7555559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555568 : List Nat := [2, 1, 1, 1, 3, 3, 2, 2, 3, 5]
def baseStart_7555568 : Nat := 118140960795 + 7555568 * 2 ^ 59
def prefixEnd_7555568 : Nat := 4983230072969 + 3 ^ 40 * 7555568 * 2
def baseEnd_7555568 : Nat := 1293212667243266679717527

theorem tailTrace_7555568 : CollatzResearch.WordTrace tailWord_7555568 prefixEnd_7555568 1293212667243266679717527 := by
  unfold tailWord_7555568
  simp only [CollatzResearch.WordTrace]
  refine ⟨137787102145737499563225679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183716136194316666084300905 137787102145737499563225679)
  ·
    refine ⟨206680653218606249344838519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137787102145737499563225679 206680653218606249344838519)
    ·
      refine ⟨310020979827909374017257779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206680653218606249344838519 310020979827909374017257779)
      ·
        refine ⟨465031469741864061025886669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310020979827909374017257779 465031469741864061025886669)
        ·
          refine ⟨174386801153199022884707501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 465031469741864061025886669 174386801153199022884707501)
          ·
            refine ⟨65395050432449633581765313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174386801153199022884707501 65395050432449633581765313)
            ·
              refine ⟨49046287824337225186323985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65395050432449633581765313 49046287824337225186323985)
              ·
                refine ⟨36784715868252918889742989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49046287824337225186323985 36784715868252918889742989)
                ·
                  refine ⟨13794268450594844583653621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36784715868252918889742989 13794268450594844583653621)
                  ·
                    refine ⟨1293212667243266679717527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13794268450594844583653621 1293212667243266679717527)
                    ·
                      rfl

theorem cell23_7555568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 3, 5].length) (baseStart_7555568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555568 prefixEnd_7555568 := by exact prefixLift 7555568
  have htrace : WordTrace (prefixWord ++ tailWord_7555568) baseStart_7555568 baseEnd_7555568 := by
    simpa [prefixWord, tailWord_7555568, baseEnd_7555568] using wordTrace_append hprefix tailTrace_7555568
  have hstable : (prefixWord ++ tailWord_7555568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555568).length < 2 ^ (prefixWord ++ tailWord_7555568).sum := by decide
  have hdescent : baseEnd_7555568 < baseStart_7555568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555585 : List Nat := [1, 2, 4, 1, 3, 2, 1, 1, 3, 5]
def baseStart_7555585 : Nat := 118140960795 + 7555585 * 2 ^ 59
def prefixEnd_7555585 : Nat := 4983230072969 + 3 ^ 40 * 7555585 * 2
def baseEnd_7555585 : Nat := 1293215576966975490880001

theorem tailTrace_7555585 : CollatzResearch.WordTrace tailWord_7555585 prefixEnd_7555585 1293215576966975490880001 := by
  unfold tailWord_7555585
  simp only [CollatzResearch.WordTrace]
  refine ⟨275574824332413411029820209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183716549554942274019880139 275574824332413411029820209)
  ·
    refine ⟨206681118249310058272365157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275574824332413411029820209 206681118249310058272365157)
    ·
      refine ⟨38752709671745635926068467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206681118249310058272365157 38752709671745635926068467)
      ·
        refine ⟨58129064507618453889102701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38752709671745635926068467 58129064507618453889102701)
        ·
          refine ⟨21798399190356920208413513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58129064507618453889102701 21798399190356920208413513)
          ·
            refine ⟨16348799392767690156310135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21798399190356920208413513 16348799392767690156310135)
            ·
              refine ⟨24523199089151535234465203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16348799392767690156310135 24523199089151535234465203)
              ·
                refine ⟨36784798633727302851697805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24523199089151535234465203 36784798633727302851697805)
                ·
                  refine ⟨13794299487647738569386677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36784798633727302851697805 13794299487647738569386677)
                  ·
                    refine ⟨1293215576966975490880001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13794299487647738569386677 1293215576966975490880001)
                    ·
                      rfl

theorem cell23_7555585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_7555585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555585 prefixEnd_7555585 := by exact prefixLift 7555585
  have htrace : WordTrace (prefixWord ++ tailWord_7555585) baseStart_7555585 baseEnd_7555585 := by
    simpa [prefixWord, tailWord_7555585, baseEnd_7555585] using wordTrace_append hprefix tailTrace_7555585
  have hstable : (prefixWord ++ tailWord_7555585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555585).length < 2 ^ (prefixWord ++ tailWord_7555585).sum := by decide
  have hdescent : baseEnd_7555585 < baseStart_7555585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555616 : List Nat := [2, 1, 1, 6, 2, 1, 1, 4, 1, 1, 3]
def baseStart_7555616 : Nat := 118140960795 + 7555616 * 2 ^ 59
def prefixEnd_7555616 : Nat := 4983230072969 + 3 ^ 40 * 7555616 * 2
def baseEnd_7555616 : Nat := 3879662648801215851352361

theorem tailTrace_7555616 : CollatzResearch.WordTrace tailWord_7555616 prefixEnd_7555616 3879662648801215851352361 := by
  unfold tailWord_7555616
  simp only [CollatzResearch.WordTrace]
  refine ⟨137787977497650551662099351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183717303330200735549465801 137787977497650551662099351)
  ·
    refine ⟨206681966246475827493149027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137787977497650551662099351 206681966246475827493149027)
    ·
      refine ⟨310022949369713741239723541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206681966246475827493149027 310022949369713741239723541)
      ·
        refine ⟨14532325751705331620612041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 310022949369713741239723541 14532325751705331620612041)
        ·
          refine ⟨10899244313778998715459031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14532325751705331620612041 10899244313778998715459031)
          ·
            refine ⟨16348866470668498073188547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10899244313778998715459031 16348866470668498073188547)
            ·
              refine ⟨24523299706002747109782821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16348866470668498073188547 24523299706002747109782821)
              ·
                refine ⟨4598118694875515083084279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24523299706002747109782821 4598118694875515083084279)
                ·
                  refine ⟨6897178042313272624626419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4598118694875515083084279 6897178042313272624626419)
                  ·
                    refine ⟨10345767063469908936939629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6897178042313272624626419 10345767063469908936939629)
                    ·
                      refine ⟨3879662648801215851352361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10345767063469908936939629 3879662648801215851352361)
                      ·
                        rfl

theorem cell23_7555616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_7555616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555616 prefixEnd_7555616 := by exact prefixLift 7555616
  have htrace : WordTrace (prefixWord ++ tailWord_7555616) baseStart_7555616 baseEnd_7555616 := by
    simpa [prefixWord, tailWord_7555616, baseEnd_7555616] using wordTrace_append hprefix tailTrace_7555616
  have hstable : (prefixWord ++ tailWord_7555616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555616).length < 2 ^ (prefixWord ++ tailWord_7555616).sum := by decide
  have hdescent : baseEnd_7555616 < baseStart_7555616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555635 : List Nat := [1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 4]
def baseStart_7555635 : Nat := 118140960795 + 7555635 * 2 ^ 59
def prefixEnd_7555635 : Nat := 4983230072969 + 3 ^ 40 * 7555635 * 2
def baseEnd_7555635 : Nat := 3879672404933651277014773

theorem tailTrace_7555635 : CollatzResearch.WordTrace tailWord_7555635 prefixEnd_7555635 3879672404933651277014773 := by
  unfold tailWord_7555635
  simp only [CollatzResearch.WordTrace]
  refine ⟨275576647982232269569140359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183717765321488179712760239 275576647982232269569140359)
  ·
    refine ⟨413364971973348404353710539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275576647982232269569140359 413364971973348404353710539)
    ·
      refine ⟨620047457960022606530565809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413364971973348404353710539 620047457960022606530565809)
      ·
        refine ⟨465035593470016954897924357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 620047457960022606530565809 465035593470016954897924357)
        ·
          refine ⟨87194173775628179043360817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 465035593470016954897924357 87194173775628179043360817)
          ·
            refine ⟨65395630331721134282520613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87194173775628179043360817 65395630331721134282520613)
            ·
              refine ⟨12261680687197712677972615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65395630331721134282520613 12261680687197712677972615)
              ·
                refine ⟨18392521030796569016958923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12261680687197712677972615 18392521030796569016958923)
                ·
                  refine ⟨27588781546194853525438385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18392521030796569016958923 27588781546194853525438385)
                  ·
                    refine ⟨20691586159646140144078789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27588781546194853525438385 20691586159646140144078789)
                    ·
                      refine ⟨3879672404933651277014773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20691586159646140144078789 3879672404933651277014773)
                      ·
                        rfl

theorem cell23_7555635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 4].length) (baseStart_7555635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555635 prefixEnd_7555635 := by exact prefixLift 7555635
  have htrace : WordTrace (prefixWord ++ tailWord_7555635) baseStart_7555635 baseEnd_7555635 := by
    simpa [prefixWord, tailWord_7555635, baseEnd_7555635] using wordTrace_append hprefix tailTrace_7555635
  have hstable : (prefixWord ++ tailWord_7555635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555635).length < 2 ^ (prefixWord ++ tailWord_7555635).sum := by decide
  have hdescent : baseEnd_7555635 < baseStart_7555635 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555742 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_7555742 : Nat := 118140960795 + 7555742 * 2 ^ 59
def prefixEnd_7555742 : Nat := 4983230072969 + 3 ^ 40 * 7555742 * 2
def baseEnd_7555742 : Nat := 3879727347363682358376781

theorem tailTrace_7555742 : CollatzResearch.WordTrace tailWord_7555742 prefixEnd_7555742 3879727347363682358376781 := by
  unfold tailWord_7555742
  simp only [CollatzResearch.WordTrace]
  refine ⟨34447568824105578355410685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183720367061896417895523653 34447568824105578355410685)
  ·
    refine ⟨12917838309039591883279007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34447568824105578355410685 12917838309039591883279007)
    ·
      refine ⟨19376757463559387824918511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12917838309039591883279007 19376757463559387824918511)
      ·
        refine ⟨29065136195339081737377767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19376757463559387824918511 29065136195339081737377767)
        ·
          refine ⟨43597704293008622606066651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29065136195339081737377767 43597704293008622606066651)
          ·
            refine ⟨65396556439512933909099977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43597704293008622606066651 65396556439512933909099977)
            ·
              refine ⟨49047417329634700431824983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65396556439512933909099977 49047417329634700431824983)
              ·
                refine ⟨73571125994452050647737475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49047417329634700431824983 73571125994452050647737475)
                ·
                  refine ⟨110356688991678075971606213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73571125994452050647737475 110356688991678075971606213)
                  ·
                    refine ⟨20691879185939639244676165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110356688991678075971606213 20691879185939639244676165)
                    ·
                      refine ⟨3879727347363682358376781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20691879185939639244676165 3879727347363682358376781)
                      ·
                        rfl

theorem cell23_7555742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_7555742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555742 prefixEnd_7555742 := by exact prefixLift 7555742
  have htrace : WordTrace (prefixWord ++ tailWord_7555742) baseStart_7555742 baseEnd_7555742 := by
    simpa [prefixWord, tailWord_7555742, baseEnd_7555742] using wordTrace_append hprefix tailTrace_7555742
  have hstable : (prefixWord ++ tailWord_7555742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555742).length < 2 ^ (prefixWord ++ tailWord_7555742).sum := by decide
  have hdescent : baseEnd_7555742 < baseStart_7555742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555775 : List Nat := [1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 5]
def baseStart_7555775 : Nat := 118140960795 + 7555775 * 2 ^ 59
def prefixEnd_7555775 : Nat := 4983230072969 + 3 ^ 40 * 7555775 * 2
def baseEnd_7555775 : Nat := 3879744292225280729264129

theorem tailTrace_7555775 : CollatzResearch.WordTrace tailWord_7555775 prefixEnd_7555775 3879744292225280729264129 := by
  unfold tailWord_7555775
  simp only [CollatzResearch.WordTrace]
  refine ⟨275581754201725073479236779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183721169467816715652824519 275581754201725073479236779)
  ·
    refine ⟨413372631302587610218855169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275581754201725073479236779 413372631302587610218855169)
    ·
      refine ⟨310029473476940707664141377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413372631302587610218855169 310029473476940707664141377)
      ·
        refine ⟨232522105107705530748106033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310029473476940707664141377 232522105107705530748106033)
        ·
          refine ⟨174391578830779148061079525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232522105107705530748106033 174391578830779148061079525)
          ·
            refine ⟨32698421030771090261452411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174391578830779148061079525 32698421030771090261452411)
            ·
              refine ⟨49047631546156635392178617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32698421030771090261452411 49047631546156635392178617)
              ·
                refine ⟨36785723659617476544133963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49047631546156635392178617 36785723659617476544133963)
                ·
                  refine ⟨55178585489426214816200945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36785723659617476544133963 55178585489426214816200945)
                  ·
                    refine ⟨41383939117069661112150709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55178585489426214816200945 41383939117069661112150709)
                    ·
                      refine ⟨3879744292225280729264129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41383939117069661112150709 3879744292225280729264129)
                      ·
                        rfl

theorem cell23_7555775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_7555775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555775 prefixEnd_7555775 := by exact prefixLift 7555775
  have htrace : WordTrace (prefixWord ++ tailWord_7555775) baseStart_7555775 baseEnd_7555775 := by
    simpa [prefixWord, tailWord_7555775, baseEnd_7555775] using wordTrace_append hprefix tailTrace_7555775
  have hstable : (prefixWord ++ tailWord_7555775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555775).length < 2 ^ (prefixWord ++ tailWord_7555775).sum := by decide
  have hdescent : baseEnd_7555775 < baseStart_7555775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555786 : List Nat := [3, 1, 2, 1, 4, 3, 2, 2, 5]
def baseStart_7555786 : Nat := 118140960795 + 7555786 * 2 ^ 59
def prefixEnd_7555786 : Nat := 4983230072969 + 3 ^ 40 * 7555786 * 2
def baseEnd_7555786 : Nat := 431083326723608909580731

theorem tailTrace_7555786 : CollatzResearch.WordTrace tailWord_7555786 prefixEnd_7555786 431083326723608909580731 := by
  unfold tailWord_7555786
  simp only [CollatzResearch.WordTrace]
  refine ⟨68895538851171305589471803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183721436936456814905258141 68895538851171305589471803)
  ·
    refine ⟨103343308276756958384207705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68895538851171305589471803 103343308276756958384207705)
    ·
      refine ⟨77507481207567718788155779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103343308276756958384207705 77507481207567718788155779)
      ·
        refine ⟨116261221811351578182233669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77507481207567718788155779 116261221811351578182233669)
        ·
          refine ⟨21798979089628420909168813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116261221811351578182233669 21798979089628420909168813)
          ·
            refine ⟨8174617158610657840938305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21798979089628420909168813 8174617158610657840938305)
            ·
              refine ⟨6130962868957993380703729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8174617158610657840938305 6130962868957993380703729)
              ·
                refine ⟨4598222151718495035527797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6130962868957993380703729 4598222151718495035527797)
                ·
                  refine ⟨431083326723608909580731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4598222151718495035527797 431083326723608909580731)
                  ·
                    rfl

theorem cell23_7555786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2, 5].length) (baseStart_7555786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555786 prefixEnd_7555786 := by exact prefixLift 7555786
  have htrace : WordTrace (prefixWord ++ tailWord_7555786) baseStart_7555786 baseEnd_7555786 := by
    simpa [prefixWord, tailWord_7555786, baseEnd_7555786] using wordTrace_append hprefix tailTrace_7555786
  have hstable : (prefixWord ++ tailWord_7555786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555786).length < 2 ^ (prefixWord ++ tailWord_7555786).sum := by decide
  have hdescent : baseEnd_7555786 < baseStart_7555786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555812 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 5, 4]
def baseStart_7555812 : Nat := 118140960795 + 7555812 * 2 ^ 59
def prefixEnd_7555812 : Nat := 4983230072969 + 3 ^ 40 * 7555812 * 2
def baseEnd_7555812 : Nat := 1293254430336499028167153

theorem tailTrace_7555812 : CollatzResearch.WordTrace tailWord_7555812 prefixEnd_7555812 1293254430336499028167153 := by
  unfold tailWord_7555812
  simp only [CollatzResearch.WordTrace]
  refine ⟨137791551851295514399166845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183722069135060685865555793 137791551851295514399166845)
  ·
    refine ⟨51671831944235817899687567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137791551851295514399166845 51671831944235817899687567)
    ·
      refine ⟨77507747916353726849531351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51671831944235817899687567 77507747916353726849531351)
      ·
        refine ⟨116261621874530590274297027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77507747916353726849531351 116261621874530590274297027)
        ·
          refine ⟨174392432811795885411445541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116261621874530590274297027 174392432811795885411445541)
          ·
            refine ⟨32698581152211728514646039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174392432811795885411445541 32698581152211728514646039)
            ·
              refine ⟨49047871728317592771969059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32698581152211728514646039 49047871728317592771969059)
              ·
                refine ⟨73571807592476389157953589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49047871728317592771969059 73571807592476389157953589)
                ·
                  refine ⟨6897356961794661483558149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73571807592476389157953589 6897356961794661483558149)
                  ·
                    refine ⟨1293254430336499028167153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6897356961794661483558149 1293254430336499028167153)
                    ·
                      rfl

theorem cell23_7555812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_7555812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555812 prefixEnd_7555812 := by exact prefixLift 7555812
  have htrace : WordTrace (prefixWord ++ tailWord_7555812) baseStart_7555812 baseEnd_7555812 := by
    simpa [prefixWord, tailWord_7555812, baseEnd_7555812] using wordTrace_append hprefix tailTrace_7555812
  have hstable : (prefixWord ++ tailWord_7555812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555812).length < 2 ^ (prefixWord ++ tailWord_7555812).sum := by decide
  have hdescent : baseEnd_7555812 < baseStart_7555812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555816 : List Nat := [2, 1, 4, 1, 5, 1, 1, 1, 2, 5]
def baseStart_7555816 : Nat := 118140960795 + 7555816 * 2 ^ 59
def prefixEnd_7555816 : Nat := 4983230072969 + 3 ^ 40 * 7555816 * 2
def baseEnd_7555816 : Nat := 1293255114977371689617147

theorem tailTrace_7555816 : CollatzResearch.WordTrace tailWord_7555816 prefixEnd_7555816 1293255114977371689617147 := by
  unfold tailWord_7555816
  simp only [CollatzResearch.WordTrace]
  refine ⟨137791624797288268740739651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183722166396384358320986201 137791624797288268740739651)
  ·
    refine ⟨206687437195932403111109477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137791624797288268740739651 206687437195932403111109477)
    ·
      refine ⟨38753894474237325583333027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206687437195932403111109477 38753894474237325583333027)
      ·
        refine ⟨58130841711355988374999541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38753894474237325583333027 58130841711355988374999541)
        ·
          refine ⟨5449766410439623910156207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58130841711355988374999541 5449766410439623910156207)
          ·
            refine ⟨8174649615659435865234311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5449766410439623910156207 8174649615659435865234311)
            ·
              refine ⟨12261974423489153797851467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8174649615659435865234311 12261974423489153797851467)
              ·
                refine ⟨18392961635233730696777201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12261974423489153797851467 18392961635233730696777201)
                ·
                  refine ⟨13794721226425298022582901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18392961635233730696777201 13794721226425298022582901)
                  ·
                    refine ⟨1293255114977371689617147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13794721226425298022582901 1293255114977371689617147)
                    ·
                      rfl

theorem cell23_7555816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_7555816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555816 prefixEnd_7555816 := by exact prefixLift 7555816
  have htrace : WordTrace (prefixWord ++ tailWord_7555816) baseStart_7555816 baseEnd_7555816 := by
    simpa [prefixWord, tailWord_7555816, baseEnd_7555816] using wordTrace_append hprefix tailTrace_7555816
  have hstable : (prefixWord ++ tailWord_7555816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555816).length < 2 ^ (prefixWord ++ tailWord_7555816).sum := by decide
  have hdescent : baseEnd_7555816 < baseStart_7555816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555825 : List Nat := [1, 2, 2, 2, 2, 2, 2, 2, 8]
def baseStart_7555825 : Nat := 118140960795 + 7555825 * 2 ^ 59
def prefixEnd_7555825 : Nat := 4983230072969 + 3 ^ 40 * 7555825 * 2
def baseEnd_7555825 : Nat := 431085551806445059293211

theorem tailTrace_7555825 : CollatzResearch.WordTrace tailWord_7555825 prefixEnd_7555825 431085551806445059293211 := by
  unfold tailWord_7555825
  simp only [CollatzResearch.WordTrace]
  refine ⟨275583577851543932018556929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183722385234362621345704619 275583577851543932018556929)
  ·
    refine ⟨206687683388657949013917697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275583577851543932018556929 206687683388657949013917697)
    ·
      refine ⟨155015762541493461760438273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206687683388657949013917697 155015762541493461760438273)
      ·
        refine ⟨116261821906120096320328705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155015762541493461760438273 116261821906120096320328705)
        ·
          refine ⟨87196366429590072240246529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116261821906120096320328705 87196366429590072240246529)
          ·
            refine ⟨65397274822192554180184897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87196366429590072240246529 65397274822192554180184897)
            ·
              refine ⟨49047956116644415635138673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65397274822192554180184897 49047956116644415635138673)
              ·
                refine ⟨36785967087483311726354005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49047956116644415635138673 36785967087483311726354005)
                ·
                  refine ⟨431085551806445059293211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36785967087483311726354005 431085551806445059293211)
                  ·
                    rfl

theorem cell23_7555825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 8].length) (baseStart_7555825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555825 prefixEnd_7555825 := by exact prefixLift 7555825
  have htrace : WordTrace (prefixWord ++ tailWord_7555825) baseStart_7555825 baseEnd_7555825 := by
    simpa [prefixWord, tailWord_7555825, baseEnd_7555825] using wordTrace_append hprefix tailTrace_7555825
  have hstable : (prefixWord ++ tailWord_7555825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555825).length < 2 ^ (prefixWord ++ tailWord_7555825).sum := by decide
  have hdescent : baseEnd_7555825 < baseStart_7555825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555910 : List Nat := [6, 1, 1, 2, 2, 2, 2, 1, 6]
def baseStart_7555910 : Nat := 118140960795 + 7555910 * 2 ^ 59
def prefixEnd_7555910 : Nat := 4983230072969 + 3 ^ 40 * 7555910 * 2
def baseEnd_7555910 : Nat := 431090401345959744564001

theorem tailTrace_7555910 : CollatzResearch.WordTrace tailWord_7555910 prefixEnd_7555910 431090401345959744564001 := by
  unfold tailWord_7555910
  simp only [CollatzResearch.WordTrace]
  refine ⟨8612083689257374735481287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 183724452037490661023600789 8612083689257374735481287)
  ·
    refine ⟨12918125533886062103221931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8612083689257374735481287 12918125533886062103221931)
    ·
      refine ⟨19377188300829093154832897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12918125533886062103221931 19377188300829093154832897)
      ·
        refine ⟨14532891225621819866124673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19377188300829093154832897 14532891225621819866124673)
        ·
          refine ⟨10899668419216364899593505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14532891225621819866124673 10899668419216364899593505)
          ·
            refine ⟨8174751314412273674695129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10899668419216364899593505 8174751314412273674695129)
            ·
              refine ⟨6131063485809205256021347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8174751314412273674695129 6131063485809205256021347)
              ·
                refine ⟨9196595228713807884032021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6131063485809205256021347 9196595228713807884032021)
                ·
                  refine ⟨431090401345959744564001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9196595228713807884032021 431090401345959744564001)
                  ·
                    rfl

theorem cell23_7555910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_7555910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555910 prefixEnd_7555910 := by exact prefixLift 7555910
  have htrace : WordTrace (prefixWord ++ tailWord_7555910) baseStart_7555910 baseEnd_7555910 := by
    simpa [prefixWord, tailWord_7555910, baseEnd_7555910] using wordTrace_append hprefix tailTrace_7555910
  have hstable : (prefixWord ++ tailWord_7555910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555910).length < 2 ^ (prefixWord ++ tailWord_7555910).sum := by decide
  have hdescent : baseEnd_7555910 < baseStart_7555910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555912 : List Nat := [2, 1, 3, 1, 1, 3, 1, 4, 1, 1, 5]
def baseStart_7555912 : Nat := 118140960795 + 7555912 * 2 ^ 59
def prefixEnd_7555912 : Nat := 4983230072969 + 3 ^ 40 * 7555912 * 2
def baseEnd_7555912 : Nat := 3879814639074946693250999

theorem tailTrace_7555912 : CollatzResearch.WordTrace tailWord_7555912 prefixEnd_7555912 3879814639074946693250999 := by
  unfold tailWord_7555912
  simp only [CollatzResearch.WordTrace]
  refine ⟨137793375501114372938486995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183724500668152497251315993 137793375501114372938486995)
  ·
    refine ⟨206690063251671559407730493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137793375501114372938486995 206690063251671559407730493)
    ·
      refine ⟨77508773719376834777898935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206690063251671559407730493 77508773719376834777898935)
      ·
        refine ⟨116263160579065252166848403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77508773719376834777898935 116263160579065252166848403)
        ·
          refine ⟨174394740868597878250272605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116263160579065252166848403 174394740868597878250272605)
          ·
            refine ⟨65398027825724204343852227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174394740868597878250272605 65398027825724204343852227)
            ·
              refine ⟨98097041738586306515778341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65398027825724204343852227 98097041738586306515778341)
              ·
                refine ⟨18393195325984932471708439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98097041738586306515778341 18393195325984932471708439)
                ·
                  refine ⟨27589792988977398707562659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18393195325984932471708439 27589792988977398707562659)
                  ·
                    refine ⟨41384689483466098061343989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27589792988977398707562659 41384689483466098061343989)
                    ·
                      refine ⟨3879814639074946693250999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41384689483466098061343989 3879814639074946693250999)
                      ·
                        rfl

theorem cell23_7555912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_7555912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555912 prefixEnd_7555912 := by exact prefixLift 7555912
  have htrace : WordTrace (prefixWord ++ tailWord_7555912) baseStart_7555912 baseEnd_7555912 := by
    simpa [prefixWord, tailWord_7555912, baseEnd_7555912] using wordTrace_append hprefix tailTrace_7555912
  have hstable : (prefixWord ++ tailWord_7555912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555912).length < 2 ^ (prefixWord ++ tailWord_7555912).sum := by decide
  have hdescent : baseEnd_7555912 < baseStart_7555912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555922 : List Nat := [3, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_7555922 : Nat := 118140960795 + 7555922 * 2 ^ 59
def prefixEnd_7555922 : Nat := 4983230072969 + 3 ^ 40 * 7555922 * 2
def baseEnd_7555922 : Nat := 3879819773881491654125953

theorem tailTrace_7555922 : CollatzResearch.WordTrace tailWord_7555922 prefixEnd_7555922 3879819773881491654125953 := by
  unfold tailWord_7555922
  simp only [CollatzResearch.WordTrace]
  refine ⟨68896778933048129396209505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183724743821461678389892013 68896778933048129396209505)
  ·
    refine ⟨51672584199786097047157129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68896778933048129396209505 51672584199786097047157129)
    ·
      refine ⟨38754438149839572785367847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51672584199786097047157129 38754438149839572785367847)
      ·
        refine ⟨58131657224759359178051771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38754438149839572785367847 58131657224759359178051771)
        ·
          refine ⟨87197485837139038767077657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58131657224759359178051771 87197485837139038767077657)
          ·
            refine ⟨65398114377854279075308243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87197485837139038767077657 65398114377854279075308243)
            ·
              refine ⟨98097171566781418612962365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65398114377854279075308243 98097171566781418612962365)
              ·
                refine ⟨36786439337543031979860887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98097171566781418612962365 36786439337543031979860887)
                ·
                  refine ⟨55179659006314547969791331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36786439337543031979860887 55179659006314547969791331)
                  ·
                    refine ⟨82769488509471821954686997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55179659006314547969791331 82769488509471821954686997)
                    ·
                      refine ⟨3879819773881491654125953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82769488509471821954686997 3879819773881491654125953)
                      ·
                        rfl

theorem cell23_7555922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_7555922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555922 prefixEnd_7555922 := by exact prefixLift 7555922
  have htrace : WordTrace (prefixWord ++ tailWord_7555922) baseStart_7555922 baseEnd_7555922 := by
    simpa [prefixWord, tailWord_7555922, baseEnd_7555922] using wordTrace_append hprefix tailTrace_7555922
  have hstable : (prefixWord ++ tailWord_7555922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555922).length < 2 ^ (prefixWord ++ tailWord_7555922).sum := by decide
  have hdescent : baseEnd_7555922 < baseStart_7555922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555929 : List Nat := [1, 2, 1, 2, 2, 5, 1, 1, 3, 2, 3]
def baseStart_7555929 : Nat := 118140960795 + 7555929 * 2 ^ 59
def prefixEnd_7555929 : Nat := 4983230072969 + 3 ^ 40 * 7555929 * 2
def baseEnd_7555929 : Nat := 3879823368246073126738421

theorem tailTrace_7555929 : CollatzResearch.WordTrace tailWord_7555929 prefixEnd_7555929 3879823368246073126738421 := by
  unfold tailWord_7555929
  simp only [CollatzResearch.WordTrace]
  refine ⟨275587371043167157780342841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183724914028778105186895227 275587371043167157780342841)
  ·
    refine ⟨206690528282375368335257131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275587371043167157780342841 206690528282375368335257131)
    ·
      refine ⟨310035792423563052502885697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206690528282375368335257131 310035792423563052502885697)
      ·
        refine ⟨232526844317672289377164273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310035792423563052502885697 232526844317672289377164273)
        ·
          refine ⟨174395133238254217032873205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232526844317672289377164273 174395133238254217032873205)
          ·
            refine ⟨16349543741086332846831863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174395133238254217032873205 16349543741086332846831863)
            ·
              refine ⟨24524315611629499270247795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16349543741086332846831863 24524315611629499270247795)
              ·
                refine ⟨36786473417444248905371693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24524315611629499270247795 36786473417444248905371693)
                ·
                  refine ⟨13794927531541593339514385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36786473417444248905371693 13794927531541593339514385)
                  ·
                    refine ⟨10346195648656195004635789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13794927531541593339514385 10346195648656195004635789)
                    ·
                      refine ⟨3879823368246073126738421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10346195648656195004635789 3879823368246073126738421)
                      ·
                        rfl

theorem cell23_7555929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 2, 3].length) (baseStart_7555929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555929 prefixEnd_7555929 := by exact prefixLift 7555929
  have htrace : WordTrace (prefixWord ++ tailWord_7555929) baseStart_7555929 baseEnd_7555929 := by
    simpa [prefixWord, tailWord_7555929, baseEnd_7555929] using wordTrace_append hprefix tailTrace_7555929
  have hstable : (prefixWord ++ tailWord_7555929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555929).length < 2 ^ (prefixWord ++ tailWord_7555929).sum := by decide
  have hdescent : baseEnd_7555929 < baseStart_7555929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555939 : List Nat := [1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 4]
def baseStart_7555939 : Nat := 118140960795 + 7555939 * 2 ^ 59
def prefixEnd_7555939 : Nat := 4983230072969 + 3 ^ 40 * 7555939 * 2
def baseEnd_7555939 : Nat := 3879828503052618087613375

theorem tailTrace_7555939 : CollatzResearch.WordTrace tailWord_7555939 prefixEnd_7555939 3879828503052618087613375 := by
  unfold tailWord_7555939
  simp only [CollatzResearch.WordTrace]
  refine ⟨275587735773130929488206871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183725157182087286325471247 275587735773130929488206871)
  ·
    refine ⟨413381603659696394232310307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275587735773130929488206871 413381603659696394232310307)
    ·
      refine ⟨620072405489544591348465461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413381603659696394232310307 620072405489544591348465461)
      ·
        refine ⟨58131788014644805438918637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 620072405489544591348465461 58131788014644805438918637)
        ·
          refine ⟨21799420505491802039594489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58131788014644805438918637 21799420505491802039594489)
          ·
            refine ⟨16349565379118851529695867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21799420505491802039594489 16349565379118851529695867)
            ·
              refine ⟨24524348068678277294543801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16349565379118851529695867 24524348068678277294543801)
              ·
                refine ⟨18393261051508707970907851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24524348068678277294543801 18393261051508707970907851)
                ·
                  refine ⟨27589891577263061956361777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18393261051508707970907851 27589891577263061956361777)
                  ·
                    refine ⟨20692418682947296467271333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27589891577263061956361777 20692418682947296467271333)
                    ·
                      refine ⟨3879828503052618087613375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20692418682947296467271333 3879828503052618087613375)
                      ·
                        rfl

theorem cell23_7555939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_7555939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555939 prefixEnd_7555939 := by exact prefixLift 7555939
  have htrace : WordTrace (prefixWord ++ tailWord_7555939) baseStart_7555939 baseEnd_7555939 := by
    simpa [prefixWord, tailWord_7555939, baseEnd_7555939] using wordTrace_append hprefix tailTrace_7555939
  have hstable : (prefixWord ++ tailWord_7555939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555939).length < 2 ^ (prefixWord ++ tailWord_7555939).sum := by decide
  have hdescent : baseEnd_7555939 < baseStart_7555939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555959 : List Nat := [1, 1, 3, 1, 1, 2, 1, 5, 4, 1, 3]
def baseStart_7555959 : Nat := 118140960795 + 7555959 * 2 ^ 59
def prefixEnd_7555959 : Nat := 4983230072969 + 3 ^ 40 * 7555959 * 2
def baseEnd_7555959 : Nat := 3879838772665708009363283

theorem tailTrace_7555959 : CollatzResearch.WordTrace tailWord_7555959 prefixEnd_7555959 3879838772665708009363283 := by
  unfold tailWord_7555959
  simp only [CollatzResearch.WordTrace]
  refine ⟨275588465233058472903934931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183725643488705648602623287 275588465233058472903934931)
  ·
    refine ⟨413382697849587709355902397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275588465233058472903934931 413382697849587709355902397)
    ·
      refine ⟨155018511693595391008463399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413382697849587709355902397 155018511693595391008463399)
      ·
        refine ⟨232527767540393086512695099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155018511693595391008463399 232527767540393086512695099)
        ·
          refine ⟨348791651310589629769042649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232527767540393086512695099 348791651310589629769042649)
          ·
            refine ⟨261593738482942222326781987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348791651310589629769042649 261593738482942222326781987)
            ·
              refine ⟨392390607724413333490172981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261593738482942222326781987 392390607724413333490172981)
              ·
                refine ⟨36786619474163750014703717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 392390607724413333490172981 36786619474163750014703717)
                ·
                  refine ⟨6897491151405703127756947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36786619474163750014703717 6897491151405703127756947)
                  ·
                    refine ⟨10346236727108554691635421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6897491151405703127756947 10346236727108554691635421)
                    ·
                      refine ⟨3879838772665708009363283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10346236727108554691635421 3879838772665708009363283)
                      ·
                        rfl

theorem cell23_7555959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4, 1, 3].length) (baseStart_7555959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555959 prefixEnd_7555959 := by exact prefixLift 7555959
  have htrace : WordTrace (prefixWord ++ tailWord_7555959) baseStart_7555959 baseEnd_7555959 := by
    simpa [prefixWord, tailWord_7555959, baseEnd_7555959] using wordTrace_append hprefix tailTrace_7555959
  have hstable : (prefixWord ++ tailWord_7555959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555959).length < 2 ^ (prefixWord ++ tailWord_7555959).sum := by decide
  have hdescent : baseEnd_7555959 < baseStart_7555959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555972 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_7555972 : Nat := 118140960795 + 7555972 * 2 ^ 59
def prefixEnd_7555972 : Nat := 4983230072969 + 3 ^ 40 * 7555972 * 2
def baseEnd_7555972 : Nat := 3879845447914216458500723

theorem tailTrace_7555972 : CollatzResearch.WordTrace tailWord_7555972 prefixEnd_7555972 3879845447914216458500723 := by
  unfold tailWord_7555972
  simp only [CollatzResearch.WordTrace]
  refine ⟨137794469691005688062079085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183725959588007584082772113 137794469691005688062079085)
  ·
    refine ⟨51672926134127133023279657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137794469691005688062079085 51672926134127133023279657)
    ·
      refine ⟨38754694600595349767459743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51672926134127133023279657 38754694600595349767459743)
      ·
        refine ⟨58132041900893024651189615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38754694600595349767459743 58132041900893024651189615)
        ·
          refine ⟨87198062851339536976784423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58132041900893024651189615 87198062851339536976784423)
          ·
            refine ⟨130797094277009305465176635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87198062851339536976784423 130797094277009305465176635)
            ·
              refine ⟨196195641415513958197764953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130797094277009305465176635 196195641415513958197764953)
              ·
                refine ⟨147146731061635468648323715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196195641415513958197764953 147146731061635468648323715)
                ·
                  refine ⟨220720096592453202972485573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147146731061635468648323715 220720096592453202972485573)
                  ·
                    refine ⟨41385018111084975557341045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 220720096592453202972485573 41385018111084975557341045)
                    ·
                      refine ⟨3879845447914216458500723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41385018111084975557341045 3879845447914216458500723)
                      ·
                        rfl

theorem cell23_7555972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_7555972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555972 prefixEnd_7555972 := by exact prefixLift 7555972
  have htrace : WordTrace (prefixWord ++ tailWord_7555972) baseStart_7555972 baseEnd_7555972 := by
    simpa [prefixWord, tailWord_7555972, baseEnd_7555972] using wordTrace_append hprefix tailTrace_7555972
  have hstable : (prefixWord ++ tailWord_7555972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555972).length < 2 ^ (prefixWord ++ tailWord_7555972).sum := by decide
  have hdescent : baseEnd_7555972 < baseStart_7555972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7555976 : List Nat := [2, 1, 3, 3, 2, 2, 2, 1, 1, 3, 3]
def baseStart_7555976 : Nat := 118140960795 + 7555976 * 2 ^ 59
def prefixEnd_7555976 : Nat := 4983230072969 + 3 ^ 40 * 7555976 * 2
def baseEnd_7555976 : Nat := 3879847501836834442850705

theorem tailTrace_7555976 : CollatzResearch.WordTrace tailWord_7555976 prefixEnd_7555976 3879847501836834442850705 := by
  unfold tailWord_7555976
  simp only [CollatzResearch.WordTrace]
  refine ⟨137794542636998442403651891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183726056849331256538202521 137794542636998442403651891)
  ·
    refine ⟨206691813955497663605477837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137794542636998442403651891 206691813955497663605477837)
    ·
      refine ⟨77509430233311623852054189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206691813955497663605477837 77509430233311623852054189)
      ·
        refine ⟨29066036337491858944520321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77509430233311623852054189 29066036337491858944520321)
        ·
          refine ⟨21799527253118894208390241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29066036337491858944520321 21799527253118894208390241)
          ·
            refine ⟨16349645439839170656292681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21799527253118894208390241 16349645439839170656292681)
            ·
              refine ⟨12262234079879377992219511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16349645439839170656292681 12262234079879377992219511)
              ·
                refine ⟨18393351119819066988329267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12262234079879377992219511 18393351119819066988329267)
                ·
                  refine ⟨27590026679728600482493901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18393351119819066988329267 27590026679728600482493901)
                  ·
                    refine ⟨10346260004898225180935213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27590026679728600482493901 10346260004898225180935213)
                    ·
                      refine ⟨3879847501836834442850705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10346260004898225180935213 3879847501836834442850705)
                      ·
                        rfl

theorem cell23_7555976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_7555976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7555976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7555976 prefixEnd_7555976 := by exact prefixLift 7555976
  have htrace : WordTrace (prefixWord ++ tailWord_7555976) baseStart_7555976 baseEnd_7555976 := by
    simpa [prefixWord, tailWord_7555976, baseEnd_7555976] using wordTrace_append hprefix tailTrace_7555976
  have hstable : (prefixWord ++ tailWord_7555976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7555976).length < 2 ^ (prefixWord ++ tailWord_7555976).sum := by decide
  have hdescent : baseEnd_7555976 < baseStart_7555976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7555976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556003 : List Nat := [1, 1, 1, 4, 1, 2, 6, 1, 1, 3, 2]
def baseStart_7556003 : Nat := 118140960795 + 7556003 * 2 ^ 59
def prefixEnd_7556003 : Nat := 4983230072969 + 3 ^ 40 * 7556003 * 2
def baseEnd_7556003 : Nat := 3879861365814505837213081

theorem tailTrace_7556003 : CollatzResearch.WordTrace tailWord_7556003 prefixEnd_7556003 3879861365814505837213081 := by
  unfold tailWord_7556003
  simp only [CollatzResearch.WordTrace]
  refine ⟨275590070044899068418536663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183726713363266045612357775 275590070044899068418536663)
  ·
    refine ⟨413385105067348602627804995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275590070044899068418536663 413385105067348602627804995)
    ·
      refine ⟨620077657601022903941707493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413385105067348602627804995 620077657601022903941707493)
      ·
        refine ⟨116264560800191794489070155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 620077657601022903941707493 116264560800191794489070155)
        ·
          refine ⟨174396841200287691733605233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116264560800191794489070155 174396841200287691733605233)
          ·
            refine ⟨130797630900215768800203925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174396841200287691733605233 130797630900215768800203925)
            ·
              refine ⟨6131138948447614162509559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130797630900215768800203925 6131138948447614162509559)
              ·
                refine ⟨9196708422671421243764339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6131138948447614162509559 9196708422671421243764339)
                ·
                  refine ⟨13795062634007131865646509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9196708422671421243764339 13795062634007131865646509)
                  ·
                    refine ⟨5173148487752674449617441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13795062634007131865646509 5173148487752674449617441)
                    ·
                      refine ⟨3879861365814505837213081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5173148487752674449617441 3879861365814505837213081)
                      ·
                        rfl

theorem cell23_7556003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 1, 3, 2].length) (baseStart_7556003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556003 prefixEnd_7556003 := by exact prefixLift 7556003
  have htrace : WordTrace (prefixWord ++ tailWord_7556003) baseStart_7556003 baseEnd_7556003 := by
    simpa [prefixWord, tailWord_7556003, baseEnd_7556003] using wordTrace_append hprefix tailTrace_7556003
  have hstable : (prefixWord ++ tailWord_7556003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556003).length < 2 ^ (prefixWord ++ tailWord_7556003).sum := by decide
  have hdescent : baseEnd_7556003 < baseStart_7556003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556012 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 4]
def baseStart_7556012 : Nat := 118140960795 + 7556012 * 2 ^ 59
def prefixEnd_7556012 : Nat := 4983230072969 + 3 ^ 40 * 7556012 * 2
def baseEnd_7556012 : Nat := 3879865987140396302000539

theorem tailTrace_7556012 : CollatzResearch.WordTrace tailWord_7556012 prefixEnd_7556012 3879865987140396302000539 := by
  unfold tailWord_7556012
  simp only [CollatzResearch.WordTrace]
  refine ⟨137795199150933231477807145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183726932201244308637076193 137795199150933231477807145)
  ·
    refine ⟨103346399363199923608355359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137795199150933231477807145 103346399363199923608355359)
    ·
      refine ⟨155019599044799885412533039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103346399363199923608355359 155019599044799885412533039)
      ·
        refine ⟨232529398567199828118799559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155019599044799885412533039 232529398567199828118799559)
        ·
          refine ⟨348794097850799742178199339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232529398567199828118799559 348794097850799742178199339)
          ·
            refine ⟨523191146776199613267299009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348794097850799742178199339 523191146776199613267299009)
            ·
              refine ⟨392393360082149709950474257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 523191146776199613267299009 392393360082149709950474257)
              ·
                refine ⟨294295020061612282462855693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 392393360082149709950474257 294295020061612282462855693)
                ·
                  refine ⟨110360632523104605923570885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294295020061612282462855693 110360632523104605923570885)
                  ·
                    refine ⟨20692618598082113610669541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110360632523104605923570885 20692618598082113610669541)
                    ·
                      refine ⟨3879865987140396302000539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20692618598082113610669541 3879865987140396302000539)
                      ·
                        rfl

theorem cell23_7556012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_7556012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556012 prefixEnd_7556012 := by exact prefixLift 7556012
  have htrace : WordTrace (prefixWord ++ tailWord_7556012) baseStart_7556012 baseEnd_7556012 := by
    simpa [prefixWord, tailWord_7556012, baseEnd_7556012] using wordTrace_append hprefix tailTrace_7556012
  have hstable : (prefixWord ++ tailWord_7556012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556012).length < 2 ^ (prefixWord ++ tailWord_7556012).sum := by decide
  have hdescent : baseEnd_7556012 < baseStart_7556012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556056 : List Nat := [2, 1, 2, 2, 2, 3, 3, 3, 5]
def baseStart_7556056 : Nat := 118140960795 + 7556056 * 2 ^ 59
def prefixEnd_7556056 : Nat := 4983230072969 + 3 ^ 40 * 7556056 * 2
def baseEnd_7556056 : Nat := 431098731143243792205593

theorem tailTrace_7556056 : CollatzResearch.WordTrace tailWord_7556056 prefixEnd_7556056 431098731143243792205593 := by
  unfold tailWord_7556056
  simp only [CollatzResearch.WordTrace]
  refine ⟨137796001556853529235108011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183728002075804705646810681 137796001556853529235108011)
  ·
    refine ⟨206694002335280293852662017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137796001556853529235108011 206694002335280293852662017)
    ·
      refine ⟨155020501751460220389496513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206694002335280293852662017 155020501751460220389496513)
      ·
        refine ⟨116265376313595165292122385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155020501751460220389496513 116265376313595165292122385)
        ·
          refine ⟨87199032235196373969091789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116265376313595165292122385 87199032235196373969091789)
          ·
            refine ⟨32699637088198640238409421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87199032235196373969091789 32699637088198640238409421)
            ·
              refine ⟨12262363908074490089403533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32699637088198640238409421 12262363908074490089403533)
              ·
                refine ⟨4598386465527933783526325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12262363908074490089403533 4598386465527933783526325)
                ·
                  refine ⟨431098731143243792205593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4598386465527933783526325 431098731143243792205593)
                  ·
                    rfl

theorem cell23_7556056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3, 5].length) (baseStart_7556056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556056 prefixEnd_7556056 := by exact prefixLift 7556056
  have htrace : WordTrace (prefixWord ++ tailWord_7556056) baseStart_7556056 baseEnd_7556056 := by
    simpa [prefixWord, tailWord_7556056, baseEnd_7556056] using wordTrace_append hprefix tailTrace_7556056
  have hstable : (prefixWord ++ tailWord_7556056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556056).length < 2 ^ (prefixWord ++ tailWord_7556056).sum := by decide
  have hdescent : baseEnd_7556056 < baseStart_7556056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556079 : List Nat := [1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 5]
def baseStart_7556079 : Nat := 118140960795 + 7556079 * 2 ^ 59
def prefixEnd_7556079 : Nat := 4983230072969 + 3 ^ 40 * 7556079 * 2
def baseEnd_7556079 : Nat := 3879900390344247539862731

theorem tailTrace_7556079 : CollatzResearch.WordTrace tailWord_7556079 prefixEnd_7556079 3879900390344247539862731 := by
  unfold tailWord_7556079
  simp only [CollatzResearch.WordTrace]
  refine ⟨275592841992623733398303291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183728561328415822265535527 275592841992623733398303291)
  ·
    refine ⟨413389262988935600097454937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275592841992623733398303291 413389262988935600097454937)
    ·
      refine ⟨310041947241701700073091203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413389262988935600097454937 310041947241701700073091203)
      ·
        refine ⟨465062920862552550109636805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310041947241701700073091203 465062920862552550109636805)
        ·
          refine ⟨87199297661728603145556901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 465062920862552550109636805 87199297661728603145556901)
          ·
            refine ⟨16349868311574113089791919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87199297661728603145556901 16349868311574113089791919)
            ·
              refine ⟨24524802467361169634687879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16349868311574113089791919 24524802467361169634687879)
              ·
                refine ⟨36787203701041754452031819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24524802467361169634687879 36787203701041754452031819)
                ·
                  refine ⟨55180805551562631678047729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36787203701041754452031819 55180805551562631678047729)
                  ·
                    refine ⟨41385604163671973758535797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55180805551562631678047729 41385604163671973758535797)
                    ·
                      refine ⟨3879900390344247539862731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41385604163671973758535797 3879900390344247539862731)
                      ·
                        rfl

theorem cell23_7556079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 5].length) (baseStart_7556079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556079 prefixEnd_7556079 := by exact prefixLift 7556079
  have htrace : WordTrace (prefixWord ++ tailWord_7556079) baseStart_7556079 baseEnd_7556079 := by
    simpa [prefixWord, tailWord_7556079, baseEnd_7556079] using wordTrace_append hprefix tailTrace_7556079
  have hstable : (prefixWord ++ tailWord_7556079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556079).length < 2 ^ (prefixWord ++ tailWord_7556079).sum := by decide
  have hdescent : baseEnd_7556079 < baseStart_7556079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556089 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 4, 1, 4]
def baseStart_7556089 : Nat := 118140960795 + 7556089 * 2 ^ 59
def prefixEnd_7556089 : Nat := 4983230072969 + 3 ^ 40 * 7556089 * 2
def baseEnd_7556089 : Nat := 3879905525150792500737685

theorem tailTrace_7556089 : CollatzResearch.WordTrace tailWord_7556089 prefixEnd_7556089 3879905525150792500737685 := by
  unfold tailWord_7556089
  simp only [CollatzResearch.WordTrace]
  refine ⟨275593206722587505106167321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183728804481725003404111547 275593206722587505106167321)
  ·
    refine ⟨206694905041940628829625491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275593206722587505106167321 206694905041940628829625491)
    ·
      refine ⟨310042357562910943244438237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206694905041940628829625491 310042357562910943244438237)
      ·
        refine ⟨116265884086091603716664339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310042357562910943244438237 116265884086091603716664339)
        ·
          refine ⟨174398826129137405574996509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116265884086091603716664339 174398826129137405574996509)
          ·
            refine ⟨65399559798426527090623691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174398826129137405574996509 65399559798426527090623691)
            ·
              refine ⟨98099339697639790635935537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65399559798426527090623691 98099339697639790635935537)
              ·
                refine ⟨73574504773229842976951653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98099339697639790635935537 73574504773229842976951653)
                ·
                  refine ⟨13795219644980595558178435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73574504773229842976951653 13795219644980595558178435)
                  ·
                    refine ⟨20692829467470893337267653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13795219644980595558178435 20692829467470893337267653)
                    ·
                      refine ⟨3879905525150792500737685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20692829467470893337267653 3879905525150792500737685)
                      ·
                        rfl

theorem cell23_7556089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_7556089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556089 prefixEnd_7556089 := by exact prefixLift 7556089
  have htrace : WordTrace (prefixWord ++ tailWord_7556089) baseStart_7556089 baseEnd_7556089 := by
    simpa [prefixWord, tailWord_7556089, baseEnd_7556089] using wordTrace_append hprefix tailTrace_7556089
  have hstable : (prefixWord ++ tailWord_7556089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556089).length < 2 ^ (prefixWord ++ tailWord_7556089).sum := by decide
  have hdescent : baseEnd_7556089 < baseStart_7556089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556106 : List Nat := [3, 1, 2, 2, 3, 1, 1, 3, 2, 1, 4]
def baseStart_7556106 : Nat := 118140960795 + 7556106 * 2 ^ 59
def prefixEnd_7556106 : Nat := 4983230072969 + 3 ^ 40 * 7556106 * 2
def baseEnd_7556106 : Nat := 3879914254321918934225107

theorem tailTrace_7556106 : CollatzResearch.WordTrace tailWord_7556106 prefixEnd_7556106 3879914254321918934225107 := by
  unfold tailWord_7556106
  simp only [CollatzResearch.WordTrace]
  refine ⟨68898456690881479252384043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183729217842350611339690781 68898456690881479252384043)
  ·
    refine ⟨103347685036322218878576065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68898456690881479252384043 103347685036322218878576065)
    ·
      refine ⟨77510763777241664158932049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103347685036322218878576065 77510763777241664158932049)
      ·
        refine ⟨58133072832931248119199037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77510763777241664158932049 58133072832931248119199037)
        ·
          refine ⟨21799902312349218044699639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58133072832931248119199037 21799902312349218044699639)
          ·
            refine ⟨32699853468523827067049459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21799902312349218044699639 32699853468523827067049459)
            ·
              refine ⟨49049780202785740600574189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32699853468523827067049459 49049780202785740600574189)
              ·
                refine ⟨18393667576044652725215321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49049780202785740600574189 18393667576044652725215321)
                ·
                  refine ⟨13795250682033489543911491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18393667576044652725215321 13795250682033489543911491)
                  ·
                    refine ⟨20692876023050234315867237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13795250682033489543911491 20692876023050234315867237)
                    ·
                      refine ⟨3879914254321918934225107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20692876023050234315867237 3879914254321918934225107)
                      ·
                        rfl

theorem cell23_7556106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_7556106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556106 prefixEnd_7556106 := by exact prefixLift 7556106
  have htrace : WordTrace (prefixWord ++ tailWord_7556106) baseStart_7556106 baseEnd_7556106 := by
    simpa [prefixWord, tailWord_7556106, baseEnd_7556106] using wordTrace_append hprefix tailTrace_7556106
  have hstable : (prefixWord ++ tailWord_7556106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556106).length < 2 ^ (prefixWord ++ tailWord_7556106).sum := by decide
  have hdescent : baseEnd_7556106 < baseStart_7556106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556133 : List Nat := [1, 3, 1, 2, 2, 2, 3, 4, 1, 4]
def baseStart_7556133 : Nat := 118140960795 + 7556133 * 2 ^ 59
def prefixEnd_7556133 : Nat := 4983230072969 + 3 ^ 40 * 7556133 * 2
def baseEnd_7556133 : Nat := 1293309372766530109529161

theorem tailTrace_7556133 : CollatzResearch.WordTrace tailWord_7556133 prefixEnd_7556133 1293309372766530109529161 := by
  unfold tailWord_7556133
  simp only [CollatzResearch.WordTrace]
  refine ⟨275594811534428100620769053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183729874356285400413846035 275594811534428100620769053)
  ·
    refine ⟨103348054325410537732788395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275594811534428100620769053 103348054325410537732788395)
    ·
      refine ⟨155022081488115806599182593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103348054325410537732788395 155022081488115806599182593)
      ·
        refine ⟨116266561116086854949386945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155022081488115806599182593 116266561116086854949386945)
        ·
          refine ⟨87199920837065141212040209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116266561116086854949386945 87199920837065141212040209)
          ·
            refine ⟨65399940627798855909030157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87199920837065141212040209 65399940627798855909030157)
            ·
              refine ⟨24524977735424570965886309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65399940627798855909030157 24524977735424570965886309)
              ·
                refine ⟨4598433325392107056103683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24524977735424570965886309 4598433325392107056103683)
                ·
                  refine ⟨6897649988088160584155525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4598433325392107056103683 6897649988088160584155525)
                  ·
                    refine ⟨1293309372766530109529161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6897649988088160584155525 1293309372766530109529161)
                    ·
                      rfl

theorem cell23_7556133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4, 1, 4].length) (baseStart_7556133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556133 prefixEnd_7556133 := by exact prefixLift 7556133
  have htrace : WordTrace (prefixWord ++ tailWord_7556133) baseStart_7556133 baseEnd_7556133 := by
    simpa [prefixWord, tailWord_7556133, baseEnd_7556133] using wordTrace_append hprefix tailTrace_7556133
  have hstable : (prefixWord ++ tailWord_7556133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556133).length < 2 ^ (prefixWord ++ tailWord_7556133).sum := by decide
  have hdescent : baseEnd_7556133 < baseStart_7556133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556216 : List Nat := [2, 1, 2, 1, 1, 1, 4, 3, 3, 2, 3]
def baseStart_7556216 : Nat := 118140960795 + 7556216 * 2 ^ 59
def prefixEnd_7556216 : Nat := 4983230072969 + 3 ^ 40 * 7556216 * 2
def baseEnd_7556216 : Nat := 3879970737193913503849601

theorem tailTrace_7556216 : CollatzResearch.WordTrace tailWord_7556216 prefixEnd_7556216 3879970737193913503849601 := by
  unfold tailWord_7556216
  simp only [CollatzResearch.WordTrace]
  refine ⟨137798919396563702898020251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183731892528751603864027001 137798919396563702898020251)
  ·
    refine ⟨206698379094845554347030377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137798919396563702898020251 206698379094845554347030377)
    ·
      refine ⟨155023784321134165760272783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206698379094845554347030377 155023784321134165760272783)
      ·
        refine ⟨232535676481701248640409175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155023784321134165760272783 232535676481701248640409175)
        ·
          refine ⟨348803514722551872960613763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232535676481701248640409175 348803514722551872960613763)
          ·
            refine ⟨523205272083827809440920645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348803514722551872960613763 523205272083827809440920645)
            ·
              refine ⟨98100988515717714270172621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 523205272083827809440920645 98100988515717714270172621)
              ·
                refine ⟨36787870693394142851314733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98100988515717714270172621 36787870693394142851314733)
                ·
                  refine ⟨13795451510022803569243025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36787870693394142851314733 13795451510022803569243025)
                  ·
                    refine ⟨10346588632517102676932269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13795451510022803569243025 10346588632517102676932269)
                    ·
                      refine ⟨3879970737193913503849601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10346588632517102676932269 3879970737193913503849601)
                      ·
                        rfl

theorem cell23_7556216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 3, 2, 3].length) (baseStart_7556216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556216 prefixEnd_7556216 := by exact prefixLift 7556216
  have htrace : WordTrace (prefixWord ++ tailWord_7556216) baseStart_7556216 baseEnd_7556216 := by
    simpa [prefixWord, tailWord_7556216, baseEnd_7556216] using wordTrace_append hprefix tailTrace_7556216
  have hstable : (prefixWord ++ tailWord_7556216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556216).length < 2 ^ (prefixWord ++ tailWord_7556216).sum := by decide
  have hdescent : baseEnd_7556216 < baseStart_7556216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556233 : List Nat := [1, 2, 1, 1, 4, 3, 2, 3, 1, 2, 3]
def baseStart_7556233 : Nat := 118140960795 + 7556233 * 2 ^ 59
def prefixEnd_7556233 : Nat := 4983230072969 + 3 ^ 40 * 7556233 * 2
def baseEnd_7556233 : Nat := 3879979466365039937337023

theorem tailTrace_7556233 : CollatzResearch.WordTrace tailWord_7556233 prefixEnd_7556233 3879979466365039937337023 := by
  unfold tailWord_7556233
  simp only [CollatzResearch.WordTrace]
  refine ⟨275598458834065817699409353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183732305889377211799606235 275598458834065817699409353)
  ·
    refine ⟨206698844125549363274557015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275598458834065817699409353 206698844125549363274557015)
    ·
      refine ⟨310048266188324044911835523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206698844125549363274557015 310048266188324044911835523)
      ·
        refine ⟨465072399282486067367753285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310048266188324044911835523 465072399282486067367753285)
        ·
          refine ⟨87201074865466137631453741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 465072399282486067367753285 87201074865466137631453741)
          ·
            refine ⟨32700403074549801611795153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87201074865466137631453741 32700403074549801611795153)
            ·
              refine ⟨24525302305912351208846365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32700403074549801611795153 24525302305912351208846365)
              ·
                refine ⟨9196988364717131703317387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24525302305912351208846365 9196988364717131703317387)
                ·
                  refine ⟨13795482547075697554976081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9196988364717131703317387 13795482547075697554976081)
                  ·
                    refine ⟨10346611910306773166232061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13795482547075697554976081 10346611910306773166232061)
                    ·
                      refine ⟨3879979466365039937337023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10346611910306773166232061 3879979466365039937337023)
                      ·
                        rfl

theorem cell23_7556233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 2, 3].length) (baseStart_7556233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556233 prefixEnd_7556233 := by exact prefixLift 7556233
  have htrace : WordTrace (prefixWord ++ tailWord_7556233) baseStart_7556233 baseEnd_7556233 := by
    simpa [prefixWord, tailWord_7556233, baseEnd_7556233] using wordTrace_append hprefix tailTrace_7556233
  have hstable : (prefixWord ++ tailWord_7556233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556233).length < 2 ^ (prefixWord ++ tailWord_7556233).sum := by decide
  have hdescent : baseEnd_7556233 < baseStart_7556233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556247 : List Nat := [1, 1, 3, 3, 3, 3, 1, 1, 3, 2, 2]
def baseStart_7556247 : Nat := 118140960795 + 7556247 * 2 ^ 59
def prefixEnd_7556247 : Nat := 4983230072969 + 3 ^ 40 * 7556247 * 2
def baseEnd_7556247 : Nat := 3879986655094202882561959

theorem tailTrace_7556247 : CollatzResearch.WordTrace tailWord_7556247 prefixEnd_7556247 3879986655094202882561959 := by
  unfold tailWord_7556247
  simp only [CollatzResearch.WordTrace]
  refine ⟨275598969456015098090418995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183732646304010065393612663 275598969456015098090418995)
  ·
    refine ⟨413398454184022647135628493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275598969456015098090418995 413398454184022647135628493)
    ·
      refine ⟨155024420319008492675860685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413398454184022647135628493 155024420319008492675860685)
      ·
        refine ⟨58134157619628184753447757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155024420319008492675860685 58134157619628184753447757)
        ·
          refine ⟨21800309107360569282542909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58134157619628184753447757 21800309107360569282542909)
          ·
            refine ⟨8175115915260213480953591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21800309107360569282542909 8175115915260213480953591)
            ·
              refine ⟨12262673872890320221430387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8175115915260213480953591 12262673872890320221430387)
              ·
                refine ⟨18394010809335480332145581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12262673872890320221430387 18394010809335480332145581)
                ·
                  refine ⟨6897754053500805124554593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18394010809335480332145581 6897754053500805124554593)
                  ·
                    refine ⟨5173315540125603843415945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6897754053500805124554593 5173315540125603843415945)
                    ·
                      refine ⟨3879986655094202882561959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5173315540125603843415945 3879986655094202882561959)
                      ·
                        rfl

theorem cell23_7556247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_7556247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556247 prefixEnd_7556247 := by exact prefixLift 7556247
  have htrace : WordTrace (prefixWord ++ tailWord_7556247) baseStart_7556247 baseEnd_7556247 := by
    simpa [prefixWord, tailWord_7556247, baseEnd_7556247] using wordTrace_append hprefix tailTrace_7556247
  have hstable : (prefixWord ++ tailWord_7556247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556247).length < 2 ^ (prefixWord ++ tailWord_7556247).sum := by decide
  have hdescent : baseEnd_7556247 < baseStart_7556247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556320 : List Nat := [2, 1, 1, 3, 1, 5, 2, 1, 1, 4, 2]
def baseStart_7556320 : Nat := 118140960795 + 7556320 * 2 ^ 59
def prefixEnd_7556320 : Nat := 4983230072969 + 3 ^ 40 * 7556320 * 2
def baseEnd_7556320 : Nat := 3880024139181981096949123

theorem tailTrace_7556320 : CollatzResearch.WordTrace tailWord_7556320 prefixEnd_7556320 3880024139181981096949123 := by
  unfold tailWord_7556320
  simp only [CollatzResearch.WordTrace]
  refine ⟨137800815992375315778913207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183734421323167087705217609 137800815992375315778913207)
  ·
    refine ⟨206701223988562973668369811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137800815992375315778913207 206701223988562973668369811)
    ·
      refine ⟨310051835982844460502554717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206701223988562973668369811 310051835982844460502554717)
      ·
        refine ⟨116269438493566672688458019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310051835982844460502554717 116269438493566672688458019)
        ·
          refine ⟨174404157740350009032687029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116269438493566672688458019 174404157740350009032687029)
          ·
            refine ⟨16350389788157813346814409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174404157740350009032687029 16350389788157813346814409)
            ·
              refine ⟨12262792341118360010110807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16350389788157813346814409 12262792341118360010110807)
              ·
                refine ⟨18394188511677540015166211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12262792341118360010110807 18394188511677540015166211)
                ·
                  refine ⟨27591282767516310022749317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18394188511677540015166211 27591282767516310022749317)
                  ·
                    refine ⟨5173365518909308129265497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27591282767516310022749317 5173365518909308129265497)
                    ·
                      refine ⟨3880024139181981096949123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5173365518909308129265497 3880024139181981096949123)
                      ·
                        rfl

theorem cell23_7556320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 1, 4, 2].length) (baseStart_7556320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556320 prefixEnd_7556320 := by exact prefixLift 7556320
  have htrace : WordTrace (prefixWord ++ tailWord_7556320) baseStart_7556320 baseEnd_7556320 := by
    simpa [prefixWord, tailWord_7556320, baseEnd_7556320] using wordTrace_append hprefix tailTrace_7556320
  have hstable : (prefixWord ++ tailWord_7556320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556320).length < 2 ^ (prefixWord ++ tailWord_7556320).sum := by decide
  have hdescent : baseEnd_7556320 < baseStart_7556320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556353 : List Nat := [1, 2, 4, 1, 1, 3, 1, 2, 2, 3, 3]
def baseStart_7556353 : Nat := 118140960795 + 7556353 * 2 ^ 59
def prefixEnd_7556353 : Nat := 4983230072969 + 3 ^ 40 * 7556353 * 2
def baseEnd_7556353 : Nat := 3880041084043579467836471

theorem tailTrace_7556353 : CollatzResearch.WordTrace tailWord_7556353 prefixEnd_7556353 3880041084043579467836471 := by
  unfold tailWord_7556353
  simp only [CollatzResearch.WordTrace]
  refine ⟨275602835593631078193777713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183735223729087385462518475 275602835593631078193777713)
  ·
    refine ⟨206702126695223308645333285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275602835593631078193777713 206702126695223308645333285)
    ·
      refine ⟨38756648755354370370999991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206702126695223308645333285 38756648755354370370999991)
      ·
        refine ⟨58134973133031555556499987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38756648755354370370999991 58134973133031555556499987)
        ·
          refine ⟨87202459699547333334749981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58134973133031555556499987 87202459699547333334749981)
          ·
            refine ⟨32700922387330250000531243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87202459699547333334749981 32700922387330250000531243)
            ·
              refine ⟨49051383580995375000796865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32700922387330250000531243 49051383580995375000796865)
              ·
                refine ⟨36788537685746531250597649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49051383580995375000796865 36788537685746531250597649)
                ·
                  refine ⟨27591403264309898437948237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36788537685746531250597649 27591403264309898437948237)
                  ·
                    refine ⟨10346776224116211914230589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27591403264309898437948237 10346776224116211914230589)
                    ·
                      refine ⟨3880041084043579467836471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10346776224116211914230589 3880041084043579467836471)
                      ·
                        rfl

theorem cell23_7556353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_7556353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556353 prefixEnd_7556353 := by exact prefixLift 7556353
  have htrace : WordTrace (prefixWord ++ tailWord_7556353) baseStart_7556353 baseEnd_7556353 := by
    simpa [prefixWord, tailWord_7556353, baseEnd_7556353] using wordTrace_append hprefix tailTrace_7556353
  have hstable : (prefixWord ++ tailWord_7556353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556353).length < 2 ^ (prefixWord ++ tailWord_7556353).sum := by decide
  have hdescent : baseEnd_7556353 < baseStart_7556353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556354 : List Nat := [3, 4, 1, 1, 3, 1, 1, 1, 4, 2, 2]
def baseStart_7556354 : Nat := 118140960795 + 7556354 * 2 ^ 59
def prefixEnd_7556354 : Nat := 4983230072969 + 3 ^ 40 * 7556354 * 2
def baseEnd_7556354 : Nat := 3880041597524233963923967

theorem tailTrace_7556354 : CollatzResearch.WordTrace tailWord_7556354 prefixEnd_7556354 3880041597524233963923967 := by
  unfold tailWord_7556354
  simp only [CollatzResearch.WordTrace]
  refine ⟨68900718016656863841141029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183735248044418303576376077 68900718016656863841141029)
  ·
    refine ⟨12918884628123161970213943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68900718016656863841141029 12918884628123161970213943)
    ·
      refine ⟨19378326942184742955320915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12918884628123161970213943 19378326942184742955320915)
      ·
        refine ⟨29067490413277114432981373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19378326942184742955320915 29067490413277114432981373)
        ·
          refine ⟨10900308904978917912368015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29067490413277114432981373 10900308904978917912368015)
          ·
            refine ⟨16350463357468376868552023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10900308904978917912368015 16350463357468376868552023)
            ·
              refine ⟨24525695036202565302828035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16350463357468376868552023 24525695036202565302828035)
              ·
                refine ⟨36788542554303847954242053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24525695036202565302828035 36788542554303847954242053)
                ·
                  refine ⟨6897851728931971491420385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36788542554303847954242053 6897851728931971491420385)
                  ·
                    refine ⟨5173388796698978618565289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6897851728931971491420385 5173388796698978618565289)
                    ·
                      refine ⟨3880041597524233963923967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5173388796698978618565289 3880041597524233963923967)
                      ·
                        rfl

theorem cell23_7556354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_7556354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556354 prefixEnd_7556354 := by exact prefixLift 7556354
  have htrace : WordTrace (prefixWord ++ tailWord_7556354) baseStart_7556354 baseEnd_7556354 := by
    simpa [prefixWord, tailWord_7556354, baseEnd_7556354] using wordTrace_append hprefix tailTrace_7556354
  have hstable : (prefixWord ++ tailWord_7556354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556354).length < 2 ^ (prefixWord ++ tailWord_7556354).sum := by decide
  have hdescent : baseEnd_7556354 < baseStart_7556354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556396 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 5]
def baseStart_7556396 : Nat := 118140960795 + 7556396 * 2 ^ 59
def prefixEnd_7556396 : Nat := 4983230072969 + 3 ^ 40 * 7556396 * 2
def baseEnd_7556396 : Nat := 3880063163711722799598773

theorem tailTrace_7556396 : CollatzResearch.WordTrace tailWord_7556396 prefixEnd_7556396 3880063163711722799598773 := by
  unfold tailWord_7556396
  simp only [CollatzResearch.WordTrace]
  refine ⟨137802201966237648268796521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183736269288316864358395361 137802201966237648268796521)
  ·
    refine ⟨103351651474678236201597391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137802201966237648268796521 103351651474678236201597391)
    ·
      refine ⟨155027477212017354302396087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103351651474678236201597391 155027477212017354302396087)
      ·
        refine ⟨232541215818026031453594131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155027477212017354302396087 232541215818026031453594131)
        ·
          refine ⟨348811823727039047180391197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232541215818026031453594131 348811823727039047180391197)
          ·
            refine ⟨130804433897639642692646699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 348811823727039047180391197 130804433897639642692646699)
            ·
              refine ⟨196206650846459464038970049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130804433897639642692646699 196206650846459464038970049)
              ·
                refine ⟨147154988134844598029227537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196206650846459464038970049 147154988134844598029227537)
                ·
                  refine ⟨110366241101133448521920653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147154988134844598029227537 110366241101133448521920653)
                  ·
                    refine ⟨41387340412925043195720245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110366241101133448521920653 41387340412925043195720245)
                    ·
                      refine ⟨3880063163711722799598773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41387340412925043195720245 3880063163711722799598773)
                      ·
                        rfl

theorem cell23_7556396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_7556396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556396 prefixEnd_7556396 := by exact prefixLift 7556396
  have htrace : WordTrace (prefixWord ++ tailWord_7556396) baseStart_7556396 baseEnd_7556396 := by
    simpa [prefixWord, tailWord_7556396, baseEnd_7556396] using wordTrace_append hprefix tailTrace_7556396
  have hstable : (prefixWord ++ tailWord_7556396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556396).length < 2 ^ (prefixWord ++ tailWord_7556396).sum := by decide
  have hdescent : baseEnd_7556396 < baseStart_7556396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556416 : List Nat := [2, 1, 1, 2, 2, 1, 3, 3, 8]
def baseStart_7556416 : Nat := 118140960795 + 7556416 * 2 ^ 59
def prefixEnd_7556416 : Nat := 4983230072969 + 3 ^ 40 * 7556416 * 2
def baseEnd_7556416 : Nat := 431119270369423635705409

theorem tailTrace_7556416 : CollatzResearch.WordTrace tailWord_7556416 prefixEnd_7556416 431119270369423635705409 := by
  unfold tailWord_7556416
  simp only [CollatzResearch.WordTrace]
  refine ⟨137802566696201419976660551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183736755594935226635547401 137802566696201419976660551)
  ·
    refine ⟨206703850044302129964990827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137802566696201419976660551 206703850044302129964990827)
    ·
      refine ⟨310055775066453194947486241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206703850044302129964990827 310055775066453194947486241)
      ·
        refine ⟨232541831299839896210614681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310055775066453194947486241 232541831299839896210614681)
        ·
          refine ⟨174406373474879922157961011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232541831299839896210614681 174406373474879922157961011)
          ·
            refine ⟨261609560212319883236941517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174406373474879922157961011 261609560212319883236941517)
            ·
              refine ⟨98103585079619956213853069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261609560212319883236941517 98103585079619956213853069)
              ·
                refine ⟨36788844404857483580194901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98103585079619956213853069 36788844404857483580194901)
                ·
                  refine ⟨431119270369423635705409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36788844404857483580194901 431119270369423635705409)
                  ·
                    rfl

theorem cell23_7556416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 8].length) (baseStart_7556416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556416 prefixEnd_7556416 := by exact prefixLift 7556416
  have htrace : WordTrace (prefixWord ++ tailWord_7556416) baseStart_7556416 baseEnd_7556416 := by
    simpa [prefixWord, tailWord_7556416, baseEnd_7556416] using wordTrace_append hprefix tailTrace_7556416
  have hstable : (prefixWord ++ tailWord_7556416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556416).length < 2 ^ (prefixWord ++ tailWord_7556416).sum := by decide
  have hdescent : baseEnd_7556416 < baseStart_7556416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556422 : List Nat := [6, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2]
def baseStart_7556422 : Nat := 118140960795 + 7556422 * 2 ^ 59
def prefixEnd_7556422 : Nat := 4983230072969 + 3 ^ 40 * 7556422 * 2
def baseEnd_7556422 : Nat := 3880076514208739697873655

theorem tailTrace_7556422 : CollatzResearch.WordTrace tailWord_7556422 prefixEnd_7556422 3880076514208739697873655 := by
  unfold tailWord_7556422
  simp only [CollatzResearch.WordTrace]
  refine ⟨8612667257199409468063735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 183736901486920735318693013 8612667257199409468063735)
  ·
    refine ⟨12919000885799114202095603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8612667257199409468063735 12919000885799114202095603)
    ·
      refine ⟨19378501328698671303143405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12919000885799114202095603 19378501328698671303143405)
      ·
        refine ⟨7266937998262001738678777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19378501328698671303143405 7266937998262001738678777)
        ·
          refine ⟨5450203498696501304009083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7266937998262001738678777 5450203498696501304009083)
          ·
            refine ⟨8175305248044751956013625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5450203498696501304009083 8175305248044751956013625)
            ·
              refine ⟨6131478936033563967010219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8175305248044751956013625 6131478936033563967010219)
              ·
                refine ⟨9197218404050345950515329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6131478936033563967010219 9197218404050345950515329)
                ·
                  refine ⟨6897913803037759462886497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9197218404050345950515329 6897913803037759462886497)
                  ·
                    refine ⟨5173435352278319597164873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6897913803037759462886497 5173435352278319597164873)
                    ·
                      refine ⟨3880076514208739697873655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5173435352278319597164873 3880076514208739697873655)
                      ·
                        rfl

theorem cell23_7556422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_7556422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556422 prefixEnd_7556422 := by exact prefixLift 7556422
  have htrace : WordTrace (prefixWord ++ tailWord_7556422) baseStart_7556422 baseEnd_7556422 := by
    simpa [prefixWord, tailWord_7556422, baseEnd_7556422] using wordTrace_append hprefix tailTrace_7556422
  have hstable : (prefixWord ++ tailWord_7556422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556422).length < 2 ^ (prefixWord ++ tailWord_7556422).sum := by decide
  have hdescent : baseEnd_7556422 < baseStart_7556422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556433 : List Nat := [1, 2, 2, 1, 4, 1, 3, 3, 6]
def baseStart_7556433 : Nat := 118140960795 + 7556433 * 2 ^ 59
def prefixEnd_7556433 : Nat := 4983230072969 + 3 ^ 40 * 7556433 * 2
def baseEnd_7556433 : Nat := 431120240277326572759567

theorem tailTrace_7556433 : CollatzResearch.WordTrace tailWord_7556433 prefixEnd_7556433 431120240277326572759567 := by
  unfold tailWord_7556433
  simp only [CollatzResearch.WordTrace]
  refine ⟨275605753433341251856689953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183737168955560834571126635 275605753433341251856689953)
  ·
    refine ⟨206704315075005938892517465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275605753433341251856689953 206704315075005938892517465)
    ·
      refine ⟨155028236306254454169388099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206704315075005938892517465 155028236306254454169388099)
      ·
        refine ⟨232542354459381681254082149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155028236306254454169388099 232542354459381681254082149)
        ·
          refine ⟨43601691461134065235140403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232542354459381681254082149 43601691461134065235140403)
          ·
            refine ⟨65402537191701097852710605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43601691461134065235140403 65402537191701097852710605)
            ·
              refine ⟨24525951446887911694766477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65402537191701097852710605 24525951446887911694766477)
              ·
                refine ⟨9197231792582966885537429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24525951446887911694766477 9197231792582966885537429)
                ·
                  refine ⟨431120240277326572759567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9197231792582966885537429 431120240277326572759567)
                  ·
                    rfl

theorem cell23_7556433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 6].length) (baseStart_7556433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556433 prefixEnd_7556433 := by exact prefixLift 7556433
  have htrace : WordTrace (prefixWord ++ tailWord_7556433) baseStart_7556433 baseEnd_7556433 := by
    simpa [prefixWord, tailWord_7556433, baseEnd_7556433] using wordTrace_append hprefix tailTrace_7556433
  have hstable : (prefixWord ++ tailWord_7556433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556433).length < 2 ^ (prefixWord ++ tailWord_7556433).sum := by decide
  have hdescent : baseEnd_7556433 < baseStart_7556433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556494 : List Nat := [4, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3]
def baseStart_7556494 : Nat := 118140960795 + 7556494 * 2 ^ 59
def prefixEnd_7556494 : Nat := 4983230072969 + 3 ^ 40 * 7556494 * 2
def baseEnd_7556494 : Nat := 3880113484815863416173323

theorem tailTrace_7556494 : CollatzResearch.WordTrace tailWord_7556494 prefixEnd_7556494 3880113484815863416173323 := by
  unfold tailWord_7556494
  simp only [CollatzResearch.WordTrace]
  refine ⟨34450997285765032409332567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183738652190746839516440357 34450997285765032409332567)
  ·
    refine ⟨51676495928647548613998851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34450997285765032409332567 51676495928647548613998851)
    ·
      refine ⟨77514743892971322920998277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51676495928647548613998851 77514743892971322920998277)
      ·
        refine ⟨14534014479932123047687177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77514743892971322920998277 14534014479932123047687177)
        ·
          refine ⟨10900510859949092285765383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14534014479932123047687177 10900510859949092285765383)
          ·
            refine ⟨16350766289923638428648075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10900510859949092285765383 16350766289923638428648075)
            ·
              refine ⟨24526149434885457642972113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16350766289923638428648075 24526149434885457642972113)
              ·
                refine ⟨18394612076164093232229085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24526149434885457642972113 18394612076164093232229085)
                ·
                  refine ⟨6897979528561534962085907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18394612076164093232229085 6897979528561534962085907)
                  ·
                    refine ⟨10346969292842302443128861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6897979528561534962085907 10346969292842302443128861)
                    ·
                      refine ⟨3880113484815863416173323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10346969292842302443128861 3880113484815863416173323)
                      ·
                        rfl

theorem cell23_7556494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_7556494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556494 prefixEnd_7556494 := by exact prefixLift 7556494
  have htrace : WordTrace (prefixWord ++ tailWord_7556494) baseStart_7556494 baseEnd_7556494 := by
    simpa [prefixWord, tailWord_7556494, baseEnd_7556494] using wordTrace_append hprefix tailTrace_7556494
  have hstable : (prefixWord ++ tailWord_7556494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556494).length < 2 ^ (prefixWord ++ tailWord_7556494).sum := by decide
  have hdescent : baseEnd_7556494 < baseStart_7556494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556514 : List Nat := [3, 3, 1, 2, 1, 4, 2, 1, 1, 5]
def baseStart_7556514 : Nat := 118140960795 + 7556514 * 2 ^ 59
def prefixEnd_7556514 : Nat := 4983230072969 + 3 ^ 40 * 7556514 * 2
def baseEnd_7556514 : Nat := 1293374584809651112641077

theorem tailTrace_7556514 : CollatzResearch.WordTrace tailWord_7556514 prefixEnd_7556514 1293374584809651112641077 := by
  unfold tailWord_7556514
  simp only [CollatzResearch.WordTrace]
  refine ⟨68902176936511950672597149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183739138497365201793592397 68902176936511950672597149)
  ·
    refine ⟨25838316351191981502223931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68902176936511950672597149 25838316351191981502223931)
    ·
      refine ⟨38757474526787972253335897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25838316351191981502223931 38757474526787972253335897)
      ·
        refine ⟨29068105895090979190001923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38757474526787972253335897 29068105895090979190001923)
        ·
          refine ⟨43602158842636468785002885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29068105895090979190001923 43602158842636468785002885)
          ·
            refine ⟨8175404782994337897188041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43602158842636468785002885 8175404782994337897188041)
            ·
              refine ⟨6131553587245753422891031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8175404782994337897188041 6131553587245753422891031)
              ·
                refine ⟨9197330380868630134336547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6131553587245753422891031 9197330380868630134336547)
                ·
                  refine ⟨13795995571302945201504821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9197330380868630134336547 13795995571302945201504821)
                  ·
                    refine ⟨1293374584809651112641077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13795995571302945201504821 1293374584809651112641077)
                    ·
                      rfl

theorem cell23_7556514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_7556514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556514 prefixEnd_7556514 := by exact prefixLift 7556514
  have htrace : WordTrace (prefixWord ++ tailWord_7556514) baseStart_7556514 baseEnd_7556514 := by
    simpa [prefixWord, tailWord_7556514, baseEnd_7556514] using wordTrace_append hprefix tailTrace_7556514
  have hstable : (prefixWord ++ tailWord_7556514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556514).length < 2 ^ (prefixWord ++ tailWord_7556514).sum := by decide
  have hdescent : baseEnd_7556514 < baseStart_7556514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556590 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_7556590 : Nat := 118140960795 + 7556590 * 2 ^ 59
def prefixEnd_7556590 : Nat := 4983230072969 + 3 ^ 40 * 7556590 * 2
def baseEnd_7556590 : Nat := 3880162778958695040572881

theorem tailTrace_7556590 : CollatzResearch.WordTrace tailWord_7556590 prefixEnd_7556590 3880162778958695040572881 := by
  unfold tailWord_7556590
  simp only [CollatzResearch.WordTrace]
  refine ⟨34451434961721558458769403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183740986462514978446770149 34451434961721558458769403)
  ·
    refine ⟨51677152442582337688154105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34451434961721558458769403 51677152442582337688154105)
    ·
      refine ⟨38757864331936753266115579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51677152442582337688154105 38757864331936753266115579)
      ·
        refine ⟨58136796497905129899173369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38757864331936753266115579 58136796497905129899173369)
        ·
          refine ⟨43602597373428847424380027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58136796497905129899173369 43602597373428847424380027)
          ·
            refine ⟨65403896060143271136570041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43602597373428847424380027 65403896060143271136570041)
            ·
              refine ⟨49052922045107453352427531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65403896060143271136570041 49052922045107453352427531)
              ·
                refine ⟨73579383067661180028641297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49052922045107453352427531 73579383067661180028641297)
                ·
                  refine ⟨55184537300745885021480973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73579383067661180028641297 55184537300745885021480973)
                  ·
                    refine ⟨20694201487779706883055365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55184537300745885021480973 20694201487779706883055365)
                    ·
                      refine ⟨3880162778958695040572881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20694201487779706883055365 3880162778958695040572881)
                      ·
                        rfl

theorem cell23_7556590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_7556590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556590 prefixEnd_7556590 := by exact prefixLift 7556590
  have htrace : WordTrace (prefixWord ++ tailWord_7556590) baseStart_7556590 baseEnd_7556590 := by
    simpa [prefixWord, tailWord_7556590, baseEnd_7556590] using wordTrace_append hprefix tailTrace_7556590
  have hstable : (prefixWord ++ tailWord_7556590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556590).length < 2 ^ (prefixWord ++ tailWord_7556590).sum := by decide
  have hdescent : baseEnd_7556590 < baseStart_7556590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556607 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 6, 2, 2]
def baseStart_7556607 : Nat := 118140960795 + 7556607 * 2 ^ 59
def prefixEnd_7556607 : Nat := 4983230072969 + 3 ^ 40 * 7556607 * 2
def baseEnd_7556607 : Nat := 3880171508129821474060303

theorem tailTrace_7556607 : CollatzResearch.WordTrace tailWord_7556607 prefixEnd_7556607 3880171508129821474060303 := by
  unfold tailWord_7556607
  simp only [CollatzResearch.WordTrace]
  refine ⟨275612099734710879573524075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183741399823140586382349383 275612099734710879573524075)
  ·
    refine ⟨413418149602066319360286113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275612099734710879573524075 413418149602066319360286113)
    ·
      refine ⟨310063612201549739520214585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413418149602066319360286113 310063612201549739520214585)
      ·
        refine ⟨232547709151162304640160939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310063612201549739520214585 232547709151162304640160939)
        ·
          refine ⟨348821563726743456960241409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232547709151162304640160939 348821563726743456960241409)
          ·
            refine ⟨261616172795057592720181057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348821563726743456960241409 261616172795057592720181057)
            ·
              refine ⟨196212129596293194540135793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261616172795057592720181057 196212129596293194540135793)
              ·
                refine ⟨147159097197219895905101845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196212129596293194540135793 147159097197219895905101845)
                ·
                  refine ⟨6898082681119682620551649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147159097197219895905101845 6898082681119682620551649)
                  ·
                    refine ⟨5173562010839761965413737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6898082681119682620551649 5173562010839761965413737)
                    ·
                      refine ⟨3880171508129821474060303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5173562010839761965413737 3880171508129821474060303)
                      ·
                        rfl

theorem cell23_7556607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6, 2, 2].length) (baseStart_7556607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556607 prefixEnd_7556607 := by exact prefixLift 7556607
  have htrace : WordTrace (prefixWord ++ tailWord_7556607) baseStart_7556607 baseEnd_7556607 := by
    simpa [prefixWord, tailWord_7556607, baseEnd_7556607] using wordTrace_append hprefix tailTrace_7556607
  have hstable : (prefixWord ++ tailWord_7556607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556607).length < 2 ^ (prefixWord ++ tailWord_7556607).sum := by decide
  have hdescent : baseEnd_7556607 < baseStart_7556607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556613 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 9]
def baseStart_7556613 : Nat := 118140960795 + 7556613 * 2 ^ 59
def prefixEnd_7556613 : Nat := 4983230072969 + 3 ^ 40 * 7556613 * 2
def baseEnd_7556613 : Nat := 431130509890416494509475

theorem tailTrace_7556613 : CollatzResearch.WordTrace tailWord_7556613 prefixEnd_7556613 431130509890416494509475 := by
  unfold tailWord_7556613
  simp only [CollatzResearch.WordTrace]
  refine ⟨275612318572689142598242493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183741545715126095065494995 275612318572689142598242493)
  ·
    refine ⟨103354619464758428474340935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275612318572689142598242493 103354619464758428474340935)
    ·
      refine ⟨155031929197137642711511403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103354619464758428474340935 155031929197137642711511403)
      ·
        refine ⟨232547893795706464067267105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155031929197137642711511403 232547893795706464067267105)
        ·
          refine ⟨174410920346779848050450329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232547893795706464067267105 174410920346779848050450329)
          ·
            refine ⟨130808190260084886037837747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174410920346779848050450329 130808190260084886037837747)
            ·
              refine ⟨196212285390127329056756621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130808190260084886037837747 196212285390127329056756621)
              ·
                refine ⟨73579607021297748396283733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196212285390127329056756621 73579607021297748396283733)
                ·
                  refine ⟨431130509890416494509475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73579607021297748396283733 431130509890416494509475)
                  ·
                    rfl

theorem cell23_7556613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 9].length) (baseStart_7556613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556613 prefixEnd_7556613 := by exact prefixLift 7556613
  have htrace : WordTrace (prefixWord ++ tailWord_7556613) baseStart_7556613 baseEnd_7556613 := by
    simpa [prefixWord, tailWord_7556613, baseEnd_7556613] using wordTrace_append hprefix tailTrace_7556613
  have hstable : (prefixWord ++ tailWord_7556613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556613).length < 2 ^ (prefixWord ++ tailWord_7556613).sum := by decide
  have hdescent : baseEnd_7556613 < baseStart_7556613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556633 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 2, 4, 6]
def baseStart_7556633 : Nat := 118140960795 + 7556633 * 2 ^ 59
def prefixEnd_7556633 : Nat := 4983230072969 + 3 ^ 40 * 7556633 * 2
def baseEnd_7556633 : Nat := 3880184858626838372335183

theorem tailTrace_7556633 : CollatzResearch.WordTrace tailWord_7556633 prefixEnd_7556633 3880184858626838372335183 := by
  unfold tailWord_7556633
  simp only [CollatzResearch.WordTrace]
  refine ⟨275613048032616686013970553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183742032021744457342647035 275613048032616686013970553)
  ·
    refine ⟨206709786024462514510477915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275613048032616686013970553 206709786024462514510477915)
    ·
      refine ⟨310064679036693771765716873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206709786024462514510477915 310064679036693771765716873)
      ·
        refine ⟨232548509277520328824287655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310064679036693771765716873 232548509277520328824287655)
        ·
          refine ⟨348822763916280493236431483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232548509277520328824287655 348822763916280493236431483)
          ·
            refine ⟨523234145874420739854647225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348822763916280493236431483 523234145874420739854647225)
            ·
              refine ⟨392425609405815554890985419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 523234145874420739854647225 392425609405815554890985419)
              ·
                refine ⟨588638414108723332336478129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392425609405815554890985419 588638414108723332336478129)
                ·
                  refine ⟨441478810581542499252358597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 588638414108723332336478129 441478810581542499252358597)
                  ·
                    refine ⟨82777276984039218609817237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 441478810581542499252358597 82777276984039218609817237)
                    ·
                      refine ⟨3880184858626838372335183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82777276984039218609817237 3880184858626838372335183)
                      ·
                        rfl

theorem cell23_7556633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_7556633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556633 prefixEnd_7556633 := by exact prefixLift 7556633
  have htrace : WordTrace (prefixWord ++ tailWord_7556633) baseStart_7556633 baseEnd_7556633 := by
    simpa [prefixWord, tailWord_7556633, baseEnd_7556633] using wordTrace_append hprefix tailTrace_7556633
  have hstable : (prefixWord ++ tailWord_7556633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556633).length < 2 ^ (prefixWord ++ tailWord_7556633).sum := by decide
  have hdescent : baseEnd_7556633 < baseStart_7556633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556641 : List Nat := [1, 2, 3, 2, 2, 3, 2, 2, 2, 2, 2]
def baseStart_7556641 : Nat := 118140960795 + 7556641 * 2 ^ 59
def prefixEnd_7556641 : Nat := 4983230072969 + 3 ^ 40 * 7556641 * 2
def baseEnd_7556641 : Nat := 3880188966472074341035147

theorem tailTrace_7556641 : CollatzResearch.WordTrace tailWord_7556641 prefixEnd_7556641 3880188966472074341035147 := by
  unfold tailWord_7556641
  simp only [CollatzResearch.WordTrace]
  refine ⟨275613339816587703380261777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183742226544391802253507851 275613339816587703380261777)
  ·
    refine ⟨206710004862440777535196333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275613339816587703380261777 206710004862440777535196333)
    ·
      refine ⟨77516251823415291575698625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206710004862440777535196333 77516251823415291575698625)
      ·
        refine ⟨58137188867561468681773969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77516251823415291575698625 58137188867561468681773969)
        ·
          refine ⟨43602891650671101511330477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58137188867561468681773969 43602891650671101511330477)
          ·
            refine ⟨16351084369001663066748929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43602891650671101511330477 16351084369001663066748929)
            ·
              refine ⟨12263313276751247300061697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16351084369001663066748929 12263313276751247300061697)
              ·
                refine ⟨9197484957563435475046273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12263313276751247300061697 9197484957563435475046273)
                ·
                  refine ⟨6898113718172576606284705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9197484957563435475046273 6898113718172576606284705)
                  ·
                    refine ⟨5173585288629432454713529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6898113718172576606284705 5173585288629432454713529)
                    ·
                      refine ⟨3880188966472074341035147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5173585288629432454713529 3880188966472074341035147)
                      ·
                        rfl

theorem cell23_7556641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_7556641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556641 prefixEnd_7556641 := by exact prefixLift 7556641
  have htrace : WordTrace (prefixWord ++ tailWord_7556641) baseStart_7556641 baseEnd_7556641 := by
    simpa [prefixWord, tailWord_7556641, baseEnd_7556641] using wordTrace_append hprefix tailTrace_7556641
  have hstable : (prefixWord ++ tailWord_7556641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556641).length < 2 ^ (prefixWord ++ tailWord_7556641).sum := by decide
  have hdescent : baseEnd_7556641 < baseStart_7556641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556707 : List Nat := [1, 1, 1, 5, 1, 3, 1, 3, 3, 4]
def baseStart_7556707 : Nat := 118140960795 + 7556707 * 2 ^ 59
def prefixEnd_7556707 : Nat := 4983230072969 + 3 ^ 40 * 7556707 * 2
def baseEnd_7556707 : Nat := 1293407618731757027603281

theorem tailTrace_7556707 : CollatzResearch.WordTrace tailWord_7556707 prefixEnd_7556707 1293407618731757027603281 := by
  unfold tailWord_7556707
  simp only [CollatzResearch.WordTrace]
  refine ⟨275615747034348596652164375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183743831356232397768109583 275615747034348596652164375)
  ·
    refine ⟨413423620551522894978246563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275615747034348596652164375 413423620551522894978246563)
    ·
      refine ⟨620135430827284342467369845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413423620551522894978246563 620135430827284342467369845)
      ·
        refine ⟨58137696640057907106315923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 620135430827284342467369845 58137696640057907106315923)
        ·
          refine ⟨87206544960086860659473885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58137696640057907106315923 87206544960086860659473885)
          ·
            refine ⟨32702454360032572747302707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87206544960086860659473885 32702454360032572747302707)
            ·
              refine ⟨49053681540048859120954061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32702454360032572747302707 49053681540048859120954061)
              ·
                refine ⟨18395130577518322170357773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49053681540048859120954061 18395130577518322170357773)
                ·
                  refine ⟨6898173966569370813884165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18395130577518322170357773 6898173966569370813884165)
                  ·
                    refine ⟨1293407618731757027603281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6898173966569370813884165 1293407618731757027603281)
                    ·
                      rfl

theorem cell23_7556707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3, 4].length) (baseStart_7556707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556707 prefixEnd_7556707 := by exact prefixLift 7556707
  have htrace : WordTrace (prefixWord ++ tailWord_7556707) baseStart_7556707 baseEnd_7556707 := by
    simpa [prefixWord, tailWord_7556707, baseEnd_7556707] using wordTrace_append hprefix tailTrace_7556707
  have hstable : (prefixWord ++ tailWord_7556707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556707).length < 2 ^ (prefixWord ++ tailWord_7556707).sum := by decide
  have hdescent : baseEnd_7556707 < baseStart_7556707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556714 : List Nat := [3, 1, 3, 2, 1, 2, 2, 1, 2, 4, 2]
def baseStart_7556714 : Nat := 118140960795 + 7556714 * 2 ^ 59
def prefixEnd_7556714 : Nat := 4983230072969 + 3 ^ 40 * 7556714 * 2
def baseEnd_7556714 : Nat := 3880226450559852555422311

theorem tailTrace_7556714 : CollatzResearch.WordTrace tailWord_7556714 prefixEnd_7556714 3880226450559852555422311 := by
  unfold tailWord_7556714
  simp only [CollatzResearch.WordTrace]
  refine ⟨68904000586330809211917299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183744001563548824565112797 68904000586330809211917299)
  ·
    refine ⟨103356000879496213817875949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68904000586330809211917299 103356000879496213817875949)
    ·
      refine ⟨38758500329811080181703481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103356000879496213817875949 38758500329811080181703481)
      ·
        refine ⟨29068875247358310136277611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38758500329811080181703481 29068875247358310136277611)
        ·
          refine ⟨43603312871037465204416417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29068875247358310136277611 43603312871037465204416417)
          ·
            refine ⟨32702484653278098903312313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43603312871037465204416417 32702484653278098903312313)
            ·
              refine ⟨24526863489958574177484235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32702484653278098903312313 24526863489958574177484235)
              ·
                refine ⟨36790295234937861266226353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24526863489958574177484235 36790295234937861266226353)
                ·
                  refine ⟨27592721426203395949669765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36790295234937861266226353 27592721426203395949669765)
                  ·
                    refine ⟨5173635267413136740563081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27592721426203395949669765 5173635267413136740563081)
                    ·
                      refine ⟨3880226450559852555422311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5173635267413136740563081 3880226450559852555422311)
                      ·
                        rfl

theorem cell23_7556714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_7556714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556714 prefixEnd_7556714 := by exact prefixLift 7556714
  have htrace : WordTrace (prefixWord ++ tailWord_7556714) baseStart_7556714 baseEnd_7556714 := by
    simpa [prefixWord, tailWord_7556714, baseEnd_7556714] using wordTrace_append hprefix tailTrace_7556714
  have hstable : (prefixWord ++ tailWord_7556714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556714).length < 2 ^ (prefixWord ++ tailWord_7556714).sum := by decide
  have hdescent : baseEnd_7556714 < baseStart_7556714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556780 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 7, 6]
def baseStart_7556780 : Nat := 118140960795 + 7556780 * 2 ^ 59
def prefixEnd_7556780 : Nat := 4983230072969 + 3 ^ 40 * 7556780 * 2
def baseEnd_7556780 : Nat := 1293420113427683099065669

theorem tailTrace_7556780 : CollatzResearch.WordTrace tailWord_7556780 prefixEnd_7556780 1293420113427683099065669 := by
  unfold tailWord_7556780
  simp only [CollatzResearch.WordTrace]
  refine ⟨137809204781542065059785897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183745606375389420079714529 137809204781542065059785897)
  ·
    refine ⟨103356903586156548794839423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137809204781542065059785897 103356903586156548794839423)
    ·
      refine ⟨155035355379234823192259135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103356903586156548794839423 155035355379234823192259135)
      ·
        refine ⟨232553033068852234788388703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155035355379234823192259135 232553033068852234788388703)
        ·
          refine ⟨348829549603278352182583055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232553033068852234788388703 348829549603278352182583055)
          ·
            refine ⟨523244324404917528273874583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348829549603278352182583055 523244324404917528273874583)
            ·
              refine ⟨784866486607376292410811875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523244324404917528273874583 784866486607376292410811875)
              ·
                refine ⟨1177299729911064438616217813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 784866486607376292410811875 1177299729911064438616217813)
                ·
                  refine ⟨27592962419790572780067605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1177299729911064438616217813 27592962419790572780067605)
                  ·
                    refine ⟨1293420113427683099065669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27592962419790572780067605 1293420113427683099065669)
                    ·
                      rfl

theorem cell23_7556780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 6].length) (baseStart_7556780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556780 prefixEnd_7556780 := by exact prefixLift 7556780
  have htrace : WordTrace (prefixWord ++ tailWord_7556780) baseStart_7556780 baseEnd_7556780 := by
    simpa [prefixWord, tailWord_7556780, baseEnd_7556780] using wordTrace_append hprefix tailTrace_7556780
  have hstable : (prefixWord ++ tailWord_7556780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556780).length < 2 ^ (prefixWord ++ tailWord_7556780).sum := by decide
  have hdescent : baseEnd_7556780 < baseStart_7556780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556787 : List Nat := [1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 4]
def baseStart_7556787 : Nat := 118140960795 + 7556787 * 2 ^ 59
def prefixEnd_7556787 : Nat := 4983230072969 + 3 ^ 40 * 7556787 * 2
def baseEnd_7556787 : Nat := 3880263934647630769809475

theorem tailTrace_7556787 : CollatzResearch.WordTrace tailWord_7556787 prefixEnd_7556787 3880263934647630769809475 := by
  unfold tailWord_7556787
  simp only [CollatzResearch.WordTrace]
  refine ⟨275618664874058770315076615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183745776582705846876717743 275618664874058770315076615)
  ·
    refine ⟨413427997311088155472614923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275618664874058770315076615 413427997311088155472614923)
    ·
      refine ⟨620141995966632233208922385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413427997311088155472614923 620141995966632233208922385)
      ·
        refine ⟨465106496974974174906691789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 620141995966632233208922385 465106496974974174906691789)
        ·
          refine ⟨174414936365615315590009421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 465106496974974174906691789 174414936365615315590009421)
          ·
            refine ⟨65405601137105743346253533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174414936365615315590009421 65405601137105743346253533)
            ·
              refine ⟨24527100426414653754845075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65405601137105743346253533 24527100426414653754845075)
              ·
                refine ⟨36790650639621980632267613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24527100426414653754845075 36790650639621980632267613)
                ·
                  refine ⟨13796493989858242737100355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36790650639621980632267613 13796493989858242737100355)
                  ·
                    refine ⟨20694740984787364105650533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13796493989858242737100355 20694740984787364105650533)
                    ·
                      refine ⟨3880263934647630769809475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20694740984787364105650533 3880263934647630769809475)
                      ·
                        rfl

theorem cell23_7556787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 4].length) (baseStart_7556787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556787 prefixEnd_7556787 := by exact prefixLift 7556787
  have htrace : WordTrace (prefixWord ++ tailWord_7556787) baseStart_7556787 baseEnd_7556787 := by
    simpa [prefixWord, tailWord_7556787, baseEnd_7556787] using wordTrace_append hprefix tailTrace_7556787
  have hstable : (prefixWord ++ tailWord_7556787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556787).length < 2 ^ (prefixWord ++ tailWord_7556787).sum := by decide
  have hdescent : baseEnd_7556787 < baseStart_7556787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556791 : List Nat := [1, 1, 3, 1, 5, 2, 2, 1, 2, 3, 2]
def baseStart_7556791 : Nat := 118140960795 + 7556791 * 2 ^ 59
def prefixEnd_7556791 : Nat := 4983230072969 + 3 ^ 40 * 7556791 * 2
def baseEnd_7556791 : Nat := 3880265988570248754159457

theorem tailTrace_7556791 : CollatzResearch.WordTrace tailWord_7556791 prefixEnd_7556791 3880265988570248754159457 := by
  unfold tailWord_7556791
  simp only [CollatzResearch.WordTrace]
  refine ⟨275618810766044278998222227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183745873844029519332148151 275618810766044278998222227)
  ·
    refine ⟨413428216149066418497333341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275618810766044278998222227 413428216149066418497333341)
    ·
      refine ⟨155035581055899906936500003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413428216149066418497333341 155035581055899906936500003)
      ·
        refine ⟨232553371583849860404750005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155035581055899906936500003 232553371583849860404750005)
        ·
          refine ⟨21801878585985924412945313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 232553371583849860404750005 21801878585985924412945313)
          ·
            refine ⟨16351408939489443309708985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21801878585985924412945313 16351408939489443309708985)
            ·
              refine ⟨12263556704617082482281739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16351408939489443309708985 12263556704617082482281739)
              ·
                refine ⟨18395335056925623723422609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12263556704617082482281739 18395335056925623723422609)
                ·
                  refine ⟨13796501292694217792566957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18395335056925623723422609 13796501292694217792566957)
                  ·
                    refine ⟨5173687984760331672212609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13796501292694217792566957 5173687984760331672212609)
                    ·
                      refine ⟨3880265988570248754159457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5173687984760331672212609 3880265988570248754159457)
                      ·
                        rfl

theorem cell23_7556791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 3, 2].length) (baseStart_7556791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556791 prefixEnd_7556791 := by exact prefixLift 7556791
  have htrace : WordTrace (prefixWord ++ tailWord_7556791) baseStart_7556791 baseEnd_7556791 := by
    simpa [prefixWord, tailWord_7556791, baseEnd_7556791] using wordTrace_append hprefix tailTrace_7556791
  have hstable : (prefixWord ++ tailWord_7556791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556791).length < 2 ^ (prefixWord ++ tailWord_7556791).sum := by decide
  have hdescent : baseEnd_7556791 < baseStart_7556791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556797 : List Nat := [1, 4, 1, 2, 1, 2, 3, 2, 1, 6]
def baseStart_7556797 : Nat := 118140960795 + 7556797 * 2 ^ 59
def prefixEnd_7556797 : Nat := 4983230072969 + 3 ^ 40 * 7556797 * 2
def baseEnd_7556797 : Nat := 1293423023151391910228143

theorem tailTrace_7556797 : CollatzResearch.WordTrace tailWord_7556797 prefixEnd_7556797 1293423023151391910228143 := by
  unfold tailWord_7556797
  simp only [CollatzResearch.WordTrace]
  refine ⟨275619029604022542022940645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183746019736015028015293763 275619029604022542022940645)
  ·
    refine ⟨51678568050754226629301371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275619029604022542022940645 51678568050754226629301371)
    ·
      refine ⟨77517852076131339943952057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51678568050754226629301371 77517852076131339943952057)
      ·
        refine ⟨58138389057098504957964043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77517852076131339943952057 58138389057098504957964043)
        ·
          refine ⟨87207583585647757436946065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58138389057098504957964043 87207583585647757436946065)
          ·
            refine ⟨65405687689235818077709549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87207583585647757436946065 65405687689235818077709549)
            ·
              refine ⟨24527132883463431779141081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65405687689235818077709549 24527132883463431779141081)
              ·
                refine ⟨18395349662597573834355811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24527132883463431779141081 18395349662597573834355811)
                ·
                  refine ⟨27593024493896360751533717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18395349662597573834355811 27593024493896360751533717)
                  ·
                    refine ⟨1293423023151391910228143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27593024493896360751533717 1293423023151391910228143)
                    ·
                      rfl

theorem cell23_7556797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_7556797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556797 prefixEnd_7556797 := by exact prefixLift 7556797
  have htrace : WordTrace (prefixWord ++ tailWord_7556797) baseStart_7556797 baseEnd_7556797 := by
    simpa [prefixWord, tailWord_7556797, baseEnd_7556797] using wordTrace_append hprefix tailTrace_7556797
  have hstable : (prefixWord ++ tailWord_7556797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556797).length < 2 ^ (prefixWord ++ tailWord_7556797).sum := by decide
  have hdescent : baseEnd_7556797 < baseStart_7556797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556810 : List Nat := [3, 1, 2, 1, 16]
def baseStart_7556810 : Nat := 118140960795 + 7556810 * 2 ^ 59
def prefixEnd_7556810 : Nat := 4983230072969 + 3 ^ 40 * 7556810 * 2
def baseEnd_7556810 : Nat := 5322737647054436460661

theorem tailTrace_7556810 : CollatzResearch.WordTrace tailWord_7556810 prefixEnd_7556810 5322737647054436460661 := by
  unfold tailWord_7556810
  simp only [CollatzResearch.WordTrace]
  refine ⟨68904875938243861310790971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183746335835316963495442589 68904875938243861310790971)
  ·
    refine ⟨103357313907365791966186457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68904875938243861310790971 103357313907365791966186457)
    ·
      refine ⟨77517985430524343974639843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103357313907365791966186457 77517985430524343974639843)
      ·
        refine ⟨116276978145786515961959765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77517985430524343974639843 116276978145786515961959765)
        ·
          refine ⟨5322737647054436460661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 116276978145786515961959765 5322737647054436460661)
          ·
            rfl

theorem cell23_7556810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 16].length) (baseStart_7556810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556810 prefixEnd_7556810 := by exact prefixLift 7556810
  have htrace : WordTrace (prefixWord ++ tailWord_7556810) baseStart_7556810 baseEnd_7556810 := by
    simpa [prefixWord, tailWord_7556810, baseEnd_7556810] using wordTrace_append hprefix tailTrace_7556810
  have hstable : (prefixWord ++ tailWord_7556810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556810).length < 2 ^ (prefixWord ++ tailWord_7556810).sum := by decide
  have hdescent : baseEnd_7556810 < baseStart_7556810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556898 : List Nat := [3, 3, 1, 1, 2, 1, 4, 2, 1, 3, 2]
def baseStart_7556898 : Nat := 118140960795 + 7556898 * 2 ^ 59
def prefixEnd_7556898 : Nat := 4983230072969 + 3 ^ 40 * 7556898 * 2
def baseEnd_7556898 : Nat := 3880320931000279835521465

theorem tailTrace_7556898 : CollatzResearch.WordTrace tailWord_7556898 prefixEnd_7556898 3880320931000279835521465 := by
  unfold tailWord_7556898
  simp only [CollatzResearch.WordTrace]
  refine ⟨68905678344164159068091837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183748475584437757514911565 68905678344164159068091837)
  ·
    refine ⟨25839629379061559650534439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68905678344164159068091837 25839629379061559650534439)
    ·
      refine ⟨38759444068592339475801659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25839629379061559650534439 38759444068592339475801659)
      ·
        refine ⟨58139166102888509213702489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38759444068592339475801659 58139166102888509213702489)
        ·
          refine ⟨43604374577166381910276867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58139166102888509213702489 43604374577166381910276867)
          ·
            refine ⟨65406561865749572865415301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43604374577166381910276867 65406561865749572865415301)
            ·
              refine ⟨12263730349828044912265369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65406561865749572865415301 12263730349828044912265369)
              ·
                refine ⟨9197797762371033684199027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12263730349828044912265369 9197797762371033684199027)
                ·
                  refine ⟨13796696643556550526298541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9197797762371033684199027 13796696643556550526298541)
                  ·
                    refine ⟨5173761241333706447361953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13796696643556550526298541 5173761241333706447361953)
                    ·
                      refine ⟨3880320931000279835521465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5173761241333706447361953 3880320931000279835521465)
                      ·
                        rfl

theorem cell23_7556898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_7556898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556898 prefixEnd_7556898 := by exact prefixLift 7556898
  have htrace : WordTrace (prefixWord ++ tailWord_7556898) baseStart_7556898 baseEnd_7556898 := by
    simpa [prefixWord, tailWord_7556898, baseEnd_7556898] using wordTrace_append hprefix tailTrace_7556898
  have hstable : (prefixWord ++ tailWord_7556898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556898).length < 2 ^ (prefixWord ++ tailWord_7556898).sum := by decide
  have hdescent : baseEnd_7556898 < baseStart_7556898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556914 : List Nat := [3, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5]
def baseStart_7556914 : Nat := 118140960795 + 7556914 * 2 ^ 59
def prefixEnd_7556914 : Nat := 4983230072969 + 3 ^ 40 * 7556914 * 2
def baseEnd_7556914 : Nat := 3880329146690751772921391

theorem tailTrace_7556914 : CollatzResearch.WordTrace tailWord_7556914 prefixEnd_7556914 3880329146690751772921391 := by
  unfold tailWord_7556914
  simp only [CollatzResearch.WordTrace]
  refine ⟨68905824236149667751237449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183748864629732447336633197 68905824236149667751237449)
  ·
    refine ⟨51679368177112250813428087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68905824236149667751237449 51679368177112250813428087)
    ·
      refine ⟨77519052265668376220142131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51679368177112250813428087 77519052265668376220142131)
      ·
        refine ⟨116278578398502564330213197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77519052265668376220142131 116278578398502564330213197)
        ·
          refine ⟨43604466899438461623829949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116278578398502564330213197 43604466899438461623829949)
          ·
            refine ⟨16351675087289423108936231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43604466899438461623829949 16351675087289423108936231)
            ·
              refine ⟨24527512630934134663404347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16351675087289423108936231 24527512630934134663404347)
              ·
                refine ⟨36791268946401201995106521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24527512630934134663404347 36791268946401201995106521)
                ·
                  refine ⟨27593451709800901496329891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36791268946401201995106521 27593451709800901496329891)
                  ·
                    refine ⟨41390177564701352244494837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27593451709800901496329891 41390177564701352244494837)
                    ·
                      refine ⟨3880329146690751772921391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41390177564701352244494837 3880329146690751772921391)
                      ·
                        rfl

theorem cell23_7556914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_7556914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556914 prefixEnd_7556914 := by exact prefixLift 7556914
  have htrace : WordTrace (prefixWord ++ tailWord_7556914) baseStart_7556914 baseEnd_7556914 := by
    simpa [prefixWord, tailWord_7556914, baseEnd_7556914] using wordTrace_append hprefix tailTrace_7556914
  have hstable : (prefixWord ++ tailWord_7556914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556914).length < 2 ^ (prefixWord ++ tailWord_7556914).sum := by decide
  have hdescent : baseEnd_7556914 < baseStart_7556914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556945 : List Nat := [1, 2, 2, 1, 5, 1, 4, 1, 2, 2, 2]
def baseStart_7556945 : Nat := 118140960795 + 7556945 * 2 ^ 59
def prefixEnd_7556945 : Nat := 4983230072969 + 3 ^ 40 * 7556945 * 2
def baseEnd_7556945 : Nat := 3880345064591041151633749

theorem tailTrace_7556945 : CollatzResearch.WordTrace tailWord_7556945 prefixEnd_7556945 3880345064591041151633749 := by
  unfold tailWord_7556945
  simp only [CollatzResearch.WordTrace]
  refine ⟨275624427607486363299328289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183749618404990908866218859 275624427607486363299328289)
  ·
    refine ⟨206718320705614772474496217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275624427607486363299328289 206718320705614772474496217)
    ·
      refine ⟨155038740529211079355872163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206718320705614772474496217 155038740529211079355872163)
      ·
        refine ⟨232558110793816619033808245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155038740529211079355872163 232558110793816619033808245)
        ·
          refine ⟨21802322886920308034419523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 232558110793816619033808245 21802322886920308034419523)
          ·
            refine ⟨32703484330380462051629285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21802322886920308034419523 32703484330380462051629285)
            ·
              refine ⟨6131903311946336634680491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32703484330380462051629285 6131903311946336634680491)
              ·
                refine ⟨9197854967919504952020737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6131903311946336634680491 9197854967919504952020737)
                ·
                  refine ⟨6898391225939628714015553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9197854967919504952020737 6898391225939628714015553)
                  ·
                    refine ⟨5173793419454721535511665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6898391225939628714015553 5173793419454721535511665)
                    ·
                      refine ⟨3880345064591041151633749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5173793419454721535511665 3880345064591041151633749)
                      ·
                        rfl

theorem cell23_7556945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 2, 2, 2].length) (baseStart_7556945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556945 prefixEnd_7556945 := by exact prefixLift 7556945
  have htrace : WordTrace (prefixWord ++ tailWord_7556945) baseStart_7556945 baseEnd_7556945 := by
    simpa [prefixWord, tailWord_7556945, baseEnd_7556945] using wordTrace_append hprefix tailTrace_7556945
  have hstable : (prefixWord ++ tailWord_7556945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556945).length < 2 ^ (prefixWord ++ tailWord_7556945).sum := by decide
  have hdescent : baseEnd_7556945 < baseStart_7556945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7556987 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 5]
def baseStart_7556987 : Nat := 118140960795 + 7556987 * 2 ^ 59
def prefixEnd_7556987 : Nat := 4983230072969 + 3 ^ 40 * 7556987 * 2
def baseEnd_7556987 : Nat := 3880366630778529987308555

theorem tailTrace_7556987 : CollatzResearch.WordTrace tailWord_7556987 prefixEnd_7556987 3880366630778529987308555 := by
  unfold tailWord_7556987
  simp only [CollatzResearch.WordTrace]
  refine ⟨275625959473334204472357215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183750639648889469648238143 275625959473334204472357215)
  ·
    refine ⟨413438939210001306708535823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275625959473334204472357215 413438939210001306708535823)
    ·
      refine ⟨620158408815001960062803735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413438939210001306708535823 620158408815001960062803735)
      ·
        refine ⟨930237613222502940094205603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620158408815001960062803735 930237613222502940094205603)
        ·
          refine ⟨1395356419833754410141308405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 930237613222502940094205603 1395356419833754410141308405)
          ·
            refine ⟨130814664359414475950747663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1395356419833754410141308405 130814664359414475950747663)
            ·
              refine ⟨196221996539121713926121495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130814664359414475950747663 196221996539121713926121495)
              ·
                refine ⟨294332994808682570889182243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196221996539121713926121495 294332994808682570889182243)
                ·
                  refine ⟨441499492213023856333773365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294332994808682570889182243 441499492213023856333773365)
                  ·
                    refine ⟨41390577394970986531291253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 441499492213023856333773365 41390577394970986531291253)
                    ·
                      refine ⟨3880366630778529987308555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41390577394970986531291253 3880366630778529987308555)
                      ·
                        rfl

theorem cell23_7556987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 5].length) (baseStart_7556987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7556987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7556987 prefixEnd_7556987 := by exact prefixLift 7556987
  have htrace : WordTrace (prefixWord ++ tailWord_7556987) baseStart_7556987 baseEnd_7556987 := by
    simpa [prefixWord, tailWord_7556987, baseEnd_7556987] using wordTrace_append hprefix tailTrace_7556987
  have hstable : (prefixWord ++ tailWord_7556987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7556987).length < 2 ^ (prefixWord ++ tailWord_7556987).sum := by decide
  have hdescent : baseEnd_7556987 < baseStart_7556987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7556987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557001 : List Nat := [1, 2, 1, 1, 5, 1, 3, 1, 2, 4, 2]
def baseStart_7557001 : Nat := 118140960795 + 7557001 * 2 ^ 59
def prefixEnd_7557001 : Nat := 4983230072969 + 3 ^ 40 * 7557001 * 2
def baseEnd_7557001 : Nat := 3880373819507692932533491

theorem tailTrace_7557001 : CollatzResearch.WordTrace tailWord_7557001 prefixEnd_7557001 3880373819507692932533491 := by
  unfold tailWord_7557001
  simp only [CollatzResearch.WordTrace]
  refine ⟨275626470095283484863366857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183750980063522323242244571 275626470095283484863366857)
  ·
    refine ⟨206719852571462613647525143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275626470095283484863366857 206719852571462613647525143)
    ·
      refine ⟨310079778857193920471287715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206719852571462613647525143 310079778857193920471287715)
      ·
        refine ⟨465119668285790880706931573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310079778857193920471287715 465119668285790880706931573)
        ·
          refine ⟨43604968901792895066274835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 465119668285790880706931573 43604968901792895066274835)
          ·
            refine ⟨65407453352689342599412253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43604968901792895066274835 65407453352689342599412253)
            ·
              refine ⟨24527795007258503474779595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65407453352689342599412253 24527795007258503474779595)
              ·
                refine ⟨36791692510887755212169393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24527795007258503474779595 36791692510887755212169393)
                ·
                  refine ⟨27593769383165816409127045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36791692510887755212169393 27593769383165816409127045)
                  ·
                    refine ⟨5173831759343590576711321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27593769383165816409127045 5173831759343590576711321)
                    ·
                      refine ⟨3880373819507692932533491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5173831759343590576711321 3880373819507692932533491)
                      ·
                        rfl

theorem cell23_7557001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 4, 2].length) (baseStart_7557001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557001 prefixEnd_7557001 := by exact prefixLift 7557001
  have htrace : WordTrace (prefixWord ++ tailWord_7557001) baseStart_7557001 baseEnd_7557001 := by
    simpa [prefixWord, tailWord_7557001, baseEnd_7557001] using wordTrace_append hprefix tailTrace_7557001
  have hstable : (prefixWord ++ tailWord_7557001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557001).length < 2 ^ (prefixWord ++ tailWord_7557001).sum := by decide
  have hdescent : baseEnd_7557001 < baseStart_7557001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557004 : List Nat := [2, 2, 1, 2, 1, 2, 1, 4, 1, 4, 3]
def baseStart_7557004 : Nat := 118140960795 + 7557004 * 2 ^ 59
def prefixEnd_7557004 : Nat := 4983230072969 + 3 ^ 40 * 7557004 * 2
def baseEnd_7557004 : Nat := 3880375359949656420795977

theorem tailTrace_7557004 : CollatzResearch.WordTrace tailWord_7557004 prefixEnd_7557004 3880375359949656420795977 := by
  unfold tailWord_7557004
  simp only [CollatzResearch.WordTrace]
  refine ⟨137813289757136308187863033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183751053009515077583817377 137813289757136308187863033)
  ·
    refine ⟨103359967317852231140897275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137813289757136308187863033 103359967317852231140897275)
    ·
      refine ⟨155039950976778346711345913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103359967317852231140897275 155039950976778346711345913)
      ·
        refine ⟨116279963232583760033509435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155039950976778346711345913 116279963232583760033509435)
        ·
          refine ⟨174419944848875640050264153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116279963232583760033509435 174419944848875640050264153)
          ·
            refine ⟨130814958636656730037698115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174419944848875640050264153 130814958636656730037698115)
            ·
              refine ⟨196222437954985095056547173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130814958636656730037698115 196222437954985095056547173)
              ·
                refine ⟨36791707116559705323102595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196222437954985095056547173 36791707116559705323102595)
                ·
                  refine ⟨55187560674839557984653893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36791707116559705323102595 55187560674839557984653893)
                  ·
                    refine ⟨10347667626532417122122605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55187560674839557984653893 10347667626532417122122605)
                    ·
                      refine ⟨3880375359949656420795977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10347667626532417122122605 3880375359949656420795977)
                      ·
                        rfl

theorem cell23_7557004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_7557004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557004 prefixEnd_7557004 := by exact prefixLift 7557004
  have htrace : WordTrace (prefixWord ++ tailWord_7557004) baseStart_7557004 baseEnd_7557004 := by
    simpa [prefixWord, tailWord_7557004, baseEnd_7557004] using wordTrace_append hprefix tailTrace_7557004
  have hstable : (prefixWord ++ tailWord_7557004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557004).length < 2 ^ (prefixWord ++ tailWord_7557004).sum := by decide
  have hdescent : baseEnd_7557004 < baseStart_7557004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557018 : List Nat := [3, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4]
def baseStart_7557018 : Nat := 118140960795 + 7557018 * 2 ^ 59
def prefixEnd_7557018 : Nat := 4983230072969 + 3 ^ 40 * 7557018 * 2
def baseEnd_7557018 : Nat := 3880382548678819366020913

theorem tailTrace_7557018 : CollatzResearch.WordTrace tailWord_7557018 prefixEnd_7557018 3880382548678819366020913 := by
  unfold tailWord_7557018
  simp only [CollatzResearch.WordTrace]
  refine ⟨68906772534055474191683927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183751393424147931177823805 68906772534055474191683927)
  ·
    refine ⟨103360158801083211287525891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68906772534055474191683927 103360158801083211287525891)
    ·
      refine ⟨155040238201624816931288837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103360158801083211287525891 155040238201624816931288837)
      ·
        refine ⟨29070044662804653174616657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155040238201624816931288837 29070044662804653174616657)
        ·
          refine ⟨21802533497103489880962493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29070044662804653174616657 21802533497103489880962493)
          ·
            refine ⟨8175950061413808705360935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21802533497103489880962493 8175950061413808705360935)
            ·
              refine ⟨12263925092120713058041403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8175950061413808705360935 12263925092120713058041403)
              ·
                refine ⟨18395887638181069587062105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12263925092120713058041403 18395887638181069587062105)
                ·
                  refine ⟨13796915728635802190296579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18395887638181069587062105 13796915728635802190296579)
                  ·
                    refine ⟨20695373592953703285444869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13796915728635802190296579 20695373592953703285444869)
                    ·
                      refine ⟨3880382548678819366020913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20695373592953703285444869 3880382548678819366020913)
                      ·
                        rfl

theorem cell23_7557018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_7557018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557018 prefixEnd_7557018 := by exact prefixLift 7557018
  have htrace : WordTrace (prefixWord ++ tailWord_7557018) baseStart_7557018 baseEnd_7557018 := by
    simpa [prefixWord, tailWord_7557018, baseEnd_7557018] using wordTrace_append hprefix tailTrace_7557018
  have hstable : (prefixWord ++ tailWord_7557018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557018).length < 2 ^ (prefixWord ++ tailWord_7557018).sum := by decide
  have hdescent : baseEnd_7557018 < baseStart_7557018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557021 : List Nat := [1, 4, 2, 1, 2, 3, 1, 1, 1, 4, 3]
def baseStart_7557021 : Nat := 118140960795 + 7557021 * 2 ^ 59
def prefixEnd_7557021 : Nat := 4983230072969 + 3 ^ 40 * 7557021 * 2
def baseEnd_7557021 : Nat := 3880384089120782854283399

theorem tailTrace_7557021 : CollatzResearch.WordTrace tailWord_7557021 prefixEnd_7557021 3880384089120782854283399 := by
  unfold tailWord_7557021
  simp only [CollatzResearch.WordTrace]
  refine ⟨275627199555211028279094917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183751466370140685519396611 275627199555211028279094917)
  ·
    refine ⟨51680099916602067802330297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275627199555211028279094917 51680099916602067802330297)
    ·
      refine ⟨38760074937451550851747723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51680099916602067802330297 38760074937451550851747723)
      ·
        refine ⟨58140112406177326277621585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38760074937451550851747723 58140112406177326277621585)
        ·
          refine ⟨43605084304632994708216189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58140112406177326277621585 43605084304632994708216189)
          ·
            refine ⟨16351906614237373015581071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43605084304632994708216189 16351906614237373015581071)
            ·
              refine ⟨24527859921356059523371607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16351906614237373015581071 24527859921356059523371607)
              ·
                refine ⟨36791789882034089285057411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24527859921356059523371607 36791789882034089285057411)
                ·
                  refine ⟨55187684823051133927586117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36791789882034089285057411 55187684823051133927586117)
                  ·
                    refine ⟨10347690904322087611422397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55187684823051133927586117 10347690904322087611422397)
                    ·
                      refine ⟨3880384089120782854283399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10347690904322087611422397 3880384089120782854283399)
                      ·
                        rfl

theorem cell23_7557021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_7557021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557021 prefixEnd_7557021 := by exact prefixLift 7557021
  have htrace : WordTrace (prefixWord ++ tailWord_7557021) baseStart_7557021 baseEnd_7557021 := by
    simpa [prefixWord, tailWord_7557021, baseEnd_7557021] using wordTrace_append hprefix tailTrace_7557021
  have hstable : (prefixWord ++ tailWord_7557021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557021).length < 2 ^ (prefixWord ++ tailWord_7557021).sum := by decide
  have hdescent : baseEnd_7557021 < baseStart_7557021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557028 : List Nat := [2, 3, 1, 2, 1, 3, 1, 5, 1, 4]
def baseStart_7557028 : Nat := 118140960795 + 7557028 * 2 ^ 59
def prefixEnd_7557028 : Nat := 4983230072969 + 3 ^ 40 * 7557028 * 2
def baseEnd_7557028 : Nat := 1293462561161788108965289

theorem tailTrace_7557028 : CollatzResearch.WordTrace tailWord_7557028 prefixEnd_7557028 1293462561161788108965289 := by
  unfold tailWord_7557028
  simp only [CollatzResearch.WordTrace]
  refine ⟨137813727433092834237299869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183751636577457112316399825 137813727433092834237299869)
  ·
    refine ⟨51680147787409812838987451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137813727433092834237299869 51680147787409812838987451)
    ·
      refine ⟨77520221681114719258481177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51680147787409812838987451 77520221681114719258481177)
      ·
        refine ⟨58140166260836039443860883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77520221681114719258481177 58140166260836039443860883)
        ·
          refine ⟨87210249391254059165791325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58140166260836039443860883 87210249391254059165791325)
          ·
            refine ⟨32703843521720272187171747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87210249391254059165791325 32703843521720272187171747)
            ·
              refine ⟨49055765282580408280757621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32703843521720272187171747 49055765282580408280757621)
              ·
                refine ⟨4598977995241913276321027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49055765282580408280757621 4598977995241913276321027)
                ·
                  refine ⟨6898466992862869914481541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4598977995241913276321027 6898466992862869914481541)
                  ·
                    refine ⟨1293462561161788108965289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6898466992862869914481541 1293462561161788108965289)
                    ·
                      rfl

theorem cell23_7557028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_7557028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557028 prefixEnd_7557028 := by exact prefixLift 7557028
  have htrace : WordTrace (prefixWord ++ tailWord_7557028) baseStart_7557028 baseEnd_7557028 := by
    simpa [prefixWord, tailWord_7557028, baseEnd_7557028] using wordTrace_append hprefix tailTrace_7557028
  have hstable : (prefixWord ++ tailWord_7557028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557028).length < 2 ^ (prefixWord ++ tailWord_7557028).sum := by decide
  have hdescent : baseEnd_7557028 < baseStart_7557028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557041 : List Nat := [1, 2, 2, 4, 2, 1, 3, 2, 6]
def baseStart_7557041 : Nat := 118140960795 + 7557041 * 2 ^ 59
def prefixEnd_7557041 : Nat := 4983230072969 + 3 ^ 40 * 7557041 * 2
def baseEnd_7557041 : Nat := 431154928748208086225923

theorem tailTrace_7557041 : CollatzResearch.WordTrace tailWord_7557041 prefixEnd_7557041 431154928748208086225923 := by
  unfold tailWord_7557041
  simp only [CollatzResearch.WordTrace]
  refine ⟨275627929015138571694822977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183751952676759047796548651 275627929015138571694822977)
  ·
    refine ⟨206720946761353928771117233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275627929015138571694822977 206720946761353928771117233)
    ·
      refine ⟨155040710071015446578337925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206720946761353928771117233 155040710071015446578337925)
      ·
        refine ⟨29070133138315396233438361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155040710071015446578337925 29070133138315396233438361)
        ·
          refine ⟨21802599853736547175078771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29070133138315396233438361 21802599853736547175078771)
          ·
            refine ⟨32703899780604820762618157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21802599853736547175078771 32703899780604820762618157)
            ·
              refine ⟨12263962417726807785981809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32703899780604820762618157 12263962417726807785981809)
              ·
                refine ⟨9197971813295105839486357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12263962417726807785981809 9197971813295105839486357)
                ·
                  refine ⟨431154928748208086225923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9197971813295105839486357 431154928748208086225923)
                  ·
                    rfl

theorem cell23_7557041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 6].length) (baseStart_7557041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557041 prefixEnd_7557041 := by exact prefixLift 7557041
  have htrace : WordTrace (prefixWord ++ tailWord_7557041) baseStart_7557041 baseEnd_7557041 := by
    simpa [prefixWord, tailWord_7557041, baseEnd_7557041] using wordTrace_append hprefix tailTrace_7557041
  have hstable : (prefixWord ++ tailWord_7557041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557041).length < 2 ^ (prefixWord ++ tailWord_7557041).sum := by decide
  have hdescent : baseEnd_7557041 < baseStart_7557041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557051 : List Nat := [1, 1, 1, 1, 1, 2, 2, 7, 3, 1, 3]
def baseStart_7557051 : Nat := 118140960795 + 7557051 * 2 ^ 59
def prefixEnd_7557051 : Nat := 4983230072969 + 3 ^ 40 * 7557051 * 2
def baseEnd_7557051 : Nat := 3880399493540417736908261

theorem tailTrace_7557051 : CollatzResearch.WordTrace tailWord_7557051 prefixEnd_7557051 3880399493540417736908261 := by
  unfold tailWord_7557051
  simp only [CollatzResearch.WordTrace]
  refine ⟨275628293745102343402687007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183752195830068228935124671 275628293745102343402687007)
  ·
    refine ⟨413442440617653515104030511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275628293745102343402687007 413442440617653515104030511)
    ·
      refine ⟨620163660926480272656045767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413442440617653515104030511 620163660926480272656045767)
      ·
        refine ⟨930245491389720408984068651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620163660926480272656045767 930245491389720408984068651)
        ·
          refine ⟨1395368237084580613476102977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 930245491389720408984068651 1395368237084580613476102977)
          ·
            refine ⟨1046526177813435460107077233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1395368237084580613476102977 1046526177813435460107077233)
            ·
              refine ⟨784894633360076595080307925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1046526177813435460107077233 784894633360076595080307925)
              ·
                refine ⟨18395967969376795197194717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 784894633360076595080307925 18395967969376795197194717)
                ·
                  refine ⟨6898487988516298198948019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18395967969376795197194717 6898487988516298198948019)
                  ·
                    refine ⟨10347731982774447298422029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6898487988516298198948019 10347731982774447298422029)
                    ·
                      refine ⟨3880399493540417736908261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10347731982774447298422029 3880399493540417736908261)
                      ·
                        rfl

theorem cell23_7557051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3, 1, 3].length) (baseStart_7557051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557051 prefixEnd_7557051 := by exact prefixLift 7557051
  have htrace : WordTrace (prefixWord ++ tailWord_7557051) baseStart_7557051 baseEnd_7557051 := by
    simpa [prefixWord, tailWord_7557051, baseEnd_7557051] using wordTrace_append hprefix tailTrace_7557051
  have hstable : (prefixWord ++ tailWord_7557051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557051).length < 2 ^ (prefixWord ++ tailWord_7557051).sum := by decide
  have hdescent : baseEnd_7557051 < baseStart_7557051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557061 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 6, 3, 2]
def baseStart_7557061 : Nat := 118140960795 + 7557061 * 2 ^ 59
def prefixEnd_7557061 : Nat := 4983230072969 + 3 ^ 40 * 7557061 * 2
def baseEnd_7557061 : Nat := 3880404628346962697783215

theorem tailTrace_7557061 : CollatzResearch.WordTrace tailWord_7557061 prefixEnd_7557061 3880404628346962697783215 := by
  unfold tailWord_7557061
  simp only [CollatzResearch.WordTrace]
  refine ⟨275628658475066115110551037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183752438983377410073700691 275628658475066115110551037)
  ·
    refine ⟨103360746928149793166456639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275628658475066115110551037 103360746928149793166456639)
    ·
      refine ⟨155041120392224689749684959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103360746928149793166456639 155041120392224689749684959)
      ·
        refine ⟨232561680588337034624527439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155041120392224689749684959 232561680588337034624527439)
        ·
          refine ⟨348842520882505551936791159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232561680588337034624527439 348842520882505551936791159)
          ·
            refine ⟨523263781323758327905186739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348842520882505551936791159 523263781323758327905186739)
            ·
              refine ⟨784895671985637491857780109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523263781323758327905186739 784895671985637491857780109)
              ·
                refine ⟨294335876994614059446667541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 784895671985637491857780109 294335876994614059446667541)
                ·
                  refine ⟨13796994234122534036562541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 294335876994614059446667541 13796994234122534036562541)
                  ·
                    refine ⟨5173872837795950263710953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13796994234122534036562541 5173872837795950263710953)
                    ·
                      refine ⟨3880404628346962697783215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5173872837795950263710953 3880404628346962697783215)
                      ·
                        rfl

theorem cell23_7557061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 3, 2].length) (baseStart_7557061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557061 prefixEnd_7557061 := by exact prefixLift 7557061
  have htrace : WordTrace (prefixWord ++ tailWord_7557061) baseStart_7557061 baseEnd_7557061 := by
    simpa [prefixWord, tailWord_7557061, baseEnd_7557061] using wordTrace_append hprefix tailTrace_7557061
  have hstable : (prefixWord ++ tailWord_7557061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557061).length < 2 ^ (prefixWord ++ tailWord_7557061).sum := by decide
  have hdescent : baseEnd_7557061 < baseStart_7557061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557068 : List Nat := [2, 2, 1, 4, 1, 2, 2, 2, 3, 1, 3]
def baseStart_7557068 : Nat := 118140960795 + 7557068 * 2 ^ 59
def prefixEnd_7557068 : Nat := 4983230072969 + 3 ^ 40 * 7557068 * 2
def baseEnd_7557068 : Nat := 3880408222711544170395683

theorem tailTrace_7557068 : CollatzResearch.WordTrace tailWord_7557068 prefixEnd_7557068 3880408222711544170395683 := by
  unfold tailWord_7557068
  simp only [CollatzResearch.WordTrace]
  refine ⟨137814456893020377653027929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183752609190693836870703905 137814456893020377653027929)
  ·
    refine ⟨103360842669765283239770947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137814456893020377653027929 103360842669765283239770947)
    ·
      refine ⟨155041264004647924859656421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103360842669765283239770947 155041264004647924859656421)
      ·
        refine ⟨29070237000871485911185579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155041264004647924859656421 29070237000871485911185579)
        ·
          refine ⟨43605355501307228866778369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29070237000871485911185579 43605355501307228866778369)
          ·
            refine ⟨32704016625980421650083777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43605355501307228866778369 32704016625980421650083777)
            ·
              refine ⟨24528012469485316237562833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32704016625980421650083777 24528012469485316237562833)
              ·
                refine ⟨18396009352113987178172125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24528012469485316237562833 18396009352113987178172125)
                ·
                  refine ⟨6898503507042745191814547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18396009352113987178172125 6898503507042745191814547)
                  ·
                    refine ⟨10347755260564117787721821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6898503507042745191814547 10347755260564117787721821)
                    ·
                      refine ⟨3880408222711544170395683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10347755260564117787721821 3880408222711544170395683)
                      ·
                        rfl

theorem cell23_7557068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_7557068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557068 prefixEnd_7557068 := by exact prefixLift 7557068
  have htrace : WordTrace (prefixWord ++ tailWord_7557068) baseStart_7557068 baseEnd_7557068 := by
    simpa [prefixWord, tailWord_7557068, baseEnd_7557068] using wordTrace_append hprefix tailTrace_7557068
  have hstable : (prefixWord ++ tailWord_7557068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557068).length < 2 ^ (prefixWord ++ tailWord_7557068).sum := by decide
  have hdescent : baseEnd_7557068 < baseStart_7557068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557071 : List Nat := [1, 1, 2, 1, 1, 5, 4, 2, 1, 5]
def baseStart_7557071 : Nat := 118140960795 + 7557071 * 2 ^ 59
def prefixEnd_7557071 : Nat := 4983230072969 + 3 ^ 40 * 7557071 * 2
def baseEnd_7557071 : Nat := 1293469921051169219552723

theorem tailTrace_7557071 : CollatzResearch.WordTrace tailWord_7557071 prefixEnd_7557071 1293469921051169219552723 := by
  unfold tailWord_7557071
  simp only [CollatzResearch.WordTrace]
  refine ⟨275629023205029886818415067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183752682136686591212276711 275629023205029886818415067)
  ·
    refine ⟨413443534807544830227622601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275629023205029886818415067 413443534807544830227622601)
    ·
      refine ⟨310082651105658622670716951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413443534807544830227622601 310082651105658622670716951)
      ·
        refine ⟨465123976658487934006075427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310082651105658622670716951 465123976658487934006075427)
        ·
          refine ⟨697685964987731901009113141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465123976658487934006075427 697685964987731901009113141)
          ·
            refine ⟨65408059217599865719604357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 697685964987731901009113141 65408059217599865719604357)
            ·
              refine ⟨12264011103299974822425817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65408059217599865719604357 12264011103299974822425817)
              ·
                refine ⟨9198008327474981116819363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12264011103299974822425817 9198008327474981116819363)
                ·
                  refine ⟨13797012491212471675229045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9198008327474981116819363 13797012491212471675229045)
                  ·
                    refine ⟨1293469921051169219552723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13797012491212471675229045 1293469921051169219552723)
                    ·
                      rfl

theorem cell23_7557071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 5].length) (baseStart_7557071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557071 prefixEnd_7557071 := by exact prefixLift 7557071
  have htrace : WordTrace (prefixWord ++ tailWord_7557071) baseStart_7557071 baseEnd_7557071 := by
    simpa [prefixWord, tailWord_7557071, baseEnd_7557071] using wordTrace_append hprefix tailTrace_7557071
  have hstable : (prefixWord ++ tailWord_7557071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557071).length < 2 ^ (prefixWord ++ tailWord_7557071).sum := by decide
  have hdescent : baseEnd_7557071 < baseStart_7557071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557095 : List Nat := [1, 1, 5, 2, 3, 1, 1, 2, 2, 3, 2]
def baseStart_7557095 : Nat := 118140960795 + 7557095 * 2 ^ 59
def prefixEnd_7557095 : Nat := 4983230072969 + 3 ^ 40 * 7557095 * 2
def baseEnd_7557095 : Nat := 3880422086689215564758059

theorem tailTrace_7557095 : CollatzResearch.WordTrace tailWord_7557095 prefixEnd_7557095 3880422086689215564758059 := by
  unfold tailWord_7557095
  simp only [CollatzResearch.WordTrace]
  refine ⟨275629898556942938917288739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183753265704628625944859159 275629898556942938917288739)
  ·
    refine ⟨413444847835414408375933109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275629898556942938917288739 413444847835414408375933109)
    ·
      refine ⟨38760454484570100785243729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 413444847835414408375933109 38760454484570100785243729)
      ·
        refine ⟨29070340863427575588932797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38760454484570100785243729 29070340863427575588932797)
        ·
          refine ⟨10901377823785340845849799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29070340863427575588932797 10901377823785340845849799)
          ·
            refine ⟨16352066735678011268774699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10901377823785340845849799 16352066735678011268774699)
            ·
              refine ⟨24528100103517016903162049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16352066735678011268774699 24528100103517016903162049)
              ·
                refine ⟨18396075077637762677371537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24528100103517016903162049 18396075077637762677371537)
                ·
                  refine ⟨13797056308228322008028653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18396075077637762677371537 13797056308228322008028653)
                  ·
                    refine ⟨5173896115585620753010745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13797056308228322008028653 5173896115585620753010745)
                    ·
                      refine ⟨3880422086689215564758059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5173896115585620753010745 3880422086689215564758059)
                      ·
                        rfl

theorem cell23_7557095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_7557095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557095 prefixEnd_7557095 := by exact prefixLift 7557095
  have htrace : WordTrace (prefixWord ++ tailWord_7557095) baseStart_7557095 baseEnd_7557095 := by
    simpa [prefixWord, tailWord_7557095, baseEnd_7557095] using wordTrace_append hprefix tailTrace_7557095
  have hstable : (prefixWord ++ tailWord_7557095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557095).length < 2 ^ (prefixWord ++ tailWord_7557095).sum := by decide
  have hdescent : baseEnd_7557095 < baseStart_7557095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557104 : List Nat := [2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 6]
def baseStart_7557104 : Nat := 118140960795 + 7557104 * 2 ^ 59
def prefixEnd_7557104 : Nat := 4983230072969 + 3 ^ 40 * 7557104 * 2
def baseEnd_7557104 : Nat := 3880426708015106029545517

theorem tailTrace_7557104 : CollatzResearch.WordTrace tailWord_7557104 prefixEnd_7557104 3880426708015106029545517 := by
  unfold tailWord_7557104
  simp only [CollatzResearch.WordTrace]
  refine ⟨137815113406955166727183183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183753484542606888969577577 137815113406955166727183183)
  ·
    refine ⟨206722670110432750090774775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137815113406955166727183183 206722670110432750090774775)
    ·
      refine ⟨310084005165649125136162163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206722670110432750090774775 310084005165649125136162163)
      ·
        refine ⟨465126007748473687704243245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310084005165649125136162163 465126007748473687704243245)
        ·
          refine ⟨174422252905677632889091217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 465126007748473687704243245 174422252905677632889091217)
          ·
            refine ⟨130816689679258224666818413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174422252905677632889091217 130816689679258224666818413)
            ·
              refine ⟨49056258629721834250056905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130816689679258224666818413 49056258629721834250056905)
              ·
                refine ⟨36792193972291375687542679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49056258629721834250056905 36792193972291375687542679)
                ·
                  refine ⟨55188290958437063531314019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36792193972291375687542679 55188290958437063531314019)
                  ·
                    refine ⟨82782436437655595296971029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55188290958437063531314019 82782436437655595296971029)
                    ·
                      refine ⟨3880426708015106029545517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82782436437655595296971029 3880426708015106029545517)
                      ·
                        rfl

theorem cell23_7557104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 6].length) (baseStart_7557104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557104 prefixEnd_7557104 := by exact prefixLift 7557104
  have htrace : WordTrace (prefixWord ++ tailWord_7557104) baseStart_7557104 baseEnd_7557104 := by
    simpa [prefixWord, tailWord_7557104, baseEnd_7557104] using wordTrace_append hprefix tailTrace_7557104
  have hstable : (prefixWord ++ tailWord_7557104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557104).length < 2 ^ (prefixWord ++ tailWord_7557104).sum := by decide
  have hdescent : baseEnd_7557104 < baseStart_7557104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557121 : List Nat := [1, 2, 4, 1, 2, 1, 2, 3, 1, 2, 4]
def baseStart_7557121 : Nat := 118140960795 + 7557121 * 2 ^ 59
def prefixEnd_7557121 : Nat := 4983230072969 + 3 ^ 40 * 7557121 * 2
def baseEnd_7557121 : Nat := 3880435437186232463032939

theorem tailTrace_7557121 : CollatzResearch.WordTrace tailWord_7557121 prefixEnd_7557121 3880435437186232463032939 := by
  unfold tailWord_7557121
  simp only [CollatzResearch.WordTrace]
  refine ⟨275630846854848745357735217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183753897903232496905156811 275630846854848745357735217)
  ·
    refine ⟨206723135141136559018301413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275630846854848745357735217 206723135141136559018301413)
    ·
      refine ⟨38760587838963104815931515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206723135141136559018301413 38760587838963104815931515)
      ·
        refine ⟨58140881758444657223897273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38760587838963104815931515 58140881758444657223897273)
        ·
          refine ⟨43605661318833492917922955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58140881758444657223897273 43605661318833492917922955)
          ·
            refine ⟨65408491978250239376884433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43605661318833492917922955 65408491978250239376884433)
            ·
              refine ⟨49056368983687679532663325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65408491978250239376884433 49056368983687679532663325)
              ·
                refine ⟨18396138368882879824748747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49056368983687679532663325 18396138368882879824748747)
                ·
                  refine ⟨27594207553324319737123121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18396138368882879824748747 27594207553324319737123121)
                  ·
                    refine ⟨20695655664993239802842341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27594207553324319737123121 20695655664993239802842341)
                    ·
                      refine ⟨3880435437186232463032939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20695655664993239802842341 3880435437186232463032939)
                      ·
                        rfl

theorem cell23_7557121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_7557121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557121 prefixEnd_7557121 := by exact prefixLift 7557121
  have htrace : WordTrace (prefixWord ++ tailWord_7557121) baseStart_7557121 baseEnd_7557121 := by
    simpa [prefixWord, tailWord_7557121, baseEnd_7557121] using wordTrace_append hprefix tailTrace_7557121
  have hstable : (prefixWord ++ tailWord_7557121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557121).length < 2 ^ (prefixWord ++ tailWord_7557121).sum := by decide
  have hdescent : baseEnd_7557121 < baseStart_7557121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557168 : List Nat := [2, 1, 1, 1, 2, 5, 1, 2, 3, 3, 2]
def baseStart_7557168 : Nat := 118140960795 + 7557168 * 2 ^ 59
def prefixEnd_7557168 : Nat := 4983230072969 + 3 ^ 40 * 7557168 * 2
def baseEnd_7557168 : Nat := 3880459570776993779145223

theorem tailTrace_7557168 : CollatzResearch.WordTrace tailWord_7557168 prefixEnd_7557168 3880459570776993779145223 := by
  unfold tailWord_7557168
  simp only [CollatzResearch.WordTrace]
  refine ⟨137816280542839236192348079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183755040723785648256464105 137816280542839236192348079)
  ·
    refine ⟨206724420814258854288522119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137816280542839236192348079 206724420814258854288522119)
    ·
      refine ⟨310086631221388281432783179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206724420814258854288522119 310086631221388281432783179)
      ·
        refine ⟨465129946832082422149174769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310086631221388281432783179 465129946832082422149174769)
        ·
          refine ⟨348847460124061816611881077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465129946832082422149174769 348847460124061816611881077)
          ·
            refine ⟨32704449386630795307363851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 348847460124061816611881077 32704449386630795307363851)
            ·
              refine ⟨49056674079946192961045777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32704449386630795307363851 49056674079946192961045777)
              ·
                refine ⟨36792505559959644720784333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49056674079946192961045777 36792505559959644720784333)
                ·
                  refine ⟨13797189584984866770294125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36792505559959644720784333 13797189584984866770294125)
                  ·
                    refine ⟨5173946094369325038860297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13797189584984866770294125 5173946094369325038860297)
                    ·
                      refine ⟨3880459570776993779145223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5173946094369325038860297 3880459570776993779145223)
                      ·
                        rfl

theorem cell23_7557168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 3, 3, 2].length) (baseStart_7557168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557168 prefixEnd_7557168 := by exact prefixLift 7557168
  have htrace : WordTrace (prefixWord ++ tailWord_7557168) baseStart_7557168 baseEnd_7557168 := by
    simpa [prefixWord, tailWord_7557168, baseEnd_7557168] using wordTrace_append hprefix tailTrace_7557168
  have hstable : (prefixWord ++ tailWord_7557168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557168).length < 2 ^ (prefixWord ++ tailWord_7557168).sum := by decide
  have hdescent : baseEnd_7557168 < baseStart_7557168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557181 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 2, 3, 4]
def baseStart_7557181 : Nat := 118140960795 + 7557181 * 2 ^ 59
def prefixEnd_7557181 : Nat := 4983230072969 + 3 ^ 40 * 7557181 * 2
def baseEnd_7557181 : Nat := 3880466246025502228282663

theorem tailTrace_7557181 : CollatzResearch.WordTrace tailWord_7557181 prefixEnd_7557181 3880466246025502228282663 := by
  unfold tailWord_7557181
  simp only [CollatzResearch.WordTrace]
  refine ⟨275633035234631375604919397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183755356823087583736612931 275633035234631375604919397)
  ·
    refine ⟨51681194106493382925922387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275633035234631375604919397 51681194106493382925922387)
    ·
      refine ⟨77521791159740074388883581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51681194106493382925922387 77521791159740074388883581)
      ·
        refine ⟨29070671684902527895831343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77521791159740074388883581 29070671684902527895831343)
        ·
          refine ⟨43606007527353791843747015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29070671684902527895831343 43606007527353791843747015)
          ·
            refine ⟨65409011291030687765620523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43606007527353791843747015 65409011291030687765620523)
            ·
              refine ⟨98113516936546031648430785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65409011291030687765620523 98113516936546031648430785)
              ·
                refine ⟨73585137702409523736323089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98113516936546031648430785 73585137702409523736323089)
                ·
                  refine ⟨55188853276807142802242317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73585137702409523736323089 55188853276807142802242317)
                  ·
                    refine ⟨20695819978802678550840869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55188853276807142802242317 20695819978802678550840869)
                    ·
                      refine ⟨3880466246025502228282663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20695819978802678550840869 3880466246025502228282663)
                      ·
                        rfl

theorem cell23_7557181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_7557181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557181 prefixEnd_7557181 := by exact prefixLift 7557181
  have htrace : WordTrace (prefixWord ++ tailWord_7557181) baseStart_7557181 baseEnd_7557181 := by
    simpa [prefixWord, tailWord_7557181, baseEnd_7557181] using wordTrace_append hprefix tailTrace_7557181
  have hstable : (prefixWord ++ tailWord_7557181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557181).length < 2 ^ (prefixWord ++ tailWord_7557181).sum := by decide
  have hdescent : baseEnd_7557181 < baseStart_7557181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557185 : List Nat := [1, 2, 5, 1, 2, 1, 2, 1, 3, 3, 2]
def baseStart_7557185 : Nat := 118140960795 + 7557185 * 2 ^ 59
def prefixEnd_7557185 : Nat := 4983230072969 + 3 ^ 40 * 7557185 * 2
def baseEnd_7557185 : Nat := 3880468299948120212632645

theorem tailTrace_7557185 : CollatzResearch.WordTrace tailWord_7557185 prefixEnd_7557185 3880468299948120212632645 := by
  unfold tailWord_7557185
  simp only [CollatzResearch.WordTrace]
  refine ⟨275633181126616884288065009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183755454084411256192043339 275633181126616884288065009)
  ·
    refine ⟨206724885844962663216048757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275633181126616884288065009 206724885844962663216048757)
    ·
      refine ⟨19380458047965249676504571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206724885844962663216048757 19380458047965249676504571)
      ·
        refine ⟨29070687071947874514756857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19380458047965249676504571 29070687071947874514756857)
        ·
          refine ⟨21803015303960905886067643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29070687071947874514756857 21803015303960905886067643)
          ·
            refine ⟨32704522955941358829101465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21803015303960905886067643 32704522955941358829101465)
            ·
              refine ⟨24528392216956019121826099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32704522955941358829101465 24528392216956019121826099)
              ·
                refine ⟨36792588325434028682739149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24528392216956019121826099 36792588325434028682739149)
                ·
                  refine ⟨13797220622037760756027181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36792588325434028682739149 13797220622037760756027181)
                  ·
                    refine ⟨5173957733264160283510193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13797220622037760756027181 5173957733264160283510193)
                    ·
                      refine ⟨3880468299948120212632645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5173957733264160283510193 3880468299948120212632645)
                      ·
                        rfl

theorem cell23_7557185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_7557185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557185 prefixEnd_7557185 := by exact prefixLift 7557185
  have htrace : WordTrace (prefixWord ++ tailWord_7557185) baseStart_7557185 baseEnd_7557185 := by
    simpa [prefixWord, tailWord_7557185, baseEnd_7557185] using wordTrace_append hprefix tailTrace_7557185
  have hstable : (prefixWord ++ tailWord_7557185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557185).length < 2 ^ (prefixWord ++ tailWord_7557185).sum := by decide
  have hdescent : baseEnd_7557185 < baseStart_7557185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557202 : List Nat := [3, 2, 2, 1, 4, 1, 1, 3, 1, 3, 2]
def baseStart_7557202 : Nat := 118140960795 + 7557202 * 2 ^ 59
def prefixEnd_7557202 : Nat := 4983230072969 + 3 ^ 40 * 7557202 * 2
def baseEnd_7557202 : Nat := 3880477029119246646120067

theorem tailTrace_7557202 : CollatzResearch.WordTrace tailWord_7557202 prefixEnd_7557202 3880477029119246646120067 := by
  unfold tailWord_7557202
  simp only [CollatzResearch.WordTrace]
  refine ⟨68908450291888824047858465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183755867445036864127622573 68908450291888824047858465)
  ·
    refine ⟨51681337718916618035893849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68908450291888824047858465 51681337718916618035893849)
    ·
      refine ⟨38761003289187463526920387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51681337718916618035893849 38761003289187463526920387)
      ·
        refine ⟨58141504933781195290380581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38761003289187463526920387 58141504933781195290380581)
        ·
          refine ⟨10901532175083974116946359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58141504933781195290380581 10901532175083974116946359)
          ·
            refine ⟨16352298262625961175419539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10901532175083974116946359 16352298262625961175419539)
            ·
              refine ⟨24528447393938941763129309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16352298262625961175419539 24528447393938941763129309)
              ·
                refine ⟨9198167772727103161173491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24528447393938941763129309 9198167772727103161173491)
                ·
                  refine ⟨13797251659090654741760237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9198167772727103161173491 13797251659090654741760237)
                  ·
                    refine ⟨5173969372158995528160089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13797251659090654741760237 5173969372158995528160089)
                    ·
                      refine ⟨3880477029119246646120067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5173969372158995528160089 3880477029119246646120067)
                      ·
                        rfl

theorem cell23_7557202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_7557202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557202 prefixEnd_7557202 := by exact prefixLift 7557202
  have htrace : WordTrace (prefixWord ++ tailWord_7557202) baseStart_7557202 baseEnd_7557202 := by
    simpa [prefixWord, tailWord_7557202, baseEnd_7557202] using wordTrace_append hprefix tailTrace_7557202
  have hstable : (prefixWord ++ tailWord_7557202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557202).length < 2 ^ (prefixWord ++ tailWord_7557202).sum := by decide
  have hdescent : baseEnd_7557202 < baseStart_7557202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557215 : List Nat := [1, 1, 2, 3, 1, 1, 2, 6, 2, 2, 2]
def baseStart_7557215 : Nat := 118140960795 + 7557215 * 2 ^ 59
def prefixEnd_7557215 : Nat := 4983230072969 + 3 ^ 40 * 7557215 * 2
def baseEnd_7557215 : Nat := 3880483704367755095257507

theorem tailTrace_7557215 : CollatzResearch.WordTrace tailWord_7557215 prefixEnd_7557215 3880483704367755095257507 := by
  unfold tailWord_7557215
  simp only [CollatzResearch.WordTrace]
  refine ⟨275634275316508199411657099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183756183544338799607771399 275634275316508199411657099)
  ·
    refine ⟨413451412974762299117485649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275634275316508199411657099 413451412974762299117485649)
    ·
      refine ⟨310088559731071724338114237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413451412974762299117485649 310088559731071724338114237)
      ·
        refine ⟨116283209899151896626792839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310088559731071724338114237 116283209899151896626792839)
        ·
          refine ⟨174424814848727844940189259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116283209899151896626792839 174424814848727844940189259)
          ·
            refine ⟨261637222273091767410283889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174424814848727844940189259 261637222273091767410283889)
            ·
              refine ⟨196227916704818825557712917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261637222273091767410283889 196227916704818825557712917)
              ·
                refine ⟨9198183595538382448017793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 196227916704818825557712917 9198183595538382448017793)
                ·
                  refine ⟨6898637696653786836013345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9198183595538382448017793 6898637696653786836013345)
                  ·
                    refine ⟨5173978272490340127010009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6898637696653786836013345 5173978272490340127010009)
                    ·
                      refine ⟨3880483704367755095257507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5173978272490340127010009 3880483704367755095257507)
                      ·
                        rfl

theorem cell23_7557215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2, 2, 2].length) (baseStart_7557215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557215 prefixEnd_7557215 := by exact prefixLift 7557215
  have htrace : WordTrace (prefixWord ++ tailWord_7557215) baseStart_7557215 baseEnd_7557215 := by
    simpa [prefixWord, tailWord_7557215, baseEnd_7557215] using wordTrace_append hprefix tailTrace_7557215
  have hstable : (prefixWord ++ tailWord_7557215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557215).length < 2 ^ (prefixWord ++ tailWord_7557215).sum := by decide
  have hdescent : baseEnd_7557215 < baseStart_7557215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557221 : List Nat := [1, 3, 1, 3, 2, 2, 1, 3, 7]
def baseStart_7557221 : Nat := 118140960795 + 7557221 * 2 ^ 59
def prefixEnd_7557221 : Nat := 4983230072969 + 3 ^ 40 * 7557221 * 2
def baseEnd_7557221 : Nat := 431165198361298007975831

theorem tailTrace_7557221 : CollatzResearch.WordTrace tailWord_7557221 prefixEnd_7557221 431165198361298007975831 := by
  unfold tailWord_7557221
  simp only [CollatzResearch.WordTrace]
  refine ⟨275634494154486462436375517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183756329436324308290917011 275634494154486462436375517)
  ·
    refine ⟨103362935307932423413640819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275634494154486462436375517 103362935307932423413640819)
    ·
      refine ⟨155044402961898635120461229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103362935307932423413640819 155044402961898635120461229)
      ·
        refine ⟨58141651110711988170172961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155044402961898635120461229 58141651110711988170172961)
        ·
          refine ⟨43606238333033991127629721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58141651110711988170172961 43606238333033991127629721)
          ·
            refine ⟨32704678749775493345722291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43606238333033991127629721 32704678749775493345722291)
            ·
              refine ⟨49057018124663240018583437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32704678749775493345722291 49057018124663240018583437)
              ·
                refine ⟨18396381796748715006968789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49057018124663240018583437 18396381796748715006968789)
                ·
                  refine ⟨431165198361298007975831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18396381796748715006968789 431165198361298007975831)
                  ·
                    rfl

theorem cell23_7557221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 7].length) (baseStart_7557221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557221 prefixEnd_7557221 := by exact prefixLift 7557221
  have htrace : WordTrace (prefixWord ++ tailWord_7557221) baseStart_7557221 baseEnd_7557221 := by
    simpa [prefixWord, tailWord_7557221, baseEnd_7557221] using wordTrace_append hprefix tailTrace_7557221
  have hstable : (prefixWord ++ tailWord_7557221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557221).length < 2 ^ (prefixWord ++ tailWord_7557221).sum := by decide
  have hdescent : baseEnd_7557221 < baseStart_7557221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557238 : List Nat := [5, 1, 1, 2, 1, 2, 2, 2, 7]
def baseStart_7557238 : Nat := 118140960795 + 7557238 * 2 ^ 59
def prefixEnd_7557238 : Nat := 4983230072969 + 3 ^ 40 * 7557238 * 2
def baseEnd_7557238 : Nat := 431166168269200945029989

theorem tailTrace_7557238 : CollatzResearch.WordTrace tailWord_7557238 prefixEnd_7557238 431166168269200945029989 := by
  unfold tailWord_7557238
  simp only [CollatzResearch.WordTrace]
  refine ⟨17227194637214054646234023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183756742796949916226496245 17227194637214054646234023)
  ·
    refine ⟨25840791955821081969351035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17227194637214054646234023 25840791955821081969351035)
    ·
      refine ⟨38761187933731622954026553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25840791955821081969351035 38761187933731622954026553)
      ·
        refine ⟨29070890950298717215519915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38761187933731622954026553 29070890950298717215519915)
        ·
          refine ⟨43606336425448075823279873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29070890950298717215519915 43606336425448075823279873)
          ·
            refine ⟨32704752319086056867459905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43606336425448075823279873 32704752319086056867459905)
            ·
              refine ⟨24528564239314542650594929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32704752319086056867459905 24528564239314542650594929)
              ·
                refine ⟨18396423179485906987946197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24528564239314542650594929 18396423179485906987946197)
                ·
                  refine ⟨431166168269200945029989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18396423179485906987946197 431166168269200945029989)
                  ·
                    rfl

theorem cell23_7557238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_7557238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557238 prefixEnd_7557238 := by exact prefixLift 7557238
  have htrace : WordTrace (prefixWord ++ tailWord_7557238) baseStart_7557238 baseEnd_7557238 := by
    simpa [prefixWord, tailWord_7557238, baseEnd_7557238] using wordTrace_append hprefix tailTrace_7557238
  have hstable : (prefixWord ++ tailWord_7557238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557238).length < 2 ^ (prefixWord ++ tailWord_7557238).sum := by decide
  have hdescent : baseEnd_7557238 < baseStart_7557238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557251 : List Nat := [1, 1, 1, 3, 3, 3, 2, 1, 1, 7]
def baseStart_7557251 : Nat := 118140960795 + 7557251 * 2 ^ 59
def prefixEnd_7557251 : Nat := 4983230072969 + 3 ^ 40 * 7557251 * 2
def baseEnd_7557251 : Nat := 1293500729890438984802447

theorem tailTrace_7557251 : CollatzResearch.WordTrace tailWord_7557251 prefixEnd_7557251 1293500729890438984802447 := by
  unfold tailWord_7557251
  simp only [CollatzResearch.WordTrace]
  refine ⟨275635588344377777559967607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183757058896251851706645071 275635588344377777559967607)
  ·
    refine ⟨413453382516566666339951411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275635588344377777559967607 413453382516566666339951411)
    ·
      refine ⟨620180073774849999509927117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413453382516566666339951411 620180073774849999509927117)
      ·
        refine ⟨232567527665568749816222669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 620180073774849999509927117 232567527665568749816222669)
        ·
          refine ⟨87212822874588281181083501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232567527665568749816222669 87212822874588281181083501)
          ·
            refine ⟨32704808577970605442906313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87212822874588281181083501 32704808577970605442906313)
            ·
              refine ⟨24528606433477954082179735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32704808577970605442906313 24528606433477954082179735)
              ·
                refine ⟨36792909650216931123269603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24528606433477954082179735 36792909650216931123269603)
                ·
                  refine ⟨55189364475325396684904405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36792909650216931123269603 55189364475325396684904405)
                  ·
                    refine ⟨1293500729890438984802447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55189364475325396684904405 1293500729890438984802447)
                    ·
                      rfl

theorem cell23_7557251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 7].length) (baseStart_7557251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557251 prefixEnd_7557251 := by exact prefixLift 7557251
  have htrace : WordTrace (prefixWord ++ tailWord_7557251) baseStart_7557251 baseEnd_7557251 := by
    simpa [prefixWord, tailWord_7557251, baseEnd_7557251] using wordTrace_append hprefix tailTrace_7557251
  have hstable : (prefixWord ++ tailWord_7557251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557251).length < 2 ^ (prefixWord ++ tailWord_7557251).sum := by decide
  have hdescent : baseEnd_7557251 < baseStart_7557251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557272 : List Nat := [2, 1, 2, 4, 3, 1, 3, 2, 5]
def baseStart_7557272 : Nat := 118140960795 + 7557272 * 2 ^ 59
def prefixEnd_7557272 : Nat := 4983230072969 + 3 ^ 40 * 7557272 * 2
def baseEnd_7557272 : Nat := 431168108085006819138305

theorem tailTrace_7557272 : CollatzResearch.WordTrace tailWord_7557272 prefixEnd_7557272 431168108085006819138305 := by
  unfold tailWord_7557272
  simp only [CollatzResearch.WordTrace]
  refine ⟨137818177138650849073241035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183757569518201132097654713 137818177138650849073241035)
  ·
    refine ⟨206727265707976273609861553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137818177138650849073241035 206727265707976273609861553)
    ·
      refine ⟨155045449280982205207396165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206727265707976273609861553 155045449280982205207396165)
      ·
        refine ⟨29071021740184163476386781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155045449280982205207396165 29071021740184163476386781)
        ·
          refine ⟨10901633152569061303645043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29071021740184163476386781 10901633152569061303645043)
          ·
            refine ⟨16352449728853591955467565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10901633152569061303645043 16352449728853591955467565)
            ·
              refine ⟨6132168648320096983300337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16352449728853591955467565 6132168648320096983300337)
              ·
                refine ⟨4599126486240072737475253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6132168648320096983300337 4599126486240072737475253)
                ·
                  refine ⟨431168108085006819138305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4599126486240072737475253 431168108085006819138305)
                  ·
                    rfl

theorem cell23_7557272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2, 5].length) (baseStart_7557272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557272 prefixEnd_7557272 := by exact prefixLift 7557272
  have htrace : WordTrace (prefixWord ++ tailWord_7557272) baseStart_7557272 baseEnd_7557272 := by
    simpa [prefixWord, tailWord_7557272, baseEnd_7557272] using wordTrace_append hprefix tailTrace_7557272
  have hstable : (prefixWord ++ tailWord_7557272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557272).length < 2 ^ (prefixWord ++ tailWord_7557272).sum := by decide
  have hdescent : baseEnd_7557272 < baseStart_7557272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557298 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 5, 4]
def baseStart_7557298 : Nat := 118140960795 + 7557298 * 2 ^ 59
def prefixEnd_7557298 : Nat := 4983230072969 + 3 ^ 40 * 7557298 * 2
def baseEnd_7557298 : Nat := 1293508774420692756839875

theorem tailTrace_7557298 : CollatzResearch.WordTrace tailWord_7557298 prefixEnd_7557298 1293508774420692756839875 := by
  unfold tailWord_7557298
  simp only [CollatzResearch.WordTrace]
  refine ⟨68909325643801876146732137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183758201716805003057952365 68909325643801876146732137)
  ·
    refine ⟨51681994232851407110049103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68909325643801876146732137 51681994232851407110049103)
    ·
      refine ⟨77522991349277110665073655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51681994232851407110049103 77522991349277110665073655)
      ·
        refine ⟨116284487023915665997610483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77522991349277110665073655 116284487023915665997610483)
        ·
          refine ⟨174426730535873498996415725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116284487023915665997610483 174426730535873498996415725)
          ·
            refine ⟨65410023950952562123655897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174426730535873498996415725 65410023950952562123655897)
            ·
              refine ⟨49057517963214421592741923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65410023950952562123655897 49057517963214421592741923)
              ·
                refine ⟨73586276944821632389112885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49057517963214421592741923 73586276944821632389112885)
                ·
                  refine ⟨6898713463577028036479333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73586276944821632389112885 6898713463577028036479333)
                  ·
                    refine ⟨1293508774420692756839875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6898713463577028036479333 1293508774420692756839875)
                    ·
                      rfl

theorem cell23_7557298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_7557298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557298 prefixEnd_7557298 := by exact prefixLift 7557298
  have htrace : WordTrace (prefixWord ++ tailWord_7557298) baseStart_7557298 baseEnd_7557298 := by
    simpa [prefixWord, tailWord_7557298, baseEnd_7557298] using wordTrace_append hprefix tailTrace_7557298
  have hstable : (prefixWord ++ tailWord_7557298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557298).length < 2 ^ (prefixWord ++ tailWord_7557298).sum := by decide
  have hdescent : baseEnd_7557298 < baseStart_7557298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557355 : List Nat := [1, 1, 1, 1, 2, 5, 3, 2, 3, 1, 3]
def baseStart_7557355 : Nat := 118140960795 + 7557355 * 2 ^ 59
def prefixEnd_7557355 : Nat := 4983230072969 + 3 ^ 40 * 7557355 * 2
def baseEnd_7557355 : Nat := 3880555591659384547506863

theorem tailTrace_7557355 : CollatzResearch.WordTrace tailWord_7557355 prefixEnd_7557355 3880555591659384547506863 := by
  unfold tailWord_7557355
  simp only [CollatzResearch.WordTrace]
  refine ⟨275639381536001003321753519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183759587690667335547835679 275639381536001003321753519)
  ·
    refine ⟨413459072304001504982630279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275639381536001003321753519 413459072304001504982630279)
    ·
      refine ⟨620188608456002257473945419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413459072304001504982630279 620188608456002257473945419)
      ·
        refine ⟨930282912684003386210918129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620188608456002257473945419 930282912684003386210918129)
        ·
          refine ⟨697712184513002539658188597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 930282912684003386210918129 697712184513002539658188597)
          ·
            refine ⟨65410517298093988092955181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 697712184513002539658188597 65410517298093988092955181)
            ·
              refine ⟨24528943986785245534858193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65410517298093988092955181 24528943986785245534858193)
              ·
                refine ⟨18396707990088934151143645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24528943986785245534858193 18396707990088934151143645)
                ·
                  refine ⟨6898765496283350306678867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18396707990088934151143645 6898765496283350306678867)
                  ·
                    refine ⟨10348148244425025460018301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6898765496283350306678867 10348148244425025460018301)
                    ·
                      refine ⟨3880555591659384547506863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10348148244425025460018301 3880555591659384547506863)
                      ·
                        rfl

theorem cell23_7557355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3, 1, 3].length) (baseStart_7557355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557355 prefixEnd_7557355 := by exact prefixLift 7557355
  have htrace : WordTrace (prefixWord ++ tailWord_7557355) baseStart_7557355 baseEnd_7557355 := by
    simpa [prefixWord, tailWord_7557355, baseEnd_7557355] using wordTrace_append hprefix tailTrace_7557355
  have hstable : (prefixWord ++ tailWord_7557355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557355).length < 2 ^ (prefixWord ++ tailWord_7557355).sum := by decide
  have hdescent : baseEnd_7557355 < baseStart_7557355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557412 : List Nat := [2, 3, 1, 3, 1, 3, 2, 2, 1, 1, 4]
def baseStart_7557412 : Nat := 118140960795 + 7557412 * 2 ^ 59
def prefixEnd_7557412 : Nat := 4983230072969 + 3 ^ 40 * 7557412 * 2
def baseEnd_7557412 : Nat := 3880584860056690824494101

theorem tailTrace_7557412 : CollatzResearch.WordTrace tailWord_7557412 prefixEnd_7557412 3880584860056690824494101 := by
  unfold tailWord_7557412
  simp only [CollatzResearch.WordTrace]
  refine ⟨137820730248397251028289245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183760973664529668037718993 137820730248397251028289245)
  ·
    refine ⟨51682773843148969135608467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137820730248397251028289245 51682773843148969135608467)
    ·
      refine ⟨77524160764723453703412701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51682773843148969135608467 77524160764723453703412701)
      ·
        refine ⟨29071560286771295138779763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77524160764723453703412701 29071560286771295138779763)
        ·
          refine ⟨43607340430156942708169645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29071560286771295138779763 43607340430156942708169645)
          ·
            refine ⟨16352752661308853515563617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43607340430156942708169645 16352752661308853515563617)
            ·
              refine ⟨12264564495981640136672713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16352752661308853515563617 12264564495981640136672713)
              ·
                refine ⟨9198423371986230102504535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12264564495981640136672713 9198423371986230102504535)
                ·
                  refine ⟨13797635057979345153756803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9198423371986230102504535 13797635057979345153756803)
                  ·
                    refine ⟨20696452586969017730635205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13797635057979345153756803 20696452586969017730635205)
                    ·
                      refine ⟨3880584860056690824494101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20696452586969017730635205 3880584860056690824494101)
                      ·
                        rfl

theorem cell23_7557412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_7557412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557412 prefixEnd_7557412 := by exact prefixLift 7557412
  have htrace : WordTrace (prefixWord ++ tailWord_7557412) baseStart_7557412 baseEnd_7557412 := by
    simpa [prefixWord, tailWord_7557412, baseEnd_7557412] using wordTrace_append hprefix tailTrace_7557412
  have hstable : (prefixWord ++ tailWord_7557412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557412).length < 2 ^ (prefixWord ++ tailWord_7557412).sum := by decide
  have hdescent : baseEnd_7557412 < baseStart_7557412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557515 : List Nat := [1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 4]
def baseStart_7557515 : Nat := 118140960795 + 7557515 * 2 ^ 59
def prefixEnd_7557515 : Nat := 4983230072969 + 3 ^ 40 * 7557515 * 2
def baseEnd_7557515 : Nat := 3880637748564103921506127

theorem tailTrace_7557515 : CollatzResearch.WordTrace tailWord_7557515 prefixEnd_7557515 3880637748564103921506127 := by
  unfold tailWord_7557515
  simp only [CollatzResearch.WordTrace]
  refine ⟨275645217215421350647577999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183763478143614233765051999 275645217215421350647577999)
  ·
    refine ⟨413467825823132025971366999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275645217215421350647577999 413467825823132025971366999)
    ·
      refine ⟨620201738734698038957050499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413467825823132025971366999 620201738734698038957050499)
      ·
        refine ⟨930302608102047058435575749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620201738734698038957050499 930302608102047058435575749)
        ·
          refine ⟨174431739019133823456670453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 930302608102047058435575749 174431739019133823456670453)
          ·
            refine ⟨16352975533043795949062855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174431739019133823456670453 16352975533043795949062855)
            ·
              refine ⟨24529463299565693923594283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16352975533043795949062855 24529463299565693923594283)
              ·
                refine ⟨36794194949348540885391425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24529463299565693923594283 36794194949348540885391425)
                ·
                  refine ⟨27595646212011405664043569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36794194949348540885391425 27595646212011405664043569)
                  ·
                    refine ⟨20696734659008554248032677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27595646212011405664043569 20696734659008554248032677)
                    ·
                      refine ⟨3880637748564103921506127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20696734659008554248032677 3880637748564103921506127)
                      ·
                        rfl

theorem cell23_7557515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 4].length) (baseStart_7557515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557515 prefixEnd_7557515 := by exact prefixLift 7557515
  have htrace : WordTrace (prefixWord ++ tailWord_7557515) baseStart_7557515 baseEnd_7557515 := by
    simpa [prefixWord, tailWord_7557515, baseEnd_7557515] using wordTrace_append hprefix tailTrace_7557515
  have hstable : (prefixWord ++ tailWord_7557515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557515).length < 2 ^ (prefixWord ++ tailWord_7557515).sum := by decide
  have hdescent : baseEnd_7557515 < baseStart_7557515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557535 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 1, 5, 3]
def baseStart_7557535 : Nat := 118140960795 + 7557535 * 2 ^ 59
def prefixEnd_7557535 : Nat := 4983230072969 + 3 ^ 40 * 7557535 * 2
def baseEnd_7557535 : Nat := 3880648018177193843256035

theorem tailTrace_7557535 : CollatzResearch.WordTrace tailWord_7557535 prefixEnd_7557535 3880648018177193843256035 := by
  unfold tailWord_7557535
  simp only [CollatzResearch.WordTrace]
  refine ⟨275645946675348894063306059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183763964450232596042204039 275645946675348894063306059)
  ·
    refine ⟨413468920013023341094959089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275645946675348894063306059 413468920013023341094959089)
    ·
      refine ⟨310101690009767505821219317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413468920013023341094959089 310101690009767505821219317)
      ·
        refine ⟨29072033438415703670739311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 310101690009767505821219317 29072033438415703670739311)
        ·
          refine ⟨43608050157623555506108967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29072033438415703670739311 43608050157623555506108967)
          ·
            refine ⟨65412075236435333259163451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43608050157623555506108967 65412075236435333259163451)
            ·
              refine ⟨98118112854652999888745177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65412075236435333259163451 98118112854652999888745177)
              ·
                refine ⟨73588584640989749916558883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98118112854652999888745177 73588584640989749916558883)
                ·
                  refine ⟨110382876961484624874838325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73588584640989749916558883 110382876961484624874838325)
                  ·
                    refine ⟨10348394715139183582016093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110382876961484624874838325 10348394715139183582016093)
                    ·
                      refine ⟨3880648018177193843256035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10348394715139183582016093 3880648018177193843256035)
                      ·
                        rfl

theorem cell23_7557535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_7557535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557535 prefixEnd_7557535 := by exact prefixLift 7557535
  have htrace : WordTrace (prefixWord ++ tailWord_7557535) baseStart_7557535 baseEnd_7557535 := by
    simpa [prefixWord, tailWord_7557535, baseEnd_7557535] using wordTrace_append hprefix tailTrace_7557535
  have hstable : (prefixWord ++ tailWord_7557535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557535).length < 2 ^ (prefixWord ++ tailWord_7557535).sum := by decide
  have hdescent : baseEnd_7557535 < baseStart_7557535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557575 : List Nat := [1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 4]
def baseStart_7557575 : Nat := 118140960795 + 7557575 * 2 ^ 59
def prefixEnd_7557575 : Nat := 4983230072969 + 3 ^ 40 * 7557575 * 2
def baseEnd_7557575 : Nat := 3880668557403373686755851

theorem tailTrace_7557575 : CollatzResearch.WordTrace tailWord_7557575 prefixEnd_7557575 3880668557403373686755851 := by
  unfold tailWord_7557575
  simp only [CollatzResearch.WordTrace]
  refine ⟨275647405595203980894762179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183764937063469320596508119 275647405595203980894762179)
  ·
    refine ⟨413471108392805971342143269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275647405595203980894762179 413471108392805971342143269)
    ·
      refine ⟨77525832823651119626651863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 413471108392805971342143269 77525832823651119626651863)
      ·
        refine ⟨116288749235476679439977795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77525832823651119626651863 116288749235476679439977795)
        ·
          refine ⟨174433123853215019159966693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116288749235476679439977795 174433123853215019159966693)
          ·
            refine ⟨32706210722477816092493755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174433123853215019159966693 32706210722477816092493755)
            ·
              refine ⟨49059316083716724138740633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32706210722477816092493755 49059316083716724138740633)
              ·
                refine ⟨36794487062787543104055475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49059316083716724138740633 36794487062787543104055475)
                ·
                  refine ⟨55191730594181314656083213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36794487062787543104055475 55191730594181314656083213)
                  ·
                    refine ⟨20696898972817992996031205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55191730594181314656083213 20696898972817992996031205)
                    ·
                      refine ⟨3880668557403373686755851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20696898972817992996031205 3880668557403373686755851)
                      ·
                        rfl

theorem cell23_7557575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_7557575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557575 prefixEnd_7557575 := by exact prefixLift 7557575
  have htrace : WordTrace (prefixWord ++ tailWord_7557575) baseStart_7557575 baseEnd_7557575 := by
    simpa [prefixWord, tailWord_7557575, baseEnd_7557575] using wordTrace_append hprefix tailTrace_7557575
  have hstable : (prefixWord ++ tailWord_7557575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557575).length < 2 ^ (prefixWord ++ tailWord_7557575).sum := by decide
  have hdescent : baseEnd_7557575 < baseStart_7557575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557612 : List Nat := [2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 3]
def baseStart_7557612 : Nat := 118140960795 + 7557612 * 2 ^ 59
def prefixEnd_7557612 : Nat := 4983230072969 + 3 ^ 40 * 7557612 * 2
def baseEnd_7557612 : Nat := 3880687556187590041993181

theorem tailTrace_7557612 : CollatzResearch.WordTrace tailWord_7557612 prefixEnd_7557612 3880687556187590041993181 := by
  unfold tailWord_7557612
  simp only [CollatzResearch.WordTrace]
  refine ⟨137824377548034968106929545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183765836730713290809239393 137824377548034968106929545)
  ·
    refine ⟨103368283161026226080197159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137824377548034968106929545 103368283161026226080197159)
    ·
      refine ⟨155052424741539339120295739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103368283161026226080197159 155052424741539339120295739)
      ·
        refine ⟨232578637112309008680443609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155052424741539339120295739 232578637112309008680443609)
        ·
          refine ⟨174433977834231756510332707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232578637112309008680443609 174433977834231756510332707)
          ·
            refine ⟨261650966751347634765499061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174433977834231756510332707 261650966751347634765499061)
            ·
              refine ⟨24529778132938840759265537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 261650966751347634765499061 24529778132938840759265537)
              ·
                refine ⟨18397333599704130569449153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24529778132938840759265537 18397333599704130569449153)
                ·
                  refine ⟨13798000199778097927086865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18397333599704130569449153 13798000199778097927086865)
                  ·
                    refine ⟨10348500149833573445315149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13798000199778097927086865 10348500149833573445315149)
                    ·
                      refine ⟨3880687556187590041993181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10348500149833573445315149 3880687556187590041993181)
                      ·
                        rfl

theorem cell23_7557612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 3].length) (baseStart_7557612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557612 prefixEnd_7557612 := by exact prefixLift 7557612
  have htrace : WordTrace (prefixWord ++ tailWord_7557612) baseStart_7557612 baseEnd_7557612 := by
    simpa [prefixWord, tailWord_7557612, baseEnd_7557612] using wordTrace_append hprefix tailTrace_7557612
  have hstable : (prefixWord ++ tailWord_7557612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557612).length < 2 ^ (prefixWord ++ tailWord_7557612).sum := by decide
  have hdescent : baseEnd_7557612 < baseStart_7557612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557615 : List Nat := [1, 1, 2, 1, 4, 1, 1, 6, 6]
def baseStart_7557615 : Nat := 118140960795 + 7557615 * 2 ^ 59
def prefixEnd_7557615 : Nat := 4983230072969 + 3 ^ 40 * 7557615 * 2
def baseEnd_7557615 : Nat := 431187677403283725583963

theorem tailTrace_7557615 : CollatzResearch.WordTrace tailWord_7557615 prefixEnd_7557615 431187677403283725583963 := by
  unfold tailWord_7557615
  simp only [CollatzResearch.WordTrace]
  refine ⟨275648864515059067726218299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183765909676706045150812199 275648864515059067726218299)
  ·
    refine ⟨413473296772588601589327449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275648864515059067726218299 413473296772588601589327449)
    ·
      refine ⟨310104972579441451191995587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413473296772588601589327449 310104972579441451191995587)
      ·
        refine ⟨465157458869162176787993381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310104972579441451191995587 465157458869162176787993381)
        ·
          refine ⟨87217023537967908147748759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 465157458869162176787993381 87217023537967908147748759)
          ·
            refine ⟨130825535306951862221623139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87217023537967908147748759 130825535306951862221623139)
            ·
              refine ⟨196238302960427793332434709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130825535306951862221623139 196238302960427793332434709)
              ·
                refine ⟨9198670451270052812457877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 196238302960427793332434709 9198670451270052812457877)
                ·
                  refine ⟨431187677403283725583963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9198670451270052812457877 431187677403283725583963)
                  ·
                    rfl

theorem cell23_7557615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 6].length) (baseStart_7557615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557615 prefixEnd_7557615 := by exact prefixLift 7557615
  have htrace : WordTrace (prefixWord ++ tailWord_7557615) baseStart_7557615 baseEnd_7557615 := by
    simpa [prefixWord, tailWord_7557615, baseEnd_7557615] using wordTrace_append hprefix tailTrace_7557615
  have hstable : (prefixWord ++ tailWord_7557615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557615).length < 2 ^ (prefixWord ++ tailWord_7557615).sum := by decide
  have hdescent : baseEnd_7557615 < baseStart_7557615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557669 : List Nat := [1, 3, 1, 2, 2, 1, 4, 2, 2, 3, 2]
def baseStart_7557669 : Nat := 118140960795 + 7557669 * 2 ^ 59
def prefixEnd_7557669 : Nat := 4983230072969 + 3 ^ 40 * 7557669 * 2
def baseEnd_7557669 : Nat := 3880716824584896318980419

theorem tailTrace_7557669 : CollatzResearch.WordTrace tailWord_7557669 prefixEnd_7557669 3880716824584896318980419 := by
  unfold tailWord_7557669
  simp only [CollatzResearch.WordTrace]
  refine ⟨275650834056863434948684061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183767222704575623299122707 275650834056863434948684061)
  ·
    refine ⟨103369062771323788105756523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275650834056863434948684061 103369062771323788105756523)
    ·
      refine ⟨155053594156985682158634785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103369062771323788105756523 155053594156985682158634785)
      ·
        refine ⟨116290195617739261618976089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155053594156985682158634785 116290195617739261618976089)
        ·
          refine ⟨87217646713304446214232067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116290195617739261618976089 87217646713304446214232067)
          ·
            refine ⟨130826470069956669321348101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87217646713304446214232067 130826470069956669321348101)
            ·
              refine ⟨24529963138116875497752769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130826470069956669321348101 24529963138116875497752769)
              ·
                refine ⟨18397472353587656623314577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24529963138116875497752769 18397472353587656623314577)
                ·
                  refine ⟨13798104265190742467485933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18397472353587656623314577 13798104265190742467485933)
                  ·
                    refine ⟨5174289099446528425307225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13798104265190742467485933 5174289099446528425307225)
                    ·
                      refine ⟨3880716824584896318980419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5174289099446528425307225 3880716824584896318980419)
                      ·
                        rfl

theorem cell23_7557669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 3, 2].length) (baseStart_7557669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557669 prefixEnd_7557669 := by exact prefixLift 7557669
  have htrace : WordTrace (prefixWord ++ tailWord_7557669) baseStart_7557669 baseEnd_7557669 := by
    simpa [prefixWord, tailWord_7557669, baseEnd_7557669] using wordTrace_append hprefix tailTrace_7557669
  have hstable : (prefixWord ++ tailWord_7557669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557669).length < 2 ^ (prefixWord ++ tailWord_7557669).sum := by decide
  have hdescent : baseEnd_7557669 < baseStart_7557669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557682 : List Nat := [3, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4]
def baseStart_7557682 : Nat := 118140960795 + 7557682 * 2 ^ 59
def prefixEnd_7557682 : Nat := 4983230072969 + 3 ^ 40 * 7557682 * 2
def baseEnd_7557682 : Nat := 3880723499833404768117859

theorem tailTrace_7557682 : CollatzResearch.WordTrace tailWord_7557682 prefixEnd_7557682 3880723499833404768117859 := by
  unfold tailWord_7557682
  simp only [CollatzResearch.WordTrace]
  refine ⟨68912827051454084542226825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183767538803877558779271533 68912827051454084542226825)
  ·
    refine ⟨51684620288590563406670119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68912827051454084542226825 51684620288590563406670119)
    ·
      refine ⟨77526930432885845110005179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51684620288590563406670119 77526930432885845110005179)
      ·
        refine ⟨116290395649328767665007769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77526930432885845110005179 116290395649328767665007769)
        ·
          refine ⟨87217796736996575748755827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116290395649328767665007769 87217796736996575748755827)
          ·
            refine ⟨130826695105494863623133741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87217796736996575748755827 130826695105494863623133741)
            ·
              refine ⟨49060010664560573858675153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130826695105494863623133741 49060010664560573858675153)
              ·
                refine ⟨36795007998420430394006365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49060010664560573858675153 36795007998420430394006365)
                ·
                  refine ⟨13798127999407661397752387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36795007998420430394006365 13798127999407661397752387)
                  ·
                    refine ⟨20697191999111492096628581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13798127999407661397752387 20697191999111492096628581)
                    ·
                      refine ⟨3880723499833404768117859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20697191999111492096628581 3880723499833404768117859)
                      ·
                        rfl

theorem cell23_7557682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_7557682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557682 prefixEnd_7557682 := by exact prefixLift 7557682
  have htrace : WordTrace (prefixWord ++ tailWord_7557682) baseStart_7557682 baseEnd_7557682 := by
    simpa [prefixWord, tailWord_7557682, baseEnd_7557682] using wordTrace_append hprefix tailTrace_7557682
  have hstable : (prefixWord ++ tailWord_7557682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557682).length < 2 ^ (prefixWord ++ tailWord_7557682).sum := by decide
  have hdescent : baseEnd_7557682 < baseStart_7557682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557692 : List Nat := [2, 2, 2, 2, 3, 1, 1, 3, 1, 6]
def baseStart_7557692 : Nat := 118140960795 + 7557692 * 2 ^ 59
def prefixEnd_7557692 : Nat := 4983230072969 + 3 ^ 40 * 7557692 * 2
def baseEnd_7557692 : Nat := 1293576211546649909664271

theorem tailTrace_7557692 : CollatzResearch.WordTrace tailWord_7557692 prefixEnd_7557692 1293576211546649909664271 := by
  unfold tailWord_7557692
  simp only [CollatzResearch.WordTrace]
  refine ⟨137825836467890054938385665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183767781957186739917847553 137825836467890054938385665)
  ·
    refine ⟨103369377350917541203789249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137825836467890054938385665 103369377350917541203789249)
    ·
      refine ⟨77527033013188155902841937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103369377350917541203789249 77527033013188155902841937)
      ·
        refine ⟨58145274759891116927131453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77527033013188155902841937 58145274759891116927131453)
        ·
          refine ⟨21804478034959168847674295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58145274759891116927131453 21804478034959168847674295)
          ·
            refine ⟨32706717052438753271511443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21804478034959168847674295 32706717052438753271511443)
            ·
              refine ⟨49060075578658129907267165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32706717052438753271511443 49060075578658129907267165)
              ·
                refine ⟨18397528341996798715225187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49060075578658129907267165 18397528341996798715225187)
                ·
                  refine ⟨27596292512995198072837781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18397528341996798715225187 27596292512995198072837781)
                  ·
                    refine ⟨1293576211546649909664271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27596292512995198072837781 1293576211546649909664271)
                    ·
                      rfl

theorem cell23_7557692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_7557692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557692 prefixEnd_7557692 := by exact prefixLift 7557692
  have htrace : WordTrace (prefixWord ++ tailWord_7557692) baseStart_7557692 baseEnd_7557692 := by
    simpa [prefixWord, tailWord_7557692, baseEnd_7557692] using wordTrace_append hprefix tailTrace_7557692
  have hstable : (prefixWord ++ tailWord_7557692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557692).length < 2 ^ (prefixWord ++ tailWord_7557692).sum := by decide
  have hdescent : baseEnd_7557692 < baseStart_7557692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557709 : List Nat := [1, 6, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_7557709 : Nat := 118140960795 + 7557709 * 2 ^ 59
def prefixEnd_7557709 : Nat := 4983230072969 + 3 ^ 40 * 7557709 * 2
def baseEnd_7557709 : Nat := 1293579121270358720826745

theorem tailTrace_7557709 : CollatzResearch.WordTrace tailWord_7557709 prefixEnd_7557709 1293579121270358720826745 := by
  unfold tailWord_7557709
  simp only [CollatzResearch.WordTrace]
  refine ⟨275652292976718521780140181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183768195317812347853426787 275652292976718521780140181)
  ·
    refine ⟨12921201233283680708444071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 275652292976718521780140181 12921201233283680708444071)
    ·
      refine ⟨19381801849925521062666107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12921201233283680708444071 19381801849925521062666107)
      ·
        refine ⟨29072702774888281593999161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19381801849925521062666107 29072702774888281593999161)
        ·
          refine ⟨21804527081166211195499371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29072702774888281593999161 21804527081166211195499371)
          ·
            refine ⟨32706790621749316793249057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21804527081166211195499371 32706790621749316793249057)
            ·
              refine ⟨24530092966311987594936793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32706790621749316793249057 24530092966311987594936793)
              ·
                refine ⟨18397569724733990696202595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24530092966311987594936793 18397569724733990696202595)
                ·
                  refine ⟨27596354587100986044303893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18397569724733990696202595 27596354587100986044303893)
                  ·
                    refine ⟨1293579121270358720826745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27596354587100986044303893 1293579121270358720826745)
                    ·
                      rfl

theorem cell23_7557709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_7557709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557709 prefixEnd_7557709 := by exact prefixLift 7557709
  have htrace : WordTrace (prefixWord ++ tailWord_7557709) baseStart_7557709 baseEnd_7557709 := by
    simpa [prefixWord, tailWord_7557709, baseEnd_7557709] using wordTrace_append hprefix tailTrace_7557709
  have hstable : (prefixWord ++ tailWord_7557709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557709).length < 2 ^ (prefixWord ++ tailWord_7557709).sum := by decide
  have hdescent : baseEnd_7557709 < baseStart_7557709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557716 : List Nat := [2, 4, 1, 1, 1, 3, 4, 1, 1, 1, 4]
def baseStart_7557716 : Nat := 118140960795 + 7557716 * 2 ^ 59
def prefixEnd_7557716 : Nat := 4983230072969 + 3 ^ 40 * 7557716 * 2
def baseEnd_7557716 : Nat := 3880740958175657635092703

theorem tailTrace_7557716 : CollatzResearch.WordTrace tailWord_7557716 prefixEnd_7557716 3880740958175657635092703 := by
  unfold tailWord_7557716
  simp only [CollatzResearch.WordTrace]
  refine ⟨137826274143846580987822501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183768365525128774650430001 137826274143846580987822501)
  ·
    refine ⟨25842426401971233935216719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137826274143846580987822501 25842426401971233935216719)
    ·
      refine ⟨38763639602956850902825079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25842426401971233935216719 38763639602956850902825079)
      ·
        refine ⟨58145459404435276354237619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38763639602956850902825079 58145459404435276354237619)
        ·
          refine ⟨87218189106652914531356429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58145459404435276354237619 87218189106652914531356429)
          ·
            refine ⟨32706820914994842949258661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87218189106652914531356429 32706820914994842949258661)
            ·
              refine ⟨6132528921561533052985999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32706820914994842949258661 6132528921561533052985999)
              ·
                refine ⟨9198793382342299579478999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6132528921561533052985999 9198793382342299579478999)
                ·
                  refine ⟨13798190073513449369218499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9198793382342299579478999 13798190073513449369218499)
                  ·
                    refine ⟨20697285110270174053827749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13798190073513449369218499 20697285110270174053827749)
                    ·
                      refine ⟨3880740958175657635092703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20697285110270174053827749 3880740958175657635092703)
                      ·
                        rfl

theorem cell23_7557716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_7557716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557716 prefixEnd_7557716 := by exact prefixLift 7557716
  have htrace : WordTrace (prefixWord ++ tailWord_7557716) baseStart_7557716 baseEnd_7557716 := by
    simpa [prefixWord, tailWord_7557716, baseEnd_7557716] using wordTrace_append hprefix tailTrace_7557716
  have hstable : (prefixWord ++ tailWord_7557716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557716).length < 2 ^ (prefixWord ++ tailWord_7557716).sum := by decide
  have hdescent : baseEnd_7557716 < baseStart_7557716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557719 : List Nat := [1, 1, 3, 2, 2, 2, 3, 3, 1, 2, 3]
def baseStart_7557719 : Nat := 118140960795 + 7557719 * 2 ^ 59
def prefixEnd_7557719 : Nat := 4983230072969 + 3 ^ 40 * 7557719 * 2
def baseEnd_7557719 : Nat := 3880742498617621123355189

theorem tailTrace_7557719 : CollatzResearch.WordTrace tailWord_7557719 prefixEnd_7557719 3880742498617621123355189 := by
  unfold tailWord_7557719
  simp only [CollatzResearch.WordTrace]
  refine ⟨275652657706682293488004211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183768438471121528992002807 275652657706682293488004211)
  ·
    refine ⟨413478986560023440232006317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275652657706682293488004211 413478986560023440232006317)
    ·
      refine ⟨155054619960008790087002369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413478986560023440232006317 155054619960008790087002369)
      ·
        refine ⟨116290964970006592565251777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155054619960008790087002369 116290964970006592565251777)
        ·
          refine ⟨87218223727504944423938833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116290964970006592565251777 87218223727504944423938833)
          ·
            refine ⟨65413667795628708317954125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87218223727504944423938833 65413667795628708317954125)
            ·
              refine ⟨24530125423360765619232797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65413667795628708317954125 24530125423360765619232797)
              ·
                refine ⟨9198797033760287107212299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24530125423360765619232797 9198797033760287107212299)
                ·
                  refine ⟨13798195550640430660818449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9198797033760287107212299 13798195550640430660818449)
                  ·
                    refine ⟨10348646662980322995613837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13798195550640430660818449 10348646662980322995613837)
                    ·
                      refine ⟨3880742498617621123355189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10348646662980322995613837 3880742498617621123355189)
                      ·
                        rfl

theorem cell23_7557719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_7557719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557719 prefixEnd_7557719 := by exact prefixLift 7557719
  have htrace : WordTrace (prefixWord ++ tailWord_7557719) baseStart_7557719 baseEnd_7557719 := by
    simpa [prefixWord, tailWord_7557719, baseEnd_7557719] using wordTrace_append hprefix tailTrace_7557719
  have hstable : (prefixWord ++ tailWord_7557719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557719).length < 2 ^ (prefixWord ++ tailWord_7557719).sum := by decide
  have hdescent : baseEnd_7557719 < baseStart_7557719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557733 : List Nat := [1, 3, 1, 3, 4, 1, 2, 1, 3, 2, 2]
def baseStart_7557733 : Nat := 118140960795 + 7557733 * 2 ^ 59
def prefixEnd_7557733 : Nat := 4983230072969 + 3 ^ 40 * 7557733 * 2
def baseEnd_7557733 : Nat := 3880749687346784068580125

theorem tailTrace_7557733 : CollatzResearch.WordTrace tailWord_7557733 prefixEnd_7557733 3880749687346784068580125 := by
  unfold tailWord_7557733
  simp only [CollatzResearch.WordTrace]
  refine ⟨275653168328631573879013853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183768778885754382586009235 275653168328631573879013853)
  ·
    refine ⟨103369938123236840204630195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275653168328631573879013853 103369938123236840204630195)
    ·
      refine ⟨155054907184855260306945293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103369938123236840204630195 155054907184855260306945293)
      ·
        refine ⟨58145590194320722615104485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155054907184855260306945293 58145590194320722615104485)
        ·
          refine ⟨10902298161435135490332091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58145590194320722615104485 10902298161435135490332091)
          ·
            refine ⟨16353447242152703235498137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10902298161435135490332091 16353447242152703235498137)
            ·
              refine ⟨12265085431614527426623603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16353447242152703235498137 12265085431614527426623603)
              ·
                refine ⟨18397628147421791139935405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12265085431614527426623603 18397628147421791139935405)
                ·
                  refine ⟨6899110555283171677475777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18397628147421791139935405 6899110555283171677475777)
                  ·
                    refine ⟨5174332916462378758106833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6899110555283171677475777 5174332916462378758106833)
                    ·
                      refine ⟨3880749687346784068580125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5174332916462378758106833 3880749687346784068580125)
                      ·
                        rfl

theorem cell23_7557733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_7557733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557733 prefixEnd_7557733 := by exact prefixLift 7557733
  have htrace : WordTrace (prefixWord ++ tailWord_7557733) baseStart_7557733 baseEnd_7557733 := by
    simpa [prefixWord, tailWord_7557733, baseEnd_7557733] using wordTrace_append hprefix tailTrace_7557733
  have hstable : (prefixWord ++ tailWord_7557733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557733).length < 2 ^ (prefixWord ++ tailWord_7557733).sum := by decide
  have hdescent : baseEnd_7557733 < baseStart_7557733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557746 : List Nat := [3, 2, 1, 2, 4, 2, 1, 1, 1, 2, 4]
def baseStart_7557746 : Nat := 118140960795 + 7557746 * 2 ^ 59
def prefixEnd_7557746 : Nat := 4983230072969 + 3 ^ 40 * 7557746 * 2
def baseEnd_7557746 : Nat := 3880756362595292517717565

theorem tailTrace_7557746 : CollatzResearch.WordTrace tailWord_7557746 prefixEnd_7557746 3880756362595292517717565 := by
  unfold tailWord_7557746
  simp only [CollatzResearch.WordTrace]
  refine ⟨68913410619396119274809273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183769094985056318066158061 68913410619396119274809273)
  ·
    refine ⟨51685057964547089456106955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68913410619396119274809273 51685057964547089456106955)
    ·
      refine ⟨77527586946820634184160433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51685057964547089456106955 77527586946820634184160433)
      ·
        refine ⟨58145690210115475638120325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77527586946820634184160433 58145690210115475638120325)
        ·
          refine ⟨10902316914396651682147561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58145690210115475638120325 10902316914396651682147561)
          ·
            refine ⟨8176737685797488761610671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10902316914396651682147561 8176737685797488761610671)
            ·
              refine ⟨12265106528696233142416007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8176737685797488761610671 12265106528696233142416007)
              ·
                refine ⟨18397659793044349713624011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12265106528696233142416007 18397659793044349713624011)
                ·
                  refine ⟨27596489689566524570436017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18397659793044349713624011 27596489689566524570436017)
                  ·
                    refine ⟨20697367267174893427827013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27596489689566524570436017 20697367267174893427827013)
                    ·
                      refine ⟨3880756362595292517717565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20697367267174893427827013 3880756362595292517717565)
                      ·
                        rfl

theorem cell23_7557746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_7557746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557746 prefixEnd_7557746 := by exact prefixLift 7557746
  have htrace : WordTrace (prefixWord ++ tailWord_7557746) baseStart_7557746 baseEnd_7557746 := by
    simpa [prefixWord, tailWord_7557746, baseEnd_7557746] using wordTrace_append hprefix tailTrace_7557746
  have hstable : (prefixWord ++ tailWord_7557746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557746).length < 2 ^ (prefixWord ++ tailWord_7557746).sum := by decide
  have hdescent : baseEnd_7557746 < baseStart_7557746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557755 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 8]
def baseStart_7557755 : Nat := 118140960795 + 7557755 * 2 ^ 59
def prefixEnd_7557755 : Nat := 4983230072969 + 3 ^ 40 * 7557755 * 2
def baseEnd_7557755 : Nat := 3880760983921182982505023

theorem tailTrace_7557755 : CollatzResearch.WordTrace tailWord_7557755 prefixEnd_7557755 3880760983921182982505023 := by
  unfold tailWord_7557755
  simp only [CollatzResearch.WordTrace]
  refine ⟨275653970734551871636314719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183769313823034581090876479 275653970734551871636314719)
  ·
    refine ⟨413480956101827807454472079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275653970734551871636314719 413480956101827807454472079)
    ·
      refine ⟨620221434152741711181708119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413480956101827807454472079 620221434152741711181708119)
      ·
        refine ⟨930332151229112566772562179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620221434152741711181708119 930332151229112566772562179)
        ·
          refine ⟨1395498226843668850158843269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 930332151229112566772562179 1395498226843668850158843269)
          ·
            refine ⟨261655917533187909404783113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1395498226843668850158843269 261655917533187909404783113)
            ·
              refine ⟨196241938149890932053587335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261655917533187909404783113 196241938149890932053587335)
              ·
                refine ⟨294362907224836398080381003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196241938149890932053587335 294362907224836398080381003)
                ·
                  refine ⟨441544360837254597120571505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294362907224836398080381003 441544360837254597120571505)
                  ·
                    refine ⟨331158270627940947840428629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 441544360837254597120571505 331158270627940947840428629)
                    ·
                      refine ⟨3880760983921182982505023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 331158270627940947840428629 3880760983921182982505023)
                      ·
                        rfl

theorem cell23_7557755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 8].length) (baseStart_7557755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557755 prefixEnd_7557755 := by exact prefixLift 7557755
  have htrace : WordTrace (prefixWord ++ tailWord_7557755) baseStart_7557755 baseEnd_7557755 := by
    simpa [prefixWord, tailWord_7557755, baseEnd_7557755] using wordTrace_append hprefix tailTrace_7557755
  have hstable : (prefixWord ++ tailWord_7557755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557755).length < 2 ^ (prefixWord ++ tailWord_7557755).sum := by decide
  have hdescent : baseEnd_7557755 < baseStart_7557755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557849 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 1, 7, 2]
def baseStart_7557849 : Nat := 118140960795 + 7557849 * 2 ^ 59
def prefixEnd_7557849 : Nat := 4983230072969 + 3 ^ 40 * 7557849 * 2
def baseEnd_7557849 : Nat := 3880809251102705614729591

theorem tailTrace_7557849 : CollatzResearch.WordTrace tailWord_7557849 prefixEnd_7557849 3880809251102705614729591 := by
  unfold tailWord_7557849
  simp only [CollatzResearch.WordTrace]
  refine ⟨275657399196211325690236601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183771599464140883793491067 275657399196211325690236601)
  ·
    refine ⟨206743049397158494267677451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275657399196211325690236601 206743049397158494267677451)
    ·
      refine ⟨310114574095737741401516177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206743049397158494267677451 310114574095737741401516177)
      ·
        refine ⟨232585930571803306051137133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310114574095737741401516177 232585930571803306051137133)
        ·
          refine ⟨87219723964426239769176425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232585930571803306051137133 87219723964426239769176425)
          ·
            refine ⟨65414792973319679826882319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87219723964426239769176425 65414792973319679826882319)
            ·
              refine ⟨98122189459979519740323479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65414792973319679826882319 98122189459979519740323479)
              ·
                refine ⟨147183284189969279610485219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98122189459979519740323479 147183284189969279610485219)
                ·
                  refine ⟨220774926284953919415727829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147183284189969279610485219 220774926284953919415727829)
                  ·
                    refine ⟨5174412334803607486306121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 220774926284953919415727829 5174412334803607486306121)
                    ·
                      refine ⟨3880809251102705614729591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5174412334803607486306121 3880809251102705614729591)
                      ·
                        rfl

theorem cell23_7557849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 7, 2].length) (baseStart_7557849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557849 prefixEnd_7557849 := by exact prefixLift 7557849
  have htrace : WordTrace (prefixWord ++ tailWord_7557849) baseStart_7557849 baseEnd_7557849 := by
    simpa [prefixWord, tailWord_7557849, baseEnd_7557849] using wordTrace_append hprefix tailTrace_7557849
  have hstable : (prefixWord ++ tailWord_7557849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557849).length < 2 ^ (prefixWord ++ tailWord_7557849).sum := by decide
  have hdescent : baseEnd_7557849 < baseStart_7557849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557879 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 3, 6, 2]
def baseStart_7557879 : Nat := 118140960795 + 7557879 * 2 ^ 59
def prefixEnd_7557879 : Nat := 4983230072969 + 3 ^ 40 * 7557879 * 2
def baseEnd_7557879 : Nat := 3880824655522340497354453

theorem tailTrace_7557879 : CollatzResearch.WordTrace tailWord_7557879 prefixEnd_7557879 3880824655522340497354453 := by
  unfold tailWord_7557879
  simp only [CollatzResearch.WordTrace]
  refine ⟨275658493386102640813828691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183772328924068427209219127 275658493386102640813828691)
  ·
    refine ⟨413487740079153961220743037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275658493386102640813828691 413487740079153961220743037)
    ·
      refine ⟨155057902529682735457778639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413487740079153961220743037 155057902529682735457778639)
      ·
        refine ⟨232586853794524103186667959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155057902529682735457778639 232586853794524103186667959)
        ·
          refine ⟨348880280691786154780001939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232586853794524103186667959 348880280691786154780001939)
          ·
            refine ⟨523320421037679232170002909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348880280691786154780001939 523320421037679232170002909)
            ·
              refine ⟨196245157889129712063751091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 523320421037679232170002909 196245157889129712063751091)
              ·
                refine ⟨294367736833694568095626637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196245157889129712063751091 294367736833694568095626637)
                ·
                  refine ⟨110387901312635463035859989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294367736833694568095626637 110387901312635463035859989)
                  ·
                    refine ⟨5174432874029787329805937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110387901312635463035859989 5174432874029787329805937)
                    ·
                      refine ⟨3880824655522340497354453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5174432874029787329805937 3880824655522340497354453)
                      ·
                        rfl

theorem cell23_7557879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 6, 2].length) (baseStart_7557879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557879 prefixEnd_7557879 := by exact prefixLift 7557879
  have htrace : WordTrace (prefixWord ++ tailWord_7557879) baseStart_7557879 baseEnd_7557879 := by
    simpa [prefixWord, tailWord_7557879, baseEnd_7557879] using wordTrace_append hprefix tailTrace_7557879
  have hstable : (prefixWord ++ tailWord_7557879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557879).length < 2 ^ (prefixWord ++ tailWord_7557879).sum := by decide
  have hdescent : baseEnd_7557879 < baseStart_7557879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557889 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 7, 4]
def baseStart_7557889 : Nat := 118140960795 + 7557889 * 2 ^ 59
def prefixEnd_7557889 : Nat := 4983230072969 + 3 ^ 40 * 7557889 * 2
def baseEnd_7557889 : Nat := 1293609930109628486076469

theorem tailTrace_7557889 : CollatzResearch.WordTrace tailWord_7557889 prefixEnd_7557889 1293609930109628486076469 := by
  unfold tailWord_7557889
  simp only [CollatzResearch.WordTrace]
  refine ⟨275658858116066412521692721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183772572077377608347795147 275658858116066412521692721)
  ·
    refine ⟨206744143587049809391269541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275658858116066412521692721 206744143587049809391269541)
    ·
      refine ⟨38764526922571839260863039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206744143587049809391269541 38764526922571839260863039)
      ·
        refine ⟨58146790383857758891294559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38764526922571839260863039 58146790383857758891294559)
        ·
          refine ⟨87220185575786638336941839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58146790383857758891294559 87220185575786638336941839)
          ·
            refine ⟨130830278363679957505412759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87220185575786638336941839 130830278363679957505412759)
            ·
              refine ⟨196245417545519936258119139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130830278363679957505412759 196245417545519936258119139)
              ·
                refine ⟨294368126318279904387178709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196245417545519936258119139 294368126318279904387178709)
                ·
                  refine ⟨6899252960584685259074501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 294368126318279904387178709 6899252960584685259074501)
                  ·
                    refine ⟨1293609930109628486076469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6899252960584685259074501 1293609930109628486076469)
                    ·
                      rfl

theorem cell23_7557889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_7557889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557889 prefixEnd_7557889 := by exact prefixLift 7557889
  have htrace : WordTrace (prefixWord ++ tailWord_7557889) baseStart_7557889 baseEnd_7557889 := by
    simpa [prefixWord, tailWord_7557889, baseEnd_7557889] using wordTrace_append hprefix tailTrace_7557889
  have hstable : (prefixWord ++ tailWord_7557889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557889).length < 2 ^ (prefixWord ++ tailWord_7557889).sum := by decide
  have hdescent : baseEnd_7557889 < baseStart_7557889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557896 : List Nat := [2, 1, 3, 2, 2, 2, 1, 2, 2, 4, 2]
def baseStart_7557896 : Nat := 118140960795 + 7557896 * 2 ^ 59
def prefixEnd_7557896 : Nat := 4983230072969 + 3 ^ 40 * 7557896 * 2
def baseEnd_7557896 : Nat := 3880833384693466930841875

theorem tailTrace_7557896 : CollatzResearch.WordTrace tailWord_7557896 prefixEnd_7557896 3880833384693466930841875 := by
  unfold tailWord_7557896
  simp only [CollatzResearch.WordTrace]
  refine ⟨137829556713520526358598771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183772742284694035144798361 137829556713520526358598771)
  ·
    refine ⟨206744335070280789537898157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137829556713520526358598771 206744335070280789537898157)
    ·
      refine ⟨77529125651355296076711809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206744335070280789537898157 77529125651355296076711809)
      ·
        refine ⟨58146844238516472057533857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77529125651355296076711809 58146844238516472057533857)
        ·
          refine ⟨43610133178887354043150393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58146844238516472057533857 43610133178887354043150393)
          ·
            refine ⟨32707599884165515532362795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43610133178887354043150393 32707599884165515532362795)
            ·
              refine ⟨49061399826248273298544193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32707599884165515532362795 49061399826248273298544193)
              ·
                refine ⟨36796049869686204973908145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49061399826248273298544193 36796049869686204973908145)
                ·
                  refine ⟨27597037402264653730431109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36796049869686204973908145 27597037402264653730431109)
                  ·
                    refine ⟨5174444512924622574455833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27597037402264653730431109 5174444512924622574455833)
                    ·
                      refine ⟨3880833384693466930841875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5174444512924622574455833 3880833384693466930841875)
                      ·
                        rfl

theorem cell23_7557896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_7557896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557896 prefixEnd_7557896 := by exact prefixLift 7557896
  have htrace : WordTrace (prefixWord ++ tailWord_7557896) baseStart_7557896 baseEnd_7557896 := by
    simpa [prefixWord, tailWord_7557896, baseEnd_7557896] using wordTrace_append hprefix tailTrace_7557896
  have hstable : (prefixWord ++ tailWord_7557896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557896).length < 2 ^ (prefixWord ++ tailWord_7557896).sum := by decide
  have hdescent : baseEnd_7557896 < baseStart_7557896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557899 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 4, 2, 3]
def baseStart_7557899 : Nat := 118140960795 + 7557899 * 2 ^ 59
def prefixEnd_7557899 : Nat := 4983230072969 + 3 ^ 40 * 7557899 * 2
def baseEnd_7557899 : Nat := 3880834925135430419104361

theorem tailTrace_7557899 : CollatzResearch.WordTrace tailWord_7557899 prefixEnd_7557899 3880834925135430419104361 := by
  unfold tailWord_7557899
  simp only [CollatzResearch.WordTrace]
  refine ⟨275659222846030184229556751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183772815230686789486371167 275659222846030184229556751)
  ·
    refine ⟨413488834269045276344335127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275659222846030184229556751 413488834269045276344335127)
    ·
      refine ⟨620233251403567914516502691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413488834269045276344335127 620233251403567914516502691)
      ·
        refine ⟨930349877105351871774754037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620233251403567914516502691 930349877105351871774754037)
        ·
          refine ⟨87220300978626737978883191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 930349877105351871774754037 87220300978626737978883191)
          ·
            refine ⟨130830451467940106968324787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87220300978626737978883191 130830451467940106968324787)
            ·
              refine ⟨196245677201910160452487181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130830451467940106968324787 196245677201910160452487181)
              ·
                refine ⟨73592128950716310169682693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196245677201910160452487181 73592128950716310169682693)
                ·
                  refine ⟨13798524178259308156815505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73592128950716310169682693 13798524178259308156815505)
                  ·
                    refine ⟨10348893133694481117611629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13798524178259308156815505 10348893133694481117611629)
                    ·
                      refine ⟨3880834925135430419104361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10348893133694481117611629 3880834925135430419104361)
                      ·
                        rfl

theorem cell23_7557899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2, 3].length) (baseStart_7557899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557899 prefixEnd_7557899 := by exact prefixLift 7557899
  have htrace : WordTrace (prefixWord ++ tailWord_7557899) baseStart_7557899 baseEnd_7557899 := by
    simpa [prefixWord, tailWord_7557899, baseEnd_7557899] using wordTrace_append hprefix tailTrace_7557899
  have hstable : (prefixWord ++ tailWord_7557899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557899).length < 2 ^ (prefixWord ++ tailWord_7557899).sum := by decide
  have hdescent : baseEnd_7557899 < baseStart_7557899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7557989 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 3, 1, 5]
def baseStart_7557989 : Nat := 118140960795 + 7557989 * 2 ^ 59
def prefixEnd_7557989 : Nat := 4983230072969 + 3 ^ 40 * 7557989 * 2
def baseEnd_7557989 : Nat := 3880881138394335066978947

theorem tailTrace_7557989 : CollatzResearch.WordTrace tailWord_7557989 prefixEnd_7557989 3880881138394335066978947 := by
  unfold tailWord_7557989
  simp only [CollatzResearch.WordTrace]
  refine ⟨275662505415704129600333021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183775003610469419733555347 275662505415704129600333021)
  ·
    refine ⟨103373439530889048600124883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275662505415704129600333021 103373439530889048600124883)
    ·
      refine ⟨155060159296333572900187325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103373439530889048600124883 155060159296333572900187325)
      ·
        refine ⟨58147559736125089837570247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155060159296333572900187325 58147559736125089837570247)
        ·
          refine ⟨87221339604187634756355371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58147559736125089837570247 87221339604187634756355371)
          ·
            refine ⟨130832009406281452134533057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87221339604187634756355371 130832009406281452134533057)
            ·
              refine ⟨98124007054711089100899793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130832009406281452134533057 98124007054711089100899793)
              ·
                refine ⟨73593005291033316825674845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98124007054711089100899793 73593005291033316825674845)
                ·
                  refine ⟨27597376984137493809628067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73593005291033316825674845 27597376984137493809628067)
                  ·
                    refine ⟨41396065476206240714442101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27597376984137493809628067 41396065476206240714442101)
                    ·
                      refine ⟨3880881138394335066978947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41396065476206240714442101 3880881138394335066978947)
                      ·
                        rfl

theorem cell23_7557989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_7557989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7557989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7557989 prefixEnd_7557989 := by exact prefixLift 7557989
  have htrace : WordTrace (prefixWord ++ tailWord_7557989) baseStart_7557989 baseEnd_7557989 := by
    simpa [prefixWord, tailWord_7557989, baseEnd_7557989] using wordTrace_append hprefix tailTrace_7557989
  have hstable : (prefixWord ++ tailWord_7557989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7557989).length < 2 ^ (prefixWord ++ tailWord_7557989).sum := by decide
  have hdescent : baseEnd_7557989 < baseStart_7557989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7557989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558014 : List Nat := [4, 2, 3, 1, 2, 1, 1, 4, 1, 1, 3]
def baseStart_7558014 : Nat := 118140960795 + 7558014 * 2 ^ 59
def prefixEnd_7558014 : Nat := 4983230072969 + 3 ^ 40 * 7558014 * 2
def baseEnd_7558014 : Nat := 3880893975410697469166333

theorem tailTrace_7558014 : CollatzResearch.WordTrace tailWord_7558014 prefixEnd_7558014 3880893975410697469166333 := by
  unfold tailWord_7558014
  simp only [CollatzResearch.WordTrace]
  refine ⟨34457927155076694858749137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183775611493742372579995397 34457927155076694858749137)
  ·
    refine ⟨25843445366307521144061853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34457927155076694858749137 25843445366307521144061853)
    ·
      refine ⟨9691292012365320429023195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25843445366307521144061853 9691292012365320429023195)
      ·
        refine ⟨14536938018547980643534793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9691292012365320429023195 14536938018547980643534793)
        ·
          refine ⟨10902703513910985482651095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14536938018547980643534793 10902703513910985482651095)
          ·
            refine ⟨16354055270866478223976643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10902703513910985482651095 16354055270866478223976643)
            ·
              refine ⟨24531082906299717335964965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16354055270866478223976643 24531082906299717335964965)
              ·
                refine ⟨4599578044931197000493431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24531082906299717335964965 4599578044931197000493431)
                ·
                  refine ⟨6899367067396795500740147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4599578044931197000493431 6899367067396795500740147)
                  ·
                    refine ⟨10349050601095193251110221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6899367067396795500740147 10349050601095193251110221)
                    ·
                      refine ⟨3880893975410697469166333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10349050601095193251110221 3880893975410697469166333)
                      ·
                        rfl

theorem cell23_7558014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_7558014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558014 prefixEnd_7558014 := by exact prefixLift 7558014
  have htrace : WordTrace (prefixWord ++ tailWord_7558014) baseStart_7558014 baseEnd_7558014 := by
    simpa [prefixWord, tailWord_7558014, baseEnd_7558014] using wordTrace_append hprefix tailTrace_7558014
  have hstable : (prefixWord ++ tailWord_7558014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558014).length < 2 ^ (prefixWord ++ tailWord_7558014).sum := by decide
  have hdescent : baseEnd_7558014 < baseStart_7558014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558026 : List Nat := [3, 1, 2, 4, 1, 1, 3, 8]
def baseStart_7558026 : Nat := 118140960795 + 7558026 * 2 ^ 59
def prefixEnd_7558026 : Nat := 4983230072969 + 3 ^ 40 * 7558026 * 2
def baseEnd_7558026 : Nat := 143737042117724126748751

theorem tailTrace_7558026 : CollatzResearch.WordTrace tailWord_7558026 prefixEnd_7558026 143737042117724126748751 := by
  unfold tailWord_7558026
  simp only [CollatzResearch.WordTrace]
  refine ⟨68915963729142521229857483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183775903277713389946286621 68915963729142521229857483)
  ·
    refine ⟨103373945593713781844786225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68915963729142521229857483 103373945593713781844786225)
    ·
      refine ⟨77530459195285336383589669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103373945593713781844786225 77530459195285336383589669)
      ·
        refine ⟨14536961099116000571923063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77530459195285336383589669 14536961099116000571923063)
        ·
          refine ⟨21805441648674000857884595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14536961099116000571923063 21805441648674000857884595)
          ·
            refine ⟨32708162473011001286826893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21805441648674000857884595 32708162473011001286826893)
            ·
              refine ⟨12265560927379125482560085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32708162473011001286826893 12265560927379125482560085)
              ·
                refine ⟨143737042117724126748751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12265560927379125482560085 143737042117724126748751)
                ·
                  rfl

theorem cell23_7558026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 8].length) (baseStart_7558026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558026 prefixEnd_7558026 := by exact prefixLift 7558026
  have htrace : WordTrace (prefixWord ++ tailWord_7558026) baseStart_7558026 baseEnd_7558026 := by
    simpa [prefixWord, tailWord_7558026, baseEnd_7558026] using wordTrace_append hprefix tailTrace_7558026
  have hstable : (prefixWord ++ tailWord_7558026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558026).length < 2 ^ (prefixWord ++ tailWord_7558026).sum := by decide
  have hdescent : baseEnd_7558026 < baseStart_7558026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558039 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 2, 7]
def baseStart_7558039 : Nat := 118140960795 + 7558039 * 2 ^ 59
def prefixEnd_7558039 : Nat := 4983230072969 + 3 ^ 40 * 7558039 * 2
def baseEnd_7558039 : Nat := 1293635604142353290451239

theorem tailTrace_7558039 : CollatzResearch.WordTrace tailWord_7558039 prefixEnd_7558039 1293635604142353290451239 := by
  unfold tailWord_7558039
  simp only [CollatzResearch.WordTrace]
  refine ⟨275664329065522988139653171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183776219377015325426435447 275664329065522988139653171)
  ·
    refine ⟨413496493598284482209479757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275664329065522988139653171 413496493598284482209479757)
    ·
      refine ⟨155061185099356680828554909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413496493598284482209479757 155061185099356680828554909)
      ·
        refine ⟨58147944412258755310708091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155061185099356680828554909 58147944412258755310708091)
        ·
          refine ⟨87221916618388132966062137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58147944412258755310708091 87221916618388132966062137)
          ·
            refine ⟨65416437463791099724546603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87221916618388132966062137 65416437463791099724546603)
            ·
              refine ⟨98124656195686649586819905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65416437463791099724546603 98124656195686649586819905)
              ·
                refine ⟨73593492146764987190114929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98124656195686649586819905 73593492146764987190114929)
                ·
                  refine ⟨55195119110073740392586197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73593492146764987190114929 55195119110073740392586197)
                  ·
                    refine ⟨1293635604142353290451239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55195119110073740392586197 1293635604142353290451239)
                    ·
                      rfl

theorem cell23_7558039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 7].length) (baseStart_7558039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558039 prefixEnd_7558039 := by exact prefixLift 7558039
  have htrace : WordTrace (prefixWord ++ tailWord_7558039) baseStart_7558039 baseEnd_7558039 := by
    simpa [prefixWord, tailWord_7558039, baseEnd_7558039] using wordTrace_append hprefix tailTrace_7558039
  have hstable : (prefixWord ++ tailWord_7558039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558039).length < 2 ^ (prefixWord ++ tailWord_7558039).sum := by decide
  have hdescent : baseEnd_7558039 < baseStart_7558039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558059 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 4]
def baseStart_7558059 : Nat := 118140960795 + 7558059 * 2 ^ 59
def prefixEnd_7558059 : Nat := 4983230072969 + 3 ^ 40 * 7558059 * 2
def baseEnd_7558059 : Nat := 3880917082040149793103625

theorem tailTrace_7558059 : CollatzResearch.WordTrace tailWord_7558059 prefixEnd_7558059 3880917082040149793103625 := by
  unfold tailWord_7558059
  simp only [CollatzResearch.WordTrace]
  refine ⟨275665058525450531555381231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183776705683633687703587487 275665058525450531555381231)
  ·
    refine ⟨413497587788175797333071847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275665058525450531555381231 413497587788175797333071847)
    ·
      refine ⟨620246381682263695999607771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413497587788175797333071847 620246381682263695999607771)
      ·
        refine ⟨930369572523395543999411657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620246381682263695999607771 930369572523395543999411657)
        ·
          refine ⟨697777179392546657999558743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 930369572523395543999411657 697777179392546657999558743)
          ·
            refine ⟨1046665769088819986999338115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697777179392546657999558743 1046665769088819986999338115)
            ·
              refine ⟨1569998653633229980499007173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1046665769088819986999338115 1569998653633229980499007173)
              ·
                refine ⟨294374747556230621343563845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1569998653633229980499007173 294374747556230621343563845)
                ·
                  refine ⟨55195265166793241501918221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 294374747556230621343563845 55195265166793241501918221)
                  ·
                    refine ⟨20698224437547465563219333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55195265166793241501918221 20698224437547465563219333)
                    ·
                      refine ⟨3880917082040149793103625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20698224437547465563219333 3880917082040149793103625)
                      ·
                        rfl

theorem cell23_7558059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 4].length) (baseStart_7558059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558059 prefixEnd_7558059 := by exact prefixLift 7558059
  have htrace : WordTrace (prefixWord ++ tailWord_7558059) baseStart_7558059 baseEnd_7558059 := by
    simpa [prefixWord, tailWord_7558059, baseEnd_7558059] using wordTrace_append hprefix tailTrace_7558059
  have hstable : (prefixWord ++ tailWord_7558059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558059).length < 2 ^ (prefixWord ++ tailWord_7558059).sum := by decide
  have hdescent : baseEnd_7558059 < baseStart_7558059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558079 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 5]
def baseStart_7558079 : Nat := 118140960795 + 7558079 * 2 ^ 59
def prefixEnd_7558079 : Nat := 4983230072969 + 3 ^ 40 * 7558079 * 2
def baseEnd_7558079 : Nat := 3880927351653239714853533

theorem tailTrace_7558079 : CollatzResearch.WordTrace tailWord_7558079 prefixEnd_7558079 3880927351653239714853533 := by
  unfold tailWord_7558079
  simp only [CollatzResearch.WordTrace]
  refine ⟨275665787985378074971109291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183777191990252049980739527 275665787985378074971109291)
  ·
    refine ⟨413498681978067112456663937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275665787985378074971109291 413498681978067112456663937)
    ·
      refine ⟨310124011483550334342497953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413498681978067112456663937 310124011483550334342497953)
      ·
        refine ⟨232593008612662750756873465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310124011483550334342497953 232593008612662750756873465)
        ·
          refine ⟨174444756459497063067655099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232593008612662750756873465 174444756459497063067655099)
          ·
            refine ⟨261667134689245594601482649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174444756459497063067655099 261667134689245594601482649)
            ·
              refine ⟨196250351016934195951111987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261667134689245594601482649 196250351016934195951111987)
              ·
                refine ⟨294375526525401293926667981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196250351016934195951111987 294375526525401293926667981)
                ·
                  refine ⟨110390822447025485222500493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294375526525401293926667981 110390822447025485222500493)
                  ·
                    refine ⟨41396558417634556958437685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110390822447025485222500493 41396558417634556958437685)
                    ·
                      refine ⟨3880927351653239714853533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41396558417634556958437685 3880927351653239714853533)
                      ·
                        rfl

theorem cell23_7558079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_7558079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558079 prefixEnd_7558079 := by exact prefixLift 7558079
  have htrace : WordTrace (prefixWord ++ tailWord_7558079) baseStart_7558079 baseEnd_7558079 := by
    simpa [prefixWord, tailWord_7558079, baseEnd_7558079] using wordTrace_append hprefix tailTrace_7558079
  have hstable : (prefixWord ++ tailWord_7558079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558079).length < 2 ^ (prefixWord ++ tailWord_7558079).sum := by decide
  have hdescent : baseEnd_7558079 < baseStart_7558079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558193 : List Nat := [1, 2, 2, 3, 1, 2, 2, 3, 3, 4]
def baseStart_7558193 : Nat := 118140960795 + 7558193 * 2 ^ 59
def prefixEnd_7558193 : Nat := 4983230072969 + 3 ^ 40 * 7558193 * 2
def baseEnd_7558193 : Nat := 1293661962815950756276003

theorem tailTrace_7558193 : CollatzResearch.WordTrace tailWord_7558193 prefixEnd_7558193 1293661962815950756276003 := by
  unfold tailWord_7558193
  simp only [CollatzResearch.WordTrace]
  refine ⟨275669945906965072440759233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183779963937976714960506155 275669945906965072440759233)
  ·
    refine ⟨206752459430223804330569425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275669945906965072440759233 206752459430223804330569425)
    ·
      refine ⟨155064344572667853247927069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206752459430223804330569425 155064344572667853247927069)
      ·
        refine ⟨58149129214750444967972651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155064344572667853247927069 58149129214750444967972651)
        ·
          refine ⟨87223693822125667451958977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58149129214750444967972651 87223693822125667451958977)
          ·
            refine ⟨65417770366594250588969233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87223693822125667451958977 65417770366594250588969233)
            ·
              refine ⟨49063327774945687941726925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65417770366594250588969233 49063327774945687941726925)
              ·
                refine ⟨18398747915604632978147597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49063327774945687941726925 18398747915604632978147597)
                ·
                  refine ⟨6899530468351737366805349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18398747915604632978147597 6899530468351737366805349)
                  ·
                    refine ⟨1293661962815950756276003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6899530468351737366805349 1293661962815950756276003)
                    ·
                      rfl

theorem cell23_7558193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3, 4].length) (baseStart_7558193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558193 prefixEnd_7558193 := by exact prefixLift 7558193
  have htrace : WordTrace (prefixWord ++ tailWord_7558193) baseStart_7558193 baseEnd_7558193 := by
    simpa [prefixWord, tailWord_7558193, baseEnd_7558193] using wordTrace_append hprefix tailTrace_7558193
  have hstable : (prefixWord ++ tailWord_7558193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558193).length < 2 ^ (prefixWord ++ tailWord_7558193).sum := by decide
  have hdescent : baseEnd_7558193 < baseStart_7558193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558200 : List Nat := [2, 1, 2, 1, 5, 2, 1, 1, 2, 4, 2]
def baseStart_7558200 : Nat := 118140960795 + 7558200 * 2 ^ 59
def prefixEnd_7558200 : Nat := 4983230072969 + 3 ^ 40 * 7558200 * 2
def baseEnd_7558200 : Nat := 3880989482812433741440477

theorem tailTrace_7558200 : CollatzResearch.WordTrace tailWord_7558200 prefixEnd_7558200 3880989482812433741440477 := by
  unfold tailWord_7558200
  simp only [CollatzResearch.WordTrace]
  refine ⟨137835100608969856318132027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183780134145293141757509369 137835100608969856318132027)
  ·
    refine ⟨206752650913454784477198041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137835100608969856318132027 206752650913454784477198041)
    ·
      refine ⟨155064488185091088357898531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206752650913454784477198041 155064488185091088357898531)
      ·
        refine ⟨232596732277636632536847797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155064488185091088357898531 232596732277636632536847797)
        ·
          refine ⟨21805943651028434300329481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 232596732277636632536847797 21805943651028434300329481)
          ·
            refine ⟨16354457738271325725247111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21805943651028434300329481 16354457738271325725247111)
            ·
              refine ⟨24531686607406988587870667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16354457738271325725247111 24531686607406988587870667)
              ·
                refine ⟨36797529911110482881806001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24531686607406988587870667 36797529911110482881806001)
                ·
                  refine ⟨27598147433332862161354501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36797529911110482881806001 27598147433332862161354501)
                  ·
                    refine ⟨5174652643749911655253969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27598147433332862161354501 5174652643749911655253969)
                    ·
                      refine ⟨3880989482812433741440477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5174652643749911655253969 3880989482812433741440477)
                      ·
                        rfl

theorem cell23_7558200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 2, 4, 2].length) (baseStart_7558200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558200 prefixEnd_7558200 := by exact prefixLift 7558200
  have htrace : WordTrace (prefixWord ++ tailWord_7558200) baseStart_7558200 baseEnd_7558200 := by
    simpa [prefixWord, tailWord_7558200, baseEnd_7558200] using wordTrace_append hprefix tailTrace_7558200
  have hstable : (prefixWord ++ tailWord_7558200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558200).length < 2 ^ (prefixWord ++ tailWord_7558200).sum := by decide
  have hdescent : baseEnd_7558200 < baseStart_7558200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558300 : List Nat := [2, 2, 3, 2, 1, 2, 2, 1, 4, 4]
def baseStart_7558300 : Nat := 118140960795 + 7558300 * 2 ^ 59
def prefixEnd_7558300 : Nat := 4983230072969 + 3 ^ 40 * 7558300 * 2
def baseEnd_7558300 : Nat := 1293680276959294450063339

theorem tailTrace_7558300 : CollatzResearch.WordTrace tailWord_7558300 prefixEnd_7558300 1293680276959294450063339 := by
  unfold tailWord_7558300
  simp only [CollatzResearch.WordTrace]
  refine ⟨137836924258788714857452177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183782565678384953143269569 137836924258788714857452177)
  ·
    refine ⟨103377693194091536143089133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137836924258788714857452177 103377693194091536143089133)
    ·
      refine ⟨38766634947784326053658425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103377693194091536143089133 38766634947784326053658425)
      ·
        refine ⟨29074976210838244540243819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38766634947784326053658425 29074976210838244540243819)
        ·
          refine ⟨43612464316257366810365729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29074976210838244540243819 43612464316257366810365729)
          ·
            refine ⟨32709348237193025107774297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43612464316257366810365729 32709348237193025107774297)
            ·
              refine ⟨24532011177894768830830723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32709348237193025107774297 24532011177894768830830723)
              ·
                refine ⟨36798016766842153246246085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24532011177894768830830723 36798016766842153246246085)
                ·
                  refine ⟨6899628143782903733671141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36798016766842153246246085 6899628143782903733671141)
                  ·
                    refine ⟨1293680276959294450063339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6899628143782903733671141 1293680276959294450063339)
                    ·
                      rfl

theorem cell23_7558300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_7558300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558300 prefixEnd_7558300 := by exact prefixLift 7558300
  have htrace : WordTrace (prefixWord ++ tailWord_7558300) baseStart_7558300 baseEnd_7558300 := by
    simpa [prefixWord, tailWord_7558300, baseEnd_7558300] using wordTrace_append hprefix tailTrace_7558300
  have hstable : (prefixWord ++ tailWord_7558300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558300).length < 2 ^ (prefixWord ++ tailWord_7558300).sum := by decide
  have hdescent : baseEnd_7558300 < baseStart_7558300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558337 : List Nat := [1, 2, 6, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_7558337 : Nat := 118140960795 + 7558337 * 2 ^ 59
def prefixEnd_7558337 : Nat := 4983230072969 + 3 ^ 40 * 7558337 * 2
def baseEnd_7558337 : Nat := 3881059829662099705427347

theorem tailTrace_7558337 : CollatzResearch.WordTrace tailWord_7558337 prefixEnd_7558337 3881059829662099705427347 := by
  unfold tailWord_7558337
  simp only [CollatzResearch.WordTrace]
  refine ⟨275675198018443385034001265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183783465345628923356000843 275675198018443385034001265)
  ·
    refine ⟨206756398513832538775500949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275675198018443385034001265 206756398513832538775500949)
    ·
      refine ⟨9691706180335900255101607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 206756398513832538775500949 9691706180335900255101607)
      ·
        refine ⟨14537559270503850382652411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9691706180335900255101607 14537559270503850382652411)
        ·
          refine ⟨21806338905755775573978617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14537559270503850382652411 21806338905755775573978617)
          ·
            refine ⟨16354754179316831680483963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21806338905755775573978617 16354754179316831680483963)
            ·
              refine ⟨24532131268975247520725945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16354754179316831680483963 24532131268975247520725945)
              ·
                refine ⟨18399098451731435640544459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24532131268975247520725945 18399098451731435640544459)
                ·
                  refine ⟨27598647677597153460816689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18399098451731435640544459 27598647677597153460816689)
                  ·
                    refine ⟨20698985758197865095612517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27598647677597153460816689 20698985758197865095612517)
                    ·
                      refine ⟨3881059829662099705427347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20698985758197865095612517 3881059829662099705427347)
                      ·
                        rfl

theorem cell23_7558337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_7558337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558337 prefixEnd_7558337 := by exact prefixLift 7558337
  have htrace : WordTrace (prefixWord ++ tailWord_7558337) baseStart_7558337 baseEnd_7558337 := by
    simpa [prefixWord, tailWord_7558337, baseEnd_7558337] using wordTrace_append hprefix tailTrace_7558337
  have hstable : (prefixWord ++ tailWord_7558337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558337).length < 2 ^ (prefixWord ++ tailWord_7558337).sum := by decide
  have hdescent : baseEnd_7558337 < baseStart_7558337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558393 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 1, 4, 4]
def baseStart_7558393 : Nat := 118140960795 + 7558393 * 2 ^ 59
def prefixEnd_7558393 : Nat := 4983230072969 + 3 ^ 40 * 7558393 * 2
def baseEnd_7558393 : Nat := 3881088584578751486327089

theorem tailTrace_7558393 : CollatzResearch.WordTrace tailWord_7558393 prefixEnd_7558393 3881088584578751486327089 := by
  unfold tailWord_7558393
  simp only [CollatzResearch.WordTrace]
  refine ⟨275677240506240506598039833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183784827004160337732026555 275677240506240506598039833)
  ·
    refine ⟨206757930379680379948529875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275677240506240506598039833 206757930379680379948529875)
    ·
      refine ⟨310136895569520569922794813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206757930379680379948529875 310136895569520569922794813)
      ·
        refine ⟨116301335838570213721048055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310136895569520569922794813 116301335838570213721048055)
        ·
          refine ⟨174452003757855320581572083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116301335838570213721048055 174452003757855320581572083)
          ·
            refine ⟨261678005636782980872358125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174452003757855320581572083 261678005636782980872358125)
            ·
              refine ⟨98129252113793617827134297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261678005636782980872358125 98129252113793617827134297)
              ·
                refine ⟨73596939085345213370350723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98129252113793617827134297 73596939085345213370350723)
                ·
                  refine ⟨110395408628017820055526085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73596939085345213370350723 110395408628017820055526085)
                  ·
                    refine ⟨20699139117753341260411141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110395408628017820055526085 20699139117753341260411141)
                    ·
                      refine ⟨3881088584578751486327089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20699139117753341260411141 3881088584578751486327089)
                      ·
                        rfl

theorem cell23_7558393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_7558393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558393 prefixEnd_7558393 := by exact prefixLift 7558393
  have htrace : WordTrace (prefixWord ++ tailWord_7558393) baseStart_7558393 baseEnd_7558393 := by
    simpa [prefixWord, tailWord_7558393, baseEnd_7558393] using wordTrace_append hprefix tailTrace_7558393
  have hstable : (prefixWord ++ tailWord_7558393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558393).length < 2 ^ (prefixWord ++ tailWord_7558393).sum := by decide
  have hdescent : baseEnd_7558393 < baseStart_7558393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558401 : List Nat := [1, 2, 4, 1, 1, 5, 2, 1, 1, 3, 2]
def baseStart_7558401 : Nat := 118140960795 + 7558401 * 2 ^ 59
def prefixEnd_7558401 : Nat := 4983230072969 + 3 ^ 40 * 7558401 * 2
def baseEnd_7558401 : Nat := 3881092692423987455027053

theorem tailTrace_7558401 : CollatzResearch.WordTrace tailWord_7558401 prefixEnd_7558401 3881092692423987455027053 := by
  unfold tailWord_7558401
  simp only [CollatzResearch.WordTrace]
  refine ⟨275677532290211523964331057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183785021526807682642887371 275677532290211523964331057)
  ·
    refine ⟨206758149217658642973248293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275677532290211523964331057 206758149217658642973248293)
    ·
      refine ⟨38767152978310995557484055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206758149217658642973248293 38767152978310995557484055)
      ·
        refine ⟨58150729467466493336226083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38767152978310995557484055 58150729467466493336226083)
        ·
          refine ⟨87226094201199740004339125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58150729467466493336226083 87226094201199740004339125)
          ·
            refine ⟨8177446331362475625406793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87226094201199740004339125 8177446331362475625406793)
            ·
              refine ⟨6133084748521856719055095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8177446331362475625406793 6133084748521856719055095)
              ·
                refine ⟨9199627122782785078582643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6133084748521856719055095 9199627122782785078582643)
                ·
                  refine ⟨13799440684174177617873965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9199627122782785078582643 13799440684174177617873965)
                  ·
                    refine ⟨5174790256565316606702737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13799440684174177617873965 5174790256565316606702737)
                    ·
                      refine ⟨3881092692423987455027053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5174790256565316606702737 3881092692423987455027053)
                      ·
                        rfl

theorem cell23_7558401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_7558401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558401 prefixEnd_7558401 := by exact prefixLift 7558401
  have htrace : WordTrace (prefixWord ++ tailWord_7558401) baseStart_7558401 baseEnd_7558401 := by
    simpa [prefixWord, tailWord_7558401, baseEnd_7558401] using wordTrace_append hprefix tailTrace_7558401
  have hstable : (prefixWord ++ tailWord_7558401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558401).length < 2 ^ (prefixWord ++ tailWord_7558401).sum := by decide
  have hdescent : baseEnd_7558401 < baseStart_7558401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558414 : List Nat := [4, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2]
def baseStart_7558414 : Nat := 118140960795 + 7558414 * 2 ^ 59
def prefixEnd_7558414 : Nat := 4983230072969 + 3 ^ 40 * 7558414 * 2
def baseEnd_7558414 : Nat := 3881099367672495904164493

theorem tailTrace_7558414 : CollatzResearch.WordTrace tailWord_7558414 prefixEnd_7558414 3881099367672495904164493 := by
  unfold tailWord_7558414
  simp only [CollatzResearch.WordTrace]
  refine ⟨34459750804895553398069287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183785337626109618123036197 34459750804895553398069287)
  ·
    refine ⟨51689626207343330097103931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34459750804895553398069287 51689626207343330097103931)
    ·
      refine ⟨77534439311014995145655897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51689626207343330097103931 77534439311014995145655897)
      ·
        refine ⟨58150829483261246359241923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77534439311014995145655897 58150829483261246359241923)
        ·
          refine ⟨87226244224891869538862885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58150829483261246359241923 87226244224891869538862885)
          ·
            refine ⟨16354920792167225538536791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87226244224891869538862885 16354920792167225538536791)
            ·
              refine ⟨24532381188250838307805187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16354920792167225538536791 24532381188250838307805187)
              ·
                refine ⟨36798571782376257461707781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24532381188250838307805187 36798571782376257461707781)
                ·
                  refine ⟨6899732209195548274070209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36798571782376257461707781 6899732209195548274070209)
                  ·
                    refine ⟨5174799156896661205552657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6899732209195548274070209 5174799156896661205552657)
                    ·
                      refine ⟨3881099367672495904164493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5174799156896661205552657 3881099367672495904164493)
                      ·
                        rfl

theorem cell23_7558414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_7558414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558414 prefixEnd_7558414 := by exact prefixLift 7558414
  have htrace : WordTrace (prefixWord ++ tailWord_7558414) baseStart_7558414 baseEnd_7558414 := by
    simpa [prefixWord, tailWord_7558414, baseEnd_7558414] using wordTrace_append hprefix tailTrace_7558414
  have hstable : (prefixWord ++ tailWord_7558414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558414).length < 2 ^ (prefixWord ++ tailWord_7558414).sum := by decide
  have hdescent : baseEnd_7558414 < baseStart_7558414 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558431 : List Nat := [1, 1, 2, 4, 5, 1, 1, 1, 1, 4, 2]
def baseStart_7558431 : Nat := 118140960795 + 7558431 * 2 ^ 59
def prefixEnd_7558431 : Nat := 4983230072969 + 3 ^ 40 * 7558431 * 2
def baseEnd_7558431 : Nat := 3881108096843622337651915

theorem tailTrace_7558431 : CollatzResearch.WordTrace tailWord_7558431 prefixEnd_7558431 3881108096843622337651915 := by
  unfold tailWord_7558431
  simp only [CollatzResearch.WordTrace]
  refine ⟨275678626480102839087923147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183785750986735226058615431 275678626480102839087923147)
  ·
    refine ⟨413517939720154258631884721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275678626480102839087923147 413517939720154258631884721)
    ·
      refine ⟨310138454790115693973913541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413517939720154258631884721 310138454790115693973913541)
      ·
        refine ⟨58150960273146692620108789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 310138454790115693973913541 58150960273146692620108789)
        ·
          refine ⟨5451652525607502433135199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58150960273146692620108789 5451652525607502433135199)
          ·
            refine ⟨8177478788411253649702799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5451652525607502433135199 8177478788411253649702799)
            ·
              refine ⟨12266218182616880474554199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8177478788411253649702799 12266218182616880474554199)
              ·
                refine ⟨18399327273925320711831299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12266218182616880474554199 18399327273925320711831299)
                ·
                  refine ⟨27598990910887981067746949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18399327273925320711831299 27598990910887981067746949)
                  ·
                    refine ⟨5174810795791496450202553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27598990910887981067746949 5174810795791496450202553)
                    ·
                      refine ⟨3881108096843622337651915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5174810795791496450202553 3881108096843622337651915)
                      ·
                        rfl

theorem cell23_7558431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_7558431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558431 prefixEnd_7558431 := by exact prefixLift 7558431
  have htrace : WordTrace (prefixWord ++ tailWord_7558431) baseStart_7558431 baseEnd_7558431 := by
    simpa [prefixWord, tailWord_7558431, baseEnd_7558431] using wordTrace_append hprefix tailTrace_7558431
  have hstable : (prefixWord ++ tailWord_7558431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558431).length < 2 ^ (prefixWord ++ tailWord_7558431).sum := by decide
  have hdescent : baseEnd_7558431 < baseStart_7558431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558450 : List Nat := [3, 2, 1, 1, 4, 1, 2, 1, 1, 7]
def baseStart_7558450 : Nat := 118140960795 + 7558450 * 2 ^ 59
def prefixEnd_7558450 : Nat := 4983230072969 + 3 ^ 40 * 7558450 * 2
def baseEnd_7558450 : Nat := 1293705950992019254438109

theorem tailTrace_7558450 : CollatzResearch.WordTrace tailWord_7558450 prefixEnd_7558450 1293705950992019254438109 := by
  unfold tailWord_7558450
  simp only [CollatzResearch.WordTrace]
  refine ⟨68919829866758501333216201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183786212978022670221909869 68919829866758501333216201)
  ·
    refine ⟨51689872400068875999912151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68919829866758501333216201 51689872400068875999912151)
    ·
      refine ⟨77534808600103313999868227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51689872400068875999912151 77534808600103313999868227)
      ·
        refine ⟨116302212900154970999802341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77534808600103313999868227 116302212900154970999802341)
        ·
          refine ⟨21806664918779057062462939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116302212900154970999802341 21806664918779057062462939)
          ·
            refine ⟨32709997378168585593694409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21806664918779057062462939 32709997378168585593694409)
            ·
              refine ⟨24532498033626439195270807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32709997378168585593694409 24532498033626439195270807)
              ·
                refine ⟨36798747050439658792906211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24532498033626439195270807 36798747050439658792906211)
                ·
                  refine ⟨55198120575659488189359317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36798747050439658792906211 55198120575659488189359317)
                  ·
                    refine ⟨1293705950992019254438109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55198120575659488189359317 1293705950992019254438109)
                    ·
                      rfl

theorem cell23_7558450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_7558450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558450 prefixEnd_7558450 := by exact prefixLift 7558450
  have htrace : WordTrace (prefixWord ++ tailWord_7558450) baseStart_7558450 baseEnd_7558450 := by
    simpa [prefixWord, tailWord_7558450, baseEnd_7558450] using wordTrace_append hprefix tailTrace_7558450
  have hstable : (prefixWord ++ tailWord_7558450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558450).length < 2 ^ (prefixWord ++ tailWord_7558450).sum := by decide
  have hdescent : baseEnd_7558450 < baseStart_7558450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558490 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3]
def baseStart_7558490 : Nat := 118140960795 + 7558490 * 2 ^ 59
def prefixEnd_7558490 : Nat := 4983230072969 + 3 ^ 40 * 7558490 * 2
def baseEnd_7558490 : Nat := 3881138392202237606814143

theorem tailTrace_7558490 : CollatzResearch.WordTrace tailWord_7558490 prefixEnd_7558490 3881138392202237606814143 := by
  unfold tailWord_7558490
  simp only [CollatzResearch.WordTrace]
  refine ⟨68920194596722273041080231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183787185591259394776213949 68920194596722273041080231)
  ·
    refine ⟨103380291895083409561620347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68920194596722273041080231 103380291895083409561620347)
    ·
      refine ⟨155070437842625114342430521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103380291895083409561620347 155070437842625114342430521)
      ·
        refine ⟨116302828381968835756822891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155070437842625114342430521 116302828381968835756822891)
        ·
          refine ⟨174454242572953253635234337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116302828381968835756822891 174454242572953253635234337)
          ·
            refine ⟨130840681929714940226425753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174454242572953253635234337 130840681929714940226425753)
            ·
              refine ⟨98130511447286205169819315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130840681929714940226425753 98130511447286205169819315)
              ·
                refine ⟨147195767170929307754728973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98130511447286205169819315 147195767170929307754728973)
                ·
                  refine ⟨55198412689098490408023365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147195767170929307754728973 55198412689098490408023365)
                  ·
                    refine ⟨10349702379205966951504381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55198412689098490408023365 10349702379205966951504381)
                    ·
                      refine ⟨3881138392202237606814143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10349702379205966951504381 3881138392202237606814143)
                      ·
                        rfl

theorem cell23_7558490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_7558490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558490 prefixEnd_7558490 := by exact prefixLift 7558490
  have htrace : WordTrace (prefixWord ++ tailWord_7558490) baseStart_7558490 baseEnd_7558490 := by
    simpa [prefixWord, tailWord_7558490, baseEnd_7558490] using wordTrace_append hprefix tailTrace_7558490
  have hstable : (prefixWord ++ tailWord_7558490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558490).length < 2 ^ (prefixWord ++ tailWord_7558490).sum := by decide
  have hdescent : baseEnd_7558490 < baseStart_7558490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558504 : List Nat := [2, 1, 4, 2, 3, 1, 2, 1, 2, 1, 4]
def baseStart_7558504 : Nat := 118140960795 + 7558504 * 2 ^ 59
def prefixEnd_7558504 : Nat := 4983230072969 + 3 ^ 40 * 7558504 * 2
def baseEnd_7558504 : Nat := 3881145580931400552039079

theorem tailTrace_7558504 : CollatzResearch.WordTrace tailWord_7558504 prefixEnd_7558504 3881145580931400552039079 := by
  unfold tailWord_7558504
  simp only [CollatzResearch.WordTrace]
  refine ⟨137840644504419186277665283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183787526005892248370220377 137840644504419186277665283)
  ·
    refine ⟨206760966756628779416497925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137840644504419186277665283 206760966756628779416497925)
    ·
      refine ⟨38767681266867896140593361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206760966756628779416497925 38767681266867896140593361)
      ·
        refine ⟨29075760950150922105445021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38767681266867896140593361 29075760950150922105445021)
        ·
          refine ⟨10903410356306595789541883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29075760950150922105445021 10903410356306595789541883)
          ·
            refine ⟨16355115534459893684312825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10903410356306595789541883 16355115534459893684312825)
            ·
              refine ⟨12266336650844920263234619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16355115534459893684312825 12266336650844920263234619)
              ·
                refine ⟨18399504976267380394851929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12266336650844920263234619 18399504976267380394851929)
                ·
                  refine ⟨13799628732200535296138947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18399504976267380394851929 13799628732200535296138947)
                  ·
                    refine ⟨20699443098300802944208421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13799628732200535296138947 20699443098300802944208421)
                    ·
                      refine ⟨3881145580931400552039079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20699443098300802944208421 3881145580931400552039079)
                      ·
                        rfl

theorem cell23_7558504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_7558504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558504 prefixEnd_7558504 := by exact prefixLift 7558504
  have htrace : WordTrace (prefixWord ++ tailWord_7558504) baseStart_7558504 baseEnd_7558504 := by
    simpa [prefixWord, tailWord_7558504, baseEnd_7558504] using wordTrace_append hprefix tailTrace_7558504
  have hstable : (prefixWord ++ tailWord_7558504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558504).length < 2 ^ (prefixWord ++ tailWord_7558504).sum := by decide
  have hdescent : baseEnd_7558504 < baseStart_7558504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558514 : List Nat := [3, 2, 1, 2, 1, 2, 2, 5, 1, 4]
def baseStart_7558514 : Nat := 118140960795 + 7558514 * 2 ^ 59
def prefixEnd_7558514 : Nat := 4983230072969 + 3 ^ 40 * 7558514 * 2
def baseEnd_7558514 : Nat := 1293716905245981837638011

theorem tailTrace_7558514 : CollatzResearch.WordTrace tailWord_7558514 prefixEnd_7558514 1293716905245981837638011 := by
  unfold tailWord_7558514
  simp only [CollatzResearch.WordTrace]
  refine ⟨68920413434700536065798649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183787769159201429508796397 68920413434700536065798649)
  ·
    refine ⟨51690310076025402049348987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68920413434700536065798649 51690310076025402049348987)
    ·
      refine ⟨77535465114038103074023481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51690310076025402049348987 77535465114038103074023481)
      ·
        refine ⟨58151598835528577305517611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77535465114038103074023481 58151598835528577305517611)
        ·
          refine ⟨87227398253292865958276417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58151598835528577305517611 87227398253292865958276417)
          ·
            refine ⟨65420548689969649468707313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87227398253292865958276417 65420548689969649468707313)
            ·
              refine ⟨49065411517477237101530485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65420548689969649468707313 49065411517477237101530485)
              ·
                refine ⟨4599882329763490978268483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49065411517477237101530485 4599882329763490978268483)
                ·
                  refine ⟨6899823494645236467402725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4599882329763490978268483 6899823494645236467402725)
                  ·
                    refine ⟨1293716905245981837638011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6899823494645236467402725 1293716905245981837638011)
                    ·
                      rfl

theorem cell23_7558514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_7558514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558514 prefixEnd_7558514 := by exact prefixLift 7558514
  have htrace : WordTrace (prefixWord ++ tailWord_7558514) baseStart_7558514 baseEnd_7558514 := by
    simpa [prefixWord, tailWord_7558514, baseEnd_7558514] using wordTrace_append hprefix tailTrace_7558514
  have hstable : (prefixWord ++ tailWord_7558514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558514).length < 2 ^ (prefixWord ++ tailWord_7558514).sum := by decide
  have hdescent : baseEnd_7558514 < baseStart_7558514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558531 : List Nat := [1, 1, 1, 3, 5, 1, 4, 2, 1, 4]
def baseStart_7558531 : Nat := 118140960795 + 7558531 * 2 ^ 59
def prefixEnd_7558531 : Nat := 4983230072969 + 3 ^ 40 * 7558531 * 2
def baseEnd_7558531 : Nat := 1293719814969690648800485

theorem tailTrace_7558531 : CollatzResearch.WordTrace tailWord_7558531 prefixEnd_7558531 1293719814969690648800485 := by
  unfold tailWord_7558531
  simp only [CollatzResearch.WordTrace]
  refine ⟨275682273779740556166563447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183788182519827037444375631 275682273779740556166563447)
  ·
    refine ⟨413523410669610834249845171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275682273779740556166563447 413523410669610834249845171)
    ·
      refine ⟨620285116004416251374767757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413523410669610834249845171 620285116004416251374767757)
      ·
        refine ⟨232606918501656094265537909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 620285116004416251374767757 232606918501656094265537909)
        ·
          refine ⟨21806898609530258837394179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 232606918501656094265537909 21806898609530258837394179)
          ·
            refine ⟨32710347914295388256091269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21806898609530258837394179 32710347914295388256091269)
            ·
              refine ⟨6133190233930385298017113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32710347914295388256091269 6133190233930385298017113)
              ·
                refine ⟨4599892675447788973512835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6133190233930385298017113 4599892675447788973512835)
                ·
                  refine ⟨6899839013171683460269253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4599892675447788973512835 6899839013171683460269253)
                  ·
                    refine ⟨1293719814969690648800485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6899839013171683460269253 1293719814969690648800485)
                    ·
                      rfl

theorem cell23_7558531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2, 1, 4].length) (baseStart_7558531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558531 prefixEnd_7558531 := by exact prefixLift 7558531
  have htrace : WordTrace (prefixWord ++ tailWord_7558531) baseStart_7558531 baseEnd_7558531 := by
    simpa [prefixWord, tailWord_7558531, baseEnd_7558531] using wordTrace_append hprefix tailTrace_7558531
  have hstable : (prefixWord ++ tailWord_7558531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558531).length < 2 ^ (prefixWord ++ tailWord_7558531).sum := by decide
  have hdescent : baseEnd_7558531 < baseStart_7558531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558540 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 5, 5]
def baseStart_7558540 : Nat := 118140960795 + 7558540 * 2 ^ 59
def prefixEnd_7558540 : Nat := 4983230072969 + 3 ^ 40 * 7558540 * 2
def baseEnd_7558540 : Nat := 1293721355411654137062971

theorem tailTrace_7558540 : CollatzResearch.WordTrace tailWord_7558540 prefixEnd_7558540 1293721355411654137062971 := by
  unfold tailWord_7558540
  simp only [CollatzResearch.WordTrace]
  refine ⟨137841301018353975351820537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183788401357805300469094049 137841301018353975351820537)
  ·
    refine ⟨103380975763765481513865403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137841301018353975351820537 103380975763765481513865403)
    ·
      refine ⟨155071463645648222270798105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103380975763765481513865403 155071463645648222270798105)
      ·
        refine ⟨116303597734236166703098579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155071463645648222270798105 116303597734236166703098579)
        ·
          refine ⟨174455396601354250054647869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116303597734236166703098579 174455396601354250054647869)
          ·
            refine ⟨65420773725507843770492951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174455396601354250054647869 65420773725507843770492951)
            ·
              refine ⟨98131160588261765655739427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65420773725507843770492951 98131160588261765655739427)
              ·
                refine ⟨147196740882392648483609141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98131160588261765655739427 147196740882392648483609141)
                ·
                  refine ⟨13799694457724310795338357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147196740882392648483609141 13799694457724310795338357)
                  ·
                    refine ⟨1293721355411654137062971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13799694457724310795338357 1293721355411654137062971)
                    ·
                      rfl

theorem cell23_7558540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 5, 5].length) (baseStart_7558540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558540 prefixEnd_7558540 := by exact prefixLift 7558540
  have htrace : WordTrace (prefixWord ++ tailWord_7558540) baseStart_7558540 baseEnd_7558540 := by
    simpa [prefixWord, tailWord_7558540, baseEnd_7558540] using wordTrace_append hprefix tailTrace_7558540
  have hstable : (prefixWord ++ tailWord_7558540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558540).length < 2 ^ (prefixWord ++ tailWord_7558540).sum := by decide
  have hdescent : baseEnd_7558540 < baseStart_7558540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558554 : List Nat := [3, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3]
def baseStart_7558554 : Nat := 118140960795 + 7558554 * 2 ^ 59
def prefixEnd_7558554 : Nat := 4983230072969 + 3 ^ 40 * 7558554 * 2
def baseEnd_7558554 : Nat := 3881171254964125356413849

theorem tailTrace_7558554 : CollatzResearch.WordTrace tailWord_7558554 prefixEnd_7558554 3881171254964125356413849 := by
  unfold tailWord_7558554
  simp only [CollatzResearch.WordTrace]
  refine ⟨68920778164664307773662679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183788741772438154063100477 68920778164664307773662679)
  ·
    refine ⟨103381167246996461660494019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68920778164664307773662679 103381167246996461660494019)
    ·
      refine ⟨155071750870494692490741029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103381167246996461660494019 155071750870494692490741029)
      ·
        refine ⟨29075953288217754842013943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155071750870494692490741029 29075953288217754842013943)
        ·
          refine ⟨43613929932326632263020915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29075953288217754842013943 43613929932326632263020915)
          ·
            refine ⟨65420894898489948394531373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43613929932326632263020915 65420894898489948394531373)
            ·
              refine ⟨24532835586933730647949265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65420894898489948394531373 24532835586933730647949265)
              ·
                refine ⟨18399626690200297985961949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24532835586933730647949265 18399626690200297985961949)
                ·
                  refine ⟨6899860008825111744735731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18399626690200297985961949 6899860008825111744735731)
                  ·
                    refine ⟨10349790013237667617103597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6899860008825111744735731 10349790013237667617103597)
                    ·
                      refine ⟨3881171254964125356413849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10349790013237667617103597 3881171254964125356413849)
                      ·
                        rfl

theorem cell23_7558554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_7558554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558554 prefixEnd_7558554 := by exact prefixLift 7558554
  have htrace : WordTrace (prefixWord ++ tailWord_7558554) baseStart_7558554 baseEnd_7558554 := by
    simpa [prefixWord, tailWord_7558554, baseEnd_7558554] using wordTrace_append hprefix tailTrace_7558554
  have hstable : (prefixWord ++ tailWord_7558554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558554).length < 2 ^ (prefixWord ++ tailWord_7558554).sum := by decide
  have hdescent : baseEnd_7558554 < baseStart_7558554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558557 : List Nat := [1, 4, 2, 1, 3, 1, 2, 1, 3, 5]
def baseStart_7558557 : Nat := 118140960795 + 7558557 * 2 ^ 59
def prefixEnd_7558557 : Nat := 4983230072969 + 3 ^ 40 * 7558557 * 2
def baseEnd_7558557 : Nat := 1293724265135362948225445

theorem tailTrace_7558557 : CollatzResearch.WordTrace tailWord_7558557 prefixEnd_7558557 1293724265135362948225445 := by
  unfold tailWord_7558557
  simp only [CollatzResearch.WordTrace]
  refine ⟨275683222077646362607009925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183788814718430908404673283 275683222077646362607009925)
  ·
    refine ⟨51690604139558692988814361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275683222077646362607009925 51690604139558692988814361)
    ·
      refine ⟨38767953104669019741610771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51690604139558692988814361 38767953104669019741610771)
      ·
        refine ⟨58151929657003529612416157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38767953104669019741610771 58151929657003529612416157)
        ·
          refine ⟨21806973621376323604656059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58151929657003529612416157 21806973621376323604656059)
          ·
            refine ⟨32710460432064485406984089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21806973621376323604656059 32710460432064485406984089)
            ·
              refine ⟨24532845324048364055238067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32710460432064485406984089 24532845324048364055238067)
              ·
                refine ⟨36799267986072546082857101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24532845324048364055238067 36799267986072546082857101)
                ·
                  refine ⟨13799725494777204781071413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36799267986072546082857101 13799725494777204781071413)
                  ·
                    refine ⟨1293724265135362948225445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13799725494777204781071413 1293724265135362948225445)
                    ·
                      rfl

theorem cell23_7558557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_7558557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558557 prefixEnd_7558557 := by exact prefixLift 7558557
  have htrace : WordTrace (prefixWord ++ tailWord_7558557) baseStart_7558557 baseEnd_7558557 := by
    simpa [prefixWord, tailWord_7558557, baseEnd_7558557] using wordTrace_append hprefix tailTrace_7558557
  have hstable : (prefixWord ++ tailWord_7558557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558557).length < 2 ^ (prefixWord ++ tailWord_7558557).sum := by decide
  have hdescent : baseEnd_7558557 < baseStart_7558557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558558 : List Nat := [4, 3, 1, 2, 2, 2, 1, 1, 2, 2, 3]
def baseStart_7558558 : Nat := 118140960795 + 7558558 * 2 ^ 59
def prefixEnd_7558558 : Nat := 4983230072969 + 3 ^ 40 * 7558558 * 2
def baseEnd_7558558 : Nat := 3881173308886743340763831

theorem tailTrace_7558558 : CollatzResearch.WordTrace tailWord_7558558 prefixEnd_7558558 3881173308886743340763831 := by
  unfold tailWord_7558558
  simp only [CollatzResearch.WordTrace]
  refine ⟨34460407318830342472224541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183788839033761826518530885 34460407318830342472224541)
  ·
    refine ⟨12922652744561378427084203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34460407318830342472224541 12922652744561378427084203)
    ·
      refine ⟨19383979116842067640626305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12922652744561378427084203 19383979116842067640626305)
      ·
        refine ⟨14537984337631550730469729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19383979116842067640626305 14537984337631550730469729)
        ·
          refine ⟨10903488253223663047852297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14537984337631550730469729 10903488253223663047852297)
          ·
            refine ⟨8177616189917747285889223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10903488253223663047852297 8177616189917747285889223)
            ·
              refine ⟨12266424284876620928833835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8177616189917747285889223 12266424284876620928833835)
              ·
                refine ⟨18399636427314931393250753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12266424284876620928833835 18399636427314931393250753)
                ·
                  refine ⟨13799727320486198544938065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18399636427314931393250753 13799727320486198544938065)
                  ·
                    refine ⟨10349795490364648908703549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13799727320486198544938065 10349795490364648908703549)
                    ·
                      refine ⟨3881173308886743340763831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10349795490364648908703549 3881173308886743340763831)
                      ·
                        rfl

theorem cell23_7558558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_7558558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558558 prefixEnd_7558558 := by exact prefixLift 7558558
  have htrace : WordTrace (prefixWord ++ tailWord_7558558) baseStart_7558558 baseEnd_7558558 := by
    simpa [prefixWord, tailWord_7558558, baseEnd_7558558] using wordTrace_append hprefix tailTrace_7558558
  have hstable : (prefixWord ++ tailWord_7558558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558558).length < 2 ^ (prefixWord ++ tailWord_7558558).sum := by decide
  have hdescent : baseEnd_7558558 < baseStart_7558558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558600 : List Nat := [2, 1, 3, 1, 3, 1, 2, 10]
def baseStart_7558600 : Nat := 118140960795 + 7558600 * 2 ^ 59
def prefixEnd_7558600 : Nat := 4983230072969 + 3 ^ 40 * 7558600 * 2
def baseEnd_7558600 : Nat := 143747958336082673201431

theorem tailTrace_7558600 : CollatzResearch.WordTrace tailWord_7558600 prefixEnd_7558600 143747958336082673201431 := by
  unfold tailWord_7558600
  simp only [CollatzResearch.WordTrace]
  refine ⟨137842395208245290475412627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183789860277660387300550169 137842395208245290475412627)
  ·
    refine ⟨206763592812367935713118941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137842395208245290475412627 206763592812367935713118941)
    ·
      refine ⟨77536347304637975892419603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206763592812367935713118941 77536347304637975892419603)
      ·
        refine ⟨116304520956956963838629405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77536347304637975892419603 116304520956956963838629405)
        ·
          refine ⟨43614195358858861439486027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116304520956956963838629405 43614195358858861439486027)
          ·
            refine ⟨65421293038288292159229041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43614195358858861439486027 65421293038288292159229041)
            ·
              refine ⟨49065969778716219119421781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65421293038288292159229041 49065969778716219119421781)
              ·
                refine ⟨143747958336082673201431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49065969778716219119421781 143747958336082673201431)
                ·
                  rfl

theorem cell23_7558600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 10].length) (baseStart_7558600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558600 prefixEnd_7558600 := by exact prefixLift 7558600
  have htrace : WordTrace (prefixWord ++ tailWord_7558600) baseStart_7558600 baseEnd_7558600 := by
    simpa [prefixWord, tailWord_7558600, baseEnd_7558600] using wordTrace_append hprefix tailTrace_7558600
  have hstable : (prefixWord ++ tailWord_7558600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558600).length < 2 ^ (prefixWord ++ tailWord_7558600).sum := by decide
  have hdescent : baseEnd_7558600 < baseStart_7558600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558604 : List Nat := [2, 2, 1, 4, 2, 3, 1, 1, 1, 6]
def baseStart_7558604 : Nat := 118140960795 + 7558604 * 2 ^ 59
def prefixEnd_7558604 : Nat := 4983230072969 + 3 ^ 40 * 7558604 * 2
def baseEnd_7558604 : Nat := 1293732309665616720262873

theorem tailTrace_7558604 : CollatzResearch.WordTrace tailWord_7558604 prefixEnd_7558604 1293732309665616720262873 := by
  unfold tailWord_7558604
  simp only [CollatzResearch.WordTrace]
  refine ⟨137842468154238044816985433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183789957538984059755980577 137842468154238044816985433)
  ·
    refine ⟨103381851115678533612739075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137842468154238044816985433 103381851115678533612739075)
    ·
      refine ⟨155072776673517800419108613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103381851115678533612739075 155072776673517800419108613)
      ·
        refine ⟨29076145626284587578582865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155072776673517800419108613 29076145626284587578582865)
        ·
          refine ⟨21807109219713440683937149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29076145626284587578582865 21807109219713440683937149)
          ·
            refine ⟨8177665957392540256476431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21807109219713440683937149 8177665957392540256476431)
            ·
              refine ⟨12266498936088810384714647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8177665957392540256476431 12266498936088810384714647)
              ·
                refine ⟨18399748404133215577071971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12266498936088810384714647 18399748404133215577071971)
                ·
                  refine ⟨27599622606199823365607957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18399748404133215577071971 27599622606199823365607957)
                  ·
                    refine ⟨1293732309665616720262873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27599622606199823365607957 1293732309665616720262873)
                    ·
                      rfl

theorem cell23_7558604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 1, 6].length) (baseStart_7558604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558604 prefixEnd_7558604 := by exact prefixLift 7558604
  have htrace : WordTrace (prefixWord ++ tailWord_7558604) baseStart_7558604 baseEnd_7558604 := by
    simpa [prefixWord, tailWord_7558604, baseEnd_7558604] using wordTrace_append hprefix tailTrace_7558604
  have hstable : (prefixWord ++ tailWord_7558604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558604).length < 2 ^ (prefixWord ++ tailWord_7558604).sum := by decide
  have hdescent : baseEnd_7558604 < baseStart_7558604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558607 : List Nat := [1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 4]
def baseStart_7558607 : Nat := 118140960795 + 7558607 * 2 ^ 59
def prefixEnd_7558607 : Nat := 4983230072969 + 3 ^ 40 * 7558607 * 2
def baseEnd_7558607 : Nat := 3881198469438813649051105

theorem tailTrace_7558607 : CollatzResearch.WordTrace tailWord_7558607 prefixEnd_7558607 3881198469438813649051105 := by
  unfold tailWord_7558607
  simp only [CollatzResearch.WordTrace]
  refine ⟨275685045727465221146330075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183790030484976814097553383 275685045727465221146330075)
  ·
    refine ⟨413527568591197831719495113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275685045727465221146330075 413527568591197831719495113)
    ·
      refine ⟨310145676443398373789621335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413527568591197831719495113 310145676443398373789621335)
      ·
        refine ⟨465218514665097560684432003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310145676443398373789621335 465218514665097560684432003)
        ·
          refine ⟨697827771997646341026648005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465218514665097560684432003 697827771997646341026648005)
          ·
            refine ⟨130842707249558688942496501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 697827771997646341026648005 130842707249558688942496501)
            ·
              refine ⟨12266503804646127088359047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130842707249558688942496501 12266503804646127088359047)
              ·
                refine ⟨18399755706969190632538571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12266503804646127088359047 18399755706969190632538571)
                ·
                  refine ⟨27599633560453785948807857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18399755706969190632538571 27599633560453785948807857)
                  ·
                    refine ⟨20699725170340339461605893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27599633560453785948807857 20699725170340339461605893)
                    ·
                      refine ⟨3881198469438813649051105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20699725170340339461605893 3881198469438813649051105)
                      ·
                        rfl

theorem cell23_7558607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 4].length) (baseStart_7558607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558607 prefixEnd_7558607 := by exact prefixLift 7558607
  have htrace : WordTrace (prefixWord ++ tailWord_7558607) baseStart_7558607 baseEnd_7558607 := by
    simpa [prefixWord, tailWord_7558607, baseEnd_7558607] using wordTrace_append hprefix tailTrace_7558607
  have hstable : (prefixWord ++ tailWord_7558607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558607).length < 2 ^ (prefixWord ++ tailWord_7558607).sum := by decide
  have hdescent : baseEnd_7558607 < baseStart_7558607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558617 : List Nat := [1, 2, 1, 2, 4, 2, 4, 7]
def baseStart_7558617 : Nat := 118140960795 + 7558617 * 2 ^ 59
def prefixEnd_7558617 : Nat := 4983230072969 + 3 ^ 40 * 7558617 * 2
def baseEnd_7558617 : Nat := 143748281638716985552817

theorem tailTrace_7558617 : CollatzResearch.WordTrace tailWord_7558617 prefixEnd_7558617 143748281638716985552817 := by
  unfold tailWord_7558617
  simp only [CollatzResearch.WordTrace]
  refine ⟨275685410457428992854194105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183790273638285995236129403 275685410457428992854194105)
  ·
    refine ⟨206764057843071744640645579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275685410457428992854194105 206764057843071744640645579)
    ·
      refine ⟨310146086764607616960968369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206764057843071744640645579 310146086764607616960968369)
      ·
        refine ⟨232609565073455712720726277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310146086764607616960968369 232609565073455712720726277)
        ·
          refine ⟨43614293451272946135136177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232609565073455712720726277 43614293451272946135136177)
          ·
            refine ⟨32710720088454709601352133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43614293451272946135136177 32710720088454709601352133)
            ·
              refine ⟨6133260016585258050253525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32710720088454709601352133 6133260016585258050253525)
              ·
                refine ⟨143748281638716985552817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6133260016585258050253525 143748281638716985552817)
                ·
                  rfl

theorem cell23_7558617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 7].length) (baseStart_7558617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558617 prefixEnd_7558617 := by exact prefixLift 7558617
  have htrace : WordTrace (prefixWord ++ tailWord_7558617) baseStart_7558617 baseEnd_7558617 := by
    simpa [prefixWord, tailWord_7558617, baseEnd_7558617] using wordTrace_append hprefix tailTrace_7558617
  have hstable : (prefixWord ++ tailWord_7558617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558617).length < 2 ^ (prefixWord ++ tailWord_7558617).sum := by decide
  have hdescent : baseEnd_7558617 < baseStart_7558617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558634 : List Nat := [3, 1, 3, 1, 5, 1, 9]
def baseStart_7558634 : Nat := 118140960795 + 7558634 * 2 ^ 59
def prefixEnd_7558634 : Nat := 4983230072969 + 3 ^ 40 * 7558634 * 2
def baseEnd_7558634 : Nat := 47916201647117099301401

theorem tailTrace_7558634 : CollatzResearch.WordTrace tailWord_7558634 prefixEnd_7558634 47916201647117099301401 := by
  unfold tailWord_7558634
  simp only [CollatzResearch.WordTrace]
  refine ⟨68921507624591851189390739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183790686998911603171708637 68921507624591851189390739)
  ·
    refine ⟨103382261436887776784086109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68921507624591851189390739 103382261436887776784086109)
    ·
      refine ⟨38768348038832916294032291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103382261436887776784086109 38768348038832916294032291)
      ·
        refine ⟨58152522058249374441048437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38768348038832916294032291 58152522058249374441048437)
        ·
          refine ⟨5451798942960878853848291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58152522058249374441048437 5451798942960878853848291)
          ·
            refine ⟨8177698414441318280772437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5451798942960878853848291 8177698414441318280772437)
            ·
              refine ⟨47916201647117099301401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8177698414441318280772437 47916201647117099301401)
              ·
                rfl

theorem cell23_7558634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 9].length) (baseStart_7558634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558634 prefixEnd_7558634 := by exact prefixLift 7558634
  have htrace : WordTrace (prefixWord ++ tailWord_7558634) baseStart_7558634 baseEnd_7558634 := by
    simpa [prefixWord, tailWord_7558634, baseEnd_7558634] using wordTrace_append hprefix tailTrace_7558634
  have hstable : (prefixWord ++ tailWord_7558634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558634).length < 2 ^ (prefixWord ++ tailWord_7558634).sum := by decide
  have hdescent : baseEnd_7558634 < baseStart_7558634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558645 : List Nat := [1, 3, 5, 1, 1, 3, 1, 1, 3, 2, 2]
def baseStart_7558645 : Nat := 118140960795 + 7558645 * 2 ^ 59
def prefixEnd_7558645 : Nat := 4983230072969 + 3 ^ 40 * 7558645 * 2
def baseEnd_7558645 : Nat := 3881217981703684500375931

theorem tailTrace_7558645 : CollatzResearch.WordTrace tailWord_7558645 prefixEnd_7558645 3881217981703684500375931 := by
  unfold tailWord_7558645
  simp only [CollatzResearch.WordTrace]
  refine ⟨275686431701327553636213389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183790954467551702424142259 275686431701327553636213389)
  ·
    refine ⟨103382411887997832613580021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275686431701327553636213389 103382411887997832613580021)
    ·
      refine ⟨9692101114499796807523127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103382411887997832613580021 9692101114499796807523127)
      ·
        refine ⟨14538151671749695211284691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9692101114499796807523127 14538151671749695211284691)
        ·
          refine ⟨21807227507624542816927037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14538151671749695211284691 21807227507624542816927037)
          ·
            refine ⟨8177710315359203556347639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21807227507624542816927037 8177710315359203556347639)
            ·
              refine ⟨12266565473038805334521459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8177710315359203556347639 12266565473038805334521459)
              ·
                refine ⟨18399848209558208001782189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12266565473038805334521459 18399848209558208001782189)
                ·
                  refine ⟨6899943078584328000668321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18399848209558208001782189 6899943078584328000668321)
                  ·
                    refine ⟨5174957308938246000501241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6899943078584328000668321 5174957308938246000501241)
                    ·
                      refine ⟨3881217981703684500375931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5174957308938246000501241 3881217981703684500375931)
                      ·
                        rfl

theorem cell23_7558645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_7558645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558645 prefixEnd_7558645 := by exact prefixLift 7558645
  have htrace : WordTrace (prefixWord ++ tailWord_7558645) baseStart_7558645 baseEnd_7558645 := by
    simpa [prefixWord, tailWord_7558645, baseEnd_7558645] using wordTrace_append hprefix tailTrace_7558645
  have hstable : (prefixWord ++ tailWord_7558645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558645).length < 2 ^ (prefixWord ++ tailWord_7558645).sum := by decide
  have hdescent : baseEnd_7558645 < baseStart_7558645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558662 : List Nat := [6, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_7558662 : Nat := 118140960795 + 7558662 * 2 ^ 59
def prefixEnd_7558662 : Nat := 4983230072969 + 3 ^ 40 * 7558662 * 2
def baseEnd_7558662 : Nat := 3881226710874810933863353

theorem tailTrace_7558662 : CollatzResearch.WordTrace tailWord_7558662 prefixEnd_7558662 3881226710874810933863353 := by
  unfold tailWord_7558662
  simp only [CollatzResearch.WordTrace]
  refine ⟨8615220366945811423111945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 183791367828177310359721493 8615220366945811423111945)
  ·
    refine ⟨6461415275209358567333959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8615220366945811423111945 6461415275209358567333959)
    ·
      refine ⟨9692122912814037851000939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6461415275209358567333959 9692122912814037851000939)
      ·
        refine ⟨14538184369221056776501409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9692122912814037851000939 14538184369221056776501409)
        ·
          refine ⟨10903638276915792582376057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14538184369221056776501409 10903638276915792582376057)
          ·
            refine ⟨8177728707686844436782043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10903638276915792582376057 8177728707686844436782043)
            ·
              refine ⟨12266593061530266655173065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8177728707686844436782043 12266593061530266655173065)
              ·
                refine ⟨9199944796147699991379799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12266593061530266655173065 9199944796147699991379799)
                ·
                  refine ⟨13799917194221549987069699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9199944796147699991379799 13799917194221549987069699)
                  ·
                    refine ⟨20699875791332324980604549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13799917194221549987069699 20699875791332324980604549)
                    ·
                      refine ⟨3881226710874810933863353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20699875791332324980604549 3881226710874810933863353)
                      ·
                        rfl

theorem cell23_7558662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_7558662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558662 prefixEnd_7558662 := by exact prefixLift 7558662
  have htrace : WordTrace (prefixWord ++ tailWord_7558662) baseStart_7558662 baseEnd_7558662 := by
    simpa [prefixWord, tailWord_7558662, baseEnd_7558662] using wordTrace_append hprefix tailTrace_7558662
  have hstable : (prefixWord ++ tailWord_7558662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558662).length < 2 ^ (prefixWord ++ tailWord_7558662).sum := by decide
  have hdescent : baseEnd_7558662 < baseStart_7558662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558687 : List Nat := [1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 5]
def baseStart_7558687 : Nat := 118140960795 + 7558687 * 2 ^ 59
def prefixEnd_7558687 : Nat := 4983230072969 + 3 ^ 40 * 7558687 * 2
def baseEnd_7558687 : Nat := 3881239547891173336050737

theorem tailTrace_7558687 : CollatzResearch.WordTrace tailWord_7558687 prefixEnd_7558687 3881239547891173336050737 := by
  unfold tailWord_7558687
  simp only [CollatzResearch.WordTrace]
  refine ⟨275687963567175394809242315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183791975711450263206161543 275687963567175394809242315)
  ·
    refine ⟨413531945350763092213863473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275687963567175394809242315 413531945350763092213863473)
    ·
      refine ⟨310148959013072319160397605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413531945350763092213863473 310148959013072319160397605)
      ·
        refine ⟨58152929814951059842574551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 310148959013072319160397605 58152929814951059842574551)
        ·
          refine ⟨87229394722426589763861827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58152929814951059842574551 87229394722426589763861827)
          ·
            refine ⟨130844092083639884645792741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87229394722426589763861827 130844092083639884645792741)
            ·
              refine ⟨24533267265682478371086139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130844092083639884645792741 24533267265682478371086139)
              ·
                refine ⟨36799900898523717556629209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24533267265682478371086139 36799900898523717556629209)
                ·
                  refine ⟨27599925673892788167471907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36799900898523717556629209 27599925673892788167471907)
                  ·
                    refine ⟨41399888510839182251207861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27599925673892788167471907 41399888510839182251207861)
                    ·
                      refine ⟨3881239547891173336050737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41399888510839182251207861 3881239547891173336050737)
                      ·
                        rfl

theorem cell23_7558687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_7558687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558687 prefixEnd_7558687 := by exact prefixLift 7558687
  have htrace : WordTrace (prefixWord ++ tailWord_7558687) baseStart_7558687 baseEnd_7558687 := by
    simpa [prefixWord, tailWord_7558687, baseEnd_7558687] using wordTrace_append hprefix tailTrace_7558687
  have hstable : (prefixWord ++ tailWord_7558687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558687).length < 2 ^ (prefixWord ++ tailWord_7558687).sum := by decide
  have hdescent : baseEnd_7558687 < baseStart_7558687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558737 : List Nat := [1, 2, 2, 1, 3, 2, 3, 1, 1, 7]
def baseStart_7558737 : Nat := 118140960795 + 7558737 * 2 ^ 59
def prefixEnd_7558737 : Nat := 4983230072969 + 3 ^ 40 * 7558737 * 2
def baseEnd_7558737 : Nat := 1293755073974632713475169

theorem tailTrace_7558737 : CollatzResearch.WordTrace tailWord_7558737 prefixEnd_7558737 1293755073974632713475169 := by
  unfold tailWord_7558737
  simp only [CollatzResearch.WordTrace]
  refine ⟨275689787216994253348562465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183793191477996168899041643 275689787216994253348562465)
  ·
    refine ⟨206767340412745690011421849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275689787216994253348562465 206767340412745690011421849)
    ·
      refine ⟨155075505309559267508566387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206767340412745690011421849 155075505309559267508566387)
      ·
        refine ⟨232613257964338901262849581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155075505309559267508566387 232613257964338901262849581)
        ·
          refine ⟨87229971736627087973568593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232613257964338901262849581 87229971736627087973568593)
          ·
            refine ⟨65422478802470315980176445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87229971736627087973568593 65422478802470315980176445)
            ·
              refine ⟨24533429550926368492566167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65422478802470315980176445 24533429550926368492566167)
              ·
                refine ⟨36800144326389552738849251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24533429550926368492566167 36800144326389552738849251)
                ·
                  refine ⟨55200216489584329108273877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36800144326389552738849251 55200216489584329108273877)
                  ·
                    refine ⟨1293755073974632713475169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55200216489584329108273877 1293755073974632713475169)
                    ·
                      rfl

theorem cell23_7558737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 7].length) (baseStart_7558737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558737 prefixEnd_7558737 := by exact prefixLift 7558737
  have htrace : WordTrace (prefixWord ++ tailWord_7558737) baseStart_7558737 baseEnd_7558737 := by
    simpa [prefixWord, tailWord_7558737, baseEnd_7558737] using wordTrace_append hprefix tailTrace_7558737
  have hstable : (prefixWord ++ tailWord_7558737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558737).length < 2 ^ (prefixWord ++ tailWord_7558737).sum := by decide
  have hdescent : baseEnd_7558737 < baseStart_7558737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558784 : List Nat := [2, 1, 1, 2, 1, 4, 1, 4, 3, 4]
def baseStart_7558784 : Nat := 118140960795 + 7558784 * 2 ^ 59
def prefixEnd_7558784 : Nat := 4983230072969 + 3 ^ 40 * 7558784 * 2
def baseEnd_7558784 : Nat := 1293763118504886485512597

theorem tailTrace_7558784 : CollatzResearch.WordTrace tailWord_7558784 prefixEnd_7558784 1293763118504886485512597 := by
  unfold tailWord_7558784
  simp only [CollatzResearch.WordTrace]
  refine ⟨137845750723911990187761703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183794334298549320250348937 137845750723911990187761703)
  ·
    refine ⟨206768626085867985281642555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137845750723911990187761703 206768626085867985281642555)
    ·
      refine ⟨310152939128801977922463833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206768626085867985281642555 310152939128801977922463833)
      ·
        refine ⟨232614704346601483441847875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310152939128801977922463833 232614704346601483441847875)
        ·
          refine ⟨348922056519902225162771813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232614704346601483441847875 348922056519902225162771813)
          ·
            refine ⟨65422885597481667218019715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 348922056519902225162771813 65422885597481667218019715)
            ·
              refine ⟨98134328396222500827029573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65422885597481667218019715 98134328396222500827029573)
              ·
                refine ⟨18400186574291718905068045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98134328396222500827029573 18400186574291718905068045)
                ·
                  refine ⟨6900069965359394589400517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18400186574291718905068045 6900069965359394589400517)
                  ·
                    refine ⟨1293763118504886485512597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6900069965359394589400517 1293763118504886485512597)
                    ·
                      rfl

theorem cell23_7558784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 3, 4].length) (baseStart_7558784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558784 prefixEnd_7558784 := by exact prefixLift 7558784
  have htrace : WordTrace (prefixWord ++ tailWord_7558784) baseStart_7558784 baseEnd_7558784 := by
    simpa [prefixWord, tailWord_7558784, baseEnd_7558784] using wordTrace_append hprefix tailTrace_7558784
  have hstable : (prefixWord ++ tailWord_7558784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558784).length < 2 ^ (prefixWord ++ tailWord_7558784).sum := by decide
  have hdescent : baseEnd_7558784 < baseStart_7558784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558787 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 4]
def baseStart_7558787 : Nat := 118140960795 + 7558787 * 2 ^ 59
def prefixEnd_7558787 : Nat := 4983230072969 + 3 ^ 40 * 7558787 * 2
def baseEnd_7558787 : Nat := 3881290895956622944800277

theorem tailTrace_7558787 : CollatzResearch.WordTrace tailWord_7558787 prefixEnd_7558787 3881290895956622944800277 := by
  unfold tailWord_7558787
  simp only [CollatzResearch.WordTrace]
  refine ⟨275691610866813111887882615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183794407244542074591921743 275691610866813111887882615)
  ·
    refine ⟨413537416300219667831823923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275691610866813111887882615 413537416300219667831823923)
    ·
      refine ⟨620306124450329501747735885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413537416300219667831823923 620306124450329501747735885)
      ·
        refine ⟨232614796668873563155400957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 620306124450329501747735885 232614796668873563155400957)
        ·
          refine ⟨87230548750827586183275359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232614796668873563155400957 87230548750827586183275359)
          ·
            refine ⟨130845823126241379274913039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87230548750827586183275359 130845823126241379274913039)
            ·
              refine ⟨196268734689362068912369559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130845823126241379274913039 196268734689362068912369559)
              ·
                refine ⟨294403102034043103368554339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196268734689362068912369559 294403102034043103368554339)
                ·
                  refine ⟨441604653051064655052831509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294403102034043103368554339 441604653051064655052831509)
                  ·
                    refine ⟨20700218111768655705601477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 441604653051064655052831509 20700218111768655705601477)
                    ·
                      refine ⟨3881290895956622944800277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20700218111768655705601477 3881290895956622944800277)
                      ·
                        rfl

theorem cell23_7558787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_7558787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558787 prefixEnd_7558787 := by exact prefixLift 7558787
  have htrace : WordTrace (prefixWord ++ tailWord_7558787) baseStart_7558787 baseEnd_7558787 := by
    simpa [prefixWord, tailWord_7558787, baseEnd_7558787] using wordTrace_append hprefix tailTrace_7558787
  have hstable : (prefixWord ++ tailWord_7558787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558787).length < 2 ^ (prefixWord ++ tailWord_7558787).sum := by decide
  have hdescent : baseEnd_7558787 < baseStart_7558787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558801 : List Nat := [1, 2, 2, 1, 1, 1, 1, 9, 1, 4]
def baseStart_7558801 : Nat := 118140960795 + 7558801 * 2 ^ 59
def prefixEnd_7558801 : Nat := 4983230072969 + 3 ^ 40 * 7558801 * 2
def baseEnd_7558801 : Nat := 1293766028228595296675071

theorem tailTrace_7558801 : CollatzResearch.WordTrace tailWord_7558801 prefixEnd_7558801 1293766028228595296675071 := by
  unfold tailWord_7558801
  simp only [CollatzResearch.WordTrace]
  refine ⟨275692121488762392278892257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183794747659174928185928171 275692121488762392278892257)
  ·
    refine ⟨206769091116571794209169193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275692121488762392278892257 206769091116571794209169193)
    ·
      refine ⟨155076818337428845656876895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206769091116571794209169193 155076818337428845656876895)
      ·
        refine ⟨232615227506143268485315343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155076818337428845656876895 232615227506143268485315343)
        ·
          refine ⟨348922841259214902727973015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232615227506143268485315343 348922841259214902727973015)
          ·
            refine ⟨523384261888822354091959523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348922841259214902727973015 523384261888822354091959523)
            ·
              refine ⟨785076392833233531137939285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523384261888822354091959523 785076392833233531137939285)
              ·
                refine ⟨4600056989257227721511363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 785076392833233531137939285 4600056989257227721511363)
                ·
                  refine ⟨6900085483885841582267045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4600056989257227721511363 6900085483885841582267045)
                  ·
                    refine ⟨1293766028228595296675071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6900085483885841582267045 1293766028228595296675071)
                    ·
                      rfl

theorem cell23_7558801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9, 1, 4].length) (baseStart_7558801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558801 prefixEnd_7558801 := by exact prefixLift 7558801
  have htrace : WordTrace (prefixWord ++ tailWord_7558801) baseStart_7558801 baseEnd_7558801 := by
    simpa [prefixWord, tailWord_7558801, baseEnd_7558801] using wordTrace_append hprefix tailTrace_7558801
  have hstable : (prefixWord ++ tailWord_7558801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558801).length < 2 ^ (prefixWord ++ tailWord_7558801).sum := by decide
  have hdescent : baseEnd_7558801 < baseStart_7558801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558841 : List Nat := [1, 2, 1, 4, 1, 1, 2, 4, 3, 1, 3]
def baseStart_7558841 : Nat := 118140960795 + 7558841 * 2 ^ 59
def prefixEnd_7558841 : Nat := 4983230072969 + 3 ^ 40 * 7558841 * 2
def baseEnd_7558841 : Nat := 3881318623911965733525029

theorem tailTrace_7558841 : CollatzResearch.WordTrace tailWord_7558841 prefixEnd_7558841 3881318623911965733525029 := by
  unfold tailWord_7558841
  simp only [CollatzResearch.WordTrace]
  refine ⟨275693580408617479110348377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183795720272411652740232251 275693580408617479110348377)
  ·
    refine ⟨206770185306463109332761283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275693580408617479110348377 206770185306463109332761283)
    ·
      refine ⟨310155277959694663999141925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206770185306463109332761283 310155277959694663999141925)
      ·
        refine ⟨58154114617442749499839111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 310155277959694663999141925 58154114617442749499839111)
        ·
          refine ⟨87231171926164124249758667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58154114617442749499839111 87231171926164124249758667)
          ·
            refine ⟨130846757889246186374638001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87231171926164124249758667 130846757889246186374638001)
            ·
              refine ⟨98135068416934639780978501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130846757889246186374638001 98135068416934639780978501)
              ·
                refine ⟨18400325328175244958933469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98135068416934639780978501 18400325328175244958933469)
                ·
                  refine ⟨6900121998065716859600051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18400325328175244958933469 6900121998065716859600051)
                  ·
                    refine ⟨10350182997098575289400077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6900121998065716859600051 10350182997098575289400077)
                    ·
                      refine ⟨3881318623911965733525029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10350182997098575289400077 3881318623911965733525029)
                      ·
                        rfl

theorem cell23_7558841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_7558841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558841 prefixEnd_7558841 := by exact prefixLift 7558841
  have htrace : WordTrace (prefixWord ++ tailWord_7558841) baseStart_7558841 baseEnd_7558841 := by
    simpa [prefixWord, tailWord_7558841, baseEnd_7558841] using wordTrace_append hprefix tailTrace_7558841
  have hstable : (prefixWord ++ tailWord_7558841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558841).length < 2 ^ (prefixWord ++ tailWord_7558841).sum := by decide
  have hdescent : baseEnd_7558841 < baseStart_7558841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558884 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 3, 1, 5]
def baseStart_7558884 : Nat := 118140960795 + 7558884 * 2 ^ 59
def prefixEnd_7558884 : Nat := 4983230072969 + 3 ^ 40 * 7558884 * 2
def baseEnd_7558884 : Nat := 3881340703580109065287331

theorem tailTrace_7558884 : CollatzResearch.WordTrace tailWord_7558884 prefixEnd_7558884 3881340703580109065287331 := by
  unfold tailWord_7558884
  simp only [CollatzResearch.WordTrace]
  refine ⟨137847574373730848727081853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183796765831641131636109137 137847574373730848727081853)
  ·
    refine ⟨51692840390149068272655695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137847574373730848727081853 51692840390149068272655695)
    ·
      refine ⟨77539260585223602408983543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51692840390149068272655695 77539260585223602408983543)
      ·
        refine ⟨116308890877835403613475315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77539260585223602408983543 116308890877835403613475315)
        ·
          refine ⟨174463336316753105420212973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116308890877835403613475315 174463336316753105420212973)
          ·
            refine ⟨65423751118782414532579865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174463336316753105420212973 65423751118782414532579865)
            ·
              refine ⟨49067813339086810899434899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65423751118782414532579865 49067813339086810899434899)
              ·
                refine ⟨73601720008630216349152349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49067813339086810899434899 73601720008630216349152349)
                ·
                  refine ⟨27600645003236331130932131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73601720008630216349152349 27600645003236331130932131)
                  ·
                    refine ⟨41400967504854496696398197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27600645003236331130932131 41400967504854496696398197)
                    ·
                      refine ⟨3881340703580109065287331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41400967504854496696398197 3881340703580109065287331)
                      ·
                        rfl

theorem cell23_7558884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_7558884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558884 prefixEnd_7558884 := by exact prefixLift 7558884
  have htrace : WordTrace (prefixWord ++ tailWord_7558884) baseStart_7558884 baseEnd_7558884 := by
    simpa [prefixWord, tailWord_7558884, baseEnd_7558884] using wordTrace_append hprefix tailTrace_7558884
  have hstable : (prefixWord ++ tailWord_7558884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558884).length < 2 ^ (prefixWord ++ tailWord_7558884).sum := by decide
  have hdescent : baseEnd_7558884 < baseStart_7558884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558891 : List Nat := [1, 1, 1, 1, 2, 4, 4, 3, 2, 4]
def baseStart_7558891 : Nat := 118140960795 + 7558891 * 2 ^ 59
def prefixEnd_7558891 : Nat := 4983230072969 + 3 ^ 40 * 7558891 * 2
def baseEnd_7558891 : Nat := 1293781432648230179299933

theorem tailTrace_7558891 : CollatzResearch.WordTrace tailWord_7558891 prefixEnd_7558891 1293781432648230179299933 := by
  unfold tailWord_7558891
  simp only [CollatzResearch.WordTrace]
  refine ⟨275695404058436337649668527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183796936038957558433112351 275695404058436337649668527)
  ·
    refine ⟨413543106087654506474502791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275695404058436337649668527 413543106087654506474502791)
    ·
      refine ⟨620314659131481759711754187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413543106087654506474502791 620314659131481759711754187)
      ·
        refine ⟨930471988697222639567631281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620314659131481759711754187 930471988697222639567631281)
        ·
          refine ⟨697853991522916979675723461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 930471988697222639567631281 697853991522916979675723461)
          ·
            refine ⟨130847623410546933689198149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 697853991522916979675723461 130847623410546933689198149)
            ·
              refine ⟨24533929389477550066724653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130847623410546933689198149 24533929389477550066724653)
              ·
                refine ⟨9200223521054081275021745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24533929389477550066724653 9200223521054081275021745)
                ·
                  refine ⟨6900167640790560956266309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9200223521054081275021745 6900167640790560956266309)
                  ·
                    refine ⟨1293781432648230179299933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6900167640790560956266309 1293781432648230179299933)
                    ·
                      rfl

theorem cell23_7558891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2, 4].length) (baseStart_7558891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558891 prefixEnd_7558891 := by exact prefixLift 7558891
  have htrace : WordTrace (prefixWord ++ tailWord_7558891) baseStart_7558891 baseEnd_7558891 := by
    simpa [prefixWord, tailWord_7558891, baseEnd_7558891] using wordTrace_append hprefix tailTrace_7558891
  have hstable : (prefixWord ++ tailWord_7558891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558891).length < 2 ^ (prefixWord ++ tailWord_7558891).sum := by decide
  have hdescent : baseEnd_7558891 < baseStart_7558891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558915 : List Nat := [1, 1, 1, 3, 2, 2, 3, 5, 1, 2, 2]
def baseStart_7558915 : Nat := 118140960795 + 7558915 * 2 ^ 59
def prefixEnd_7558915 : Nat := 4983230072969 + 3 ^ 40 * 7558915 * 2
def baseEnd_7558915 : Nat := 3881356621480398443999689

theorem tailTrace_7558915 : CollatzResearch.WordTrace tailWord_7558915 prefixEnd_7558915 3881356621480398443999689 := by
  unfold tailWord_7558915
  simp only [CollatzResearch.WordTrace]
  refine ⟨275696279410349389748542199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183797519606899593165694799 275696279410349389748542199)
  ·
    refine ⟨413544419115524084622813299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275696279410349389748542199 413544419115524084622813299)
    ·
      refine ⟨620316628673286126934219949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413544419115524084622813299 620316628673286126934219949)
      ·
        refine ⟨232618735752482297600332481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 620316628673286126934219949 232618735752482297600332481)
        ·
          refine ⟨174464051814361723200249361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232618735752482297600332481 174464051814361723200249361)
          ·
            refine ⟨130848038860771292400187021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174464051814361723200249361 130848038860771292400187021)
            ·
              refine ⟨49068014572789234650070133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130848038860771292400187021 49068014572789234650070133)
              ·
                refine ⟨4600126366198990748444075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49068014572789234650070133 4600126366198990748444075)
                ·
                  refine ⟨6900189549298486122666113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4600126366198990748444075 6900189549298486122666113)
                  ·
                    refine ⟨5175142161973864591999585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6900189549298486122666113 5175142161973864591999585)
                    ·
                      refine ⟨3881356621480398443999689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5175142161973864591999585 3881356621480398443999689)
                      ·
                        rfl

theorem cell23_7558915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5, 1, 2, 2].length) (baseStart_7558915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558915 prefixEnd_7558915 := by exact prefixLift 7558915
  have htrace : WordTrace (prefixWord ++ tailWord_7558915) baseStart_7558915 baseEnd_7558915 := by
    simpa [prefixWord, tailWord_7558915, baseEnd_7558915] using wordTrace_append hprefix tailTrace_7558915
  have hstable : (prefixWord ++ tailWord_7558915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558915).length < 2 ^ (prefixWord ++ tailWord_7558915).sum := by decide
  have hdescent : baseEnd_7558915 < baseStart_7558915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558942 : List Nat := [4, 3, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_7558942 : Nat := 118140960795 + 7558942 * 2 ^ 59
def prefixEnd_7558942 : Nat := 4983230072969 + 3 ^ 40 * 7558942 * 2
def baseEnd_7558942 : Nat := 1293790161819356612787355

theorem tailTrace_7558942 : CollatzResearch.WordTrace tailWord_7558942 prefixEnd_7558942 1293790161819356612787355 := by
  unfold tailWord_7558942
  simp only [CollatzResearch.WordTrace]
  refine ⟨34462158022656446669971885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183798176120834382239850053 34462158022656446669971885)
  ·
    refine ⟨12923309258496167501239457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34462158022656446669971885 12923309258496167501239457)
    ·
      refine ⟨9692481943872125625929593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12923309258496167501239457 9692481943872125625929593)
      ·
        refine ⟨7269361457904094219447195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9692481943872125625929593 7269361457904094219447195)
        ·
          refine ⟨10904042186856141329170793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7269361457904094219447195 10904042186856141329170793)
          ·
            refine ⟨8178031640142105996878095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10904042186856141329170793 8178031640142105996878095)
            ·
              refine ⟨12267047460213158995317143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8178031640142105996878095 12267047460213158995317143)
              ·
                refine ⟨18400571190319738492975715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12267047460213158995317143 18400571190319738492975715)
                ·
                  refine ⟨27600856785479607739463573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18400571190319738492975715 27600856785479607739463573)
                  ·
                    refine ⟨1293790161819356612787355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27600856785479607739463573 1293790161819356612787355)
                    ·
                      rfl

theorem cell23_7558942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_7558942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558942 prefixEnd_7558942 := by exact prefixLift 7558942
  have htrace : WordTrace (prefixWord ++ tailWord_7558942) baseStart_7558942 baseEnd_7558942 := by
    simpa [prefixWord, tailWord_7558942, baseEnd_7558942] using wordTrace_append hprefix tailTrace_7558942
  have hstable : (prefixWord ++ tailWord_7558942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558942).length < 2 ^ (prefixWord ++ tailWord_7558942).sum := by decide
  have hdescent : baseEnd_7558942 < baseStart_7558942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558948 : List Nat := [2, 3, 1, 3, 2, 1, 3, 1, 1, 3, 3]
def baseStart_7558948 : Nat := 118140960795 + 7558948 * 2 ^ 59
def prefixEnd_7558948 : Nat := 4983230072969 + 3 ^ 40 * 7558948 * 2
def baseEnd_7558948 : Nat := 3881373566341996814887037

theorem tailTrace_7558948 : CollatzResearch.WordTrace tailWord_7558948 prefixEnd_7558948 3881373566341996814887037 := by
  unfold tailWord_7558948
  simp only [CollatzResearch.WordTrace]
  refine ⟨137848741509614918192246749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183798322012819890922995665 137848741509614918192246749)
  ·
    refine ⟨51693278066105594322092531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137848741509614918192246749 51693278066105594322092531)
    ·
      refine ⟨77539917099158391483138797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51693278066105594322092531 77539917099158391483138797)
      ·
        refine ⟨29077468912184396806177049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77539917099158391483138797 29077468912184396806177049)
        ·
          refine ⟨21808101684138297604632787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29077468912184396806177049 21808101684138297604632787)
          ·
            refine ⟨32712152526207446406949181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21808101684138297604632787 32712152526207446406949181)
            ·
              refine ⟨12267057197327792402605943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32712152526207446406949181 12267057197327792402605943)
              ·
                refine ⟨18400585795991688603908915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12267057197327792402605943 18400585795991688603908915)
                ·
                  refine ⟨27600878693987532905863373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18400585795991688603908915 27600878693987532905863373)
                  ·
                    refine ⟨10350329510245324839698765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27600878693987532905863373 10350329510245324839698765)
                    ·
                      refine ⟨3881373566341996814887037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10350329510245324839698765 3881373566341996814887037)
                      ·
                        rfl

theorem cell23_7558948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_7558948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558948 prefixEnd_7558948 := by exact prefixLift 7558948
  have htrace : WordTrace (prefixWord ++ tailWord_7558948) baseStart_7558948 baseEnd_7558948 := by
    simpa [prefixWord, tailWord_7558948, baseEnd_7558948] using wordTrace_append hprefix tailTrace_7558948
  have hstable : (prefixWord ++ tailWord_7558948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558948).length < 2 ^ (prefixWord ++ tailWord_7558948).sum := by decide
  have hdescent : baseEnd_7558948 < baseStart_7558948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558966 : List Nat := [5, 1, 2, 2, 1, 3, 1, 3, 1, 2, 2]
def baseStart_7558966 : Nat := 118140960795 + 7558966 * 2 ^ 59
def prefixEnd_7558966 : Nat := 4983230072969 + 3 ^ 40 * 7558966 * 2
def baseEnd_7558966 : Nat := 3881382808993777744461955

theorem tailTrace_7558966 : CollatzResearch.WordTrace tailWord_7558966 prefixEnd_7558966 3881382808993777744461955 := by
  unfold tailWord_7558966
  simp only [CollatzResearch.WordTrace]
  refine ⟨17231133720822789091165547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183798759688776416972432501 17231133720822789091165547)
  ·
    refine ⟨25846700581234183636748321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17231133720822789091165547 25846700581234183636748321)
    ·
      refine ⟨19385025435925637727561241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25846700581234183636748321 19385025435925637727561241)
      ·
        refine ⟨14538769076944228295670931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19385025435925637727561241 14538769076944228295670931)
        ·
          refine ⟨21808153615416342443506397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14538769076944228295670931 21808153615416342443506397)
          ·
            refine ⟨8178057605781128416314899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21808153615416342443506397 8178057605781128416314899)
            ·
              refine ⟨12267086408671692624472349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8178057605781128416314899 12267086408671692624472349)
              ·
                refine ⟨4600157403251884734177131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12267086408671692624472349 4600157403251884734177131)
                ·
                  refine ⟨6900236104877827101265697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4600157403251884734177131 6900236104877827101265697)
                  ·
                    refine ⟨5175177078658370325949273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6900236104877827101265697 5175177078658370325949273)
                    ·
                      refine ⟨3881382808993777744461955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5175177078658370325949273 3881382808993777744461955)
                      ·
                        rfl

theorem cell23_7558966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_7558966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558966 prefixEnd_7558966 := by exact prefixLift 7558966
  have htrace : WordTrace (prefixWord ++ tailWord_7558966) baseStart_7558966 baseEnd_7558966 := by
    simpa [prefixWord, tailWord_7558966, baseEnd_7558966] using wordTrace_append hprefix tailTrace_7558966
  have hstable : (prefixWord ++ tailWord_7558966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558966).length < 2 ^ (prefixWord ++ tailWord_7558966).sum := by decide
  have hdescent : baseEnd_7558966 < baseStart_7558966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558982 : List Nat := [6, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3]
def baseStart_7558982 : Nat := 118140960795 + 7558982 * 2 ^ 59
def prefixEnd_7558982 : Nat := 4983230072969 + 3 ^ 40 * 7558982 * 2
def baseEnd_7558982 : Nat := 3881391024684249681861881

theorem tailTrace_7558982 : CollatzResearch.WordTrace tailWord_7558982 prefixEnd_7558982 3881391024684249681861881 := by
  unfold tailWord_7558982
  simp only [CollatzResearch.WordTrace]
  refine ⟨8615585096909583130975975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 183799148734071106794154133 8615585096909583130975975)
  ·
    refine ⟨12923377645364374696463963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8615585096909583130975975 12923377645364374696463963)
    ·
      refine ⟨19385066468046562044695945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12923377645364374696463963 19385066468046562044695945)
      ·
        refine ⟨14538799851034921533521959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19385066468046562044695945 14538799851034921533521959)
        ·
          refine ⟨21808199776552382300282939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14538799851034921533521959 21808199776552382300282939)
          ·
            refine ⟨32712299664828573450424409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21808199776552382300282939 32712299664828573450424409)
            ·
              refine ⟨24534224748621430087818307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32712299664828573450424409 24534224748621430087818307)
              ·
                refine ⟨36801337122932145131727461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24534224748621430087818307 36801337122932145131727461)
                ·
                  refine ⟨6900250710549777212198899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36801337122932145131727461 6900250710549777212198899)
                  ·
                    refine ⟨10350376065824665818298349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6900250710549777212198899 10350376065824665818298349)
                    ·
                      refine ⟨3881391024684249681861881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10350376065824665818298349 3881391024684249681861881)
                      ·
                        rfl

theorem cell23_7558982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_7558982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558982 prefixEnd_7558982 := by exact prefixLift 7558982
  have htrace : WordTrace (prefixWord ++ tailWord_7558982) baseStart_7558982 baseEnd_7558982 := by
    simpa [prefixWord, tailWord_7558982, baseEnd_7558982] using wordTrace_append hprefix tailTrace_7558982
  have hstable : (prefixWord ++ tailWord_7558982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558982).length < 2 ^ (prefixWord ++ tailWord_7558982).sum := by decide
  have hdescent : baseEnd_7558982 < baseStart_7558982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7558999 : List Nat := [1, 1, 3, 2, 6, 1, 2, 1, 2, 1, 3]
def baseStart_7558999 : Nat := 118140960795 + 7558999 * 2 ^ 59
def prefixEnd_7558999 : Nat := 4983230072969 + 3 ^ 40 * 7558999 * 2
def baseEnd_7558999 : Nat := 3881399753855376115349303

theorem tailTrace_7558999 : CollatzResearch.WordTrace tailWord_7558999 prefixEnd_7558999 3881399753855376115349303 := by
  unfold tailWord_7558999
  simp only [CollatzResearch.WordTrace]
  refine ⟨275699343142045072094600051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183799562094696714729733367 275699343142045072094600051)
  ·
    refine ⟨413549014713067608141900077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275699343142045072094600051 413549014713067608141900077)
    ·
      refine ⟨155080880517400353053212529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413549014713067608141900077 155080880517400353053212529)
      ·
        refine ⟨116310660388050264789909397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155080880517400353053212529 116310660388050264789909397)
        ·
          refine ⟨5452062205689856162027003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 116310660388050264789909397 5452062205689856162027003)
          ·
            refine ⟨8178093308534784243040505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5452062205689856162027003 8178093308534784243040505)
            ·
              refine ⟨6133569981401088182280379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8178093308534784243040505 6133569981401088182280379)
              ·
                refine ⟨9200354972101632273420569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6133569981401088182280379 9200354972101632273420569)
                ·
                  refine ⟨6900266229076224205065427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9200354972101632273420569 6900266229076224205065427)
                  ·
                    refine ⟨10350399343614336307598141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6900266229076224205065427 10350399343614336307598141)
                    ·
                      refine ⟨3881399753855376115349303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10350399343614336307598141 3881399753855376115349303)
                      ·
                        rfl

theorem cell23_7558999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 2, 1, 3].length) (baseStart_7558999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7558999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7558999 prefixEnd_7558999 := by exact prefixLift 7558999
  have htrace : WordTrace (prefixWord ++ tailWord_7558999) baseStart_7558999 baseEnd_7558999 := by
    simpa [prefixWord, tailWord_7558999, baseEnd_7558999] using wordTrace_append hprefix tailTrace_7558999
  have hstable : (prefixWord ++ tailWord_7558999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7558999).length < 2 ^ (prefixWord ++ tailWord_7558999).sum := by decide
  have hdescent : baseEnd_7558999 < baseStart_7558999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7558999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559061 : List Nat := [1, 3, 2, 1, 1, 3, 2, 2, 1, 3, 4]
def baseStart_7559061 : Nat := 118140960795 + 7559061 * 2 ^ 59
def prefixEnd_7559061 : Nat := 4983230072969 + 3 ^ 40 * 7559061 * 2
def baseEnd_7559061 : Nat := 3881431589655954872774017

theorem tailTrace_7559061 : CollatzResearch.WordTrace tailWord_7559061 prefixEnd_7559061 3881431589655954872774017 := by
  unfold tailWord_7559061
  simp only [CollatzResearch.WordTrace]
  refine ⟨275701604467820456683357037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183801069645213637788904691 275701604467820456683357037)
  ·
    refine ⟨103388101675432671256258889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275701604467820456683357037 103388101675432671256258889)
    ·
      refine ⟨77541076256574503442194167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103388101675432671256258889 77541076256574503442194167)
      ·
        refine ⟨116311614384861755163291251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77541076256574503442194167 116311614384861755163291251)
        ·
          refine ⟨174467421577292632744936877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116311614384861755163291251 174467421577292632744936877)
          ·
            refine ⟨65425283091484737279351329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174467421577292632744936877 65425283091484737279351329)
            ·
              refine ⟨49068962318613552959513497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65425283091484737279351329 49068962318613552959513497)
              ·
                refine ⟨36801721738960164719635123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49068962318613552959513497 36801721738960164719635123)
                ·
                  refine ⟨55202582608440247079452685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36801721738960164719635123 55202582608440247079452685)
                  ·
                    refine ⟨20700968478165092654794757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55202582608440247079452685 20700968478165092654794757)
                    ·
                      refine ⟨3881431589655954872774017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20700968478165092654794757 3881431589655954872774017)
                      ·
                        rfl

theorem cell23_7559061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_7559061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559061 prefixEnd_7559061 := by exact prefixLift 7559061
  have htrace : WordTrace (prefixWord ++ tailWord_7559061) baseStart_7559061 baseEnd_7559061 := by
    simpa [prefixWord, tailWord_7559061, baseEnd_7559061] using wordTrace_append hprefix tailTrace_7559061
  have hstable : (prefixWord ++ tailWord_7559061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559061).length < 2 ^ (prefixWord ++ tailWord_7559061).sum := by decide
  have hdescent : baseEnd_7559061 < baseStart_7559061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559062 : List Nat := [5, 3, 1, 1, 2, 1, 1, 2, 7]
def baseStart_7559062 : Nat := 118140960795 + 7559062 * 2 ^ 59
def prefixEnd_7559062 : Nat := 4983230072969 + 3 ^ 40 * 7559062 * 2
def baseEnd_7559062 : Nat := 431270233681845485429057

theorem tailTrace_7559062 : CollatzResearch.WordTrace tailWord_7559062 prefixEnd_7559062 431270233681845485429057 := by
  unfold tailWord_7559062
  simp only [CollatzResearch.WordTrace]
  refine ⟨17231352558801052115883965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183801093960544555902762293 17231352558801052115883965)
  ·
    refine ⟨6461757209550394543456487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17231352558801052115883965 6461757209550394543456487)
    ·
      refine ⟨9692635814325591815184731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6461757209550394543456487 9692635814325591815184731)
      ·
        refine ⟨14538953721488387722777097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9692635814325591815184731 14538953721488387722777097)
        ·
          refine ⟨10904215291116290792082823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14538953721488387722777097 10904215291116290792082823)
          ·
            refine ⟨16356322936674436188124235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10904215291116290792082823 16356322936674436188124235)
            ·
              refine ⟨24534484405011654282186353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16356322936674436188124235 24534484405011654282186353)
              ·
                refine ⟨18400863303758740711639765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24534484405011654282186353 18400863303758740711639765)
                ·
                  refine ⟨431270233681845485429057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18400863303758740711639765 431270233681845485429057)
                  ·
                    rfl

theorem cell23_7559062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_7559062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559062 prefixEnd_7559062 := by exact prefixLift 7559062
  have htrace : WordTrace (prefixWord ++ tailWord_7559062) baseStart_7559062 baseEnd_7559062 := by
    simpa [prefixWord, tailWord_7559062, baseEnd_7559062] using wordTrace_append hprefix tailTrace_7559062
  have hstable : (prefixWord ++ tailWord_7559062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559062).length < 2 ^ (prefixWord ++ tailWord_7559062).sum := by decide
  have hdescent : baseEnd_7559062 < baseStart_7559062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559168 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 2, 6, 2]
def baseStart_7559168 : Nat := 118140960795 + 7559168 * 2 ^ 59
def prefixEnd_7559168 : Nat := 4983230072969 + 3 ^ 40 * 7559168 * 2
def baseEnd_7559168 : Nat := 3881486532085985954136025

theorem tailTrace_7559168 : CollatzResearch.WordTrace tailWord_7559168 prefixEnd_7559168 3881486532085985954136025 := by
  unfold tailWord_7559168
  simp only [CollatzResearch.WordTrace]
  refine ⟨137852753539216406978751079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183803671385621875971668105 137852753539216406978751079)
  ·
    refine ⟨206779130308824610468126619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137852753539216406978751079 206779130308824610468126619)
    ·
      refine ⟨310168695463236915702189929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206779130308824610468126619 310168695463236915702189929)
      ·
        refine ⟨232626521597427686776642447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310168695463236915702189929 232626521597427686776642447)
        ·
          refine ⟨348939782396141530164963671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232626521597427686776642447 348939782396141530164963671)
          ·
            refine ⟨523409673594212295247445507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348939782396141530164963671 523409673594212295247445507)
            ·
              refine ⟨785114510391318442871168261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523409673594212295247445507 785114510391318442871168261)
              ·
                refine ⟨147208970698372208038344049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 785114510391318442871168261 147208970698372208038344049)
                ·
                  refine ⟨110406728023779156028758037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147208970698372208038344049 110406728023779156028758037)
                  ·
                    refine ⟨5175315376114647938848033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110406728023779156028758037 5175315376114647938848033)
                    ·
                      refine ⟨3881486532085985954136025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5175315376114647938848033 3881486532085985954136025)
                      ·
                        rfl

theorem cell23_7559168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 2, 6, 2].length) (baseStart_7559168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559168 prefixEnd_7559168 := by exact prefixLift 7559168
  have htrace : WordTrace (prefixWord ++ tailWord_7559168) baseStart_7559168 baseEnd_7559168 := by
    simpa [prefixWord, tailWord_7559168, baseEnd_7559168] using wordTrace_append hprefix tailTrace_7559168
  have hstable : (prefixWord ++ tailWord_7559168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559168).length < 2 ^ (prefixWord ++ tailWord_7559168).sum := by decide
  have hdescent : baseEnd_7559168 < baseStart_7559168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559202 : List Nat := [3, 3, 1, 1, 1, 2, 5, 1, 1, 1, 4]
def baseStart_7559202 : Nat := 118140960795 + 7559202 * 2 ^ 59
def prefixEnd_7559202 : Nat := 4983230072969 + 3 ^ 40 * 7559202 * 2
def baseEnd_7559202 : Nat := 3881503990428238821110869

theorem tailTrace_7559202 : CollatzResearch.WordTrace tailWord_7559202 prefixEnd_7559202 3881503990428238821110869 := by
  unfold tailWord_7559202
  simp only [CollatzResearch.WordTrace]
  refine ⟨68926686790077409441059965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183804498106873091842826573 68926686790077409441059965)
  ·
    refine ⟨25847507546279028540397487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68926686790077409441059965 25847507546279028540397487)
    ·
      refine ⟨38771261319418542810596231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25847507546279028540397487 38771261319418542810596231)
      ·
        refine ⟨58156891979127814215894347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38771261319418542810596231 58156891979127814215894347)
        ·
          refine ⟨87235337968691721323841521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58156891979127814215894347 87235337968691721323841521)
          ·
            refine ⟨65426503476518790992881141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87235337968691721323841521 65426503476518790992881141)
            ·
              refine ⟨6133734700923636655582607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65426503476518790992881141 6133734700923636655582607)
              ·
                refine ⟨9200602051385454983373911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6133734700923636655582607 9200602051385454983373911)
                ·
                  refine ⟨13800903077078182475060867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9200602051385454983373911 13800903077078182475060867)
                  ·
                    refine ⟨20701354615617273712591301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13800903077078182475060867 20701354615617273712591301)
                    ·
                      refine ⟨3881503990428238821110869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20701354615617273712591301 3881503990428238821110869)
                      ·
                        rfl

theorem cell23_7559202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_7559202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559202 prefixEnd_7559202 := by exact prefixLift 7559202
  have htrace : WordTrace (prefixWord ++ tailWord_7559202) baseStart_7559202 baseEnd_7559202 := by
    simpa [prefixWord, tailWord_7559202, baseEnd_7559202] using wordTrace_append hprefix tailTrace_7559202
  have hstable : (prefixWord ++ tailWord_7559202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559202).length < 2 ^ (prefixWord ++ tailWord_7559202).sum := by decide
  have hdescent : baseEnd_7559202 < baseStart_7559202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559205 : List Nat := [1, 3, 1, 2, 2, 5, 1, 1, 1, 1, 5]
def baseStart_7559205 : Nat := 118140960795 + 7559205 * 2 ^ 59
def prefixEnd_7559205 : Nat := 4983230072969 + 3 ^ 40 * 7559205 * 2
def baseEnd_7559205 : Nat := 3881505530870202309373355

theorem tailTrace_7559205 : CollatzResearch.WordTrace tailWord_7559205 prefixEnd_7559205 3881505530870202309373355 := by
  unfold tailWord_7559205
  simp only [CollatzResearch.WordTrace]
  refine ⟨275706856579298769276599069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183804571052865846184399379 275706856579298769276599069)
  ·
    refine ⟨103390071217237038478724651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275706856579298769276599069 103390071217237038478724651)
    ·
      refine ⟨155085106825855557718086977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103390071217237038478724651 155085106825855557718086977)
      ·
        refine ⟨116313830119391668288565233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155085106825855557718086977 116313830119391668288565233)
        ·
          refine ⟨87235372589543751216423925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116313830119391668288565233 87235372589543751216423925)
          ·
            refine ⟨8178316180269726676539743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87235372589543751216423925 8178316180269726676539743)
            ·
              refine ⟨12267474270404590014809615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8178316180269726676539743 12267474270404590014809615)
              ·
                refine ⟨18401211405606885022214423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12267474270404590014809615 18401211405606885022214423)
                ·
                  refine ⟨27601817108410327533321635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18401211405606885022214423 27601817108410327533321635)
                  ·
                    refine ⟨41402725662615491299982453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27601817108410327533321635 41402725662615491299982453)
                    ·
                      refine ⟨3881505530870202309373355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41402725662615491299982453 3881505530870202309373355)
                      ·
                        rfl

theorem cell23_7559205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_7559205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559205 prefixEnd_7559205 := by exact prefixLift 7559205
  have htrace : WordTrace (prefixWord ++ tailWord_7559205) baseStart_7559205 baseEnd_7559205 := by
    simpa [prefixWord, tailWord_7559205, baseEnd_7559205] using wordTrace_append hprefix tailTrace_7559205
  have hstable : (prefixWord ++ tailWord_7559205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559205).length < 2 ^ (prefixWord ++ tailWord_7559205).sum := by decide
  have hdescent : baseEnd_7559205 < baseStart_7559205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559208 : List Nat := [2, 1, 5, 3, 12]
def baseStart_7559208 : Nat := 118140960795 + 7559208 * 2 ^ 59
def prefixEnd_7559208 : Nat := 4983230072969 + 3 ^ 40 * 7559208 * 2
def baseEnd_7559208 : Nat := 5324426709618883124329

theorem tailTrace_7559208 : CollatzResearch.WordTrace tailWord_7559208 prefixEnd_7559208 5324426709618883124329 := by
  unfold tailWord_7559208
  simp only [CollatzResearch.WordTrace]
  refine ⟨137853482999143950394479139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183804643998858600525972185 137853482999143950394479139)
  ·
    refine ⟨206780224498715925591718709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137853482999143950394479139 206780224498715925591718709)
    ·
      refine ⟨19385646046754618024223629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206780224498715925591718709 19385646046754618024223629)
      ·
        refine ⟨7269617267532981759083861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19385646046754618024223629 7269617267532981759083861)
        ·
          refine ⟨5324426709618883124329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7269617267532981759083861 5324426709618883124329)
          ·
            rfl

theorem cell23_7559208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 12].length) (baseStart_7559208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559208 prefixEnd_7559208 := by exact prefixLift 7559208
  have htrace : WordTrace (prefixWord ++ tailWord_7559208) baseStart_7559208 baseEnd_7559208 := by
    simpa [prefixWord, tailWord_7559208, baseEnd_7559208] using wordTrace_append hprefix tailTrace_7559208
  have hstable : (prefixWord ++ tailWord_7559208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559208).length < 2 ^ (prefixWord ++ tailWord_7559208).sum := by decide
  have hdescent : baseEnd_7559208 < baseStart_7559208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559211 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 6]
def baseStart_7559211 : Nat := 118140960795 + 7559211 * 2 ^ 59
def prefixEnd_7559211 : Nat := 4983230072969 + 3 ^ 40 * 7559211 * 2
def baseEnd_7559211 : Nat := 3881508611754129285898327

theorem tailTrace_7559211 : CollatzResearch.WordTrace tailWord_7559211 prefixEnd_7559211 3881508611754129285898327 := by
  unfold tailWord_7559211
  simp only [CollatzResearch.WordTrace]
  refine ⟨275707075417277032301317487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183804716944851354867544991 275707075417277032301317487)
  ·
    refine ⟨413560613125915548451976231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275707075417277032301317487 413560613125915548451976231)
    ·
      refine ⟨620340919688873322677964347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413560613125915548451976231 620340919688873322677964347)
      ·
        refine ⟨930511379533309984016946521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620340919688873322677964347 930511379533309984016946521)
        ·
          refine ⟨697883534649982488012709891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 930511379533309984016946521 697883534649982488012709891)
          ·
            refine ⟨1046825301974973732019064837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697883534649982488012709891 1046825301974973732019064837)
            ·
              refine ⟨196279744120307574753574657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1046825301974973732019064837 196279744120307574753574657)
              ·
                refine ⟨147209808090230681065180993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196279744120307574753574657 147209808090230681065180993)
                ·
                  refine ⟨110407356067673010798885745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147209808090230681065180993 110407356067673010798885745)
                  ·
                    refine ⟨82805517050754758099164309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110407356067673010798885745 82805517050754758099164309)
                    ·
                      refine ⟨3881508611754129285898327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82805517050754758099164309 3881508611754129285898327)
                      ·
                        rfl

theorem cell23_7559211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 6].length) (baseStart_7559211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559211 prefixEnd_7559211 := by exact prefixLift 7559211
  have htrace : WordTrace (prefixWord ++ tailWord_7559211) baseStart_7559211 baseEnd_7559211 := by
    simpa [prefixWord, tailWord_7559211, baseEnd_7559211] using wordTrace_append hprefix tailTrace_7559211
  have hstable : (prefixWord ++ tailWord_7559211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559211).length < 2 ^ (prefixWord ++ tailWord_7559211).sum := by decide
  have hdescent : baseEnd_7559211 < baseStart_7559211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559225 : List Nat := [1, 2, 1, 5, 3, 2, 1, 8]
def baseStart_7559225 : Nat := 118140960795 + 7559225 * 2 ^ 59
def prefixEnd_7559225 : Nat := 4983230072969 + 3 ^ 40 * 7559225 * 2
def baseEnd_7559225 : Nat := 143759844462344156708269

theorem tailTrace_7559225 : CollatzResearch.WordTrace tailWord_7559225 prefixEnd_7559225 143759844462344156708269 := by
  unfold tailWord_7559225
  simp only [CollatzResearch.WordTrace]
  refine ⟨275707586039226312692327129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183805057359484208461551419 275707586039226312692327129)
  ·
    refine ⟨206780689529419734519245347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275707586039226312692327129 206780689529419734519245347)
    ·
      refine ⟨310171034294129601778868021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206780689529419734519245347 310171034294129601778868021)
      ·
        refine ⟨29078534465074650166768877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 310171034294129601778868021 29078534465074650166768877)
        ·
          refine ⟨10904450424402993812538329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29078534465074650166768877 10904450424402993812538329)
          ·
            refine ⟨8178337818302245359403747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10904450424402993812538329 8178337818302245359403747)
            ·
              refine ⟨12267506727453368039105621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8178337818302245359403747 12267506727453368039105621)
              ·
                refine ⟨143759844462344156708269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12267506727453368039105621 143759844462344156708269)
                ·
                  rfl

theorem cell23_7559225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 8].length) (baseStart_7559225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559225 prefixEnd_7559225 := by exact prefixLift 7559225
  have htrace : WordTrace (prefixWord ++ tailWord_7559225) baseStart_7559225 baseEnd_7559225 := by
    simpa [prefixWord, tailWord_7559225, baseEnd_7559225] using wordTrace_append hprefix tailTrace_7559225
  have hstable : (prefixWord ++ tailWord_7559225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559225).length < 2 ^ (prefixWord ++ tailWord_7559225).sum := by decide
  have hdescent : baseEnd_7559225 < baseStart_7559225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559268 : List Nat := [2, 3, 1, 1, 2, 1, 3, 2, 2, 6]
def baseStart_7559268 : Nat := 118140960795 + 7559268 * 2 ^ 59
def prefixEnd_7559268 : Nat := 4983230072969 + 3 ^ 40 * 7559268 * 2
def baseEnd_7559268 : Nat := 1293845960050478520961855

theorem tailTrace_7559268 : CollatzResearch.WordTrace tailWord_7559268 prefixEnd_7559268 1293845960050478520961855 := by
  unfold tailWord_7559268
  simp only [CollatzResearch.WordTrace]
  refine ⟨137854577189035265518071229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183806102918713687357428305 137854577189035265518071229)
  ·
    refine ⟨51695466445888224569276711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137854577189035265518071229 51695466445888224569276711)
    ·
      refine ⟨77543199668832336853915067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51695466445888224569276711 77543199668832336853915067)
      ·
        refine ⟨116314799503248505280872601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77543199668832336853915067 116314799503248505280872601)
        ·
          refine ⟨87236099627436378960654451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116314799503248505280872601 87236099627436378960654451)
          ·
            refine ⟨130854149441154568440981677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87236099627436378960654451 130854149441154568440981677)
            ·
              refine ⟨49070306040432963165368129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130854149441154568440981677 49070306040432963165368129)
              ·
                refine ⟨36802729530324722374026097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49070306040432963165368129 36802729530324722374026097)
                ·
                  refine ⟨27602047147743541780519573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36802729530324722374026097 27602047147743541780519573)
                  ·
                    refine ⟨1293845960050478520961855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27602047147743541780519573 1293845960050478520961855)
                    ·
                      rfl

theorem cell23_7559268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_7559268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559268 prefixEnd_7559268 := by exact prefixLift 7559268
  have htrace : WordTrace (prefixWord ++ tailWord_7559268) baseStart_7559268 baseEnd_7559268 := by
    simpa [prefixWord, tailWord_7559268, baseEnd_7559268] using wordTrace_append hprefix tailTrace_7559268
  have hstable : (prefixWord ++ tailWord_7559268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559268).length < 2 ^ (prefixWord ++ tailWord_7559268).sum := by decide
  have hdescent : baseEnd_7559268 < baseStart_7559268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559269 : List Nat := [1, 3, 1, 3, 2, 4, 1, 2, 2, 1, 3]
def baseStart_7559269 : Nat := 118140960795 + 7559269 * 2 ^ 59
def prefixEnd_7559269 : Nat := 4983230072969 + 3 ^ 40 * 7559269 * 2
def baseEnd_7559269 : Nat := 3881538393632090058973061

theorem tailTrace_7559269 : CollatzResearch.WordTrace tailWord_7559269 prefixEnd_7559269 3881538393632090058973061 := by
  unfold tailWord_7559269
  simp only [CollatzResearch.WordTrace]
  refine ⟨275709190851066908206928861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183806127234044605471285907 275709190851066908206928861)
  ·
    refine ⟨103390946569150090577598323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275709190851066908206928861 103390946569150090577598323)
    ·
      refine ⟨155086419853725135866397485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103390946569150090577598323 155086419853725135866397485)
      ·
        refine ⟨58157407445146925949899057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155086419853725135866397485 58157407445146925949899057)
        ·
          refine ⟨43618055583860194462424293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58157407445146925949899057 43618055583860194462424293)
          ·
            refine ⟨8178385421973786461704555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43618055583860194462424293 8178385421973786461704555)
            ·
              refine ⟨12267578132960679692556833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8178385421973786461704555 12267578132960679692556833)
              ·
                refine ⟨9200683599720509769417625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12267578132960679692556833 9200683599720509769417625)
                ·
                  refine ⟨6900512699790382327063219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9200683599720509769417625 6900512699790382327063219)
                  ·
                    refine ⟨10350769049685573490594829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6900512699790382327063219 10350769049685573490594829)
                    ·
                      refine ⟨3881538393632090058973061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10350769049685573490594829 3881538393632090058973061)
                      ·
                        rfl

theorem cell23_7559269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_7559269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559269 prefixEnd_7559269 := by exact prefixLift 7559269
  have htrace : WordTrace (prefixWord ++ tailWord_7559269) baseStart_7559269 baseEnd_7559269 := by
    simpa [prefixWord, tailWord_7559269, baseEnd_7559269] using wordTrace_append hprefix tailTrace_7559269
  have hstable : (prefixWord ++ tailWord_7559269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559269).length < 2 ^ (prefixWord ++ tailWord_7559269).sum := by decide
  have hdescent : baseEnd_7559269 < baseStart_7559269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559286 : List Nat := [5, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3]
def baseStart_7559286 : Nat := 118140960795 + 7559286 * 2 ^ 59
def prefixEnd_7559286 : Nat := 4983230072969 + 3 ^ 40 * 7559286 * 2
def baseEnd_7559286 : Nat := 3881547122803216492460483

theorem tailTrace_7559286 : CollatzResearch.WordTrace tailWord_7559286 prefixEnd_7559286 3881547122803216492460483 := by
  unfold tailWord_7559286
  simp only [CollatzResearch.WordTrace]
  refine ⟨17231863180750332506893607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183806540594670213406865141 17231863180750332506893607)
  ·
    refine ⟨25847794771125498760340411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17231863180750332506893607 25847794771125498760340411)
    ·
      refine ⟨38771692156688248140510617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25847794771125498760340411 38771692156688248140510617)
      ·
        refine ⟨29078769117516186105382963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38771692156688248140510617 29078769117516186105382963)
        ·
          refine ⟨43618153676274279158074445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29078769117516186105382963 43618153676274279158074445)
          ·
            refine ⟨16356807628602854684277917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43618153676274279158074445 16356807628602854684277917)
            ·
              refine ⟨6133802860726070506604219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16356807628602854684277917 6133802860726070506604219)
              ·
                refine ⟨9200704291089105759906329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6133802860726070506604219 9200704291089105759906329)
                ·
                  refine ⟨6900528218316829319929747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9200704291089105759906329 6900528218316829319929747)
                  ·
                    refine ⟨10350792327475243979894621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6900528218316829319929747 10350792327475243979894621)
                    ·
                      refine ⟨3881547122803216492460483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10350792327475243979894621 3881547122803216492460483)
                      ·
                        rfl

theorem cell23_7559286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_7559286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559286 prefixEnd_7559286 := by exact prefixLift 7559286
  have htrace : WordTrace (prefixWord ++ tailWord_7559286) baseStart_7559286 baseEnd_7559286 := by
    simpa [prefixWord, tailWord_7559286, baseEnd_7559286] using wordTrace_append hprefix tailTrace_7559286
  have hstable : (prefixWord ++ tailWord_7559286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559286).length < 2 ^ (prefixWord ++ tailWord_7559286).sum := by decide
  have hdescent : baseEnd_7559286 < baseStart_7559286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559292 : List Nat := [2, 2, 2, 1, 1, 4, 3, 1, 1, 4, 2]
def baseStart_7559292 : Nat := 118140960795 + 7559292 * 2 ^ 59
def prefixEnd_7559292 : Nat := 4983230072969 + 3 ^ 40 * 7559292 * 2
def baseEnd_7559292 : Nat := 3881550203687143468985455

theorem tailTrace_7559292 : CollatzResearch.WordTrace tailWord_7559292 prefixEnd_7559292 3881550203687143468985455 := by
  unfold tailWord_7559292
  simp only [CollatzResearch.WordTrace]
  refine ⟨137855014864991791567508065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183806686486655722090010753 137855014864991791567508065)
  ·
    refine ⟨103391261148743843675631049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137855014864991791567508065 103391261148743843675631049)
    ·
      refine ⟨77543445861557882756723287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103391261148743843675631049 77543445861557882756723287)
      ·
        refine ⟨116315168792336824135084931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77543445861557882756723287 116315168792336824135084931)
        ·
          refine ⟨174472753188505236202627397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116315168792336824135084931 174472753188505236202627397)
          ·
            refine ⟨32713641222844731787992637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174472753188505236202627397 32713641222844731787992637)
            ·
              refine ⟨12267615458566774420497239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32713641222844731787992637 12267615458566774420497239)
              ·
                refine ⟨18401423187850161630745859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12267615458566774420497239 18401423187850161630745859)
                ·
                  refine ⟨27602134781775242446118789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18401423187850161630745859 27602134781775242446118789)
                  ·
                    refine ⟨5175400271582857958647273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27602134781775242446118789 5175400271582857958647273)
                    ·
                      refine ⟨3881550203687143468985455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5175400271582857958647273 3881550203687143468985455)
                      ·
                        rfl

theorem cell23_7559292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 1, 4, 2].length) (baseStart_7559292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559292 prefixEnd_7559292 := by exact prefixLift 7559292
  have htrace : WordTrace (prefixWord ++ tailWord_7559292) baseStart_7559292 baseEnd_7559292 := by
    simpa [prefixWord, tailWord_7559292, baseEnd_7559292] using wordTrace_append hprefix tailTrace_7559292
  have hstable : (prefixWord ++ tailWord_7559292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559292).length < 2 ^ (prefixWord ++ tailWord_7559292).sum := by decide
  have hdescent : baseEnd_7559292 < baseStart_7559292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559332 : List Nat := [2, 3, 1, 2, 4, 2, 1, 1, 7]
def baseStart_7559332 : Nat := 118140960795 + 7559332 * 2 ^ 59
def prefixEnd_7559332 : Nat := 4983230072969 + 3 ^ 40 * 7559332 * 2
def baseEnd_7559332 : Nat := 431285638101480368053919

theorem tailTrace_7559332 : CollatzResearch.WordTrace tailWord_7559332 prefixEnd_7559332 431285638101480368053919 := by
  unfold tailWord_7559332
  simp only [CollatzResearch.WordTrace]
  refine ⟨137855744324919334983236125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183807659099892446644314833 137855744324919334983236125)
  ·
    refine ⟨51695904121844750618713547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137855744324919334983236125 51695904121844750618713547)
    ·
      refine ⟨77543856182767125928070321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51695904121844750618713547 77543856182767125928070321)
      ·
        refine ⟨58157892137075344446052741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77543856182767125928070321 58157892137075344446052741)
        ·
          refine ⟨10904604775701627083634889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58157892137075344446052741 10904604775701627083634889)
          ·
            refine ⟨8178453581776220312726167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10904604775701627083634889 8178453581776220312726167)
            ·
              refine ⟨12267680372664330469089251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8178453581776220312726167 12267680372664330469089251)
              ·
                refine ⟨18401520558996495703633877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12267680372664330469089251 18401520558996495703633877)
                ·
                  refine ⟨431285638101480368053919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18401520558996495703633877 431285638101480368053919)
                  ·
                    rfl

theorem cell23_7559332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 7].length) (baseStart_7559332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559332 prefixEnd_7559332 := by exact prefixLift 7559332
  have htrace : WordTrace (prefixWord ++ tailWord_7559332) baseStart_7559332 baseEnd_7559332 := by
    simpa [prefixWord, tailWord_7559332, baseEnd_7559332] using wordTrace_append hprefix tailTrace_7559332
  have hstable : (prefixWord ++ tailWord_7559332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559332).length < 2 ^ (prefixWord ++ tailWord_7559332).sum := by decide
  have hdescent : baseEnd_7559332 < baseStart_7559332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559365 : List Nat := [1, 3, 1, 1, 1, 1, 5, 3, 2, 1, 4]
def baseStart_7559365 : Nat := 118140960795 + 7559365 * 2 ^ 59
def prefixEnd_7559365 : Nat := 4983230072969 + 3 ^ 40 * 7559365 * 2
def baseEnd_7559365 : Nat := 3881587687774921683372619

theorem tailTrace_7559365 : CollatzResearch.WordTrace tailWord_7559365 prefixEnd_7559365 3881587687774921683372619 := by
  unfold tailWord_7559365
  simp only [CollatzResearch.WordTrace]
  refine ⟨275712692258719116602423549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183808461505812744401615699 275712692258719116602423549)
  ·
    refine ⟨103392259597019668725908831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275712692258719116602423549 103392259597019668725908831)
    ·
      refine ⟨155088389395529503088863247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103392259597019668725908831 155088389395529503088863247)
      ·
        refine ⟨232632584093294254633294871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155088389395529503088863247 232632584093294254633294871)
        ·
          refine ⟨348948876139941381949942307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232632584093294254633294871 348948876139941381949942307)
          ·
            refine ⟨523423314209912072924913461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348948876139941381949942307 523423314209912072924913461)
            ·
              refine ⟨49070935707179256836710637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 523423314209912072924913461 49070935707179256836710637)
              ·
                refine ⟨18401600890192221313766489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49070935707179256836710637 18401600890192221313766489)
                ·
                  refine ⟨13801200667644165985324867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18401600890192221313766489 13801200667644165985324867)
                  ·
                    refine ⟨20701801001466248977987301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13801200667644165985324867 20701801001466248977987301)
                    ·
                      refine ⟨3881587687774921683372619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20701801001466248977987301 3881587687774921683372619)
                      ·
                        rfl

theorem cell23_7559365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_7559365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559365 prefixEnd_7559365 := by exact prefixLift 7559365
  have htrace : WordTrace (prefixWord ++ tailWord_7559365) baseStart_7559365 baseEnd_7559365 := by
    simpa [prefixWord, tailWord_7559365, baseEnd_7559365] using wordTrace_append hprefix tailTrace_7559365
  have hstable : (prefixWord ++ tailWord_7559365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559365).length < 2 ^ (prefixWord ++ tailWord_7559365).sum := by decide
  have hdescent : baseEnd_7559365 < baseStart_7559365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559399 : List Nat := [1, 1, 5, 3, 1, 2, 1, 1, 2, 4, 2]
def baseStart_7559399 : Nat := 118140960795 + 7559399 * 2 ^ 59
def prefixEnd_7559399 : Nat := 4983230072969 + 3 ^ 40 * 7559399 * 2
def baseEnd_7559399 : Nat := 3881605146117174550347463

theorem tailTrace_7559399 : CollatzResearch.WordTrace tailWord_7559399 prefixEnd_7559399 3881605146117174550347463 := by
  unfold tailWord_7559399
  simp only [CollatzResearch.WordTrace]
  refine ⟨275713932340595940409161251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183809288227063960272774167 275713932340595940409161251)
  ·
    refine ⟨413570898510893910613741877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275713932340595940409161251 413570898510893910613741877)
    ·
      refine ⟨38772271735396304120038301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 413570898510893910613741877 38772271735396304120038301)
      ·
        refine ⟨14539601900773614045014363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38772271735396304120038301 14539601900773614045014363)
        ·
          refine ⟨21809402851160421067521545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14539601900773614045014363 21809402851160421067521545)
          ·
            refine ⟨16357052138370315800641159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21809402851160421067521545 16357052138370315800641159)
            ·
              refine ⟨24535578207555473700961739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16357052138370315800641159 24535578207555473700961739)
              ·
                refine ⟨36803367311333210551442609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24535578207555473700961739 36803367311333210551442609)
                ·
                  refine ⟨27602525483499907913581957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36803367311333210551442609 27602525483499907913581957)
                  ·
                    refine ⟨5175473528156232733796617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27602525483499907913581957 5175473528156232733796617)
                    ·
                      refine ⟨3881605146117174550347463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5175473528156232733796617 3881605146117174550347463)
                      ·
                        rfl

theorem cell23_7559399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_7559399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559399 prefixEnd_7559399 := by exact prefixLift 7559399
  have htrace : WordTrace (prefixWord ++ tailWord_7559399) baseStart_7559399 baseEnd_7559399 := by
    simpa [prefixWord, tailWord_7559399, baseEnd_7559399] using wordTrace_append hprefix tailTrace_7559399
  have hstable : (prefixWord ++ tailWord_7559399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559399).length < 2 ^ (prefixWord ++ tailWord_7559399).sum := by decide
  have hdescent : baseEnd_7559399 < baseStart_7559399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559426 : List Nat := [3, 4, 1, 1, 2, 1, 1, 5, 1, 4]
def baseStart_7559426 : Nat := 118140960795 + 7559426 * 2 ^ 59
def prefixEnd_7559426 : Nat := 4983230072969 + 3 ^ 40 * 7559426 * 2
def baseEnd_7559426 : Nat := 1293873003364948648236613

theorem tailTrace_7559426 : CollatzResearch.WordTrace tailWord_7559426 prefixEnd_7559426 1293873003364948648236613 := by
  unfold tailWord_7559426
  simp only [CollatzResearch.WordTrace]
  refine ⟨68928729277874531005098533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183809944740998749346929421 68928729277874531005098533)
  ·
    refine ⟨12924136739601474563455975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68928729277874531005098533 12924136739601474563455975)
    ·
      refine ⟨19386205109402211845183963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12924136739601474563455975 19386205109402211845183963)
      ·
        refine ⟨29079307664103317767775945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19386205109402211845183963 29079307664103317767775945)
        ·
          refine ⟨21809480748077488325831959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29079307664103317767775945 21809480748077488325831959)
          ·
            refine ⟨32714221122116232488747939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21809480748077488325831959 32714221122116232488747939)
            ·
              refine ⟨49071331683174348733121909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32714221122116232488747939 49071331683174348733121909)
              ·
                refine ⟨4600437345297595193730179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49071331683174348733121909 4600437345297595193730179)
                ·
                  refine ⟨6900656017946392790595269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4600437345297595193730179 6900656017946392790595269)
                  ·
                    refine ⟨1293873003364948648236613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6900656017946392790595269 1293873003364948648236613)
                    ·
                      rfl

theorem cell23_7559426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_7559426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559426 prefixEnd_7559426 := by exact prefixLift 7559426
  have htrace : WordTrace (prefixWord ++ tailWord_7559426) baseStart_7559426 baseEnd_7559426 := by
    simpa [prefixWord, tailWord_7559426, baseEnd_7559426] using wordTrace_append hprefix tailTrace_7559426
  have hstable : (prefixWord ++ tailWord_7559426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559426).length < 2 ^ (prefixWord ++ tailWord_7559426).sum := by decide
  have hdescent : baseEnd_7559426 < baseStart_7559426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559475 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 5]
def baseStart_7559475 : Nat := 118140960795 + 7559475 * 2 ^ 59
def prefixEnd_7559475 : Nat := 4983230072969 + 3 ^ 40 * 7559475 * 2
def baseEnd_7559475 : Nat := 3881644170646916252997113

theorem tailTrace_7559475 : CollatzResearch.WordTrace tailWord_7559475 prefixEnd_7559475 3881644170646916252997113 := by
  unfold tailWord_7559475
  simp only [CollatzResearch.WordTrace]
  refine ⟨275716704288320605388927879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183811136192213736925951919 275716704288320605388927879)
  ·
    refine ⟨413575056432480908083391819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275716704288320605388927879 413575056432480908083391819)
    ·
      refine ⟨620362584648721362125087729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413575056432480908083391819 620362584648721362125087729)
      ·
        refine ⟨465271938486541021593815797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 620362584648721362125087729 465271938486541021593815797)
        ·
          refine ⟨43619244233113220774420231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 465271938486541021593815797 43619244233113220774420231)
          ·
            refine ⟨65428866349669831161630347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43619244233113220774420231 65428866349669831161630347)
            ·
              refine ⟨98143299524504746742445521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65428866349669831161630347 98143299524504746742445521)
              ·
                refine ⟨73607474643378560056834141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98143299524504746742445521 73607474643378560056834141)
                ·
                  refine ⟨27602802991266960021312803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73607474643378560056834141 27602802991266960021312803)
                  ·
                    refine ⟨41404204486900440031969205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27602802991266960021312803 41404204486900440031969205)
                    ·
                      refine ⟨3881644170646916252997113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41404204486900440031969205 3881644170646916252997113)
                      ·
                        rfl

theorem cell23_7559475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 5].length) (baseStart_7559475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559475 prefixEnd_7559475 := by exact prefixLift 7559475
  have htrace : WordTrace (prefixWord ++ tailWord_7559475) baseStart_7559475 baseEnd_7559475 := by
    simpa [prefixWord, tailWord_7559475, baseEnd_7559475] using wordTrace_append hprefix tailTrace_7559475
  have hstable : (prefixWord ++ tailWord_7559475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559475).length < 2 ^ (prefixWord ++ tailWord_7559475).sum := by decide
  have hdescent : baseEnd_7559475 < baseStart_7559475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559482 : List Nat := [3, 1, 1, 1, 4, 2, 1, 2, 4, 4]
def baseStart_7559482 : Nat := 118140960795 + 7559482 * 2 ^ 59
def prefixEnd_7559482 : Nat := 4983230072969 + 3 ^ 40 * 7559482 * 2
def baseEnd_7559482 : Nat := 1293882588337165908536527

theorem tailTrace_7559482 : CollatzResearch.WordTrace tailWord_7559482 prefixEnd_7559482 1293882588337165908536527 := by
  unfold tailWord_7559482
  simp only [CollatzResearch.WordTrace]
  refine ⟨68929239899823811396108175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183811306399530163722955133 68929239899823811396108175)
  ·
    refine ⟨103393859849735717094162263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68929239899823811396108175 103393859849735717094162263)
    ·
      refine ⟨155090789774603575641243395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103393859849735717094162263 155090789774603575641243395)
      ·
        refine ⟨232636184661905363461865093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155090789774603575641243395 232636184661905363461865093)
        ·
          refine ⟨43619284624107255649099705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232636184661905363461865093 43619284624107255649099705)
          ·
            refine ⟨32714463468080441736824779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43619284624107255649099705 32714463468080441736824779)
            ·
              refine ⟨49071695202120662605237169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32714463468080441736824779 49071695202120662605237169)
              ·
                refine ⟨36803771401590496953927877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49071695202120662605237169 36803771401590496953927877)
                ·
                  refine ⟨6900707137798218178861477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36803771401590496953927877 6900707137798218178861477)
                  ·
                    refine ⟨1293882588337165908536527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6900707137798218178861477 1293882588337165908536527)
                    ·
                      rfl

theorem cell23_7559482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 4, 4].length) (baseStart_7559482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559482 prefixEnd_7559482 := by exact prefixLift 7559482
  have htrace : WordTrace (prefixWord ++ tailWord_7559482) baseStart_7559482 baseEnd_7559482 := by
    simpa [prefixWord, tailWord_7559482, baseEnd_7559482] using wordTrace_append hprefix tailTrace_7559482
  have hstable : (prefixWord ++ tailWord_7559482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559482).length < 2 ^ (prefixWord ++ tailWord_7559482).sum := by decide
  have hdescent : baseEnd_7559482 < baseStart_7559482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559506 : List Nat := [3, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2]
def baseStart_7559506 : Nat := 118140960795 + 7559506 * 2 ^ 59
def prefixEnd_7559506 : Nat := 4983230072969 + 3 ^ 40 * 7559506 * 2
def baseEnd_7559506 : Nat := 3881660088547205631709471

theorem tailTrace_7559506 : CollatzResearch.WordTrace tailWord_7559506 prefixEnd_7559506 3881660088547205631709471 := by
  unfold tailWord_7559506
  simp only [CollatzResearch.WordTrace]
  refine ⟨68929458737802074420826593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183811889967472198455537581 68929458737802074420826593)
  ·
    refine ⟨51697094053351555815619945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68929458737802074420826593 51697094053351555815619945)
    ·
      refine ⟨38772820540013666861714959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51697094053351555815619945 38772820540013666861714959)
      ·
        refine ⟨58159230810020500292572439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38772820540013666861714959 58159230810020500292572439)
        ·
          refine ⟨87238846215030750438858659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58159230810020500292572439 87238846215030750438858659)
          ·
            refine ⟨130858269322546125658287989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87238846215030750438858659 130858269322546125658287989)
            ·
              refine ⟨12267962748988699280464499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130858269322546125658287989 12267962748988699280464499)
              ·
                refine ⟨18401944123483048920696749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12267962748988699280464499 18401944123483048920696749)
                ·
                  refine ⟨6900729046306143345261281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18401944123483048920696749 6900729046306143345261281)
                  ·
                    refine ⟨5175546784729607508945961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6900729046306143345261281 5175546784729607508945961)
                    ·
                      refine ⟨3881660088547205631709471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5175546784729607508945961 3881660088547205631709471)
                      ·
                        rfl

theorem cell23_7559506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_7559506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559506 prefixEnd_7559506 := by exact prefixLift 7559506
  have htrace : WordTrace (prefixWord ++ tailWord_7559506) baseStart_7559506 baseEnd_7559506 := by
    simpa [prefixWord, tailWord_7559506, baseEnd_7559506] using wordTrace_append hprefix tailTrace_7559506
  have hstable : (prefixWord ++ tailWord_7559506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559506).length < 2 ^ (prefixWord ++ tailWord_7559506).sum := by decide
  have hdescent : baseEnd_7559506 < baseStart_7559506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559535 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 5]
def baseStart_7559535 : Nat := 118140960795 + 7559535 * 2 ^ 59
def prefixEnd_7559535 : Nat := 4983230072969 + 3 ^ 40 * 7559535 * 2
def baseEnd_7559535 : Nat := 3881674979486186018246837

theorem tailTrace_7559535 : CollatzResearch.WordTrace tailWord_7559535 prefixEnd_7559535 3881674979486186018246837 := by
  unfold tailWord_7559535
  simp only [CollatzResearch.WordTrace]
  refine ⟨275718892668103235636112059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183812595112068823757408039 275718892668103235636112059)
  ·
    refine ⟨413578339002154853454168089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275718892668103235636112059 413578339002154853454168089)
    ·
      refine ⟨310183754251616140090626067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413578339002154853454168089 310183754251616140090626067)
      ·
        refine ⟨465275631377424210135939101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310183754251616140090626067 465275631377424210135939101)
        ·
          refine ⟨174478361766534078800977163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 465275631377424210135939101 174478361766534078800977163)
          ·
            refine ⟨261717542649801118201465745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174478361766534078800977163 261717542649801118201465745)
            ·
              refine ⟨196288156987350838651099309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261717542649801118201465745 196288156987350838651099309)
              ·
                refine ⟨73608058870256564494162241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196288156987350838651099309 73608058870256564494162241)
                ·
                  refine ⟨55206044152692423370621681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73608058870256564494162241 55206044152692423370621681)
                  ·
                    refine ⟨41404533114519317527966261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55206044152692423370621681 41404533114519317527966261)
                    ·
                      refine ⟨3881674979486186018246837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41404533114519317527966261 3881674979486186018246837)
                      ·
                        rfl

theorem cell23_7559535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 5].length) (baseStart_7559535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559535 prefixEnd_7559535 := by exact prefixLift 7559535
  have htrace : WordTrace (prefixWord ++ tailWord_7559535) baseStart_7559535 baseEnd_7559535 := by
    simpa [prefixWord, tailWord_7559535, baseEnd_7559535] using wordTrace_append hprefix tailTrace_7559535
  have hstable : (prefixWord ++ tailWord_7559535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559535).length < 2 ^ (prefixWord ++ tailWord_7559535).sum := by decide
  have hdescent : baseEnd_7559535 < baseStart_7559535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559556 : List Nat := [2, 3, 2, 1, 1, 2, 4, 2, 2, 1, 3]
def baseStart_7559556 : Nat := 118140960795 + 7559556 * 2 ^ 59
def prefixEnd_7559556 : Nat := 4983230072969 + 3 ^ 40 * 7559556 * 2
def baseEnd_7559556 : Nat := 3881685762579930436084241

theorem tailTrace_7559556 : CollatzResearch.WordTrace tailWord_7559556 prefixEnd_7559556 3881685762579930436084241 := by
  unfold tailWord_7559556
  simp only [CollatzResearch.WordTrace]
  refine ⟨137859829300513578111313261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183813105734018104148417681 137859829300513578111313261)
  ·
    refine ⟨51697435987692591791742473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137859829300513578111313261 51697435987692591791742473)
    ·
      refine ⟨38773076990769443843806855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51697435987692591791742473 38773076990769443843806855)
      ·
        refine ⟨58159615486154165765710283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38773076990769443843806855 58159615486154165765710283)
        ·
          refine ⟨87239423229231248648565425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58159615486154165765710283 87239423229231248648565425)
          ·
            refine ⟨65429567421923436486424069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87239423229231248648565425 65429567421923436486424069)
            ·
              refine ⟨12268043891610644341204513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65429567421923436486424069 12268043891610644341204513)
              ·
                refine ⟨9201032918707983255903385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12268043891610644341204513 9201032918707983255903385)
                ·
                  refine ⟨6900774689030987441927539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9201032918707983255903385 6900774689030987441927539)
                  ·
                    refine ⟨10351162033546481162891309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6900774689030987441927539 10351162033546481162891309)
                    ·
                      refine ⟨3881685762579930436084241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10351162033546481162891309 3881685762579930436084241)
                      ·
                        rfl

theorem cell23_7559556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_7559556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559556 prefixEnd_7559556 := by exact prefixLift 7559556
  have htrace : WordTrace (prefixWord ++ tailWord_7559556) baseStart_7559556 baseEnd_7559556 := by
    simpa [prefixWord, tailWord_7559556, baseEnd_7559556] using wordTrace_append hprefix tailTrace_7559556
  have hstable : (prefixWord ++ tailWord_7559556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559556).length < 2 ^ (prefixWord ++ tailWord_7559556).sum := by decide
  have hdescent : baseEnd_7559556 < baseStart_7559556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559566 : List Nat := [4, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2]
def baseStart_7559566 : Nat := 118140960795 + 7559566 * 2 ^ 59
def prefixEnd_7559566 : Nat := 4983230072969 + 3 ^ 40 * 7559566 * 2
def baseEnd_7559566 : Nat := 3881690897386475396959195

theorem tailTrace_7559566 : CollatzResearch.WordTrace tailWord_7559566 prefixEnd_7559566 3881690897386475396959195 := by
  unfold tailWord_7559566
  simp only [CollatzResearch.WordTrace]
  refine ⟨34465002916373865991311319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183813348887327285286993701 34465002916373865991311319)
  ·
    refine ⟨51697504374560798986966979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34465002916373865991311319 51697504374560798986966979)
    ·
      refine ⟨77546256561841198480450469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51697504374560798986966979 77546256561841198480450469)
      ·
        refine ⟨14539923105345224715084463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77546256561841198480450469 14539923105345224715084463)
        ·
          refine ⟨21809884658017837072626695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14539923105345224715084463 21809884658017837072626695)
          ·
            refine ⟨32714826987026755608940043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21809884658017837072626695 32714826987026755608940043)
            ·
              refine ⟨49072240480540133413410065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32714826987026755608940043 49072240480540133413410065)
              ·
                refine ⟨36804180360405100060057549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49072240480540133413410065 36804180360405100060057549)
                ·
                  refine ⟨13801567635151912522521581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36804180360405100060057549 13801567635151912522521581)
                  ·
                    refine ⟨5175587863181967195945593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13801567635151912522521581 5175587863181967195945593)
                    ·
                      refine ⟨3881690897386475396959195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5175587863181967195945593 3881690897386475396959195)
                      ·
                        rfl

theorem cell23_7559566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_7559566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559566 prefixEnd_7559566 := by exact prefixLift 7559566
  have htrace : WordTrace (prefixWord ++ tailWord_7559566) baseStart_7559566 baseEnd_7559566 := by
    simpa [prefixWord, tailWord_7559566, baseEnd_7559566] using wordTrace_append hprefix tailTrace_7559566
  have hstable : (prefixWord ++ tailWord_7559566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559566).length < 2 ^ (prefixWord ++ tailWord_7559566).sum := by decide
  have hdescent : baseEnd_7559566 < baseStart_7559566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559594 : List Nat := [3, 1, 6, 1, 2, 1, 2, 1, 1, 2, 3]
def baseStart_7559594 : Nat := 118140960795 + 7559594 * 2 ^ 59
def prefixEnd_7559594 : Nat := 4983230072969 + 3 ^ 40 * 7559594 * 2
def baseEnd_7559594 : Nat := 3881705274844801287409067

theorem tailTrace_7559594 : CollatzResearch.WordTrace tailWord_7559594 prefixEnd_7559594 3881705274844801287409067 := by
  unfold tailWord_7559594
  simp only [CollatzResearch.WordTrace]
  refine ⟨68930261143722372178127459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183814029716592992475006557 68930261143722372178127459)
  ·
    refine ⟨103395391715583558267191189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68930261143722372178127459 103395391715583558267191189)
    ·
      refine ⟨4846658986667979293774587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103395391715583558267191189 4846658986667979293774587)
      ·
        refine ⟨7269988480001968940661881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4846658986667979293774587 7269988480001968940661881)
        ·
          refine ⟨5452491360001476705496411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7269988480001968940661881 5452491360001476705496411)
          ·
            refine ⟨8178737040002215058244617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5452491360001476705496411 8178737040002215058244617)
            ·
              refine ⟨6134052780001661293683463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8178737040002215058244617 6134052780001661293683463)
              ·
                refine ⟨9201079170002491940525195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6134052780001661293683463 9201079170002491940525195)
                ·
                  refine ⟨13801618755003737910787793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9201079170002491940525195 13801618755003737910787793)
                  ·
                    refine ⟨10351214066252803433090845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13801618755003737910787793 10351214066252803433090845)
                    ·
                      refine ⟨3881705274844801287409067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10351214066252803433090845 3881705274844801287409067)
                      ·
                        rfl

theorem cell23_7559594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_7559594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559594 prefixEnd_7559594 := by exact prefixLift 7559594
  have htrace : WordTrace (prefixWord ++ tailWord_7559594) baseStart_7559594 baseEnd_7559594 := by
    simpa [prefixWord, tailWord_7559594, baseEnd_7559594] using wordTrace_append hprefix tailTrace_7559594
  have hstable : (prefixWord ++ tailWord_7559594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559594).length < 2 ^ (prefixWord ++ tailWord_7559594).sum := by decide
  have hdescent : baseEnd_7559594 < baseStart_7559594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559613 : List Nat := [1, 4, 1, 2, 2, 2, 3, 2, 2, 2, 2]
def baseStart_7559613 : Nat := 118140960795 + 7559613 * 2 ^ 59
def prefixEnd_7559613 : Nat := 4983230072969 + 3 ^ 40 * 7559613 * 2
def baseEnd_7559613 : Nat := 3881715030977236713071479

theorem tailTrace_7559613 : CollatzResearch.WordTrace tailWord_7559613 prefixEnd_7559613 3881715030977236713071479 := by
  unfold tailWord_7559613
  simp only [CollatzResearch.WordTrace]
  refine ⟨275721737561820654957451493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183814491707880436638300995 275721737561820654957451493)
  ·
    refine ⟨51697825792841372804522155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275721737561820654957451493 51697825792841372804522155)
    ·
      refine ⟨77546738689262059206783233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51697825792841372804522155 77546738689262059206783233)
      ·
        refine ⟨58160054016946544405087425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77546738689262059206783233 58160054016946544405087425)
        ·
          refine ⟨43620040512709908303815569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58160054016946544405087425 43620040512709908303815569)
          ·
            refine ⟨32715030384532431227861677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43620040512709908303815569 32715030384532431227861677)
            ·
              refine ⟨12268136394199661710448129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32715030384532431227861677 12268136394199661710448129)
              ·
                refine ⟨9201102295649746282836097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12268136394199661710448129 9201102295649746282836097)
                ·
                  refine ⟨6900826721737309712127073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9201102295649746282836097 6900826721737309712127073)
                  ·
                    refine ⟨5175620041302982284095305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6900826721737309712127073 5175620041302982284095305)
                    ·
                      refine ⟨3881715030977236713071479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5175620041302982284095305 3881715030977236713071479)
                      ·
                        rfl

theorem cell23_7559613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_7559613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559613 prefixEnd_7559613 := by exact prefixLift 7559613
  have htrace : WordTrace (prefixWord ++ tailWord_7559613) baseStart_7559613 baseEnd_7559613 := by
    simpa [prefixWord, tailWord_7559613, baseEnd_7559613] using wordTrace_append hprefix tailTrace_7559613
  have hstable : (prefixWord ++ tailWord_7559613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559613).length < 2 ^ (prefixWord ++ tailWord_7559613).sum := by decide
  have hdescent : baseEnd_7559613 < baseStart_7559613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559653 : List Nat := [1, 3, 1, 5, 2, 2, 1, 3, 5]
def baseStart_7559653 : Nat := 118140960795 + 7559653 * 2 ^ 59
def prefixEnd_7559653 : Nat := 4983230072969 + 3 ^ 40 * 7559653 * 2
def baseEnd_7559653 : Nat := 431303952244824061841255

theorem tailTrace_7559653 : CollatzResearch.WordTrace tailWord_7559653 prefixEnd_7559653 431303952244824061841255 := by
  unfold tailWord_7559653
  simp only [CollatzResearch.WordTrace]
  refine ⟨275723196481675741788907613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183815464321117161192605075 275723196481675741788907613)
  ·
    refine ⟨103396198680628403170840355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275723196481675741788907613 103396198680628403170840355)
    ·
      refine ⟨155094298020942604756260533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103396198680628403170840355 155094298020942604756260533)
      ·
        refine ⟨14540090439463369195899425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155094298020942604756260533 14540090439463369195899425)
        ·
          refine ⟨10905067829597526896924569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14540090439463369195899425 10905067829597526896924569)
          ·
            refine ⟨8178800872198145172693427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10905067829597526896924569 8178800872198145172693427)
            ·
              refine ⟨12268201308297217759040141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8178800872198145172693427 12268201308297217759040141)
              ·
                refine ⟨4600575490611456659640053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12268201308297217759040141 4600575490611456659640053)
                ·
                  refine ⟨431303952244824061841255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4600575490611456659640053 431303952244824061841255)
                  ·
                    rfl

theorem cell23_7559653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3, 5].length) (baseStart_7559653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559653 prefixEnd_7559653 := by exact prefixLift 7559653
  have htrace : WordTrace (prefixWord ++ tailWord_7559653) baseStart_7559653 baseEnd_7559653 := by
    simpa [prefixWord, tailWord_7559653, baseEnd_7559653] using wordTrace_append hprefix tailTrace_7559653
  have hstable : (prefixWord ++ tailWord_7559653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559653).length < 2 ^ (prefixWord ++ tailWord_7559653).sum := by decide
  have hdescent : baseEnd_7559653 < baseStart_7559653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559666 : List Nat := [3, 2, 1, 4, 2, 1, 1, 2, 2, 5]
def baseStart_7559666 : Nat := 118140960795 + 7559666 * 2 ^ 59
def prefixEnd_7559666 : Nat := 4983230072969 + 3 ^ 40 * 7559666 * 2
def baseEnd_7559666 : Nat := 1293914081817308335236245

theorem tailTrace_7559666 : CollatzResearch.WordTrace tailWord_7559666 prefixEnd_7559666 1293914081817308335236245 := by
  unfold tailWord_7559666
  simp only [CollatzResearch.WordTrace]
  refine ⟨68930917657657161252282713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183815780420419096672753901 68930917657657161252282713)
  ·
    refine ⟨51698188243242870939212035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68930917657657161252282713 51698188243242870939212035)
    ·
      refine ⟨77547282364864306408818053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51698188243242870939212035 77547282364864306408818053)
      ·
        refine ⟨14540115443412057451653385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77547282364864306408818053 14540115443412057451653385)
        ·
          refine ⟨10905086582559043088740039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14540115443412057451653385 10905086582559043088740039)
          ·
            refine ⟨16357629873838564633110059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10905086582559043088740039 16357629873838564633110059)
            ·
              refine ⟨24536444810757846949665089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16357629873838564633110059 24536444810757846949665089)
              ·
                refine ⟨18402333608068385212248817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24536444810757846949665089 18402333608068385212248817)
                ·
                  refine ⟨13801750206051288909186613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18402333608068385212248817 13801750206051288909186613)
                  ·
                    refine ⟨1293914081817308335236245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13801750206051288909186613 1293914081817308335236245)
                    ·
                      rfl

theorem cell23_7559666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_7559666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559666 prefixEnd_7559666 := by exact prefixLift 7559666
  have htrace : WordTrace (prefixWord ++ tailWord_7559666) baseStart_7559666 baseEnd_7559666 := by
    simpa [prefixWord, tailWord_7559666, baseEnd_7559666] using wordTrace_append hprefix tailTrace_7559666
  have hstable : (prefixWord ++ tailWord_7559666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559666).length < 2 ^ (prefixWord ++ tailWord_7559666).sum := by decide
  have hdescent : baseEnd_7559666 < baseStart_7559666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559703 : List Nat := [1, 1, 3, 6, 1, 1, 2, 1, 2, 1, 4]
def baseStart_7559703 : Nat := 118140960795 + 7559703 * 2 ^ 59
def prefixEnd_7559703 : Nat := 4983230072969 + 3 ^ 40 * 7559703 * 2
def baseEnd_7559703 : Nat := 3881761244236141360946065

theorem tailTrace_7559703 : CollatzResearch.WordTrace tailWord_7559703 prefixEnd_7559703 3881761244236141360946065 := by
  unfold tailWord_7559703
  simp only [CollatzResearch.WordTrace]
  refine ⟨275725020131494600328227763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183816680087663066885485175 275725020131494600328227763)
  ·
    refine ⟨413587530197241900492341645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275725020131494600328227763 413587530197241900492341645)
    ·
      refine ⟨155095323823965712684628117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413587530197241900492341645 155095323823965712684628117)
      ·
        refine ⟨7270093304248392782091943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 155095323823965712684628117 7270093304248392782091943)
        ·
          refine ⟨10905139956372589173137915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7270093304248392782091943 10905139956372589173137915)
          ·
            refine ⟨16357709934558883759706873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10905139956372589173137915 16357709934558883759706873)
            ·
              refine ⟨12268282450919162819780155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16357709934558883759706873 12268282450919162819780155)
              ·
                refine ⟨18402423676378744229670233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12268282450919162819780155 18402423676378744229670233)
                ·
                  refine ⟨13801817757284058172252675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18402423676378744229670233 13801817757284058172252675)
                  ·
                    refine ⟨20702726635926087258379013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13801817757284058172252675 20702726635926087258379013)
                    ·
                      refine ⟨3881761244236141360946065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20702726635926087258379013 3881761244236141360946065)
                      ·
                        rfl

theorem cell23_7559703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_7559703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559703 prefixEnd_7559703 := by exact prefixLift 7559703
  have htrace : WordTrace (prefixWord ++ tailWord_7559703) baseStart_7559703 baseEnd_7559703 := by
    simpa [prefixWord, tailWord_7559703, baseEnd_7559703] using wordTrace_append hprefix tailTrace_7559703
  have hstable : (prefixWord ++ tailWord_7559703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559703).length < 2 ^ (prefixWord ++ tailWord_7559703).sum := by decide
  have hdescent : baseEnd_7559703 < baseStart_7559703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559736 : List Nat := [2, 1, 2, 1, 4, 1, 2, 3, 3, 1, 3]
def baseStart_7559736 : Nat := 118140960795 + 7559736 * 2 ^ 59
def prefixEnd_7559736 : Nat := 4983230072969 + 3 ^ 40 * 7559736 * 2
def baseEnd_7559736 : Nat := 3881778189097739731833413

theorem tailTrace_7559736 : CollatzResearch.WordTrace tailWord_7559736 prefixEnd_7559736 3881778189097739731833413 := by
  unfold tailWord_7559736
  simp only [CollatzResearch.WordTrace]
  refine ⟨137863111870187523482089531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183817482493583364642786041 137863111870187523482089531)
  ·
    refine ⟨206794667805281285223134297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137863111870187523482089531 206794667805281285223134297)
    ·
      refine ⟨155096000853960963917350723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206794667805281285223134297 155096000853960963917350723)
      ·
        refine ⟨232644001280941445876026085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155096000853960963917350723 232644001280941445876026085)
        ·
          refine ⟨43620750240176521101754891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232644001280941445876026085 43620750240176521101754891)
          ·
            refine ⟨65431125360264781652632337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43620750240176521101754891 65431125360264781652632337)
            ·
              refine ⟨49073344020198586239474253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65431125360264781652632337 49073344020198586239474253)
              ·
                refine ⟨18402504007574469839802845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49073344020198586239474253 18402504007574469839802845)
                ·
                  refine ⟨6900939002840426189926067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18402504007574469839802845 6900939002840426189926067)
                  ·
                    refine ⟨10351408504260639284889101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6900939002840426189926067 10351408504260639284889101)
                    ·
                      refine ⟨3881778189097739731833413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10351408504260639284889101 3881778189097739731833413)
                      ·
                        rfl

theorem cell23_7559736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 3, 1, 3].length) (baseStart_7559736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559736 prefixEnd_7559736 := by exact prefixLift 7559736
  have htrace : WordTrace (prefixWord ++ tailWord_7559736) baseStart_7559736 baseEnd_7559736 := by
    simpa [prefixWord, tailWord_7559736, baseEnd_7559736] using wordTrace_append hprefix tailTrace_7559736
  have hstable : (prefixWord ++ tailWord_7559736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559736).length < 2 ^ (prefixWord ++ tailWord_7559736).sum := by decide
  have hdescent : baseEnd_7559736 < baseStart_7559736 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559759 : List Nat := [1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 4]
def baseStart_7559759 : Nat := 118140960795 + 7559759 * 2 ^ 59
def prefixEnd_7559759 : Nat := 4983230072969 + 3 ^ 40 * 7559759 * 2
def baseEnd_7559759 : Nat := 3881789999152793141845807

theorem tailTrace_7559759 : CollatzResearch.WordTrace tailWord_7559759 prefixEnd_7559759 3881789999152793141845807 := by
  unfold tailWord_7559759
  simp only [CollatzResearch.WordTrace]
  refine ⟨275727062619291721892266331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183818041746194481261510887 275727062619291721892266331)
  ·
    refine ⟨413590593928937582838399497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275727062619291721892266331 413590593928937582838399497)
    ·
      refine ⟨310192945446703187128799623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413590593928937582838399497 310192945446703187128799623)
      ·
        refine ⟨465289418170054780693199435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310192945446703187128799623 465289418170054780693199435)
        ·
          refine ⟨697934127255082171039799153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465289418170054780693199435 697934127255082171039799153)
          ·
            refine ⟨523450595441311628279849365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 697934127255082171039799153 523450595441311628279849365)
            ·
              refine ⟨24536746661311482575617939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 523450595441311628279849365 24536746661311482575617939)
              ·
                refine ⟨36805119991967223863426909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24536746661311482575617939 36805119991967223863426909)
                ·
                  refine ⟨13801919996987708948785091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36805119991967223863426909 13801919996987708948785091)
                  ·
                    refine ⟨20702879995481563423177637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13801919996987708948785091 20702879995481563423177637)
                    ·
                      refine ⟨3881789999152793141845807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20702879995481563423177637 3881789999152793141845807)
                      ·
                        rfl

theorem cell23_7559759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 4].length) (baseStart_7559759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559759 prefixEnd_7559759 := by exact prefixLift 7559759
  have htrace : WordTrace (prefixWord ++ tailWord_7559759) baseStart_7559759 baseEnd_7559759 := by
    simpa [prefixWord, tailWord_7559759, baseEnd_7559759] using wordTrace_append hprefix tailTrace_7559759
  have hstable : (prefixWord ++ tailWord_7559759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559759).length < 2 ^ (prefixWord ++ tailWord_7559759).sum := by decide
  have hdescent : baseEnd_7559759 < baseStart_7559759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559779 : List Nat := [1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 5]
def baseStart_7559779 : Nat := 118140960795 + 7559779 * 2 ^ 59
def prefixEnd_7559779 : Nat := 4983230072969 + 3 ^ 40 * 7559779 * 2
def baseEnd_7559779 : Nat := 3881800268765883063595715

theorem tailTrace_7559779 : CollatzResearch.WordTrace tailWord_7559779 prefixEnd_7559779 3881800268765883063595715 := by
  unfold tailWord_7559779
  simp only [CollatzResearch.WordTrace]
  refine ⟨275727792079219265307994391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183818528052812843538662927 275727792079219265307994391)
  ·
    refine ⟨413591688118828897961991587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275727792079219265307994391 413591688118828897961991587)
    ·
      refine ⟨620387532178243346942987381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413591688118828897961991587 620387532178243346942987381)
      ·
        refine ⟨58161331141710313775905067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 620387532178243346942987381 58161331141710313775905067)
        ·
          refine ⟨87241996712565470663857601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58161331141710313775905067 87241996712565470663857601)
          ·
            refine ⟨65431497534424102997893201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87241996712565470663857601 65431497534424102997893201)
            ·
              refine ⟨49073623150818077248419901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65431497534424102997893201 49073623150818077248419901)
              ·
                refine ⟨18402608681556778968157463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49073623150818077248419901 18402608681556778968157463)
                ·
                  refine ⟨27603913022335168452236195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18402608681556778968157463 27603913022335168452236195)
                  ·
                    refine ⟨41405869533502752678354293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27603913022335168452236195 41405869533502752678354293)
                    ·
                      refine ⟨3881800268765883063595715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41405869533502752678354293 3881800268765883063595715)
                      ·
                        rfl

theorem cell23_7559779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_7559779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559779 prefixEnd_7559779 := by exact prefixLift 7559779
  have htrace : WordTrace (prefixWord ++ tailWord_7559779) baseStart_7559779 baseEnd_7559779 := by
    simpa [prefixWord, tailWord_7559779, baseEnd_7559779] using wordTrace_append hprefix tailTrace_7559779
  have hstable : (prefixWord ++ tailWord_7559779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559779).length < 2 ^ (prefixWord ++ tailWord_7559779).sum := by decide
  have hdescent : baseEnd_7559779 < baseStart_7559779 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559786 : List Nat := [3, 1, 3, 2, 1, 1, 3, 1, 4, 4]
def baseStart_7559786 : Nat := 118140960795 + 7559786 * 2 ^ 59
def prefixEnd_7559786 : Nat := 4983230072969 + 3 ^ 40 * 7559786 * 2
def baseEnd_7559786 : Nat := 1293934621043488178736061

theorem tailTrace_7559786 : CollatzResearch.WordTrace tailWord_7559786 prefixEnd_7559786 1293934621043488178736061 := by
  unfold tailWord_7559786
  simp only [CollatzResearch.WordTrace]
  refine ⟨68932011847548476375874803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183818698260129270335666141 68932011847548476375874803)
  ·
    refine ⟨103398017771322714563812205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68932011847548476375874803 103398017771322714563812205)
    ·
      refine ⟨38774256664246017961429577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103398017771322714563812205 38774256664246017961429577)
      ·
        refine ⟨29080692498184513471072183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38774256664246017961429577 29080692498184513471072183)
        ·
          refine ⟨43621038747276770206608275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29080692498184513471072183 43621038747276770206608275)
          ·
            refine ⟨65431558120915155309912413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43621038747276770206608275 65431558120915155309912413)
            ·
              refine ⟨24536834295343183241217155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65431558120915155309912413 24536834295343183241217155)
              ·
                refine ⟨36805251443014774861825733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24536834295343183241217155 36805251443014774861825733)
                ·
                  refine ⟨6900984645565270286592325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36805251443014774861825733 6900984645565270286592325)
                  ·
                    refine ⟨1293934621043488178736061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6900984645565270286592325 1293934621043488178736061)
                    ·
                      rfl

theorem cell23_7559786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_7559786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559786 prefixEnd_7559786 := by exact prefixLift 7559786
  have htrace : WordTrace (prefixWord ++ tailWord_7559786) baseStart_7559786 baseEnd_7559786 := by
    simpa [prefixWord, tailWord_7559786, baseEnd_7559786] using wordTrace_append hprefix tailTrace_7559786
  have hstable : (prefixWord ++ tailWord_7559786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559786).length < 2 ^ (prefixWord ++ tailWord_7559786).sum := by decide
  have hdescent : baseEnd_7559786 < baseStart_7559786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559813 : List Nat := [1, 3, 1, 1, 4, 3, 2, 2, 1, 2, 3]
def baseStart_7559813 : Nat := 118140960795 + 7559813 * 2 ^ 59
def prefixEnd_7559813 : Nat := 4983230072969 + 3 ^ 40 * 7559813 * 2
def baseEnd_7559813 : Nat := 3881817727108135930570559

theorem tailTrace_7559813 : CollatzResearch.WordTrace tailWord_7559813 prefixEnd_7559813 3881817727108135930570559 := by
  unfold tailWord_7559813
  simp only [CollatzResearch.WordTrace]
  refine ⟨275729032161096089114732093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183819354774064059409821395 275729032161096089114732093)
  ·
    refine ⟨103398387060411033418024535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275729032161096089114732093 103398387060411033418024535)
    ·
      refine ⟨155097580590616550127036803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103398387060411033418024535 155097580590616550127036803)
      ·
        refine ⟨232646370885924825190555205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155097580590616550127036803 232646370885924825190555205)
        ·
          refine ⟨43621194541110904723229101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232646370885924825190555205 43621194541110904723229101)
          ·
            refine ⟨16357947952916589271210913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43621194541110904723229101 16357947952916589271210913)
            ·
              refine ⟨12268460964687441953408185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16357947952916589271210913 12268460964687441953408185)
              ·
                refine ⟨9201345723515581465056139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12268460964687441953408185 9201345723515581465056139)
                ·
                  refine ⟨13802018585273372197584209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9201345723515581465056139 13802018585273372197584209)
                  ·
                    refine ⟨10351513938955029148188157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13802018585273372197584209 10351513938955029148188157)
                    ·
                      refine ⟨3881817727108135930570559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10351513938955029148188157 3881817727108135930570559)
                      ·
                        rfl

theorem cell23_7559813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 2, 3].length) (baseStart_7559813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559813 prefixEnd_7559813 := by exact prefixLift 7559813
  have htrace : WordTrace (prefixWord ++ tailWord_7559813) baseStart_7559813 baseEnd_7559813 := by
    simpa [prefixWord, tailWord_7559813, baseEnd_7559813] using wordTrace_append hprefix tailTrace_7559813
  have hstable : (prefixWord ++ tailWord_7559813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559813).length < 2 ^ (prefixWord ++ tailWord_7559813).sum := by decide
  have hdescent : baseEnd_7559813 < baseStart_7559813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559879 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 4]
def baseStart_7559879 : Nat := 118140960795 + 7559879 * 2 ^ 59
def prefixEnd_7559879 : Nat := 4983230072969 + 3 ^ 40 * 7559879 * 2
def baseEnd_7559879 : Nat := 3881851616831332672345255

theorem tailTrace_7559879 : CollatzResearch.WordTrace tailWord_7559879 prefixEnd_7559879 3881851616831332672345255 := by
  unfold tailWord_7559879
  simp only [CollatzResearch.WordTrace]
  refine ⟨275731439378856982386634691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183820959585904654924423127 275731439378856982386634691)
  ·
    refine ⟨413597159068285473579952037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275731439378856982386634691 413597159068285473579952037)
    ·
      refine ⟨77549467325303526296241007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 413597159068285473579952037 77549467325303526296241007)
      ·
        refine ⟨116324200987955289444361511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77549467325303526296241007 116324200987955289444361511)
        ·
          refine ⟨174486301481932934166542267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116324200987955289444361511 174486301481932934166542267)
          ·
            refine ⟨261729452222899401249813401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174486301481932934166542267 261729452222899401249813401)
            ·
              refine ⟨196297089167174550937360051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261729452222899401249813401 196297089167174550937360051)
              ·
                refine ⟨294445633750761826406040077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196297089167174550937360051 294445633750761826406040077)
                ·
                  refine ⟨110417112656535684902265029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294445633750761826406040077 110417112656535684902265029)
                  ·
                    refine ⟨20703208623100440919174693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110417112656535684902265029 20703208623100440919174693)
                    ·
                      refine ⟨3881851616831332672345255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20703208623100440919174693 3881851616831332672345255)
                      ·
                        rfl

theorem cell23_7559879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_7559879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559879 prefixEnd_7559879 := by exact prefixLift 7559879
  have htrace : WordTrace (prefixWord ++ tailWord_7559879) baseStart_7559879 baseEnd_7559879 := by
    simpa [prefixWord, tailWord_7559879, baseEnd_7559879] using wordTrace_append hprefix tailTrace_7559879
  have hstable : (prefixWord ++ tailWord_7559879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559879).length < 2 ^ (prefixWord ++ tailWord_7559879).sum := by decide
  have hdescent : baseEnd_7559879 < baseStart_7559879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559886 : List Nat := [4, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5]
def baseStart_7559886 : Nat := 118140960795 + 7559886 * 2 ^ 59
def prefixEnd_7559886 : Nat := 4983230072969 + 3 ^ 40 * 7559886 * 2
def baseEnd_7559886 : Nat := 3881855211195914144957723

theorem tailTrace_7559886 : CollatzResearch.WordTrace tailWord_7559886 prefixEnd_7559886 3881855211195914144957723 := by
  unfold tailWord_7559886
  simp only [CollatzResearch.WordTrace]
  refine ⟨34466461836228952822767439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183821129793221081721426341 34466461836228952822767439)
  ·
    refine ⟨51699692754343429234151159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34466461836228952822767439 51699692754343429234151159)
    ·
      refine ⟨77549539131515143851226739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51699692754343429234151159 77549539131515143851226739)
      ·
        refine ⟨116324308697272715776840109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77549539131515143851226739 116324308697272715776840109)
        ·
          refine ⟨43621615761477268416315041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116324308697272715776840109 43621615761477268416315041)
          ·
            refine ⟨32716211821107951312236281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43621615761477268416315041 32716211821107951312236281)
            ·
              refine ⟨24537158865830963484177211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32716211821107951312236281 24537158865830963484177211)
              ·
                refine ⟨36805738298746445226265817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24537158865830963484177211 36805738298746445226265817)
                ·
                  refine ⟨27604303724059833919699363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36805738298746445226265817 27604303724059833919699363)
                  ·
                    refine ⟨41406455586089750879549045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27604303724059833919699363 41406455586089750879549045)
                    ·
                      refine ⟨3881855211195914144957723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41406455586089750879549045 3881855211195914144957723)
                      ·
                        rfl

theorem cell23_7559886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_7559886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559886 prefixEnd_7559886 := by exact prefixLift 7559886
  have htrace : WordTrace (prefixWord ++ tailWord_7559886) baseStart_7559886 baseEnd_7559886 := by
    simpa [prefixWord, tailWord_7559886, baseEnd_7559886] using wordTrace_append hprefix tailTrace_7559886
  have hstable : (prefixWord ++ tailWord_7559886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559886).length < 2 ^ (prefixWord ++ tailWord_7559886).sum := by decide
  have hdescent : baseEnd_7559886 < baseStart_7559886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559929 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 1, 1, 7]
def baseStart_7559929 : Nat := 118140960795 + 7559929 * 2 ^ 59
def prefixEnd_7559929 : Nat := 4983230072969 + 3 ^ 40 * 7559929 * 2
def baseEnd_7559929 : Nat := 3881877290864057476720025

theorem tailTrace_7559929 : CollatzResearch.WordTrace tailWord_7559929 prefixEnd_7559929 3881877290864057476720025 := by
  unfold tailWord_7559929
  simp only [CollatzResearch.WordTrace]
  refine ⟨275733263028675840925954841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183822175352450560617303227 275733263028675840925954841)
  ·
    refine ⟨206799947271506880694466131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275733263028675840925954841 206799947271506880694466131)
    ·
      refine ⟨310199920907260321041699197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206799947271506880694466131 310199920907260321041699197)
      ·
        refine ⟨116324970340222620390637199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310199920907260321041699197 116324970340222620390637199)
        ·
          refine ⟨174487455510333930585955799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116324970340222620390637199 174487455510333930585955799)
          ·
            refine ⟨261731183265500895878933699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174487455510333930585955799 261731183265500895878933699)
            ·
              refine ⟨392596774898251343818400549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261731183265500895878933699 392596774898251343818400549)
              ·
                refine ⟨73611895293422126965950103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 392596774898251343818400549 73611895293422126965950103)
                ·
                  refine ⟨110417842940133190448925155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73611895293422126965950103 110417842940133190448925155)
                  ·
                    refine ⟨165626764410199785673387733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110417842940133190448925155 165626764410199785673387733)
                    ·
                      refine ⟨3881877290864057476720025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 165626764410199785673387733 3881877290864057476720025)
                      ·
                        rfl

theorem cell23_7559929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_7559929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559929 prefixEnd_7559929 := by exact prefixLift 7559929
  have htrace : WordTrace (prefixWord ++ tailWord_7559929) baseStart_7559929 baseEnd_7559929 := by
    simpa [prefixWord, tailWord_7559929, baseEnd_7559929] using wordTrace_append hprefix tailTrace_7559929
  have hstable : (prefixWord ++ tailWord_7559929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559929).length < 2 ^ (prefixWord ++ tailWord_7559929).sum := by decide
  have hdescent : baseEnd_7559929 < baseStart_7559929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
