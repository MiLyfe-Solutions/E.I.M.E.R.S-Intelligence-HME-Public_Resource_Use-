import V185TrunkScan22Chunk089

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_808276 : List Nat := [2, 4, 1, 1, 2, 1, 4, 2, 2, 3]
def baseStart_808276 : Nat := 118140960795 + 808276 * 2 ^ 59
def prefixEnd_808276 : Nat := 4983230072969 + 3 ^ 40 * 808276 * 2
def baseEnd_808276 : Nat := 276689392995723233421875

theorem tailTrace_808276 : CollatzResearch.WordTrace tailWord_808276 prefixEnd_808276 276689392995723233421875 := by
  unfold tailWord_808276
  simp only [CollatzResearch.WordTrace]
  refine ⟨14740123809880784697890341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19653498413174379597187121 14740123809880784697890341)
  ·
    refine ⟨2763773214352647130854439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14740123809880784697890341 2763773214352647130854439)
    ·
      refine ⟨4145659821528970696281659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2763773214352647130854439 4145659821528970696281659)
      ·
        refine ⟨6218489732293456044422489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4145659821528970696281659 6218489732293456044422489)
        ·
          refine ⟨4663867299220092033316867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6218489732293456044422489 4663867299220092033316867)
          ·
            refine ⟨6995800948830138049975301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4663867299220092033316867 6995800948830138049975301)
            ·
              refine ⟨1311712677905650884370369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6995800948830138049975301 1311712677905650884370369)
              ·
                refine ⟨983784508429238163277777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1311712677905650884370369 983784508429238163277777)
                ·
                  refine ⟨737838381321928622458333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 983784508429238163277777 737838381321928622458333)
                  ·
                    refine ⟨276689392995723233421875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 737838381321928622458333 276689392995723233421875)
                    ·
                      rfl

theorem cell22_808276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_808276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808276 prefixEnd_808276 := by exact prefixLift 808276
  have htrace : WordTrace (prefixWord ++ tailWord_808276) baseStart_808276 baseEnd_808276 := by
    simpa [prefixWord, tailWord_808276, baseEnd_808276] using wordTrace_append hprefix tailTrace_808276
  have hstable : (prefixWord ++ tailWord_808276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808276).length < 2 ^ (prefixWord ++ tailWord_808276).sum := by decide
  have hdescent : baseEnd_808276 < baseStart_808276 := by decide
  rcases family_descends (prefixWord ++ tailWord_808276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808304 : List Nat := [2, 1, 1, 1, 4, 2, 3, 2, 3, 3]
def baseStart_808304 : Nat := 118140960795 + 808304 * 2 ^ 59
def prefixEnd_808304 : Nat := 4983230072969 + 3 ^ 40 * 808304 * 2
def baseEnd_808304 : Nat := 276698977967940493721789

theorem tailTrace_808304 : CollatzResearch.WordTrace tailWord_808304 prefixEnd_808304 276698977967940493721789 := by
  unfold tailWord_808304
  simp only [CollatzResearch.WordTrace]
  refine ⟨14740634431830065088899983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19654179242440086785199977 14740634431830065088899983)
  ·
    refine ⟨22110951647745097633349975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14740634431830065088899983 22110951647745097633349975)
    ·
      refine ⟨33166427471617646450024963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22110951647745097633349975 33166427471617646450024963)
      ·
        refine ⟨49749641207426469675037445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33166427471617646450024963 49749641207426469675037445)
        ·
          refine ⟨9328057726392463064069521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49749641207426469675037445 9328057726392463064069521)
          ·
            refine ⟨6996043294794347298052141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9328057726392463064069521 6996043294794347298052141)
            ·
              refine ⟨2623516235547880236769553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6996043294794347298052141 2623516235547880236769553)
              ·
                refine ⟨1967637176660910177577165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2623516235547880236769553 1967637176660910177577165)
                ·
                  refine ⟨737863941247841316591437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1967637176660910177577165 737863941247841316591437)
                  ·
                    refine ⟨276698977967940493721789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 737863941247841316591437 276698977967940493721789)
                    ·
                      rfl

theorem cell22_808304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 3, 3].length) (baseStart_808304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808304 prefixEnd_808304 := by exact prefixLift 808304
  have htrace : WordTrace (prefixWord ++ tailWord_808304) baseStart_808304 baseEnd_808304 := by
    simpa [prefixWord, tailWord_808304, baseEnd_808304] using wordTrace_append hprefix tailTrace_808304
  have hstable : (prefixWord ++ tailWord_808304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808304).length < 2 ^ (prefixWord ++ tailWord_808304).sum := by decide
  have hdescent : baseEnd_808304 < baseStart_808304 := by decide
  rcases family_descends (prefixWord ++ tailWord_808304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808317 : List Nat := [1, 4, 1, 1, 2, 2, 2, 2, 7]
def baseStart_808317 : Nat := 118140960795 + 808317 * 2 ^ 59
def prefixEnd_808317 : Nat := 4983230072969 + 3 ^ 40 * 808317 * 2
def baseEnd_808317 : Nat := 92234476044537597715583

theorem tailTrace_808317 : CollatzResearch.WordTrace tailWord_808317 prefixEnd_808317 92234476044537597715583 := by
  unfold tailWord_808317
  simp only [CollatzResearch.WordTrace]
  refine ⟨29481743012613033398023205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19654495341742022265348803 29481743012613033398023205)
  ·
    refine ⟨5527826814864943762129351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29481743012613033398023205 5527826814864943762129351)
    ·
      refine ⟨8291740222297415643194027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5527826814864943762129351 8291740222297415643194027)
      ·
        refine ⟨12437610333446123464791041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8291740222297415643194027 12437610333446123464791041)
        ·
          refine ⟨9328207750084592598593281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12437610333446123464791041 9328207750084592598593281)
          ·
            refine ⟨6996155812563444448944961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9328207750084592598593281 6996155812563444448944961)
            ·
              refine ⟨5247116859422583336708721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6996155812563444448944961 5247116859422583336708721)
              ·
                refine ⟨3935337644566937502531541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5247116859422583336708721 3935337644566937502531541)
                ·
                  refine ⟨92234476044537597715583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3935337644566937502531541 92234476044537597715583)
                  ·
                    rfl

theorem cell22_808317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_808317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808317 prefixEnd_808317 := by exact prefixLift 808317
  have htrace : WordTrace (prefixWord ++ tailWord_808317) baseStart_808317 baseEnd_808317 := by
    simpa [prefixWord, tailWord_808317, baseEnd_808317] using wordTrace_append hprefix tailTrace_808317
  have hstable : (prefixWord ++ tailWord_808317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808317).length < 2 ^ (prefixWord ++ tailWord_808317).sum := by decide
  have hdescent : baseEnd_808317 < baseStart_808317 := by decide
  rcases family_descends (prefixWord ++ tailWord_808317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808332 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 4, 5]
def baseStart_808332 : Nat := 118140960795 + 808332 * 2 ^ 59
def prefixEnd_808332 : Nat := 4983230072969 + 3 ^ 40 * 808332 * 2
def baseEnd_808332 : Nat := 276708562940157754021703

theorem tailTrace_808332 : CollatzResearch.WordTrace tailWord_808332 prefixEnd_808332 276708562940157754021703 := by
  unfold tailWord_808332
  simp only [CollatzResearch.WordTrace]
  refine ⟨14741145053779345479909625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19654860071705793973212833 14741145053779345479909625)
  ·
    refine ⟨11055858790334509109932219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14741145053779345479909625 11055858790334509109932219)
    ·
      refine ⟨16583788185501763664898329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11055858790334509109932219 16583788185501763664898329)
      ·
        refine ⟨12437841139126322748673747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16583788185501763664898329 12437841139126322748673747)
        ·
          refine ⟨18656761708689484123010621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12437841139126322748673747 18656761708689484123010621)
          ·
            refine ⟨6996285640758556546128983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18656761708689484123010621 6996285640758556546128983)
            ·
              refine ⟨10494428461137834819193475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6996285640758556546128983 10494428461137834819193475)
              ·
                refine ⟨15741642691706752228790213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10494428461137834819193475 15741642691706752228790213)
                ·
                  refine ⟨2951558004695016042898165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15741642691706752228790213 2951558004695016042898165)
                  ·
                    refine ⟨276708562940157754021703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2951558004695016042898165 276708562940157754021703)
                    ·
                      rfl

theorem cell22_808332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_808332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808332 prefixEnd_808332 := by exact prefixLift 808332
  have htrace : WordTrace (prefixWord ++ tailWord_808332) baseStart_808332 baseEnd_808332 := by
    simpa [prefixWord, tailWord_808332, baseEnd_808332] using wordTrace_append hprefix tailTrace_808332
  have hstable : (prefixWord ++ tailWord_808332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808332).length < 2 ^ (prefixWord ++ tailWord_808332).sum := by decide
  have hdescent : baseEnd_808332 < baseStart_808332 := by decide
  rcases family_descends (prefixWord ++ tailWord_808332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808349 : List Nat := [1, 4, 2, 1, 3, 1, 2, 1, 2, 5]
def baseStart_808349 : Nat := 118140960795 + 808349 * 2 ^ 59
def prefixEnd_808349 : Nat := 4983230072969 + 3 ^ 40 * 808349 * 2
def baseEnd_808349 : Nat := 276714382387575376346651

theorem tailTrace_808349 : CollatzResearch.WordTrace tailWord_808349 prefixEnd_808349 276714382387575376346651 := by
  unfold tailWord_808349
  simp only [CollatzResearch.WordTrace]
  refine ⟨29482910148497102863188101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19655273432331401908792067 29482910148497102863188101)
  ·
    refine ⟨5528045652843206786847769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29482910148497102863188101 5528045652843206786847769)
    ·
      refine ⟨4146034239632405090135827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5528045652843206786847769 4146034239632405090135827)
      ·
        refine ⟨6219051359448607635203741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4146034239632405090135827 6219051359448607635203741)
        ·
          refine ⟨2332144259793227863201403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6219051359448607635203741 2332144259793227863201403)
          ·
            refine ⟨3498216389689841794802105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2332144259793227863201403 3498216389689841794802105)
            ·
              refine ⟨2623662292267381346101579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3498216389689841794802105 2623662292267381346101579)
              ·
                refine ⟨3935493438401072019152369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2623662292267381346101579 3935493438401072019152369)
                ·
                  refine ⟨2951620078800804014364277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3935493438401072019152369 2951620078800804014364277)
                  ·
                    refine ⟨276714382387575376346651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2951620078800804014364277 276714382387575376346651)
                    ·
                      rfl

theorem cell22_808349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_808349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808349 prefixEnd_808349 := by exact prefixLift 808349
  have htrace : WordTrace (prefixWord ++ tailWord_808349) baseStart_808349 baseEnd_808349 := by
    simpa [prefixWord, tailWord_808349, baseEnd_808349] using wordTrace_append hprefix tailTrace_808349
  have hstable : (prefixWord ++ tailWord_808349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808349).length < 2 ^ (prefixWord ++ tailWord_808349).sum := by decide
  have hdescent : baseEnd_808349 < baseStart_808349 := by decide
  rcases family_descends (prefixWord ++ tailWord_808349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808351 : List Nat := [1, 1, 2, 5, 1, 3, 3, 1, 5]
def baseStart_808351 : Nat := 118140960795 + 808351 * 2 ^ 59
def prefixEnd_808351 : Nat := 4983230072969 + 3 ^ 40 * 808351 * 2
def baseEnd_808351 : Nat := 92238355676149345932215

theorem tailTrace_808351 : CollatzResearch.WordTrace tailWord_808351 prefixEnd_808351 92238355676149345932215 := by
  unfold tailWord_808351
  simp only [CollatzResearch.WordTrace]
  refine ⟨29482983094489857204760907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19655322062993238136507271 29482983094489857204760907)
  ·
    refine ⟨44224474641734785807141361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29482983094489857204760907 44224474641734785807141361)
    ·
      refine ⟨33168355981301089355356021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44224474641734785807141361 33168355981301089355356021)
      ·
        refine ⟨3109533373246977127064627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33168355981301089355356021 3109533373246977127064627)
        ·
          refine ⟨4664300059870465690596941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3109533373246977127064627 4664300059870465690596941)
          ·
            refine ⟨1749112522451424633973853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4664300059870465690596941 1749112522451424633973853)
            ·
              refine ⟨655917195919284237740195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1749112522451424633973853 655917195919284237740195)
              ·
                refine ⟨983875793878926356610293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 655917195919284237740195 983875793878926356610293)
                ·
                  refine ⟨92238355676149345932215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 983875793878926356610293 92238355676149345932215)
                  ·
                    rfl

theorem cell22_808351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 5].length) (baseStart_808351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808351 prefixEnd_808351 := by exact prefixLift 808351
  have htrace : WordTrace (prefixWord ++ tailWord_808351) baseStart_808351 baseEnd_808351 := by
    simpa [prefixWord, tailWord_808351, baseEnd_808351] using wordTrace_append hprefix tailTrace_808351
  have hstable : (prefixWord ++ tailWord_808351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808351).length < 2 ^ (prefixWord ++ tailWord_808351).sum := by decide
  have hdescent : baseEnd_808351 < baseStart_808351 := by decide
  rcases family_descends (prefixWord ++ tailWord_808351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808364 : List Nat := [2, 2, 1, 1, 1, 1, 5, 4, 1, 4]
def baseStart_808364 : Nat := 118140960795 + 808364 * 2 ^ 59
def prefixEnd_808364 : Nat := 4983230072969 + 3 ^ 40 * 808364 * 2
def baseEnd_808364 : Nat := 276719517194120337221605

theorem tailTrace_808364 : CollatzResearch.WordTrace tailWord_808364 prefixEnd_808364 276719517194120337221605 := by
  unfold tailWord_808364
  simp only [CollatzResearch.WordTrace]
  refine ⟨14741728621721380212492073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19655638162295173616656097 14741728621721380212492073)
  ·
    refine ⟨11056296466291035159369055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14741728621721380212492073 11056296466291035159369055)
    ·
      refine ⟨16584444699436552739053583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11056296466291035159369055 16584444699436552739053583)
      ·
        refine ⟨24876667049154829108580375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16584444699436552739053583 24876667049154829108580375)
        ·
          refine ⟨37315000573732243662870563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24876667049154829108580375 37315000573732243662870563)
          ·
            refine ⟨55972500860598365494305845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37315000573732243662870563 55972500860598365494305845)
            ·
              refine ⟨5247421955681096765091173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55972500860598365494305845 5247421955681096765091173)
              ·
                refine ⟨983891616690205643454595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5247421955681096765091173 983891616690205643454595)
                ·
                  refine ⟨1475837425035308465181893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 983891616690205643454595 1475837425035308465181893)
                  ·
                    refine ⟨276719517194120337221605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1475837425035308465181893 276719517194120337221605)
                    ·
                      rfl

theorem cell22_808364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_808364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808364 prefixEnd_808364 := by exact prefixLift 808364
  have htrace : WordTrace (prefixWord ++ tailWord_808364) baseStart_808364 baseEnd_808364 := by
    simpa [prefixWord, tailWord_808364, baseEnd_808364] using wordTrace_append hprefix tailTrace_808364
  have hstable : (prefixWord ++ tailWord_808364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808364).length < 2 ^ (prefixWord ++ tailWord_808364).sum := by decide
  have hdescent : baseEnd_808364 < baseStart_808364 := by decide
  rcases family_descends (prefixWord ++ tailWord_808364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808396 : List Nat := [2, 2, 1, 4, 2, 3, 1, 1, 6]
def baseStart_808396 : Nat := 118140960795 + 808396 * 2 ^ 59
def prefixEnd_808396 : Nat := 4983230072969 + 3 ^ 40 * 808396 * 2
def baseEnd_808396 : Nat := 92243490482694306807169

theorem tailTrace_808396 : CollatzResearch.WordTrace tailWord_808396 prefixEnd_808396 92243490482694306807169 := by
  unfold tailWord_808396
  simp only [CollatzResearch.WordTrace]
  refine ⟨14742312189663414945074521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19656416252884553260099361 14742312189663414945074521)
  ·
    refine ⟨11056734142247561208805891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14742312189663414945074521 11056734142247561208805891)
    ·
      refine ⟨16585101213371341813208837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11056734142247561208805891 16585101213371341813208837)
      ·
        refine ⟨3109706477507126589976657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16585101213371341813208837 3109706477507126589976657)
        ·
          refine ⟨2332279858130344942482493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3109706477507126589976657 2332279858130344942482493)
          ·
            refine ⟨874604946798879353430935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2332279858130344942482493 874604946798879353430935)
            ·
              refine ⟨1311907420198319030146403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874604946798879353430935 1311907420198319030146403)
              ·
                refine ⟨1967861130297478545219605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1311907420198319030146403 1967861130297478545219605)
                ·
                  refine ⟨92243490482694306807169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1967861130297478545219605 92243490482694306807169)
                  ·
                    rfl

theorem cell22_808396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 6].length) (baseStart_808396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808396 prefixEnd_808396 := by exact prefixLift 808396
  have htrace : WordTrace (prefixWord ++ tailWord_808396) baseStart_808396 baseEnd_808396 := by
    simpa [prefixWord, tailWord_808396, baseEnd_808396] using wordTrace_append hprefix tailTrace_808396
  have hstable : (prefixWord ++ tailWord_808396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808396).length < 2 ^ (prefixWord ++ tailWord_808396).sum := by decide
  have hdescent : baseEnd_808396 < baseStart_808396 := by decide
  rcases family_descends (prefixWord ++ tailWord_808396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808439 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 7, 3]
def baseStart_808439 : Nat := 118140960795 + 808439 * 2 ^ 59
def prefixEnd_808439 : Nat := 4983230072969 + 3 ^ 40 * 808439 * 2
def baseEnd_808439 : Nat := 276745191226845141596375

theorem tailTrace_808439 : CollatzResearch.WordTrace tailWord_808439 prefixEnd_808439 276745191226845141596375 := by
  unfold tailWord_808439
  simp only [CollatzResearch.WordTrace]
  refine ⟨29486192718171048233964371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19657461812114032155976247 29486192718171048233964371)
  ·
    refine ⟨44229289077256572350946557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29486192718171048233964371 44229289077256572350946557)
    ·
      refine ⟨16585983403971214631604959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44229289077256572350946557 16585983403971214631604959)
      ·
        refine ⟨24878975105956821947407439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16585983403971214631604959 24878975105956821947407439)
        ·
          refine ⟨37318462658935232921111159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24878975105956821947407439 37318462658935232921111159)
          ·
            refine ⟨55977693988402849381666739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37318462658935232921111159 55977693988402849381666739)
            ·
              refine ⟨83966540982604274072500109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55977693988402849381666739 83966540982604274072500109)
              ·
                refine ⟨31487452868476602777187541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83966540982604274072500109 31487452868476602777187541)
                ·
                  refine ⟨737987176604920377590333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 31487452868476602777187541 737987176604920377590333)
                  ·
                    refine ⟨276745191226845141596375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 737987176604920377590333 276745191226845141596375)
                    ·
                      rfl

theorem cell22_808439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7, 3].length) (baseStart_808439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808439 prefixEnd_808439 := by exact prefixLift 808439
  have htrace : WordTrace (prefixWord ++ tailWord_808439) baseStart_808439 baseEnd_808439 := by
    simpa [prefixWord, tailWord_808439, baseEnd_808439] using wordTrace_append hprefix tailTrace_808439
  have hstable : (prefixWord ++ tailWord_808439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808439).length < 2 ^ (prefixWord ++ tailWord_808439).sum := by decide
  have hdescent : baseEnd_808439 < baseStart_808439 := by decide
  rcases family_descends (prefixWord ++ tailWord_808439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808490 : List Nat := [3, 1, 4, 1, 1, 1, 4, 3, 1, 3]
def baseStart_808490 : Nat := 118140960795 + 808490 * 2 ^ 59
def prefixEnd_808490 : Nat := 4983230072969 + 3 ^ 40 * 808490 * 2
def baseEnd_808490 : Nat := 276762649569098008571219

theorem tailTrace_808490 : CollatzResearch.WordTrace tailWord_808490 prefixEnd_808490 276762649569098008571219 := by
  unfold tailWord_808490
  simp only [CollatzResearch.WordTrace]
  refine ⟨7372013210246570986017731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19658701893990855962713949 7372013210246570986017731)
  ·
    refine ⟨11058019815369856479026597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7372013210246570986017731 11058019815369856479026597)
    ·
      refine ⟨2073378715381848089817487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11058019815369856479026597 2073378715381848089817487)
      ·
        refine ⟨3110068073072772134726231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2073378715381848089817487 3110068073072772134726231)
        ·
          refine ⟨4665102109609158202089347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3110068073072772134726231 4665102109609158202089347)
          ·
            refine ⟨6997653164413737303134021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4665102109609158202089347 6997653164413737303134021)
            ·
              refine ⟨1312059968327575744337629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6997653164413737303134021 1312059968327575744337629)
              ·
                refine ⟨492022488122840904126611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1312059968327575744337629 492022488122840904126611)
                ·
                  refine ⟨738033732184261356189917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 492022488122840904126611 738033732184261356189917)
                  ·
                    refine ⟨276762649569098008571219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 738033732184261356189917 276762649569098008571219)
                    ·
                      rfl

theorem cell22_808490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_808490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808490 prefixEnd_808490 := by exact prefixLift 808490
  have htrace : WordTrace (prefixWord ++ tailWord_808490) baseStart_808490 baseEnd_808490 := by
    simpa [prefixWord, tailWord_808490, baseEnd_808490] using wordTrace_append hprefix tailTrace_808490
  have hstable : (prefixWord ++ tailWord_808490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808490).length < 2 ^ (prefixWord ++ tailWord_808490).sum := by decide
  have hdescent : baseEnd_808490 < baseStart_808490 := by decide
  rcases family_descends (prefixWord ++ tailWord_808490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808541 : List Nat := [1, 4, 4, 2, 2, 1, 1, 3, 1, 3]
def baseStart_808541 : Nat := 118140960795 + 808541 * 2 ^ 59
def prefixEnd_808541 : Nat := 4983230072969 + 3 ^ 40 * 808541 * 2
def baseEnd_808541 : Nat := 276780107911350875546063

theorem tailTrace_808541 : CollatzResearch.WordTrace tailWord_808541 prefixEnd_808541 276780107911350875546063 := by
  unfold tailWord_808541
  simp only [CollatzResearch.WordTrace]
  refine ⟨29489912963801519654177477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19659941975867679769451651 29489912963801519654177477)
  ·
    refine ⟨5529358680712784935158277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29489912963801519654177477 5529358680712784935158277)
    ·
      refine ⟨1036754752633647175342177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5529358680712784935158277 1036754752633647175342177)
      ·
        refine ⟨777566064475235381506633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1036754752633647175342177 777566064475235381506633)
        ·
          refine ⟨583174548356426536129975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 777566064475235381506633 583174548356426536129975)
          ·
            refine ⟨874761822534639804194963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583174548356426536129975 874761822534639804194963)
            ·
              refine ⟨1312142733801959706292445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874761822534639804194963 1312142733801959706292445)
              ·
                refine ⟨492053525175734889859667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1312142733801959706292445 492053525175734889859667)
                ·
                  refine ⟨738080287763602334789501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 492053525175734889859667 738080287763602334789501)
                  ·
                    refine ⟨276780107911350875546063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 738080287763602334789501 276780107911350875546063)
                    ·
                      rfl

theorem cell22_808541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_808541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808541 prefixEnd_808541 := by exact prefixLift 808541
  have htrace : WordTrace (prefixWord ++ tailWord_808541) baseStart_808541 baseEnd_808541 := by
    simpa [prefixWord, tailWord_808541, baseEnd_808541] using wordTrace_append hprefix tailTrace_808541
  have hstable : (prefixWord ++ tailWord_808541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808541).length < 2 ^ (prefixWord ++ tailWord_808541).sum := by decide
  have hdescent : baseEnd_808541 < baseStart_808541 := by decide
  rcases family_descends (prefixWord ++ tailWord_808541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808548 : List Nat := [2, 3, 1, 1, 2, 3, 3, 3, 4]
def baseStart_808548 : Nat := 118140960795 + 808548 * 2 ^ 59
def prefixEnd_808548 : Nat := 4983230072969 + 3 ^ 40 * 808548 * 2
def baseEnd_808548 : Nat := 92260834718135063540347

theorem tailTrace_808548 : CollatzResearch.WordTrace tailWord_808548 prefixEnd_808548 92260834718135063540347 := by
  unfold tailWord_808548
  simp only [CollatzResearch.WordTrace]
  refine ⟨14745084137388079924841149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19660112183184106566454865 14745084137388079924841149)
  ·
    refine ⟨5529406551520529971815431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14745084137388079924841149 5529406551520529971815431)
    ·
      refine ⟨8294109827280794957723147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5529406551520529971815431 8294109827280794957723147)
      ·
        refine ⟨12441164740921192436584721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8294109827280794957723147 12441164740921192436584721)
        ·
          refine ⟨9330873555690894327438541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12441164740921192436584721 9330873555690894327438541)
          ·
            refine ⟨3499077583384085372789453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9330873555690894327438541 3499077583384085372789453)
            ·
              refine ⟨1312154093769032014796045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3499077583384085372789453 1312154093769032014796045)
              ·
                refine ⟨492057785163387005548517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1312154093769032014796045 492057785163387005548517)
                ·
                  refine ⟨92260834718135063540347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 492057785163387005548517 92260834718135063540347)
                  ·
                    rfl

theorem cell22_808548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_808548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808548 prefixEnd_808548 := by exact prefixLift 808548
  have htrace : WordTrace (prefixWord ++ tailWord_808548) baseStart_808548 baseEnd_808548 := by
    simpa [prefixWord, tailWord_808548, baseEnd_808548] using wordTrace_append hprefix tailTrace_808548
  have hstable : (prefixWord ++ tailWord_808548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808548).length < 2 ^ (prefixWord ++ tailWord_808548).sum := by decide
  have hdescent : baseEnd_808548 < baseStart_808548 := by decide
  rcases family_descends (prefixWord ++ tailWord_808548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808580 : List Nat := [2, 3, 2, 1, 4, 1, 1, 3, 2, 3]
def baseStart_808580 : Nat := 118140960795 + 808580 * 2 ^ 59
def prefixEnd_808580 : Nat := 4983230072969 + 3 ^ 40 * 808580 * 2
def baseEnd_808580 : Nat := 276793458408367773820943

theorem tailTrace_808580 : CollatzResearch.WordTrace tailWord_808580 prefixEnd_808580 276793458408367773820943 := by
  unfold tailWord_808580
  simp only [CollatzResearch.WordTrace]
  refine ⟨14745667705330114657423597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19660890273773486209898129 14745667705330114657423597)
  ·
    refine ⟨5529625389498792996533849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14745667705330114657423597 5529625389498792996533849)
    ·
      refine ⟨4147219042124094747400387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5529625389498792996533849 4147219042124094747400387)
      ·
        refine ⟨6220828563186142121100581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4147219042124094747400387 6220828563186142121100581)
        ·
          refine ⟨1166405355597401647706359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6220828563186142121100581 1166405355597401647706359)
          ·
            refine ⟨1749608033396102471559539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1166405355597401647706359 1749608033396102471559539)
            ·
              refine ⟨2624412050094153707339309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1749608033396102471559539 2624412050094153707339309)
              ·
                refine ⟨984154518785307640252241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2624412050094153707339309 984154518785307640252241)
                ·
                  refine ⟨738115889088980730189181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 984154518785307640252241 738115889088980730189181)
                  ·
                    refine ⟨276793458408367773820943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 738115889088980730189181 276793458408367773820943)
                    ·
                      rfl

theorem cell22_808580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_808580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808580 prefixEnd_808580 := by exact prefixLift 808580
  have htrace : WordTrace (prefixWord ++ tailWord_808580) baseStart_808580 baseEnd_808580 := by
    simpa [prefixWord, tailWord_808580, baseEnd_808580] using wordTrace_append hprefix tailTrace_808580
  have hstable : (prefixWord ++ tailWord_808580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808580).length < 2 ^ (prefixWord ++ tailWord_808580).sum := by decide
  have hdescent : baseEnd_808580 < baseStart_808580 := by decide
  rcases family_descends (prefixWord ++ tailWord_808580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808616 : List Nat := [2, 1, 7, 1, 1, 2, 2, 2, 4]
def baseStart_808616 : Nat := 118140960795 + 808616 * 2 ^ 59
def prefixEnd_808616 : Nat := 4983230072969 + 3 ^ 40 * 808616 * 2
def baseEnd_808616 : Nat := 92268593981358559973611

theorem tailTrace_808616 : CollatzResearch.WordTrace tailWord_808616 prefixEnd_808616 92268593981358559973611 := by
  unfold tailWord_808616
  simp only [CollatzResearch.WordTrace]
  refine ⟨14746324219264903731578851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19661765625686538308771801 14746324219264903731578851)
  ·
    refine ⟨22119486328897355597368277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14746324219264903731578851 22119486328897355597368277)
    ·
      refine ⟨518425460833531771813319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 22119486328897355597368277 518425460833531771813319)
      ·
        refine ⟨777638191250297657719979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518425460833531771813319 777638191250297657719979)
        ·
          refine ⟨1166457286875446486579969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 777638191250297657719979 1166457286875446486579969)
          ·
            refine ⟨874842965156584864934977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1166457286875446486579969 874842965156584864934977)
            ·
              refine ⟨656132223867438648701233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 874842965156584864934977 656132223867438648701233)
              ·
                refine ⟨492099167900578986525925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 656132223867438648701233 492099167900578986525925)
                ·
                  refine ⟨92268593981358559973611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 492099167900578986525925 92268593981358559973611)
                  ·
                    rfl

theorem cell22_808616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 2, 4].length) (baseStart_808616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808616 prefixEnd_808616 := by exact prefixLift 808616
  have htrace : WordTrace (prefixWord ++ tailWord_808616) baseStart_808616 baseEnd_808616 := by
    simpa [prefixWord, tailWord_808616, baseEnd_808616] using wordTrace_append hprefix tailTrace_808616
  have hstable : (prefixWord ++ tailWord_808616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808616).length < 2 ^ (prefixWord ++ tailWord_808616).sum := by decide
  have hdescent : baseEnd_808616 < baseStart_808616 := by decide
  rcases family_descends (prefixWord ++ tailWord_808616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808636 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 1, 7]
def baseStart_808636 : Nat := 118140960795 + 808636 * 2 ^ 59
def prefixEnd_808636 : Nat := 4983230072969 + 3 ^ 40 * 808636 * 2
def baseEnd_808636 : Nat := 276812628352802294420771

theorem tailTrace_808636 : CollatzResearch.WordTrace tailWord_808636 prefixEnd_808636 276812628352802294420771 := by
  unfold tailWord_808636
  simp only [CollatzResearch.WordTrace]
  refine ⟨14746688949228675439442881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19662251932304900585923841 14746688949228675439442881)
  ·
    refine ⟨11060016711921506579582161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14746688949228675439442881 11060016711921506579582161)
    ·
      refine ⟨8295012533941129934686621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11060016711921506579582161 8295012533941129934686621)
      ·
        refine ⟨3110629700227923725507483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8295012533941129934686621 3110629700227923725507483)
        ·
          refine ⟨4665944550341885588261225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3110629700227923725507483 4665944550341885588261225)
          ·
            refine ⟨3499458412756414191195919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4665944550341885588261225 3499458412756414191195919)
            ·
              refine ⟨5249187619134621286793879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3499458412756414191195919 5249187619134621286793879)
              ·
                refine ⟨7873781428701931930190819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5249187619134621286793879 7873781428701931930190819)
                ·
                  refine ⟨11810672143052897895286229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7873781428701931930190819 11810672143052897895286229)
                  ·
                    refine ⟨276812628352802294420771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11810672143052897895286229 276812628352802294420771)
                    ·
                      rfl

theorem cell22_808636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_808636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808636 prefixEnd_808636 := by exact prefixLift 808636
  have htrace : WordTrace (prefixWord ++ tailWord_808636) baseStart_808636 baseEnd_808636 := by
    simpa [prefixWord, tailWord_808636, baseEnd_808636] using wordTrace_append hprefix tailTrace_808636
  have hstable : (prefixWord ++ tailWord_808636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808636).length < 2 ^ (prefixWord ++ tailWord_808636).sum := by decide
  have hdescent : baseEnd_808636 < baseStart_808636 := by decide
  rcases family_descends (prefixWord ++ tailWord_808636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808638 : List Nat := [4, 2, 1, 1, 2, 2, 2, 3, 5]
def baseStart_808638 : Nat := 118140960795 + 808638 * 2 ^ 59
def prefixEnd_808638 : Nat := 4983230072969 + 3 ^ 40 * 808638 * 2
def baseEnd_808638 : Nat := 92271104331224985290255

theorem tailTrace_808638 : CollatzResearch.WordTrace tailWord_808638 prefixEnd_808638 92271104331224985290255 := by
  unfold tailWord_808638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3686681355556263152557321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19662300562966736813639045 3686681355556263152557321)
  ·
    refine ⟨2765011016667197364417991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3686681355556263152557321 2765011016667197364417991)
    ·
      refine ⟨4147516525000796046626987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2765011016667197364417991 4147516525000796046626987)
      ·
        refine ⟨6221274787501194069940481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4147516525000796046626987 6221274787501194069940481)
        ·
          refine ⟨4665956090625895552455361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6221274787501194069940481 4665956090625895552455361)
          ·
            refine ⟨3499467067969421664341521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4665956090625895552455361 3499467067969421664341521)
            ·
              refine ⟨2624600300977066248256141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3499467067969421664341521 2624600300977066248256141)
              ·
                refine ⟨984225112866399843096053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2624600300977066248256141 984225112866399843096053)
                ·
                  refine ⟨92271104331224985290255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 984225112866399843096053 92271104331224985290255)
                  ·
                    rfl

theorem cell22_808638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_808638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808638 prefixEnd_808638 := by exact prefixLift 808638
  have htrace : WordTrace (prefixWord ++ tailWord_808638) baseStart_808638 baseEnd_808638 := by
    simpa [prefixWord, tailWord_808638, baseEnd_808638] using wordTrace_append hprefix tailTrace_808638
  have hstable : (prefixWord ++ tailWord_808638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808638).length < 2 ^ (prefixWord ++ tailWord_808638).sum := by decide
  have hdescent : baseEnd_808638 < baseStart_808638 := by decide
  rcases family_descends (prefixWord ++ tailWord_808638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808683 : List Nat := [1, 1, 1, 1, 2, 4, 4, 4, 4]
def baseStart_808683 : Nat := 118140960795 + 808683 * 2 ^ 59
def prefixEnd_808683 : Nat := 4983230072969 + 3 ^ 40 * 808683 * 2
def baseEnd_808683 : Nat := 92276239137769946165209

theorem tailTrace_808683 : CollatzResearch.WordTrace tailWord_808683 prefixEnd_808683 92276239137769946165209 := by
  unfold tailWord_808683
  simp only [CollatzResearch.WordTrace]
  refine ⟨29495092129287077905846703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19663394752858051937231135 29495092129287077905846703)
  ·
    refine ⟨44242638193930616858770055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29495092129287077905846703 44242638193930616858770055)
    ·
      refine ⟨66363957290895925288155083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44242638193930616858770055 66363957290895925288155083)
      ·
        refine ⟨99545935936343887932232625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66363957290895925288155083 99545935936343887932232625)
        ·
          refine ⟨74659451952257915949174469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99545935936343887932232625 74659451952257915949174469)
          ·
            refine ⟨13998647241048359240470213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74659451952257915949174469 13998647241048359240470213)
            ·
              refine ⟨2624746357696567357588165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13998647241048359240470213 2624746357696567357588165)
              ·
                refine ⟨492139942068106379547781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2624746357696567357588165 492139942068106379547781)
                ·
                  refine ⟨92276239137769946165209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 492139942068106379547781 92276239137769946165209)
                  ·
                    rfl

theorem cell22_808683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4, 4].length) (baseStart_808683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808683 prefixEnd_808683 := by exact prefixLift 808683
  have htrace : WordTrace (prefixWord ++ tailWord_808683) baseStart_808683 baseEnd_808683 := by
    simpa [prefixWord, tailWord_808683, baseEnd_808683] using wordTrace_append hprefix tailTrace_808683
  have hstable : (prefixWord ++ tailWord_808683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808683).length < 2 ^ (prefixWord ++ tailWord_808683).sum := by decide
  have hdescent : baseEnd_808683 < baseStart_808683 := by decide
  rcases family_descends (prefixWord ++ tailWord_808683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808696 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 6, 4]
def baseStart_808696 : Nat := 118140960795 + 808696 * 2 ^ 59
def prefixEnd_808696 : Nat := 4983230072969 + 3 ^ 40 * 808696 * 2
def baseEnd_808696 : Nat := 276833167578982137920587

theorem tailTrace_808696 : CollatzResearch.WordTrace tailWord_808696 prefixEnd_808696 276833167578982137920587 := by
  unfold tailWord_808696
  simp only [CollatzResearch.WordTrace]
  refine ⟨14747783139119990563034971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19663710852159987417379961 14747783139119990563034971)
  ·
    refine ⟨22121674708679985844552457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14747783139119990563034971 22121674708679985844552457)
    ·
      refine ⟨16591256031509989383414343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22121674708679985844552457 16591256031509989383414343)
      ·
        refine ⟨24886884047264984075121515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16591256031509989383414343 24886884047264984075121515)
        ·
          refine ⟨37330326070897476112682273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24886884047264984075121515 37330326070897476112682273)
          ·
            refine ⟨27997744553173107084511705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37330326070897476112682273 27997744553173107084511705)
            ·
              refine ⟨20998308414879830313383779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27997744553173107084511705 20998308414879830313383779)
              ·
                refine ⟨31497462622319745470075669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20998308414879830313383779 31497462622319745470075669)
                ·
                  refine ⟨1476443560421238068909797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31497462622319745470075669 1476443560421238068909797)
                  ·
                    refine ⟨276833167578982137920587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1476443560421238068909797 276833167578982137920587)
                    ·
                      rfl

theorem cell22_808696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_808696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808696 prefixEnd_808696 := by exact prefixLift 808696
  have htrace : WordTrace (prefixWord ++ tailWord_808696) baseStart_808696 baseEnd_808696 := by
    simpa [prefixWord, tailWord_808696, baseEnd_808696] using wordTrace_append hprefix tailTrace_808696
  have hstable : (prefixWord ++ tailWord_808696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808696).length < 2 ^ (prefixWord ++ tailWord_808696).sum := by decide
  have hdescent : baseEnd_808696 < baseStart_808696 := by decide
  rcases family_descends (prefixWord ++ tailWord_808696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808702 : List Nat := [4, 2, 2, 1, 3, 1, 2, 2, 1, 4]
def baseStart_808702 : Nat := 118140960795 + 808702 * 2 ^ 59
def prefixEnd_808702 : Nat := 4983230072969 + 3 ^ 40 * 808702 * 2
def baseEnd_808702 : Nat := 276835221501600122270569

theorem tailTrace_808702 : CollatzResearch.WordTrace tailWord_808702 prefixEnd_808702 276835221501600122270569 := by
  unfold tailWord_808702
  simp only [CollatzResearch.WordTrace]
  refine ⟨3686973139527280518848545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19663856744145496100525573 3686973139527280518848545)
  ·
    refine ⟨2765229854645460389136409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3686973139527280518848545 2765229854645460389136409)
    ·
      refine ⟨2073922390984095291852307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2765229854645460389136409 2073922390984095291852307)
      ·
        refine ⟨3110883586476142937778461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2073922390984095291852307 3110883586476142937778461)
        ·
          refine ⟨1166581344928553601666923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3110883586476142937778461 1166581344928553601666923)
          ·
            refine ⟨1749872017392830402500385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1166581344928553601666923 1749872017392830402500385)
            ·
              refine ⟨1312404013044622801875289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1749872017392830402500385 1312404013044622801875289)
              ·
                refine ⟨984303009783467101406467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1312404013044622801875289 984303009783467101406467)
                ·
                  refine ⟨1476454514675200652109701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 984303009783467101406467 1476454514675200652109701)
                  ·
                    refine ⟨276835221501600122270569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1476454514675200652109701 276835221501600122270569)
                    ·
                      rfl

theorem cell22_808702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_808702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808702 prefixEnd_808702 := by exact prefixLift 808702
  have htrace : WordTrace (prefixWord ++ tailWord_808702) baseStart_808702 baseEnd_808702 := by
    simpa [prefixWord, tailWord_808702, baseEnd_808702] using wordTrace_append hprefix tailTrace_808702
  have hstable : (prefixWord ++ tailWord_808702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808702).length < 2 ^ (prefixWord ++ tailWord_808702).sum := by decide
  have hdescent : baseEnd_808702 < baseStart_808702 := by decide
  rcases family_descends (prefixWord ++ tailWord_808702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808734 : List Nat := [4, 3, 2, 2, 1, 2, 1, 1, 6]
def baseStart_808734 : Nat := 118140960795 + 808734 * 2 ^ 59
def prefixEnd_808734 : Nat := 4983230072969 + 3 ^ 40 * 808734 * 2
def baseEnd_808734 : Nat := 92282058585187568490157

theorem tailTrace_808734 : CollatzResearch.WordTrace tailWord_808734 prefixEnd_808734 92282058585187568490157 := by
  unfold tailWord_808734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3687119031512789201994157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19664634834734875743968837 3687119031512789201994157)
  ·
    refine ⟨1382669636817295950747809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3687119031512789201994157 1382669636817295950747809)
    ·
      refine ⟨1037002227612971963060857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1382669636817295950747809 1037002227612971963060857)
      ·
        refine ⟨777751670709728972295643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1037002227612971963060857 777751670709728972295643)
        ·
          refine ⟨1166627506064593458443465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 777751670709728972295643 1166627506064593458443465)
          ·
            refine ⟨874970629548445093832599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1166627506064593458443465 874970629548445093832599)
            ·
              refine ⟨1312455944322667640748899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874970629548445093832599 1312455944322667640748899)
              ·
                refine ⟨1968683916484001461123349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1312455944322667640748899 1968683916484001461123349)
                ·
                  refine ⟨92282058585187568490157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1968683916484001461123349 92282058585187568490157)
                  ·
                    rfl

theorem cell22_808734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_808734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808734 prefixEnd_808734 := by exact prefixLift 808734
  have htrace : WordTrace (prefixWord ++ tailWord_808734) baseStart_808734 baseEnd_808734 := by
    simpa [prefixWord, tailWord_808734, baseEnd_808734] using wordTrace_append hprefix tailTrace_808734
  have hstable : (prefixWord ++ tailWord_808734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808734).length < 2 ^ (prefixWord ++ tailWord_808734).sum := by decide
  have hdescent : baseEnd_808734 < baseStart_808734 := by decide
  rcases family_descends (prefixWord ++ tailWord_808734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808835 : List Nat := [1, 1, 1, 3, 4, 2, 1, 5, 4]
def baseStart_808835 : Nat := 118140960795 + 808835 * 2 ^ 59
def prefixEnd_808835 : Nat := 4983230072969 + 3 ^ 40 * 808835 * 2
def baseEnd_808835 : Nat := 92293583373210702898387

theorem tailTrace_808835 : CollatzResearch.WordTrace tailWord_808835 prefixEnd_808835 92293583373210702898387 := by
  unfold tailWord_808835
  simp only [CollatzResearch.WordTrace]
  refine ⟨29500636024736407865379959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19667090683157605243586639 29500636024736407865379959)
  ·
    refine ⟨44250954037104611798069939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29500636024736407865379959 44250954037104611798069939)
    ·
      refine ⟨66376431055656917697104909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44250954037104611798069939 66376431055656917697104909)
      ·
        refine ⟨24891161645871344136414341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66376431055656917697104909 24891161645871344136414341)
        ·
          refine ⟨4667092808600877025577689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24891161645871344136414341 4667092808600877025577689)
          ·
            refine ⟨3500319606450657769183267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4667092808600877025577689 3500319606450657769183267)
            ·
              refine ⟨5250479409675986653774901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3500319606450657769183267 5250479409675986653774901)
              ·
                refine ⟨492232444657123748791397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5250479409675986653774901 492232444657123748791397)
                ·
                  refine ⟨92293583373210702898387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 492232444657123748791397 92293583373210702898387)
                  ·
                    rfl

theorem cell22_808835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5, 4].length) (baseStart_808835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808835 prefixEnd_808835 := by exact prefixLift 808835
  have htrace : WordTrace (prefixWord ++ tailWord_808835) baseStart_808835 baseEnd_808835 := by
    simpa [prefixWord, tailWord_808835, baseEnd_808835] using wordTrace_append hprefix tailTrace_808835
  have hstable : (prefixWord ++ tailWord_808835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808835).length < 2 ^ (prefixWord ++ tailWord_808835).sum := by decide
  have hdescent : baseEnd_808835 < baseStart_808835 := by decide
  rcases family_descends (prefixWord ++ tailWord_808835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808852 : List Nat := [2, 4, 2, 1, 1, 2, 2, 4, 4]
def baseStart_808852 : Nat := 118140960795 + 808852 * 2 ^ 59
def prefixEnd_808852 : Nat := 4983230072969 + 3 ^ 40 * 808852 * 2
def baseEnd_808852 : Nat := 92295523189016577006703

theorem tailTrace_808852 : CollatzResearch.WordTrace tailWord_808852 prefixEnd_808852 92295523189016577006703 := by
  unfold tailWord_808852
  simp only [CollatzResearch.WordTrace]
  refine ⟨14750628032837409884374405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19667504043783213179165873 14750628032837409884374405)
  ·
    refine ⟨2765742756157014353320201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14750628032837409884374405 2765742756157014353320201)
    ·
      refine ⟨2074307067117760764990151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2765742756157014353320201 2074307067117760764990151)
      ·
        refine ⟨3111460600676641147485227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2074307067117760764990151 3111460600676641147485227)
        ·
          refine ⟨4667190901014961721227841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3111460600676641147485227 4667190901014961721227841)
          ·
            refine ⟨3500393175761221290920881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4667190901014961721227841 3500393175761221290920881)
            ·
              refine ⟨2625294881820915968190661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3500393175761221290920881 2625294881820915968190661)
              ·
                refine ⟨492242790341421744035749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2625294881820915968190661 492242790341421744035749)
                ·
                  refine ⟨92295523189016577006703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 492242790341421744035749 92295523189016577006703)
                  ·
                    rfl

theorem cell22_808852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_808852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808852 prefixEnd_808852 := by exact prefixLift 808852
  have htrace : WordTrace (prefixWord ++ tailWord_808852) baseStart_808852 baseEnd_808852 := by
    simpa [prefixWord, tailWord_808852, baseEnd_808852] using wordTrace_append hprefix tailTrace_808852
  have hstable : (prefixWord ++ tailWord_808852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808852).length < 2 ^ (prefixWord ++ tailWord_808852).sum := by decide
  have hdescent : baseEnd_808852 < baseStart_808852 := by decide
  rcases family_descends (prefixWord ++ tailWord_808852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808912 : List Nat := [2, 1, 1, 1, 1, 2, 4, 6, 1, 3]
def baseStart_808912 : Nat := 118140960795 + 808912 * 2 ^ 59
def prefixEnd_808912 : Nat := 4983230072969 + 3 ^ 40 * 808912 * 2
def baseEnd_808912 : Nat := 276907108793229574519925

theorem tailTrace_808912 : CollatzResearch.WordTrace tailWord_808912 prefixEnd_808912 276907108793229574519925 := by
  unfold tailWord_808912
  simp only [CollatzResearch.WordTrace]
  refine ⟨14751722222728725007966495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19668962963638300010621993 14751722222728725007966495)
  ·
    refine ⟨22127583334093087511949743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14751722222728725007966495 22127583334093087511949743)
    ·
      refine ⟨33191375001139631267924615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22127583334093087511949743 33191375001139631267924615)
      ·
        refine ⟨49787062501709446901886923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33191375001139631267924615 49787062501709446901886923)
        ·
          refine ⟨74680593752564170352830385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49787062501709446901886923 74680593752564170352830385)
          ·
            refine ⟨56010445314423127764622789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74680593752564170352830385 56010445314423127764622789)
            ·
              refine ⟨10501958496454336455866773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56010445314423127764622789 10501958496454336455866773)
              ·
                refine ⟨492279304521297021368755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10501958496454336455866773 492279304521297021368755)
                ·
                  refine ⟨738418956781945532053133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 492279304521297021368755 738418956781945532053133)
                  ·
                    refine ⟨276907108793229574519925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 738418956781945532053133 276907108793229574519925)
                    ·
                      rfl

theorem cell22_808912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6, 1, 3].length) (baseStart_808912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808912 prefixEnd_808912 := by exact prefixLift 808912
  have htrace : WordTrace (prefixWord ++ tailWord_808912) baseStart_808912 baseEnd_808912 := by
    simpa [prefixWord, tailWord_808912, baseEnd_808912] using wordTrace_append hprefix tailTrace_808912
  have hstable : (prefixWord ++ tailWord_808912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808912).length < 2 ^ (prefixWord ++ tailWord_808912).sum := by decide
  have hdescent : baseEnd_808912 < baseStart_808912 := by decide
  rcases family_descends (prefixWord ++ tailWord_808912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808918 : List Nat := [5, 2, 1, 1, 3, 2, 2, 1, 2, 3]
def baseStart_808918 : Nat := 118140960795 + 808918 * 2 ^ 59
def prefixEnd_808918 : Nat := 4983230072969 + 3 ^ 40 * 808918 * 2
def baseEnd_808918 : Nat := 276909162715847558869907

theorem tailTrace_808918 : CollatzResearch.WordTrace tailWord_808918 prefixEnd_808918 276909162715847558869907 := by
  unfold tailWord_808918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1843978955214732065040713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19669108855623808693767605 1843978955214732065040713)
  ·
    refine ⟨1382984216411049048780535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1843978955214732065040713 1382984216411049048780535)
    ·
      refine ⟨2074476324616573573170803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1382984216411049048780535 2074476324616573573170803)
      ·
        refine ⟨3111714486924860359756205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2074476324616573573170803 3111714486924860359756205)
        ·
          refine ⟨1166892932596822634908577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3111714486924860359756205 1166892932596822634908577)
          ·
            refine ⟨875169699447616976181433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1166892932596822634908577 875169699447616976181433)
            ·
              refine ⟨656377274585712732136075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 875169699447616976181433 656377274585712732136075)
              ·
                refine ⟨984565911878569098204113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 656377274585712732136075 984565911878569098204113)
                ·
                  refine ⟨738424433908926823653085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 984565911878569098204113 738424433908926823653085)
                  ·
                    refine ⟨276909162715847558869907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 738424433908926823653085 276909162715847558869907)
                    ·
                      rfl

theorem cell22_808918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_808918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808918 prefixEnd_808918 := by exact prefixLift 808918
  have htrace : WordTrace (prefixWord ++ tailWord_808918) baseStart_808918 baseEnd_808918 := by
    simpa [prefixWord, tailWord_808918, baseEnd_808918] using wordTrace_append hprefix tailTrace_808918
  have hstable : (prefixWord ++ tailWord_808918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808918).length < 2 ^ (prefixWord ++ tailWord_808918).sum := by decide
  have hdescent : baseEnd_808918 < baseStart_808918 := by decide
  rcases family_descends (prefixWord ++ tailWord_808918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808955 : List Nat := [1, 1, 1, 1, 1, 3, 4, 5, 1, 4]
def baseStart_808955 : Nat := 118140960795 + 808955 * 2 ^ 59
def prefixEnd_808955 : Nat := 4983230072969 + 3 ^ 40 * 808955 * 2
def baseEnd_808955 : Nat := 276921828571991795694793

theorem tailTrace_808955 : CollatzResearch.WordTrace tailWord_808955 prefixEnd_808955 276921828571991795694793 := by
  unfold tailWord_808955
  simp only [CollatzResearch.WordTrace]
  refine ⟨29505012784301668359748319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19670008522867778906498879 29505012784301668359748319)
  ·
    refine ⟨44257519176452502539622479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29505012784301668359748319 44257519176452502539622479)
    ·
      refine ⟨66386278764678753809433719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44257519176452502539622479 66386278764678753809433719)
      ·
        refine ⟨99579418147018130714150579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66386278764678753809433719 99579418147018130714150579)
        ·
          refine ⟨149369127220527196071225869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99579418147018130714150579 149369127220527196071225869)
          ·
            refine ⟨56013422707697698526709701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149369127220527196071225869 56013422707697698526709701)
            ·
              refine ⟨10502516757693318473758069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56013422707697698526709701 10502516757693318473758069)
              ·
                refine ⟨984610946033748606914819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10502516757693318473758069 984610946033748606914819)
                ·
                  refine ⟨1476916419050622910372229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 984610946033748606914819 1476916419050622910372229)
                  ·
                    refine ⟨276921828571991795694793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1476916419050622910372229 276921828571991795694793)
                    ·
                      rfl

theorem cell22_808955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 4].length) (baseStart_808955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808955 prefixEnd_808955 := by exact prefixLift 808955
  have htrace : WordTrace (prefixWord ++ tailWord_808955) baseStart_808955 baseEnd_808955 := by
    simpa [prefixWord, tailWord_808955, baseEnd_808955] using wordTrace_append hprefix tailTrace_808955
  have hstable : (prefixWord ++ tailWord_808955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808955).length < 2 ^ (prefixWord ++ tailWord_808955).sum := by decide
  have hdescent : baseEnd_808955 < baseStart_808955 := by decide
  rcases family_descends (prefixWord ++ tailWord_808955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808985 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 6, 3]
def baseStart_808985 : Nat := 118140960795 + 808985 * 2 ^ 59
def prefixEnd_808985 : Nat := 4983230072969 + 3 ^ 40 * 808985 * 2
def baseEnd_808985 : Nat := 276932098185081717444701

theorem tailTrace_808985 : CollatzResearch.WordTrace tailWord_808985 prefixEnd_808985 276932098185081717444701 := by
  unfold tailWord_808985
  simp only [CollatzResearch.WordTrace]
  refine ⟨29506106974192983483340409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19670737982795322322226939 29506106974192983483340409)
  ·
    refine ⟨22129580230644737612505307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29506106974192983483340409 22129580230644737612505307)
    ·
      refine ⟨33194370345967106418757961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22129580230644737612505307 33194370345967106418757961)
      ·
        refine ⟨24895777759475329814068471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33194370345967106418757961 24895777759475329814068471)
        ·
          refine ⟨37343666639212994721102707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24895777759475329814068471 37343666639212994721102707)
          ·
            refine ⟨56015499958819492081654061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37343666639212994721102707 56015499958819492081654061)
            ·
              refine ⟨21005812484557309530620273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56015499958819492081654061 21005812484557309530620273)
              ·
                refine ⟨15754359363417982147965205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21005812484557309530620273 15754359363417982147965205)
                ·
                  refine ⟨738485595160217913185869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15754359363417982147965205 738485595160217913185869)
                  ·
                    refine ⟨276932098185081717444701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 738485595160217913185869 276932098185081717444701)
                    ·
                      rfl

theorem cell22_808985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6, 3].length) (baseStart_808985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808985 prefixEnd_808985 := by exact prefixLift 808985
  have htrace : WordTrace (prefixWord ++ tailWord_808985) baseStart_808985 baseEnd_808985 := by
    simpa [prefixWord, tailWord_808985, baseEnd_808985] using wordTrace_append hprefix tailTrace_808985
  have hstable : (prefixWord ++ tailWord_808985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808985).length < 2 ^ (prefixWord ++ tailWord_808985).sum := by decide
  have hdescent : baseEnd_808985 < baseStart_808985 := by decide
  rcases family_descends (prefixWord ++ tailWord_808985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809002 : List Nat := [3, 1, 4, 1, 2, 1, 2, 2, 1, 5]
def baseStart_809002 : Nat := 118140960795 + 809002 * 2 ^ 59
def prefixEnd_809002 : Nat := 4983230072969 + 3 ^ 40 * 809002 * 2
def baseEnd_809002 : Nat := 276937917632499339769649

theorem tailTrace_809002 : CollatzResearch.WordTrace tailWord_809002 prefixEnd_809002 276937917632499339769649 := by
  unfold tailWord_809002
  simp only [CollatzResearch.WordTrace]
  refine ⟨7376681753782848846677315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19671151343420930257806173 7376681753782848846677315)
  ·
    refine ⟨11065022630674273270015973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7376681753782848846677315 11065022630674273270015973)
    ·
      refine ⟨2074691743251426238127995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11065022630674273270015973 2074691743251426238127995)
      ·
        refine ⟨3112037614877139357191993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2074691743251426238127995 3112037614877139357191993)
        ·
          refine ⟨2334028211157854517893995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3112037614877139357191993 2334028211157854517893995)
          ·
            refine ⟨3501042316736781776840993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2334028211157854517893995 3501042316736781776840993)
            ·
              refine ⟨2625781737552586332630745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3501042316736781776840993 2625781737552586332630745)
              ·
                refine ⟨1969336303164439749473059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2625781737552586332630745 1969336303164439749473059)
                ·
                  refine ⟨2954004454746659624209589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1969336303164439749473059 2954004454746659624209589)
                  ·
                    refine ⟨276937917632499339769649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2954004454746659624209589 276937917632499339769649)
                    ·
                      rfl

theorem cell22_809002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_809002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809002 prefixEnd_809002 := by exact prefixLift 809002
  have htrace : WordTrace (prefixWord ++ tailWord_809002) baseStart_809002 baseEnd_809002 := by
    simpa [prefixWord, tailWord_809002, baseEnd_809002] using wordTrace_append hprefix tailTrace_809002
  have hstable : (prefixWord ++ tailWord_809002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809002).length < 2 ^ (prefixWord ++ tailWord_809002).sum := by decide
  have hdescent : baseEnd_809002 < baseStart_809002 := by decide
  rcases family_descends (prefixWord ++ tailWord_809002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809006 : List Nat := [4, 1, 3, 1, 1, 4, 2, 1, 1, 4]
def baseStart_809006 : Nat := 118140960795 + 809006 * 2 ^ 59
def prefixEnd_809006 : Nat := 4983230072969 + 3 ^ 40 * 809006 * 2
def baseEnd_809006 : Nat := 276939286914244662669637

theorem tailTrace_809006 : CollatzResearch.WordTrace tailWord_809006 prefixEnd_809006 276939286914244662669637 := by
  unfold tailWord_809006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3688359113389613008731859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19671248604744602713236581 3688359113389613008731859)
  ·
    refine ⟨5532538670084419513097789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3688359113389613008731859 5532538670084419513097789)
    ·
      refine ⟨2074702001281657317411671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5532538670084419513097789 2074702001281657317411671)
      ·
        refine ⟨3112053001922485976117507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2074702001281657317411671 3112053001922485976117507)
        ·
          refine ⟨4668079502883728964176261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3112053001922485976117507 4668079502883728964176261)
          ·
            refine ⟨875264906790699180783049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4668079502883728964176261 875264906790699180783049)
            ·
              refine ⟨656448680093024385587287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 875264906790699180783049 656448680093024385587287)
              ·
                refine ⟨984673020139536578380931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 656448680093024385587287 984673020139536578380931)
                ·
                  refine ⟨1477009530209304867571397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 984673020139536578380931 1477009530209304867571397)
                  ·
                    refine ⟨276939286914244662669637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1477009530209304867571397 276939286914244662669637)
                    ·
                      rfl

theorem cell22_809006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_809006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809006 prefixEnd_809006 := by exact prefixLift 809006
  have htrace : WordTrace (prefixWord ++ tailWord_809006) baseStart_809006 baseEnd_809006 := by
    simpa [prefixWord, tailWord_809006, baseEnd_809006] using wordTrace_append hprefix tailTrace_809006
  have hstable : (prefixWord ++ tailWord_809006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809006).length < 2 ^ (prefixWord ++ tailWord_809006).sum := by decide
  have hdescent : baseEnd_809006 < baseStart_809006 := by decide
  rcases family_descends (prefixWord ++ tailWord_809006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809047 : List Nat := [1, 1, 3, 2, 2, 1, 4, 2, 3, 3]
def baseStart_809047 : Nat := 118140960795 + 809047 * 2 ^ 59
def prefixEnd_809047 : Nat := 4983230072969 + 3 ^ 40 * 809047 * 2
def baseEnd_809047 : Nat := 276953322052134222394511

theorem tailTrace_809047 : CollatzResearch.WordTrace tailWord_809047 prefixEnd_809047 276953322052134222394511 := by
  unfold tailWord_809047
  simp only [CollatzResearch.WordTrace]
  refine ⟨29508368299968368072097395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19672245533312245381398263 29508368299968368072097395)
  ·
    refine ⟨44262552449952552108146093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29508368299968368072097395 44262552449952552108146093)
    ·
      refine ⟨16598457168732207040554785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44262552449952552108146093 16598457168732207040554785)
      ·
        refine ⟨12448842876549155280416089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16598457168732207040554785 12448842876549155280416089)
        ·
          refine ⟨9336632157411866460312067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12448842876549155280416089 9336632157411866460312067)
          ·
            refine ⟨14004948236117799690468101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9336632157411866460312067 14004948236117799690468101)
            ·
              refine ⟨2625927794272087441962769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14004948236117799690468101 2625927794272087441962769)
              ·
                refine ⟨1969445845704065581472077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2625927794272087441962769 1969445845704065581472077)
                ·
                  refine ⟨738542192139024593052029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1969445845704065581472077 738542192139024593052029)
                  ·
                    refine ⟨276953322052134222394511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 738542192139024593052029 276953322052134222394511)
                    ·
                      rfl

theorem cell22_809047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3, 3].length) (baseStart_809047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809047 prefixEnd_809047 := by exact prefixLift 809047
  have htrace : WordTrace (prefixWord ++ tailWord_809047) baseStart_809047 baseEnd_809047 := by
    simpa [prefixWord, tailWord_809047, baseEnd_809047] using wordTrace_append hprefix tailTrace_809047
  have hstable : (prefixWord ++ tailWord_809047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809047).length < 2 ^ (prefixWord ++ tailWord_809047).sum := by decide
  have hdescent : baseEnd_809047 < baseStart_809047 := by decide
  rcases family_descends (prefixWord ++ tailWord_809047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809060 : List Nat := [2, 3, 1, 1, 2, 1, 3, 2, 7]
def baseStart_809060 : Nat := 118140960795 + 809060 * 2 ^ 59
def prefixEnd_809060 : Nat := 4983230072969 + 3 ^ 40 * 809060 * 2
def baseEnd_809060 : Nat := 92319257405935507273157

theorem tailTrace_809060 : CollatzResearch.WordTrace tailWord_809060 prefixEnd_809060 92319257405935507273157 := by
  unfold tailWord_809060
  simp only [CollatzResearch.WordTrace]
  refine ⟨14754421224460635646160317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19672561632614180861547089 14754421224460635646160317)
  ·
    refine ⟨5532907959172738367310119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14754421224460635646160317 5532907959172738367310119)
    ·
      refine ⟨8299361938759107550965179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5532907959172738367310119 8299361938759107550965179)
      ·
        refine ⟨12449042908138661326447769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8299361938759107550965179 12449042908138661326447769)
        ·
          refine ⟨9336782181103995994835827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12449042908138661326447769 9336782181103995994835827)
          ·
            refine ⟨14005173271655993992253741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9336782181103995994835827 14005173271655993992253741)
            ·
              refine ⟨5251939976870997747095153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14005173271655993992253741 5251939976870997747095153)
              ·
                refine ⟨3938954982653248310321365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5251939976870997747095153 3938954982653248310321365)
                ·
                  refine ⟨92319257405935507273157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3938954982653248310321365 92319257405935507273157)
                  ·
                    rfl

theorem cell22_809060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_809060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809060 prefixEnd_809060 := by exact prefixLift 809060
  have htrace : WordTrace (prefixWord ++ tailWord_809060) baseStart_809060 baseEnd_809060 := by
    simpa [prefixWord, tailWord_809060, baseEnd_809060] using wordTrace_append hprefix tailTrace_809060
  have hstable : (prefixWord ++ tailWord_809060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809060).length < 2 ^ (prefixWord ++ tailWord_809060).sum := by decide
  have hdescent : baseEnd_809060 < baseStart_809060 := by decide
  rcases family_descends (prefixWord ++ tailWord_809060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809135 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 3, 6]
def baseStart_809135 : Nat := 118140960795 + 809135 * 2 ^ 59
def prefixEnd_809135 : Nat := 4983230072969 + 3 ^ 40 * 809135 * 2
def baseEnd_809135 : Nat := 276983446250531326194241

theorem tailTrace_809135 : CollatzResearch.WordTrace tailWord_809135 prefixEnd_809135 276983446250531326194241 := by
  unfold tailWord_809135
  simp only [CollatzResearch.WordTrace]
  refine ⟨29511577923649559101300859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19674385282433039400867239 29511577923649559101300859)
  ·
    refine ⟨44267366885474338651951289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29511577923649559101300859 44267366885474338651951289)
    ·
      refine ⟨33200525164105753988963467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44267366885474338651951289 33200525164105753988963467)
      ·
        refine ⟨49800787746158630983445201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33200525164105753988963467 49800787746158630983445201)
        ·
          refine ⟨37350590809618973237583901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49800787746158630983445201 37350590809618973237583901)
          ·
            refine ⟨14006471553607114964093963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37350590809618973237583901 14006471553607114964093963)
            ·
              refine ⟨21009707330410672446140945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14006471553607114964093963 21009707330410672446140945)
              ·
                refine ⟨15757280497808004334605709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21009707330410672446140945 15757280497808004334605709)
                ·
                  refine ⟨5908980186678001625477141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15757280497808004334605709 5908980186678001625477141)
                  ·
                    refine ⟨276983446250531326194241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5908980186678001625477141 276983446250531326194241)
                    ·
                      rfl

theorem cell22_809135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 6].length) (baseStart_809135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809135 prefixEnd_809135 := by exact prefixLift 809135
  have htrace : WordTrace (prefixWord ++ tailWord_809135) baseStart_809135 baseEnd_809135 := by
    simpa [prefixWord, tailWord_809135, baseEnd_809135] using wordTrace_append hprefix tailTrace_809135
  have hstable : (prefixWord ++ tailWord_809135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809135).length < 2 ^ (prefixWord ++ tailWord_809135).sum := by decide
  have hdescent : baseEnd_809135 < baseStart_809135 := by decide
  rcases family_descends (prefixWord ++ tailWord_809135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809167 : List Nat := [1, 1, 2, 1, 1, 3, 7, 6]
def baseStart_809167 : Nat := 118140960795 + 809167 * 2 ^ 59
def prefixEnd_809167 : Nat := 4983230072969 + 3 ^ 40 * 809167 * 2
def baseEnd_809167 : Nat := 30777155611610434377127

theorem tailTrace_809167 : CollatzResearch.WordTrace tailWord_809167 prefixEnd_809167 30777155611610434377127 := by
  unfold tailWord_809167
  simp only [CollatzResearch.WordTrace]
  refine ⟨29512745059533628566465755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19675163373022419044310503 29512745059533628566465755)
  ·
    refine ⟨44269117589300442849698633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29512745059533628566465755 44269117589300442849698633)
    ·
      refine ⟨33201838191975332137273975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44269117589300442849698633 33201838191975332137273975)
      ·
        refine ⟨49802757287962998205910963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33201838191975332137273975 49802757287962998205910963)
        ·
          refine ⟨74704135931944497308866445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49802757287962998205910963 74704135931944497308866445)
          ·
            refine ⟨28014050974479186490824917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74704135931944497308866445 28014050974479186490824917)
            ·
              refine ⟨656579319714355933378709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 28014050974479186490824917 656579319714355933378709)
              ·
                refine ⟨30777155611610434377127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 656579319714355933378709 30777155611610434377127)
                ·
                  rfl

theorem cell22_809167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 6].length) (baseStart_809167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809167 prefixEnd_809167 := by exact prefixLift 809167
  have htrace : WordTrace (prefixWord ++ tailWord_809167) baseStart_809167 baseEnd_809167 := by
    simpa [prefixWord, tailWord_809167, baseEnd_809167] using wordTrace_append hprefix tailTrace_809167
  have hstable : (prefixWord ++ tailWord_809167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809167).length < 2 ^ (prefixWord ++ tailWord_809167).sum := by decide
  have hdescent : baseEnd_809167 < baseStart_809167 := by decide
  rcases family_descends (prefixWord ++ tailWord_809167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809199 : List Nat := [1, 1, 2, 1, 6, 1, 1, 3, 3, 3]
def baseStart_809199 : Nat := 118140960795 + 809199 * 2 ^ 59
def prefixEnd_809199 : Nat := 4983230072969 + 3 ^ 40 * 809199 * 2
def baseEnd_809199 : Nat := 277005354758456492594045

theorem tailTrace_809199 : CollatzResearch.WordTrace tailWord_809199 prefixEnd_809199 277005354758456492594045 := by
  unfold tailWord_809199
  simp only [CollatzResearch.WordTrace]
  refine ⟨29513912195417698031630651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19675941463611798687753767 29513912195417698031630651)
  ·
    refine ⟨44270868293126547047445977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29513912195417698031630651 44270868293126547047445977)
    ·
      refine ⟨33203151219844910285584483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44270868293126547047445977 33203151219844910285584483)
      ·
        refine ⟨49804726829767365428376725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33203151219844910285584483 49804726829767365428376725)
        ·
          refine ⟨2334596570145345254455159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49804726829767365428376725 2334596570145345254455159)
          ·
            refine ⟨3501894855218017881682739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2334596570145345254455159 3501894855218017881682739)
            ·
              refine ⟨5252842282827026822524109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3501894855218017881682739 5252842282827026822524109)
              ·
                refine ⟨1969815856060135058446541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5252842282827026822524109 1969815856060135058446541)
                ·
                  refine ⟨738680946022550646917453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1969815856060135058446541 738680946022550646917453)
                  ·
                    refine ⟨277005354758456492594045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 738680946022550646917453 277005354758456492594045)
                    ·
                      rfl

theorem cell22_809199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3, 3].length) (baseStart_809199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809199 prefixEnd_809199 := by exact prefixLift 809199
  have htrace : WordTrace (prefixWord ++ tailWord_809199) baseStart_809199 baseEnd_809199 := by
    simpa [prefixWord, tailWord_809199, baseEnd_809199] using wordTrace_append hprefix tailTrace_809199
  have hstable : (prefixWord ++ tailWord_809199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809199).length < 2 ^ (prefixWord ++ tailWord_809199).sum := by decide
  have hdescent : baseEnd_809199 < baseStart_809199 := by decide
  rcases family_descends (prefixWord ++ tailWord_809199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809233 : List Nat := [1, 2, 2, 1, 1, 7, 1, 3, 1, 3]
def baseStart_809233 : Nat := 118140960795 + 809233 * 2 ^ 59
def prefixEnd_809233 : Nat := 4983230072969 + 3 ^ 40 * 809233 * 2
def baseEnd_809233 : Nat := 277016993653291737243941

theorem tailTrace_809233 : CollatzResearch.WordTrace tailWord_809233 prefixEnd_809233 277016993653291737243941 := by
  unfold tailWord_809233
  simp only [CollatzResearch.WordTrace]
  refine ⟨29515152277294521838368353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19676768184863014558912235 29515152277294521838368353)
  ·
    refine ⟨22136364207970891378776265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29515152277294521838368353 22136364207970891378776265)
    ·
      refine ⟨16602273155978168534082199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22136364207970891378776265 16602273155978168534082199)
      ·
        refine ⟨24903409733967252801123299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16602273155978168534082199 24903409733967252801123299)
        ·
          refine ⟨37355114600950879201684949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24903409733967252801123299 37355114600950879201684949)
          ·
            refine ⟨875510498459786231289491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 37355114600950879201684949 875510498459786231289491)
            ·
              refine ⟨1313265747689679346934237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 875510498459786231289491 1313265747689679346934237)
              ·
                refine ⟨492474655383629755100339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1313265747689679346934237 492474655383629755100339)
                ·
                  refine ⟨738711983075444632650509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 492474655383629755100339 738711983075444632650509)
                  ·
                    refine ⟨277016993653291737243941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 738711983075444632650509 277016993653291737243941)
                    ·
                      rfl

theorem cell22_809233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3, 1, 3].length) (baseStart_809233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809233 prefixEnd_809233 := by exact prefixLift 809233
  have htrace : WordTrace (prefixWord ++ tailWord_809233) baseStart_809233 baseEnd_809233 := by
    simpa [prefixWord, tailWord_809233, baseEnd_809233] using wordTrace_append hprefix tailTrace_809233
  have hstable : (prefixWord ++ tailWord_809233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809233).length < 2 ^ (prefixWord ++ tailWord_809233).sum := by decide
  have hdescent : baseEnd_809233 < baseStart_809233 := by decide
  rcases family_descends (prefixWord ++ tailWord_809233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809246 : List Nat := [4, 3, 2, 1, 1, 1, 2, 1, 7]
def baseStart_809246 : Nat := 118140960795 + 809246 * 2 ^ 59
def prefixEnd_809246 : Nat := 4983230072969 + 3 ^ 40 * 809246 * 2
def baseEnd_809246 : Nat := 92340481272988012222967

theorem tailTrace_809246 : CollatzResearch.WordTrace tailWord_809246 prefixEnd_809246 92340481272988012222967 := by
  unfold tailWord_809246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3689453303280928132323949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19677084284164950039061061 3689453303280928132323949)
  ·
    refine ⟨1383544988730348049621481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3689453303280928132323949 1383544988730348049621481)
    ·
      refine ⟨1037658741547761037216111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1383544988730348049621481 1037658741547761037216111)
      ·
        refine ⟨1556488112321641555824167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1037658741547761037216111 1556488112321641555824167)
        ·
          refine ⟨2334732168482462333736251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1556488112321641555824167 2334732168482462333736251)
          ·
            refine ⟨3502098252723693500604377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2334732168482462333736251 3502098252723693500604377)
            ·
              refine ⟨2626573689542770125453283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3502098252723693500604377 2626573689542770125453283)
              ·
                refine ⟨3939860534314155188179925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2626573689542770125453283 3939860534314155188179925)
                ·
                  refine ⟨92340481272988012222967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3939860534314155188179925 92340481272988012222967)
                  ·
                    rfl

theorem cell22_809246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_809246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809246 prefixEnd_809246 := by exact prefixLift 809246
  have htrace : WordTrace (prefixWord ++ tailWord_809246) baseStart_809246 baseEnd_809246 := by
    simpa [prefixWord, tailWord_809246, baseEnd_809246] using wordTrace_append hprefix tailTrace_809246
  have hstable : (prefixWord ++ tailWord_809246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809246).length < 2 ^ (prefixWord ++ tailWord_809246).sum := by decide
  have hdescent : baseEnd_809246 < baseStart_809246 := by decide
  rcases family_descends (prefixWord ++ tailWord_809246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809250 : List Nat := [3, 3, 1, 1, 3, 2, 3, 2, 1, 3]
def baseStart_809250 : Nat := 118140960795 + 809250 * 2 ^ 59
def prefixEnd_809250 : Nat := 4983230072969 + 3 ^ 40 * 809250 * 2
def baseEnd_809250 : Nat := 277022813100709359568889

theorem tailTrace_809250 : CollatzResearch.WordTrace tailWord_809250 prefixEnd_809250 277022813100709359568889 := by
  unfold tailWord_809250
  simp only [CollatzResearch.WordTrace]
  refine ⟨7378943079558233435434301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19677181545488622494491469 7378943079558233435434301)
  ·
    refine ⟨2767103654834337538287863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7378943079558233435434301 2767103654834337538287863)
    ·
      refine ⟨4150655482251506307431795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2767103654834337538287863 4150655482251506307431795)
      ·
        refine ⟨6225983223377259461147693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4150655482251506307431795 6225983223377259461147693)
        ·
          refine ⟨2334743708766472297930385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6225983223377259461147693 2334743708766472297930385)
          ·
            refine ⟨1751057781574854223447789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2334743708766472297930385 1751057781574854223447789)
            ·
              refine ⟨656646668090570333792921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1751057781574854223447789 656646668090570333792921)
              ·
                refine ⟨492485001067927750344691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 656646668090570333792921 492485001067927750344691)
                ·
                  refine ⟨738727501601891625517037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 492485001067927750344691 738727501601891625517037)
                  ·
                    refine ⟨277022813100709359568889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 738727501601891625517037 277022813100709359568889)
                    ·
                      rfl

theorem cell22_809250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_809250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809250 prefixEnd_809250 := by exact prefixLift 809250
  have htrace : WordTrace (prefixWord ++ tailWord_809250) baseStart_809250 baseEnd_809250 := by
    simpa [prefixWord, tailWord_809250, baseEnd_809250] using wordTrace_append hprefix tailTrace_809250
  have hstable : (prefixWord ++ tailWord_809250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809250).length < 2 ^ (prefixWord ++ tailWord_809250).sum := by decide
  have hdescent : baseEnd_809250 < baseStart_809250 := by decide
  rcases family_descends (prefixWord ++ tailWord_809250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809319 : List Nat := [1, 1, 5, 1, 3, 1, 3, 7]
def baseStart_809319 : Nat := 118140960795 + 809319 * 2 ^ 59
def prefixEnd_809319 : Nat := 4983230072969 + 3 ^ 40 * 809319 * 2
def baseEnd_809319 : Nat := 30782937023424019954853

theorem tailTrace_809319 : CollatzResearch.WordTrace tailWord_809319 prefixEnd_809319 30782937023424019954853 := by
  unfold tailWord_809319
  simp only [CollatzResearch.WordTrace]
  refine ⟨29518288954982958525999011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19678859303321972350666007 29518288954982958525999011)
  ·
    refine ⟨44277433432474437788998517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29518288954982958525999011 44277433432474437788998517)
    ·
      refine ⟨4151009384294478542718611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44277433432474437788998517 4151009384294478542718611)
      ·
        refine ⟨6226514076441717814077917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4151009384294478542718611 6226514076441717814077917)
        ·
          refine ⟨2334942778665644180279219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6226514076441717814077917 2334942778665644180279219)
          ·
            refine ⟨3502414167998466270418829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2334942778665644180279219 3502414167998466270418829)
            ·
              refine ⟨1313405312999424851407061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3502414167998466270418829 1313405312999424851407061)
              ·
                refine ⟨30782937023424019954853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1313405312999424851407061 30782937023424019954853)
                ·
                  rfl

theorem cell22_809319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 7].length) (baseStart_809319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809319 prefixEnd_809319 := by exact prefixLift 809319
  have htrace : WordTrace (prefixWord ++ tailWord_809319) baseStart_809319 baseEnd_809319 := by
    simpa [prefixWord, tailWord_809319, baseEnd_809319] using wordTrace_append hprefix tailTrace_809319
  have hstable : (prefixWord ++ tailWord_809319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809319).length < 2 ^ (prefixWord ++ tailWord_809319).sum := by decide
  have hdescent : baseEnd_809319 < baseStart_809319 := by decide
  rcases family_descends (prefixWord ++ tailWord_809319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809368 : List Nat := [2, 1, 2, 5, 1, 2, 2, 1, 3, 3]
def baseStart_809368 : Nat := 118140960795 + 809368 * 2 ^ 59
def prefixEnd_809368 : Nat := 4983230072969 + 3 ^ 40 * 809368 * 2
def baseEnd_809368 : Nat := 277063206912196385118527

theorem tailTrace_809368 : CollatzResearch.WordTrace tailWord_809368 prefixEnd_809368 277063206912196385118527 := by
  unfold tailWord_809368
  simp only [CollatzResearch.WordTrace]
  refine ⟨14760038065902719947266379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19680050754536959929688505 14760038065902719947266379)
  ·
    refine ⟨22140057098854079920899569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14760038065902719947266379 22140057098854079920899569)
    ·
      refine ⟨16605042824140559940674677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22140057098854079920899569 16605042824140559940674677)
      ·
        refine ⟨1556722764763177494438251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16605042824140559940674677 1556722764763177494438251)
        ·
          refine ⟨2335084147144766241657377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1556722764763177494438251 2335084147144766241657377)
          ·
            refine ⟨1751313110358574681243033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2335084147144766241657377 1751313110358574681243033)
            ·
              refine ⟨1313484832768931010932275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1751313110358574681243033 1313484832768931010932275)
              ·
                refine ⟨1970227249153396516398413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1313484832768931010932275 1970227249153396516398413)
                ·
                  refine ⟨738835218432523693649405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1970227249153396516398413 738835218432523693649405)
                  ·
                    refine ⟨277063206912196385118527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 738835218432523693649405 277063206912196385118527)
                    ·
                      rfl

theorem cell22_809368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 3, 3].length) (baseStart_809368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809368 prefixEnd_809368 := by exact prefixLift 809368
  have htrace : WordTrace (prefixWord ++ tailWord_809368) baseStart_809368 baseEnd_809368 := by
    simpa [prefixWord, tailWord_809368, baseEnd_809368] using wordTrace_append hprefix tailTrace_809368
  have hstable : (prefixWord ++ tailWord_809368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809368).length < 2 ^ (prefixWord ++ tailWord_809368).sum := by decide
  have hdescent : baseEnd_809368 < baseStart_809368 := by decide
  rcases family_descends (prefixWord ++ tailWord_809368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809379 : List Nat := [1, 1, 1, 4, 1, 4, 2, 1, 2, 5]
def baseStart_809379 : Nat := 118140960795 + 809379 * 2 ^ 59
def prefixEnd_809379 : Nat := 4983230072969 + 3 ^ 40 * 809379 * 2
def baseEnd_809379 : Nat := 277066972436996023093493

theorem tailTrace_809379 : CollatzResearch.WordTrace tailWord_809379 prefixEnd_809379 277066972436996023093493 := by
  unfold tailWord_809379
  simp only [CollatzResearch.WordTrace]
  refine ⟨29520477334765588773183191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19680318223177059182122127 29520477334765588773183191)
  ·
    refine ⟨44280716002148383159774787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29520477334765588773183191 44280716002148383159774787)
    ·
      refine ⟨66421074003222574739662181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44280716002148383159774787 66421074003222574739662181)
      ·
        refine ⟨12453951375604232763686659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66421074003222574739662181 12453951375604232763686659)
        ·
          refine ⟨18680927063406349145529989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12453951375604232763686659 18680927063406349145529989)
          ·
            refine ⟨3502673824388690464786873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18680927063406349145529989 3502673824388690464786873)
            ·
              refine ⟨2627005368291517848590155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3502673824388690464786873 2627005368291517848590155)
              ·
                refine ⟨3940508052437276772885233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2627005368291517848590155 3940508052437276772885233)
                ·
                  refine ⟨2955381039327957579663925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3940508052437276772885233 2955381039327957579663925)
                  ·
                    refine ⟨277066972436996023093493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2955381039327957579663925 277066972436996023093493)
                    ·
                      rfl

theorem cell22_809379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 5].length) (baseStart_809379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809379 prefixEnd_809379 := by exact prefixLift 809379
  have htrace : WordTrace (prefixWord ++ tailWord_809379) baseStart_809379 baseEnd_809379 := by
    simpa [prefixWord, tailWord_809379, baseEnd_809379] using wordTrace_append hprefix tailTrace_809379
  have hstable : (prefixWord ++ tailWord_809379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809379).length < 2 ^ (prefixWord ++ tailWord_809379).sum := by decide
  have hdescent : baseEnd_809379 < baseStart_809379 := by decide
  rcases family_descends (prefixWord ++ tailWord_809379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809381 : List Nat := [1, 3, 1, 2, 1, 1, 7, 1, 5]
def baseStart_809381 : Nat := 118140960795 + 809381 * 2 ^ 59
def prefixEnd_809381 : Nat := 4983230072969 + 3 ^ 40 * 809381 * 2
def baseEnd_809381 : Nat := 92355885692622894847829

theorem tailTrace_809381 : CollatzResearch.WordTrace tailWord_809381 prefixEnd_809381 92355885692622894847829 := by
  unfold tailWord_809381
  simp only [CollatzResearch.WordTrace]
  refine ⟨29520550280758343114755997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19680366853838895409837331 29520550280758343114755997)
  ·
    refine ⟨11070206355284378668033499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29520550280758343114755997 11070206355284378668033499)
    ·
      refine ⟨16605309532926568002050249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11070206355284378668033499 16605309532926568002050249)
      ·
        refine ⟨12453982149694926001537687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16605309532926568002050249 12453982149694926001537687)
        ·
          refine ⟨18680973224542389002306531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12453982149694926001537687 18680973224542389002306531)
          ·
            refine ⟨28021459836813583503459797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18680973224542389002306531 28021459836813583503459797)
            ·
              refine ⟨656752964925318363362339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 28021459836813583503459797 656752964925318363362339)
              ·
                refine ⟨985129447387977545043509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 656752964925318363362339 985129447387977545043509)
                ·
                  refine ⟨92355885692622894847829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 985129447387977545043509 92355885692622894847829)
                  ·
                    rfl

theorem cell22_809381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 5].length) (baseStart_809381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809381 prefixEnd_809381 := by exact prefixLift 809381
  have htrace : WordTrace (prefixWord ++ tailWord_809381) baseStart_809381 baseEnd_809381 := by
    simpa [prefixWord, tailWord_809381, baseEnd_809381] using wordTrace_append hprefix tailTrace_809381
  have hstable : (prefixWord ++ tailWord_809381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809381).length < 2 ^ (prefixWord ++ tailWord_809381).sum := by decide
  have hdescent : baseEnd_809381 < baseStart_809381 := by decide
  rcases family_descends (prefixWord ++ tailWord_809381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809445 : List Nat := [1, 3, 1, 5, 2, 2, 1, 2, 1, 4]
def baseStart_809445 : Nat := 118140960795 + 809445 * 2 ^ 59
def prefixEnd_809445 : Nat := 4983230072969 + 3 ^ 40 * 809445 * 2
def baseEnd_809445 : Nat := 277089565585793850943291

theorem tailTrace_809445 : CollatzResearch.WordTrace tailWord_809445 prefixEnd_809445 277089565585793850943291 := by
  unfold tailWord_809445
  simp only [CollatzResearch.WordTrace]
  refine ⟨29522884552526482045085789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19681923035017654696723859 29522884552526482045085789)
  ·
    refine ⟨11071081707197430766907171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29522884552526482045085789 11071081707197430766907171)
    ·
      refine ⟨16606622560796146150360757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11071081707197430766907171 16606622560796146150360757)
      ·
        refine ⟨1556870865074638701596321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16606622560796146150360757 1556870865074638701596321)
        ·
          refine ⟨1167653148805979026197241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1556870865074638701596321 1167653148805979026197241)
          ·
            refine ⟨875739861604484269647931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1167653148805979026197241 875739861604484269647931)
            ·
              refine ⟨1313609792406726404471897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 875739861604484269647931 1313609792406726404471897)
              ·
                refine ⟨985207344305044803353923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1313609792406726404471897 985207344305044803353923)
                ·
                  refine ⟨1477811016457567205030885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 985207344305044803353923 1477811016457567205030885)
                  ·
                    refine ⟨277089565585793850943291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1477811016457567205030885 277089565585793850943291)
                    ·
                      rfl

theorem cell22_809445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 4].length) (baseStart_809445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809445 prefixEnd_809445 := by exact prefixLift 809445
  have htrace : WordTrace (prefixWord ++ tailWord_809445) baseStart_809445 baseEnd_809445 := by
    simpa [prefixWord, tailWord_809445, baseEnd_809445] using wordTrace_append hprefix tailTrace_809445
  have hstable : (prefixWord ++ tailWord_809445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809445).length < 2 ^ (prefixWord ++ tailWord_809445).sum := by decide
  have hdescent : baseEnd_809445 < baseStart_809445 := by decide
  rcases family_descends (prefixWord ++ tailWord_809445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809456 : List Nat := [2, 1, 1, 1, 3, 3, 4, 1, 2, 4]
def baseStart_809456 : Nat := 118140960795 + 809456 * 2 ^ 59
def prefixEnd_809456 : Nat := 4983230072969 + 3 ^ 40 * 809456 * 2
def baseEnd_809456 : Nat := 277093331110593488918257

theorem tailTrace_809456 : CollatzResearch.WordTrace tailWord_809456 prefixEnd_809456 277093331110593488918257 := by
  unfold tailWord_809456
  simp only [CollatzResearch.WordTrace]
  refine ⟨14761642877743315461868111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19682190503657753949157481 14761642877743315461868111)
  ·
    refine ⟨22142464316614973192802167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14761642877743315461868111 22142464316614973192802167)
    ·
      refine ⟨33213696474922459789203251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22142464316614973192802167 33213696474922459789203251)
      ·
        refine ⟨49820544712383689683804877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33213696474922459789203251 49820544712383689683804877)
        ·
          refine ⟨18682704267143883631426829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49820544712383689683804877 18682704267143883631426829)
          ·
            refine ⟨7006014100178956361785061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18682704267143883631426829 7006014100178956361785061)
            ·
              refine ⟨1313627643783554317834699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7006014100178956361785061 1313627643783554317834699)
              ·
                refine ⟨1970441465675331476752049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1313627643783554317834699 1970441465675331476752049)
                ·
                  refine ⟨1477831099256498607564037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1970441465675331476752049 1477831099256498607564037)
                  ·
                    refine ⟨277093331110593488918257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1477831099256498607564037 277093331110593488918257)
                    ·
                      rfl

theorem cell22_809456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 2, 4].length) (baseStart_809456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809456 prefixEnd_809456 := by exact prefixLift 809456
  have htrace : WordTrace (prefixWord ++ tailWord_809456) baseStart_809456 baseEnd_809456 := by
    simpa [prefixWord, tailWord_809456, baseEnd_809456] using wordTrace_append hprefix tailTrace_809456
  have hstable : (prefixWord ++ tailWord_809456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809456).length < 2 ^ (prefixWord ++ tailWord_809456).sum := by decide
  have hdescent : baseEnd_809456 < baseStart_809456 := by decide
  rcases family_descends (prefixWord ++ tailWord_809456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809458 : List Nat := [3, 2, 1, 4, 2, 1, 1, 2, 1, 5]
def baseStart_809458 : Nat := 118140960795 + 809458 * 2 ^ 59
def prefixEnd_809458 : Nat := 4983230072969 + 3 ^ 40 * 809458 * 2
def baseEnd_809458 : Nat := 277094015751466150368251

theorem tailTrace_809458 : CollatzResearch.WordTrace tailWord_809458 prefixEnd_809458 277094015751466150368251 := by
  unfold tailWord_809458
  simp only [CollatzResearch.WordTrace]
  refine ⟨7380839675369846316327257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19682239134319590176872685 7380839675369846316327257)
  ·
    refine ⟨5535629756527384737245443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7380839675369846316327257 5535629756527384737245443)
    ·
      refine ⟨8303444634791077105868165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5535629756527384737245443 8303444634791077105868165)
      ·
        refine ⟨1556895869023326957350281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8303444634791077105868165 1556895869023326957350281)
        ·
          refine ⟨1167671901767495218012711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1556895869023326957350281 1167671901767495218012711)
          ·
            refine ⟨1751507852651242827019067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1167671901767495218012711 1751507852651242827019067)
            ·
              refine ⟨2627261778976864240528601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1751507852651242827019067 2627261778976864240528601)
              ·
                refine ⟨1970446334232648180396451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2627261778976864240528601 1970446334232648180396451)
                ·
                  refine ⟨2955669501348972270594677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1970446334232648180396451 2955669501348972270594677)
                  ·
                    refine ⟨277094015751466150368251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2955669501348972270594677 277094015751466150368251)
                    ·
                      rfl

theorem cell22_809458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_809458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809458 prefixEnd_809458 := by exact prefixLift 809458
  have htrace : WordTrace (prefixWord ++ tailWord_809458) baseStart_809458 baseEnd_809458 := by
    simpa [prefixWord, tailWord_809458, baseEnd_809458] using wordTrace_append hprefix tailTrace_809458
  have hstable : (prefixWord ++ tailWord_809458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809458).length < 2 ^ (prefixWord ++ tailWord_809458).sum := by decide
  have hdescent : baseEnd_809458 < baseStart_809458 := by decide
  rcases family_descends (prefixWord ++ tailWord_809458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809533 : List Nat := [1, 4, 1, 3, 2, 1, 3, 2, 5]
def baseStart_809533 : Nat := 118140960795 + 809533 * 2 ^ 59
def prefixEnd_809533 : Nat := 4983230072969 + 3 ^ 40 * 809533 * 2
def baseEnd_809533 : Nat := 92373229928063651581007

theorem tailTrace_809533 : CollatzResearch.WordTrace tailWord_809533 prefixEnd_809533 92373229928063651581007 := by
  unfold tailWord_809533
  simp only [CollatzResearch.WordTrace]
  refine ⟨29526094176207673074289253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19684062784138448716192835 29526094176207673074289253)
  ·
    refine ⟨5536142658038938701429235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29526094176207673074289253 5536142658038938701429235)
    ·
      refine ⟨8304213987058408052143853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5536142658038938701429235 8304213987058408052143853)
      ·
        refine ⟨3114080245146903019553945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8304213987058408052143853 3114080245146903019553945)
        ·
          refine ⟨2335560183860177264665459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3114080245146903019553945 2335560183860177264665459)
          ·
            refine ⟨3503340275790265896998189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2335560183860177264665459 3503340275790265896998189)
            ·
              refine ⟨1313752603421349711374321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3503340275790265896998189 1313752603421349711374321)
              ·
                refine ⟨985314452566012283530741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1313752603421349711374321 985314452566012283530741)
                ·
                  refine ⟨92373229928063651581007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 985314452566012283530741 92373229928063651581007)
                  ·
                    rfl

theorem cell22_809533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_809533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809533 prefixEnd_809533 := by exact prefixLift 809533
  have htrace : WordTrace (prefixWord ++ tailWord_809533) baseStart_809533 baseEnd_809533 := by
    simpa [prefixWord, tailWord_809533, baseEnd_809533] using wordTrace_append hprefix tailTrace_809533
  have hstable : (prefixWord ++ tailWord_809533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809533).length < 2 ^ (prefixWord ++ tailWord_809533).sum := by decide
  have hdescent : baseEnd_809533 < baseStart_809533 := by decide
  rcases family_descends (prefixWord ++ tailWord_809533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809591 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 4, 4]
def baseStart_809591 : Nat := 118140960795 + 809591 * 2 ^ 59
def prefixEnd_809591 : Nat := 4983230072969 + 3 ^ 40 * 809591 * 2
def baseEnd_809591 : Nat := 277139544369498136792843

theorem tailTrace_809591 : CollatzResearch.WordTrace tailWord_809591 prefixEnd_809591 277139544369498136792843 := by
  unfold tailWord_809591
  simp only [CollatzResearch.WordTrace]
  refine ⟨29528209609997548979900627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19685473073331699319933751 29528209609997548979900627)
  ·
    refine ⟨44292314414996323469850941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29528209609997548979900627 44292314414996323469850941)
    ·
      refine ⟨16609617905623621301194103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44292314414996323469850941 16609617905623621301194103)
      ·
        refine ⟨24914426858435431951791155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16609617905623621301194103 24914426858435431951791155)
        ·
          refine ⟨37371640287653147927686733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24914426858435431951791155 37371640287653147927686733)
          ·
            refine ⟨14014365107869930472882525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37371640287653147927686733 14014365107869930472882525)
            ·
              refine ⟨5255386915451223927330947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14014365107869930472882525 5255386915451223927330947)
              ·
                refine ⟨7883080373176835890996421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5255386915451223927330947 7883080373176835890996421)
                ·
                  refine ⟨1478077569970656729561829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7883080373176835890996421 1478077569970656729561829)
                  ·
                    refine ⟨277139544369498136792843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1478077569970656729561829 277139544369498136792843)
                    ·
                      rfl

theorem cell22_809591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_809591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809591 prefixEnd_809591 := by exact prefixLift 809591
  have htrace : WordTrace (prefixWord ++ tailWord_809591) baseStart_809591 baseEnd_809591 := by
    simpa [prefixWord, tailWord_809591, baseEnd_809591] using wordTrace_append hprefix tailTrace_809591
  have hstable : (prefixWord ++ tailWord_809591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809591).length < 2 ^ (prefixWord ++ tailWord_809591).sum := by decide
  have hdescent : baseEnd_809591 < baseStart_809591 := by decide
  rcases family_descends (prefixWord ++ tailWord_809591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809593 : List Nat := [1, 2, 1, 3, 3, 2, 2, 1, 4, 3]
def baseStart_809593 : Nat := 118140960795 + 809593 * 2 ^ 59
def prefixEnd_809593 : Nat := 4983230072969 + 3 ^ 40 * 809593 * 2
def baseEnd_809593 : Nat := 277140229010370798242837

theorem tailTrace_809593 : CollatzResearch.WordTrace tailWord_809593 prefixEnd_809593 277140229010370798242837 := by
  unfold tailWord_809593
  simp only [CollatzResearch.WordTrace]
  refine ⟨29528282555990303321473433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19685521703993535547648955 29528282555990303321473433)
  ·
    refine ⟨22146211916992727491105075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29528282555990303321473433 22146211916992727491105075)
    ·
      refine ⟨33219317875489091236657613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22146211916992727491105075 33219317875489091236657613)
      ·
        refine ⟨12457244203308409213746605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33219317875489091236657613 12457244203308409213746605)
        ·
          refine ⟨4671466576240653455154977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12457244203308409213746605 4671466576240653455154977)
          ·
            refine ⟨3503599932180490091366233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4671466576240653455154977 3503599932180490091366233)
            ·
              refine ⟨2627699949135367568524675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3503599932180490091366233 2627699949135367568524675)
              ·
                refine ⟨3941549923703051352787013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2627699949135367568524675 3941549923703051352787013)
                ·
                  refine ⟨739040610694322128647565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3941549923703051352787013 739040610694322128647565)
                  ·
                    refine ⟨277140229010370798242837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 739040610694322128647565 277140229010370798242837)
                    ·
                      rfl

theorem cell22_809593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4, 3].length) (baseStart_809593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809593 prefixEnd_809593 := by exact prefixLift 809593
  have htrace : WordTrace (prefixWord ++ tailWord_809593) baseStart_809593 baseEnd_809593 := by
    simpa [prefixWord, tailWord_809593, baseEnd_809593] using wordTrace_append hprefix tailTrace_809593
  have hstable : (prefixWord ++ tailWord_809593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809593).length < 2 ^ (prefixWord ++ tailWord_809593).sum := by decide
  have hdescent : baseEnd_809593 < baseStart_809593 := by decide
  rcases family_descends (prefixWord ++ tailWord_809593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809653 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 2, 6]
def baseStart_809653 : Nat := 118140960795 + 809653 * 2 ^ 59
def prefixEnd_809653 : Nat := 4983230072969 + 3 ^ 40 * 809653 * 2
def baseEnd_809653 : Nat := 277160768236550641742653

theorem tailTrace_809653 : CollatzResearch.WordTrace tailWord_809653 prefixEnd_809653 277160768236550641742653 := by
  unfold tailWord_809653
  simp only [CollatzResearch.WordTrace]
  refine ⟨29530470935772933568657613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19686980623848622379105075 29530470935772933568657613)
  ·
    refine ⟨11073926600914850088246605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29530470935772933568657613 11073926600914850088246605)
    ·
      refine ⟨4152722475343068783092477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11073926600914850088246605 4152722475343068783092477)
      ·
        refine ⟨1557270928253650793659679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4152722475343068783092477 1557270928253650793659679)
        ·
          refine ⟨2335906392380476190489519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1557270928253650793659679 2335906392380476190489519)
          ·
            refine ⟨3503859588570714285734279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2335906392380476190489519 3503859588570714285734279)
            ·
              refine ⟨5255789382856071428601419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3503859588570714285734279 5255789382856071428601419)
              ·
                refine ⟨7883684074284107142902129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5255789382856071428601419 7883684074284107142902129)
                ·
                  refine ⟨5912763055713080357176597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7883684074284107142902129 5912763055713080357176597)
                  ·
                    refine ⟨277160768236550641742653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5912763055713080357176597 277160768236550641742653)
                    ·
                      rfl

theorem cell22_809653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_809653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809653 prefixEnd_809653 := by exact prefixLift 809653
  have htrace : WordTrace (prefixWord ++ tailWord_809653) baseStart_809653 baseEnd_809653 := by
    simpa [prefixWord, tailWord_809653, baseEnd_809653] using wordTrace_append hprefix tailTrace_809653
  have hstable : (prefixWord ++ tailWord_809653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809653).length < 2 ^ (prefixWord ++ tailWord_809653).sum := by decide
  have hdescent : baseEnd_809653 < baseStart_809653 := by decide
  rcases family_descends (prefixWord ++ tailWord_809653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809696 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 10]
def baseStart_809696 : Nat := 118140960795 + 809696 * 2 ^ 59
def prefixEnd_809696 : Nat := 4983230072969 + 3 ^ 40 * 809696 * 2
def baseEnd_809696 : Nat := 92391829338437620972507

theorem tailTrace_809696 : CollatzResearch.WordTrace tailWord_809696 prefixEnd_809696 92391829338437620972507 := by
  unfold tailWord_809696
  simp only [CollatzResearch.WordTrace]
  refine ⟨14766019637308575956236471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19688026183078101274981961 14766019637308575956236471)
  ·
    refine ⟨22149029455962863934354707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14766019637308575956236471 22149029455962863934354707)
    ·
      refine ⟨33223544183944295901532061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22149029455962863934354707 33223544183944295901532061)
      ·
        refine ⟨12458829068979110963074523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33223544183944295901532061 12458829068979110963074523)
        ·
          refine ⟨18688243603468666444611785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12458829068979110963074523 18688243603468666444611785)
          ·
            refine ⟨14016182702601499833458839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18688243603468666444611785 14016182702601499833458839)
            ·
              refine ⟨21024274053902249750188259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14016182702601499833458839 21024274053902249750188259)
              ·
                refine ⟨31536411080853374625282389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21024274053902249750188259 31536411080853374625282389)
                ·
                  refine ⟨92391829338437620972507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 31536411080853374625282389 92391829338437620972507)
                  ·
                    rfl

theorem cell22_809696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 10].length) (baseStart_809696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809696 prefixEnd_809696 := by exact prefixLift 809696
  have htrace : WordTrace (prefixWord ++ tailWord_809696) baseStart_809696 baseEnd_809696 := by
    simpa [prefixWord, tailWord_809696, baseEnd_809696] using wordTrace_append hprefix tailTrace_809696
  have hstable : (prefixWord ++ tailWord_809696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809696).length < 2 ^ (prefixWord ++ tailWord_809696).sum := by decide
  have hdescent : baseEnd_809696 < baseStart_809696 := by decide
  rcases family_descends (prefixWord ++ tailWord_809696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809713 : List Nat := [1, 2, 2, 2, 2, 2, 4, 1, 6]
def baseStart_809713 : Nat := 118140960795 + 809713 * 2 ^ 59
def prefixEnd_809713 : Nat := 4983230072969 + 3 ^ 40 * 809713 * 2
def baseEnd_809713 : Nat := 92393769154243495080823

theorem tailTrace_809713 : CollatzResearch.WordTrace tailWord_809713 prefixEnd_809713 92393769154243495080823 := by
  unfold tailWord_809713
  simp only [CollatzResearch.WordTrace]
  refine ⟨29532659315555563815841793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19688439543703709210561195 29532659315555563815841793)
  ·
    refine ⟨22149494486666672861881345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29532659315555563815841793 22149494486666672861881345)
    ·
      refine ⟨16612120865000004646411009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22149494486666672861881345 16612120865000004646411009)
      ·
        refine ⟨12459090648750003484808257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16612120865000004646411009 12459090648750003484808257)
        ·
          refine ⟨9344317986562502613606193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12459090648750003484808257 9344317986562502613606193)
          ·
            refine ⟨7008238489921876960204645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9344317986562502613606193 7008238489921876960204645)
            ·
              refine ⟨1314044716860351930038371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7008238489921876960204645 1314044716860351930038371)
              ·
                refine ⟨1971067075290527895057557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1314044716860351930038371 1971067075290527895057557)
                ·
                  refine ⟨92393769154243495080823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1971067075290527895057557 92393769154243495080823)
                  ·
                    rfl

theorem cell22_809713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 6].length) (baseStart_809713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809713 prefixEnd_809713 := by exact prefixLift 809713
  have htrace : WordTrace (prefixWord ++ tailWord_809713) baseStart_809713 baseEnd_809713 := by
    simpa [prefixWord, tailWord_809713, baseEnd_809713] using wordTrace_append hprefix tailTrace_809713
  have hstable : (prefixWord ++ tailWord_809713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809713).length < 2 ^ (prefixWord ++ tailWord_809713).sum := by decide
  have hdescent : baseEnd_809713 < baseStart_809713 := by decide
  rcases family_descends (prefixWord ++ tailWord_809713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809728 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 8, 3]
def baseStart_809728 : Nat := 118140960795 + 809728 * 2 ^ 59
def prefixEnd_809728 : Nat := 4983230072969 + 3 ^ 40 * 809728 * 2
def baseEnd_809728 : Nat := 277186442269275446117423

theorem tailTrace_809728 : CollatzResearch.WordTrace tailWord_809728 prefixEnd_809728 277186442269275446117423 := by
  unfold tailWord_809728
  simp only [CollatzResearch.WordTrace]
  refine ⟨14766603205250610688818919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19688804273667480918425225 14766603205250610688818919)
  ·
    refine ⟨22149904807875916033228379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14766603205250610688818919 22149904807875916033228379)
    ·
      refine ⟨33224857211813874049842569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22149904807875916033228379 33224857211813874049842569)
      ·
        refine ⟨24918642908860405537381927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33224857211813874049842569 24918642908860405537381927)
        ·
          refine ⟨37377964363290608306072891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24918642908860405537381927 37377964363290608306072891)
          ·
            refine ⟨56066946544935912459109337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37377964363290608306072891 56066946544935912459109337)
            ·
              refine ⟨42050209908701934344332003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56066946544935912459109337 42050209908701934344332003)
              ·
                refine ⟨63075314863052901516498005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42050209908701934344332003 63075314863052901516498005)
                ·
                  refine ⟨739163846051401189646461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 63075314863052901516498005 739163846051401189646461)
                  ·
                    refine ⟨277186442269275446117423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 739163846051401189646461 277186442269275446117423)
                    ·
                      rfl

theorem cell22_809728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 8, 3].length) (baseStart_809728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809728 prefixEnd_809728 := by exact prefixLift 809728
  have htrace : WordTrace (prefixWord ++ tailWord_809728) baseStart_809728 baseEnd_809728 := by
    simpa [prefixWord, tailWord_809728, baseEnd_809728] using wordTrace_append hprefix tailTrace_809728
  have hstable : (prefixWord ++ tailWord_809728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809728).length < 2 ^ (prefixWord ++ tailWord_809728).sum := by decide
  have hdescent : baseEnd_809728 < baseStart_809728 := by decide
  rcases family_descends (prefixWord ++ tailWord_809728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809730 : List Nat := [3, 4, 1, 1, 1, 2, 2, 2, 6]
def baseStart_809730 : Nat := 118140960795 + 809730 * 2 ^ 59
def prefixEnd_809730 : Nat := 4983230072969 + 3 ^ 40 * 809730 * 2
def baseEnd_809730 : Nat := 92395708970049369189139

theorem tailTrace_809730 : CollatzResearch.WordTrace tailWord_809730 prefixEnd_809730 92395708970049369189139 := by
  unfold tailWord_809730
  simp only [CollatzResearch.WordTrace]
  refine ⟨7383319839123493929802661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19688852904329317146140429 7383319839123493929802661)
  ·
    refine ⟨1384372469835655111837999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7383319839123493929802661 1384372469835655111837999)
    ·
      refine ⟨2076558704753482667756999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1384372469835655111837999 2076558704753482667756999)
      ·
        refine ⟨3114838057130224001635499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2076558704753482667756999 3114838057130224001635499)
        ·
          refine ⟨4672257085695336002453249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3114838057130224001635499 4672257085695336002453249)
          ·
            refine ⟨3504192814271502001839937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4672257085695336002453249 3504192814271502001839937)
            ·
              refine ⟨2628144610703626501379953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3504192814271502001839937 2628144610703626501379953)
              ·
                refine ⟨1971108458027719876034965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2628144610703626501379953 1971108458027719876034965)
                ·
                  refine ⟨92395708970049369189139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1971108458027719876034965 92395708970049369189139)
                  ·
                    rfl

theorem cell22_809730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_809730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809730 prefixEnd_809730 := by exact prefixLift 809730
  have htrace : WordTrace (prefixWord ++ tailWord_809730) baseStart_809730 baseEnd_809730 := by
    simpa [prefixWord, tailWord_809730, baseEnd_809730] using wordTrace_append hprefix tailTrace_809730
  have hstable : (prefixWord ++ tailWord_809730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809730).length < 2 ^ (prefixWord ++ tailWord_809730).sum := by decide
  have hdescent : baseEnd_809730 < baseStart_809730 := by decide
  rcases family_descends (prefixWord ++ tailWord_809730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809743 : List Nat := [1, 1, 2, 1, 1, 1, 6, 3, 2, 4]
def baseStart_809743 : Nat := 118140960795 + 809743 * 2 ^ 59
def prefixEnd_809743 : Nat := 4983230072969 + 3 ^ 40 * 809743 * 2
def baseEnd_809743 : Nat := 277191577075820406992377

theorem tailTrace_809743 : CollatzResearch.WordTrace tailWord_809743 prefixEnd_809743 277191577075820406992377 := by
  unfold tailWord_809743
  simp only [CollatzResearch.WordTrace]
  refine ⟨29533753505446878939433883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19689169003631252626289255 29533753505446878939433883)
  ·
    refine ⟨44300630258170318409150825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29533753505446878939433883 44300630258170318409150825)
    ·
      refine ⟨33225472693627738806863119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44300630258170318409150825 33225472693627738806863119)
      ·
        refine ⟨49838209040441608210294679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33225472693627738806863119 49838209040441608210294679)
        ·
          refine ⟨74757313560662412315442019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49838209040441608210294679 74757313560662412315442019)
          ·
            refine ⟨112135970340993618473163029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74757313560662412315442019 112135970340993618473163029)
            ·
              refine ⟨5256373609734075865929517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112135970340993618473163029 5256373609734075865929517)
              ·
                refine ⟨1971140103650278449723569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5256373609734075865929517 1971140103650278449723569)
                ·
                  refine ⟨1478355077737708837292677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1971140103650278449723569 1478355077737708837292677)
                  ·
                    refine ⟨277191577075820406992377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1478355077737708837292677 277191577075820406992377)
                    ·
                      rfl

theorem cell22_809743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 4].length) (baseStart_809743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809743 prefixEnd_809743 := by exact prefixLift 809743
  have htrace : WordTrace (prefixWord ++ tailWord_809743) baseStart_809743 baseEnd_809743 := by
    simpa [prefixWord, tailWord_809743, baseEnd_809743] using wordTrace_append hprefix tailTrace_809743
  have hstable : (prefixWord ++ tailWord_809743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809743).length < 2 ^ (prefixWord ++ tailWord_809743).sum := by decide
  have hdescent : baseEnd_809743 < baseStart_809743 := by decide
  rcases family_descends (prefixWord ++ tailWord_809743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809760 : List Nat := [2, 1, 1, 5, 1, 3, 1, 2, 2, 4]
def baseStart_809760 : Nat := 118140960795 + 809760 * 2 ^ 59
def prefixEnd_809760 : Nat := 4983230072969 + 3 ^ 40 * 809760 * 2
def baseEnd_809760 : Nat := 277197396523238029317325

theorem tailTrace_809760 : CollatzResearch.WordTrace tailWord_809760 prefixEnd_809760 277197396523238029317325 := by
  unfold tailWord_809760
  simp only [CollatzResearch.WordTrace]
  refine ⟨14767186773192645421401367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19689582364256860561868489 14767186773192645421401367)
  ·
    refine ⟨22150780159788968132102051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14767186773192645421401367 22150780159788968132102051)
    ·
      refine ⟨33226170239683452198153077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22150780159788968132102051 33226170239683452198153077)
      ·
        refine ⟨3114953459970323643576851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33226170239683452198153077 3114953459970323643576851)
        ·
          refine ⟨4672430189955485465365277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3114953459970323643576851 4672430189955485465365277)
          ·
            refine ⟨1752161321233307049511979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4672430189955485465365277 1752161321233307049511979)
            ·
              refine ⟨2628241981849960574267969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1752161321233307049511979 2628241981849960574267969)
              ·
                refine ⟨1971181486387470430700977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2628241981849960574267969 1971181486387470430700977)
                ·
                  refine ⟨1478386114790602823025733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1971181486387470430700977 1478386114790602823025733)
                  ·
                    refine ⟨277197396523238029317325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1478386114790602823025733 277197396523238029317325)
                    ·
                      rfl

theorem cell22_809760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 2, 4].length) (baseStart_809760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809760 prefixEnd_809760 := by exact prefixLift 809760
  have htrace : WordTrace (prefixWord ++ tailWord_809760) baseStart_809760 baseEnd_809760 := by
    simpa [prefixWord, tailWord_809760, baseEnd_809760] using wordTrace_append hprefix tailTrace_809760
  have hstable : (prefixWord ++ tailWord_809760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809760).length < 2 ^ (prefixWord ++ tailWord_809760).sum := by decide
  have hdescent : baseEnd_809760 < baseStart_809760 := by decide
  rcases family_descends (prefixWord ++ tailWord_809760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809764 : List Nat := [2, 3, 1, 3, 3, 1, 3, 2, 4]
def baseStart_809764 : Nat := 118140960795 + 809764 * 2 ^ 59
def prefixEnd_809764 : Nat := 4983230072969 + 3 ^ 40 * 809764 * 2
def baseEnd_809764 : Nat := 92399588601661117405771

theorem tailTrace_809764 : CollatzResearch.WordTrace tailWord_809764 prefixEnd_809764 92399588601661117405771 := by
  unfold tailWord_809764
  simp only [CollatzResearch.WordTrace]
  refine ⟨14767259719185399762974173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19689679625580533017298897 14767259719185399762974173)
  ·
    refine ⟨5537722394694524911115315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14767259719185399762974173 5537722394694524911115315)
    ·
      refine ⟨8306583592041787366672973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5537722394694524911115315 8306583592041787366672973)
      ·
        refine ⟨3114968847015670262502365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8306583592041787366672973 3114968847015670262502365)
        ·
          refine ⟨1168113317630876348438387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3114968847015670262502365 1168113317630876348438387)
          ·
            refine ⟨1752169976446314522657581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1168113317630876348438387 1752169976446314522657581)
            ·
              refine ⟨657063741167367945996593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1752169976446314522657581 657063741167367945996593)
              ·
                refine ⟨492797805875525959497445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 657063741167367945996593 492797805875525959497445)
                ·
                  refine ⟨92399588601661117405771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 492797805875525959497445 92399588601661117405771)
                  ·
                    rfl

theorem cell22_809764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_809764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809764 prefixEnd_809764 := by exact prefixLift 809764
  have htrace : WordTrace (prefixWord ++ tailWord_809764) baseStart_809764 baseEnd_809764 := by
    simpa [prefixWord, tailWord_809764, baseEnd_809764] using wordTrace_append hprefix tailTrace_809764
  have hstable : (prefixWord ++ tailWord_809764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809764).length < 2 ^ (prefixWord ++ tailWord_809764).sum := by decide
  have hdescent : baseEnd_809764 < baseStart_809764 := by decide
  rcases family_descends (prefixWord ++ tailWord_809764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809779 : List Nat := [1, 1, 1, 2, 6, 3, 2, 1, 2, 3]
def baseStart_809779 : Nat := 118140960795 + 809779 * 2 ^ 59
def prefixEnd_809779 : Nat := 4983230072969 + 3 ^ 40 * 809779 * 2
def baseEnd_809779 : Nat := 277203900611528313092267

theorem tailTrace_809779 : CollatzResearch.WordTrace tailWord_809779 prefixEnd_809779 277203900611528313092267 := by
  unfold tailWord_809779
  simp only [CollatzResearch.WordTrace]
  refine ⟨29535066533316457087744391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19690044355544304725162927 29535066533316457087744391)
  ·
    refine ⟨44302599799974685631616587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29535066533316457087744391 44302599799974685631616587)
    ·
      refine ⟨66453899699962028447424881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44302599799974685631616587 66453899699962028447424881)
      ·
        refine ⟨49840424774971521335568661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66453899699962028447424881 49840424774971521335568661)
        ·
          refine ⟨2336269911326790062604781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49840424774971521335568661 2336269911326790062604781)
          ·
            refine ⟨876101216747546273476793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2336269911326790062604781 876101216747546273476793)
            ·
              refine ⟨657075912560659705107595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 876101216747546273476793 657075912560659705107595)
              ·
                refine ⟨985613868840989557661393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 657075912560659705107595 985613868840989557661393)
                ·
                  refine ⟨739210401630742168246045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 985613868840989557661393 739210401630742168246045)
                  ·
                    refine ⟨277203900611528313092267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 739210401630742168246045 277203900611528313092267)
                    ·
                      rfl

theorem cell22_809779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 2, 3].length) (baseStart_809779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809779 prefixEnd_809779 := by exact prefixLift 809779
  have htrace : WordTrace (prefixWord ++ tailWord_809779) baseStart_809779 baseEnd_809779 := by
    simpa [prefixWord, tailWord_809779, baseEnd_809779] using wordTrace_append hprefix tailTrace_809779
  have hstable : (prefixWord ++ tailWord_809779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809779).length < 2 ^ (prefixWord ++ tailWord_809779).sum := by decide
  have hdescent : baseEnd_809779 < baseStart_809779 := by decide
  rcases family_descends (prefixWord ++ tailWord_809779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809850 : List Nat := [3, 1, 1, 1, 1, 1, 3, 6, 1, 4]
def baseStart_809850 : Nat := 118140960795 + 809850 * 2 ^ 59
def prefixEnd_809850 : Nat := 4983230072969 + 3 ^ 40 * 809850 * 2
def baseEnd_809850 : Nat := 277228205362507794567049

theorem tailTrace_809850 : CollatzResearch.WordTrace tailWord_809850 prefixEnd_809850 277228205362507794567049 := by
  unfold tailWord_809850
  simp only [CollatzResearch.WordTrace]
  refine ⟨7384414029014809053394751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19691770744039490809052669 7384414029014809053394751)
  ·
    refine ⟨11076621043522213580092127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7384414029014809053394751 11076621043522213580092127)
    ·
      refine ⟨16614931565283320370138191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11076621043522213580092127 16614931565283320370138191)
      ·
        refine ⟨24922397347924980555207287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16614931565283320370138191 24922397347924980555207287)
        ·
          refine ⟨37383596021887470832810931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24922397347924980555207287 37383596021887470832810931)
          ·
            refine ⟨56075394032831206249216397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37383596021887470832810931 56075394032831206249216397)
            ·
              refine ⟨21028272762311702343456149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56075394032831206249216397 21028272762311702343456149)
              ·
                refine ⟨985700285733361047349507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21028272762311702343456149 985700285733361047349507)
                ·
                  refine ⟨1478550428600041571024261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 985700285733361047349507 1478550428600041571024261)
                  ·
                    refine ⟨277228205362507794567049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1478550428600041571024261 277228205362507794567049)
                    ·
                      rfl

theorem cell22_809850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_809850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809850 prefixEnd_809850 := by exact prefixLift 809850
  have htrace : WordTrace (prefixWord ++ tailWord_809850) baseStart_809850 baseEnd_809850 := by
    simpa [prefixWord, tailWord_809850, baseEnd_809850] using wordTrace_append hprefix tailTrace_809850
  have hstable : (prefixWord ++ tailWord_809850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809850).length < 2 ^ (prefixWord ++ tailWord_809850).sum := by decide
  have hdescent : baseEnd_809850 < baseStart_809850 := by decide
  rcases family_descends (prefixWord ++ tailWord_809850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809867 : List Nat := [1, 1, 1, 1, 4, 2, 6, 1, 1, 4]
def baseStart_809867 : Nat := 118140960795 + 809867 * 2 ^ 59
def prefixEnd_809867 : Nat := 4983230072969 + 3 ^ 40 * 809867 * 2
def baseEnd_809867 : Nat := 277234024809925416891997

theorem tailTrace_809867 : CollatzResearch.WordTrace tailWord_809867 prefixEnd_809867 277234024809925416891997 := by
  unfold tailWord_809867
  simp only [CollatzResearch.WordTrace]
  refine ⟨29538276156997648116947855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19692184104665098744631903 29538276156997648116947855)
  ·
    refine ⟨44307414235496472175421783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29538276156997648116947855 44307414235496472175421783)
    ·
      refine ⟨66461121353244708263132675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44307414235496472175421783 66461121353244708263132675)
      ·
        refine ⟨99691682029867062394699013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66461121353244708263132675 99691682029867062394699013)
        ·
          refine ⟨18692190380600074199006065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99691682029867062394699013 18692190380600074199006065)
          ·
            refine ⟨14019142785450055649254549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18692190380600074199006065 14019142785450055649254549)
            ·
              refine ⟨657147318067971358558807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14019142785450055649254549 657147318067971358558807)
              ·
                refine ⟨985720977101957037838211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 657147318067971358558807 985720977101957037838211)
                ·
                  refine ⟨1478581465652935556757317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 985720977101957037838211 1478581465652935556757317)
                  ·
                    refine ⟨277234024809925416891997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1478581465652935556757317 277234024809925416891997)
                    ·
                      rfl

theorem cell22_809867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 1, 4].length) (baseStart_809867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809867 prefixEnd_809867 := by exact prefixLift 809867
  have htrace : WordTrace (prefixWord ++ tailWord_809867) baseStart_809867 baseEnd_809867 := by
    simpa [prefixWord, tailWord_809867, baseEnd_809867] using wordTrace_append hprefix tailTrace_809867
  have hstable : (prefixWord ++ tailWord_809867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809867).length < 2 ^ (prefixWord ++ tailWord_809867).sum := by decide
  have hdescent : baseEnd_809867 < baseStart_809867 := by decide
  rcases family_descends (prefixWord ++ tailWord_809867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809882 : List Nat := [3, 1, 1, 4, 3, 1, 2, 1, 6]
def baseStart_809882 : Nat := 118140960795 + 809882 * 2 ^ 59
def prefixEnd_809882 : Nat := 4983230072969 + 3 ^ 40 * 809882 * 2
def baseEnd_809882 : Nat := 92413053205490125922317

theorem tailTrace_809882 : CollatzResearch.WordTrace tailWord_809882 prefixEnd_809882 92413053205490125922317 := by
  unfold tailWord_809882
  simp only [CollatzResearch.WordTrace]
  refine ⟨7384705812985826419685975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19692548834628870452495933 7384705812985826419685975)
  ·
    refine ⟨11077058719478739629528963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7384705812985826419685975 11077058719478739629528963)
    ·
      refine ⟨16615588079218109444293445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11077058719478739629528963 16615588079218109444293445)
      ·
        refine ⟨3115422764853395520805021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16615588079218109444293445 3115422764853395520805021)
        ·
          refine ⟨1168283536820023320301883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3115422764853395520805021 1168283536820023320301883)
          ·
            refine ⟨1752425305230034980452825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1168283536820023320301883 1752425305230034980452825)
            ·
              refine ⟨1314318978922526235339619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1752425305230034980452825 1314318978922526235339619)
              ·
                refine ⟨1971478468383789353009429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1314318978922526235339619 1971478468383789353009429)
                ·
                  refine ⟨92413053205490125922317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1971478468383789353009429 92413053205490125922317)
                  ·
                    rfl

theorem cell22_809882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 6].length) (baseStart_809882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809882 prefixEnd_809882 := by exact prefixLift 809882
  have htrace : WordTrace (prefixWord ++ tailWord_809882) baseStart_809882 baseEnd_809882 := by
    simpa [prefixWord, tailWord_809882, baseEnd_809882] using wordTrace_append hprefix tailTrace_809882
  have hstable : (prefixWord ++ tailWord_809882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809882).length < 2 ^ (prefixWord ++ tailWord_809882).sum := by decide
  have hdescent : baseEnd_809882 < baseStart_809882 := by decide
  rcases family_descends (prefixWord ++ tailWord_809882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809901 : List Nat := [1, 5, 2, 3, 1, 1, 2, 2, 1, 4]
def baseStart_809901 : Nat := 118140960795 + 809901 * 2 ^ 59
def prefixEnd_809901 : Nat := 4983230072969 + 3 ^ 40 * 809901 * 2
def baseEnd_809901 : Nat := 277245663704760661541893

theorem tailTrace_809901 : CollatzResearch.WordTrace tailWord_809901 prefixEnd_809901 277245663704760661541893 := by
  unfold tailWord_809901
  simp only [CollatzResearch.WordTrace]
  refine ⟨29539516238874471923685557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19693010825916314615790371 29539516238874471923685557)
  ·
    refine ⟨2769329647394481742845521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29539516238874471923685557 2769329647394481742845521)
    ·
      refine ⟨2076997235545861307134141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2769329647394481742845521 2076997235545861307134141)
      ·
        refine ⟨778873963329697990175303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2076997235545861307134141 778873963329697990175303)
        ·
          refine ⟨1168310944994546985262955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778873963329697990175303 1168310944994546985262955)
          ·
            refine ⟨1752466417491820477894433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1168310944994546985262955 1752466417491820477894433)
            ·
              refine ⟨1314349813118865358420825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1752466417491820477894433 1314349813118865358420825)
              ·
                refine ⟨985762359839149018815619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1314349813118865358420825 985762359839149018815619)
                ·
                  refine ⟨1478643539758723528223429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 985762359839149018815619 1478643539758723528223429)
                  ·
                    refine ⟨277245663704760661541893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1478643539758723528223429 277245663704760661541893)
                    ·
                      rfl

theorem cell22_809901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_809901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809901 prefixEnd_809901 := by exact prefixLift 809901
  have htrace : WordTrace (prefixWord ++ tailWord_809901) baseStart_809901 baseEnd_809901 := by
    simpa [prefixWord, tailWord_809901, baseEnd_809901] using wordTrace_append hprefix tailTrace_809901
  have hstable : (prefixWord ++ tailWord_809901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809901).length < 2 ^ (prefixWord ++ tailWord_809901).sum := by decide
  have hdescent : baseEnd_809901 < baseStart_809901 := by decide
  rcases family_descends (prefixWord ++ tailWord_809901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_809933 : List Nat := [1, 6, 3, 1, 1, 2, 1, 1, 6]
def baseStart_809933 : Nat := 118140960795 + 809933 * 2 ^ 59
def prefixEnd_809933 : Nat := 4983230072969 + 3 ^ 40 * 809933 * 2
def baseEnd_809933 : Nat := 92418872652907748247265

theorem tailTrace_809933 : CollatzResearch.WordTrace tailWord_809933 prefixEnd_809933 92418872652907748247265 := by
  unfold tailWord_809933
  simp only [CollatzResearch.WordTrace]
  refine ⟨29540683374758541388850453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19693788916505694259233635 29540683374758541388850453)
  ·
    refine ⟨1384719533191806627602365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29540683374758541388850453 1384719533191806627602365)
    ·
      refine ⟨519269824946927485350887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1384719533191806627602365 519269824946927485350887)
      ·
        refine ⟨778904737420391228026331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519269824946927485350887 778904737420391228026331)
        ·
          refine ⟨1168357106130586842039497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778904737420391228026331 1168357106130586842039497)
          ·
            refine ⟨876267829597940131529623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1168357106130586842039497 876267829597940131529623)
            ·
              refine ⟨1314401744396910197294435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 876267829597940131529623 1314401744396910197294435)
              ·
                refine ⟨1971602616595365295941653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1314401744396910197294435 1971602616595365295941653)
                ·
                  refine ⟨92418872652907748247265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1971602616595365295941653 92418872652907748247265)
                  ·
                    rfl

theorem cell22_809933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_809933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_809933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_809933 prefixEnd_809933 := by exact prefixLift 809933
  have htrace : WordTrace (prefixWord ++ tailWord_809933) baseStart_809933 baseEnd_809933 := by
    simpa [prefixWord, tailWord_809933, baseEnd_809933] using wordTrace_append hprefix tailTrace_809933
  have hstable : (prefixWord ++ tailWord_809933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_809933).length < 2 ^ (prefixWord ++ tailWord_809933).sum := by decide
  have hdescent : baseEnd_809933 < baseStart_809933 := by decide
  rcases family_descends (prefixWord ++ tailWord_809933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810017 : List Nat := [1, 2, 3, 2, 3, 2, 1, 2, 6]
def baseStart_810017 : Nat := 118140960795 + 810017 * 2 ^ 59
def prefixEnd_810017 : Nat := 4983230072969 + 3 ^ 40 * 810017 * 2
def baseEnd_810017 : Nat := 92428457625125008547179

theorem tailTrace_810017 : CollatzResearch.WordTrace tailWord_810017 prefixEnd_810017 92428457625125008547179 := by
  unfold tailWord_810017
  simp only [CollatzResearch.WordTrace]
  refine ⟨29543747106454223734908305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19695831404302815823272203 29543747106454223734908305)
  ·
    refine ⟨22157810329840667801181229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29543747106454223734908305 22157810329840667801181229)
    ·
      refine ⟨8309178873690250425442961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22157810329840667801181229 8309178873690250425442961)
      ·
        refine ⟨6231884155267687819082221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8309178873690250425442961 6231884155267687819082221)
        ·
          refine ⟨2336956558225382932155833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6231884155267687819082221 2336956558225382932155833)
          ·
            refine ⟨1752717418669037199116875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2336956558225382932155833 1752717418669037199116875)
            ·
              refine ⟨2629076128003555798675313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1752717418669037199116875 2629076128003555798675313)
              ·
                refine ⟨1971807096002666849006485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2629076128003555798675313 1971807096002666849006485)
                ·
                  refine ⟨92428457625125008547179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1971807096002666849006485 92428457625125008547179)
                  ·
                    rfl

theorem cell22_810017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 6].length) (baseStart_810017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810017 prefixEnd_810017 := by exact prefixLift 810017
  have htrace : WordTrace (prefixWord ++ tailWord_810017) baseStart_810017 baseEnd_810017 := by
    simpa [prefixWord, tailWord_810017, baseEnd_810017] using wordTrace_append hprefix tailTrace_810017
  have hstable : (prefixWord ++ tailWord_810017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810017).length < 2 ^ (prefixWord ++ tailWord_810017).sum := by decide
  have hdescent : baseEnd_810017 < baseStart_810017 := by decide
  rcases family_descends (prefixWord ++ tailWord_810017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810032 : List Nat := [2, 1, 1, 1, 2, 4, 2, 2, 4, 3]
def baseStart_810032 : Nat := 118140960795 + 810032 * 2 ^ 59
def prefixEnd_810032 : Nat := 4983230072969 + 3 ^ 40 * 810032 * 2
def baseEnd_810032 : Nat := 277290507681919986516491

theorem tailTrace_810032 : CollatzResearch.WordTrace tailWord_810032 prefixEnd_810032 277290507681919986516491 := by
  unfold tailWord_810032
  simp only [CollatzResearch.WordTrace]
  refine ⟨14772147100699940648352175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19696196134266587531136233 14772147100699940648352175)
  ·
    refine ⟨22158220651049910972528263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14772147100699940648352175 22158220651049910972528263)
    ·
      refine ⟨33237330976574866458792395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22158220651049910972528263 33237330976574866458792395)
      ·
        refine ⟨49855996464862299688188593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33237330976574866458792395 49855996464862299688188593)
        ·
          refine ⟨37391997348646724766141445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49855996464862299688188593 37391997348646724766141445)
          ·
            refine ⟨7010999502871260893651521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37391997348646724766141445 7010999502871260893651521)
            ·
              refine ⟨5258249627153445670238641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7010999502871260893651521 5258249627153445670238641)
              ·
                refine ⟨3943687220365084252678981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5258249627153445670238641 3943687220365084252678981)
                ·
                  refine ⟨739441353818453297377309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3943687220365084252678981 739441353818453297377309)
                  ·
                    refine ⟨277290507681919986516491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 739441353818453297377309 277290507681919986516491)
                    ·
                      rfl

theorem cell22_810032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 4, 3].length) (baseStart_810032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810032 prefixEnd_810032 := by exact prefixLift 810032
  have htrace : WordTrace (prefixWord ++ tailWord_810032) baseStart_810032 baseEnd_810032 := by
    simpa [prefixWord, tailWord_810032, baseEnd_810032] using wordTrace_append hprefix tailTrace_810032
  have hstable : (prefixWord ++ tailWord_810032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810032).length < 2 ^ (prefixWord ++ tailWord_810032).sum := by decide
  have hdescent : baseEnd_810032 < baseStart_810032 := by decide
  rcases family_descends (prefixWord ++ tailWord_810032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810034 : List Nat := [3, 2, 1, 1, 2, 2, 4, 3, 4]
def baseStart_810034 : Nat := 118140960795 + 810034 * 2 ^ 59
def prefixEnd_810034 : Nat := 4983230072969 + 3 ^ 40 * 810034 * 2
def baseEnd_810034 : Nat := 92430397440930882655495

theorem tailTrace_810034 : CollatzResearch.WordTrace tailWord_810034 prefixEnd_810034 92430397440930882655495 := by
  unfold tailWord_810034
  simp only [CollatzResearch.WordTrace]
  refine ⟨7386091786848158909569289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19696244764928423758851437 7386091786848158909569289)
  ·
    refine ⟨5539568840136119182176967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7386091786848158909569289 5539568840136119182176967)
    ·
      refine ⟨8309353260204178773265451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5539568840136119182176967 8309353260204178773265451)
      ·
        refine ⟨12464029890306268159898177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8309353260204178773265451 12464029890306268159898177)
        ·
          refine ⟨9348022417729701119923633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12464029890306268159898177 9348022417729701119923633)
          ·
            refine ⟨7011016813297275839942725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9348022417729701119923633 7011016813297275839942725)
            ·
              refine ⟨1314565652493239219989261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7011016813297275839942725 1314565652493239219989261)
              ·
                refine ⟨492962119684964707495973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1314565652493239219989261 492962119684964707495973)
                ·
                  refine ⟨92430397440930882655495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 492962119684964707495973 92430397440930882655495)
                  ·
                    rfl

theorem cell22_810034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_810034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810034 prefixEnd_810034 := by exact prefixLift 810034
  have htrace : WordTrace (prefixWord ++ tailWord_810034) baseStart_810034 baseEnd_810034 := by
    simpa [prefixWord, tailWord_810034, baseEnd_810034] using wordTrace_append hprefix tailTrace_810034
  have hstable : (prefixWord ++ tailWord_810034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810034).length < 2 ^ (prefixWord ++ tailWord_810034).sum := by decide
  have hdescent : baseEnd_810034 < baseStart_810034 := by decide
  rcases family_descends (prefixWord ++ tailWord_810034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810036 : List Nat := [2, 5, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_810036 : Nat := 118140960795 + 810036 * 2 ^ 59
def prefixEnd_810036 : Nat := 4983230072969 + 3 ^ 40 * 810036 * 2
def baseEnd_810036 : Nat := 277291876963665309416479

theorem tailTrace_810036 : CollatzResearch.WordTrace tailWord_810036 prefixEnd_810036 277291876963665309416479 := by
  unfold tailWord_810036
  simp only [CollatzResearch.WordTrace]
  refine ⟨14772220046692694989924981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19696293395590259986566641 14772220046692694989924981)
  ·
    refine ⟨1384895629377440155305467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14772220046692694989924981 1384895629377440155305467)
    ·
      refine ⟨2077343444066160232958201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1384895629377440155305467 2077343444066160232958201)
      ·
        refine ⟨1558007583049620174718651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2077343444066160232958201 1558007583049620174718651)
        ·
          refine ⟨2337011374574430262077977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1558007583049620174718651 2337011374574430262077977)
          ·
            refine ⟨1752758530930822696558483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2337011374574430262077977 1752758530930822696558483)
            ·
              refine ⟨2629137796396234044837725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1752758530930822696558483 2629137796396234044837725)
              ·
                refine ⟨985926673648587766814147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2629137796396234044837725 985926673648587766814147)
                ·
                  refine ⟨1478890010472881650221221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 985926673648587766814147 1478890010472881650221221)
                  ·
                    refine ⟨277291876963665309416479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1478890010472881650221221 277291876963665309416479)
                    ·
                      rfl

theorem cell22_810036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_810036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810036 prefixEnd_810036 := by exact prefixLift 810036
  have htrace : WordTrace (prefixWord ++ tailWord_810036) baseStart_810036 baseEnd_810036 := by
    simpa [prefixWord, tailWord_810036, baseEnd_810036] using wordTrace_append hprefix tailTrace_810036
  have hstable : (prefixWord ++ tailWord_810036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810036).length < 2 ^ (prefixWord ++ tailWord_810036).sum := by decide
  have hdescent : baseEnd_810036 < baseStart_810036 := by decide
  rcases family_descends (prefixWord ++ tailWord_810036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810122 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 1, 7]
def baseStart_810122 : Nat := 118140960795 + 810122 * 2 ^ 59
def prefixEnd_810122 : Nat := 4983230072969 + 3 ^ 40 * 810122 * 2
def baseEnd_810122 : Nat := 277321316521189751766215

theorem tailTrace_810122 : CollatzResearch.WordTrace tailWord_810122 prefixEnd_810122 277321316521189751766215 := by
  unfold tailWord_810122
  simp only [CollatzResearch.WordTrace]
  refine ⟨7386894192768456666870155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19698384514049217778320413 7386894192768456666870155)
  ·
    refine ⟨11080341289152685000305233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7386894192768456666870155 11080341289152685000305233)
    ·
      refine ⟨8310255966864513750228925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11080341289152685000305233 8310255966864513750228925)
      ·
        refine ⟨3116345987574192656335847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8310255966864513750228925 3116345987574192656335847)
        ·
          refine ⟨4674518981361288984503771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3116345987574192656335847 4674518981361288984503771)
          ·
            refine ⟨7011778472041933476755657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4674518981361288984503771 7011778472041933476755657)
            ·
              refine ⟨5258833854031450107566743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7011778472041933476755657 5258833854031450107566743)
              ·
                refine ⟨7888250781047175161350115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5258833854031450107566743 7888250781047175161350115)
                ·
                  refine ⟨11832376171570762742025173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7888250781047175161350115 11832376171570762742025173)
                  ·
                    refine ⟨277321316521189751766215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11832376171570762742025173 277321316521189751766215)
                    ·
                      rfl

theorem cell22_810122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_810122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810122 prefixEnd_810122 := by exact prefixLift 810122
  have htrace : WordTrace (prefixWord ++ tailWord_810122) baseStart_810122 baseEnd_810122 := by
    simpa [prefixWord, tailWord_810122, baseEnd_810122] using wordTrace_append hprefix tailTrace_810122
  have hstable : (prefixWord ++ tailWord_810122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810122).length < 2 ^ (prefixWord ++ tailWord_810122).sum := by decide
  have hdescent : baseEnd_810122 < baseStart_810122 := by decide
  rcases family_descends (prefixWord ++ tailWord_810122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810167 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 3, 5]
def baseStart_810167 : Nat := 118140960795 + 810167 * 2 ^ 59
def prefixEnd_810167 : Nat := 4983230072969 + 3 ^ 40 * 810167 * 2
def baseEnd_810167 : Nat := 277336720940824634391077

theorem tailTrace_810167 : CollatzResearch.WordTrace tailWord_810167 prefixEnd_810167 277336720940824634391077 := by
  unfold tailWord_810167
  simp only [CollatzResearch.WordTrace]
  refine ⟨29549218055910799352868755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19699478703940532901912503 29549218055910799352868755)
  ·
    refine ⟨44323827083866199029303133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29549218055910799352868755 44323827083866199029303133)
    ·
      refine ⟨16621435156449824635988675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44323827083866199029303133 16621435156449824635988675)
      ·
        refine ⟨24932152734674736953983013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16621435156449824635988675 24932152734674736953983013)
        ·
          refine ⟨4674778637751513178871815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24932152734674736953983013 4674778637751513178871815)
          ·
            refine ⟨7012167956627269768307723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4674778637751513178871815 7012167956627269768307723)
            ·
              refine ⟨10518251934940904652461585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7012167956627269768307723 10518251934940904652461585)
              ·
                refine ⟨7888688951205678489346189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10518251934940904652461585 7888688951205678489346189)
                ·
                  refine ⟨2958258356702129433504821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7888688951205678489346189 2958258356702129433504821)
                  ·
                    refine ⟨277336720940824634391077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2958258356702129433504821 277336720940824634391077)
                    ·
                      rfl

theorem cell22_810167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_810167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810167 prefixEnd_810167 := by exact prefixLift 810167
  have htrace : WordTrace (prefixWord ++ tailWord_810167) baseStart_810167 baseEnd_810167 := by
    simpa [prefixWord, tailWord_810167, baseEnd_810167] using wordTrace_append hprefix tailTrace_810167
  have hstable : (prefixWord ++ tailWord_810167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810167).length < 2 ^ (prefixWord ++ tailWord_810167).sum := by decide
  have hdescent : baseEnd_810167 < baseStart_810167 := by decide
  rcases family_descends (prefixWord ++ tailWord_810167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810199 : List Nat := [1, 1, 3, 2, 1, 2, 5, 1, 2, 4]
def baseStart_810199 : Nat := 118140960795 + 810199 * 2 ^ 59
def prefixEnd_810199 : Nat := 4983230072969 + 3 ^ 40 * 810199 * 2
def baseEnd_810199 : Nat := 277347675194787217590979

theorem tailTrace_810199 : CollatzResearch.WordTrace tailWord_810199 prefixEnd_810199 277347675194787217590979 := by
  unfold tailWord_810199
  simp only [CollatzResearch.WordTrace]
  refine ⟨29550385191794868818033651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19700256794529912545355767 29550385191794868818033651)
  ·
    refine ⟨44325577787692303227050477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29550385191794868818033651 44325577787692303227050477)
    ·
      refine ⟨16622091670384613710143929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44325577787692303227050477 16622091670384613710143929)
      ·
        refine ⟨12466568752788460282607947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16622091670384613710143929 12466568752788460282607947)
        ·
          refine ⟨18699853129182690423911921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12466568752788460282607947 18699853129182690423911921)
          ·
            refine ⟨14024889846887017817933941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18699853129182690423911921 14024889846887017817933941)
            ·
              refine ⟨1314833423145657920431307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14024889846887017817933941 1314833423145657920431307)
              ·
                refine ⟨1972250134718486880646961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1314833423145657920431307 1972250134718486880646961)
                ·
                  refine ⟨1479187601038865160485221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1972250134718486880646961 1479187601038865160485221)
                  ·
                    refine ⟨277347675194787217590979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1479187601038865160485221 277347675194787217590979)
                    ·
                      rfl

theorem cell22_810199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_810199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810199 prefixEnd_810199 := by exact prefixLift 810199
  have htrace : WordTrace (prefixWord ++ tailWord_810199) baseStart_810199 baseEnd_810199 := by
    simpa [prefixWord, tailWord_810199, baseEnd_810199] using wordTrace_append hprefix tailTrace_810199
  have hstable : (prefixWord ++ tailWord_810199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810199).length < 2 ^ (prefixWord ++ tailWord_810199).sum := by decide
  have hdescent : baseEnd_810199 < baseStart_810199 := by decide
  rcases family_descends (prefixWord ++ tailWord_810199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810205 : List Nat := [1, 4, 3, 2, 2, 2, 2, 1, 1, 4]
def baseStart_810205 : Nat := 118140960795 + 810205 * 2 ^ 59
def prefixEnd_810205 : Nat := 4983230072969 + 3 ^ 40 * 810205 * 2
def baseEnd_810205 : Nat := 277349729117405201940961

theorem tailTrace_810205 : CollatzResearch.WordTrace tailWord_810205 prefixEnd_810205 277349729117405201940961 := by
  unfold tailWord_810205
  simp only [CollatzResearch.WordTrace]
  refine ⟨29550604029773131842752069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19700402686515421228501379 29550604029773131842752069)
  ·
    refine ⟨5540738255582462220516013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29550604029773131842752069 5540738255582462220516013)
    ·
      refine ⟨2077776845843423332693505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5540738255582462220516013 2077776845843423332693505)
      ·
        refine ⟨1558332634382567499520129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2077776845843423332693505 1558332634382567499520129)
        ·
          refine ⟨1168749475786925624640097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1558332634382567499520129 1168749475786925624640097)
          ·
            refine ⟨876562106840194218480073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1168749475786925624640097 876562106840194218480073)
            ·
              refine ⟨657421580130145663860055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 876562106840194218480073 657421580130145663860055)
              ·
                refine ⟨986132370195218495790083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 657421580130145663860055 986132370195218495790083)
                ·
                  refine ⟨1479198555292827743685125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 986132370195218495790083 1479198555292827743685125)
                  ·
                    refine ⟨277349729117405201940961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1479198555292827743685125 277349729117405201940961)
                    ·
                      rfl

theorem cell22_810205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_810205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810205 prefixEnd_810205 := by exact prefixLift 810205
  have htrace : WordTrace (prefixWord ++ tailWord_810205) baseStart_810205 baseEnd_810205 := by
    simpa [prefixWord, tailWord_810205, baseEnd_810205] using wordTrace_append hprefix tailTrace_810205
  have hstable : (prefixWord ++ tailWord_810205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810205).length < 2 ^ (prefixWord ++ tailWord_810205).sum := by decide
  have hdescent : baseEnd_810205 < baseStart_810205 := by decide
  rcases family_descends (prefixWord ++ tailWord_810205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810218 : List Nat := [3, 1, 3, 1, 1, 5, 1, 2, 2, 3]
def baseStart_810218 : Nat := 118140960795 + 810218 * 2 ^ 59
def prefixEnd_810218 : Nat := 4983230072969 + 3 ^ 40 * 810218 * 2
def baseEnd_810218 : Nat := 277354179283077501365921

theorem tailTrace_810218 : CollatzResearch.WordTrace tailWord_810218 prefixEnd_810218 277354179283077501365921 := by
  unfold tailWord_810218
  simp only [CollatzResearch.WordTrace]
  refine ⟨7387769544681508765743827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19700718785817356708650205 7387769544681508765743827)
  ·
    refine ⟨11081654317022263148615741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7387769544681508765743827 11081654317022263148615741)
    ·
      refine ⟨4155620368883348680730903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11081654317022263148615741 4155620368883348680730903)
      ·
        refine ⟨6233430553325023021096355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4155620368883348680730903 6233430553325023021096355)
        ·
          refine ⟨9350145829987534531644533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6233430553325023021096355 9350145829987534531644533)
          ·
            refine ⟨876576171561331362341675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9350145829987534531644533 876576171561331362341675)
            ·
              refine ⟨1314864257341997043512513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 876576171561331362341675 1314864257341997043512513)
              ·
                refine ⟨986148193006497782634385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1314864257341997043512513 986148193006497782634385)
                ·
                  refine ⟨739611144754873336975789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 986148193006497782634385 739611144754873336975789)
                  ·
                    refine ⟨277354179283077501365921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 739611144754873336975789 277354179283077501365921)
                    ·
                      rfl

theorem cell22_810218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_810218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810218 prefixEnd_810218 := by exact prefixLift 810218
  have htrace : WordTrace (prefixWord ++ tailWord_810218) baseStart_810218 baseEnd_810218 := by
    simpa [prefixWord, tailWord_810218, baseEnd_810218] using wordTrace_append hprefix tailTrace_810218
  have hstable : (prefixWord ++ tailWord_810218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810218).length < 2 ^ (prefixWord ++ tailWord_810218).sum := by decide
  have hdescent : baseEnd_810218 < baseStart_810218 := by decide
  rcases family_descends (prefixWord ++ tailWord_810218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810248 : List Nat := [2, 1, 3, 2, 5, 1, 2, 6]
def baseStart_810248 : Nat := 118140960795 + 810248 * 2 ^ 59
def prefixEnd_810248 : Nat := 4983230072969 + 3 ^ 40 * 810248 * 2
def baseEnd_810248 : Nat := 30818272099574158123981

theorem tailTrace_810248 : CollatzResearch.WordTrace tailWord_810248 prefixEnd_810248 30818272099574158123981 := by
  unfold tailWord_810248
  simp only [CollatzResearch.WordTrace]
  refine ⟨14776086184308675093283699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19701448245744900124378265 14776086184308675093283699)
  ·
    refine ⟨22164129276463012639925549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14776086184308675093283699 22164129276463012639925549)
    ·
      refine ⟨8311548478673629739972081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22164129276463012639925549 8311548478673629739972081)
      ·
        refine ⟨6233661359005222304979061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8311548478673629739972081 6233661359005222304979061)
        ·
          refine ⟨584405752406739591091787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6233661359005222304979061 584405752406739591091787)
          ·
            refine ⟨876608628610109386637681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 584405752406739591091787 876608628610109386637681)
            ·
              refine ⟨657456471457582039978261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 876608628610109386637681 657456471457582039978261)
              ·
                refine ⟨30818272099574158123981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 657456471457582039978261 30818272099574158123981)
                ·
                  rfl

theorem cell22_810248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 6].length) (baseStart_810248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810248 prefixEnd_810248 := by exact prefixLift 810248
  have htrace : WordTrace (prefixWord ++ tailWord_810248) baseStart_810248 baseEnd_810248 := by
    simpa [prefixWord, tailWord_810248, baseEnd_810248] using wordTrace_append hprefix tailTrace_810248
  have hstable : (prefixWord ++ tailWord_810248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810248).length < 2 ^ (prefixWord ++ tailWord_810248).sum := by decide
  have hdescent : baseEnd_810248 < baseStart_810248 := by decide
  rcases family_descends (prefixWord ++ tailWord_810248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810293 : List Nat := [1, 3, 3, 1, 2, 4, 2, 1, 5]
def baseStart_810293 : Nat := 118140960795 + 810293 * 2 ^ 59
def prefixEnd_810293 : Nat := 4983230072969 + 3 ^ 40 * 810293 * 2
def baseEnd_810293 : Nat := 92459951105267435246897

theorem tailTrace_810293 : CollatzResearch.WordTrace tailWord_810293 prefixEnd_810293 92459951105267435246897 := by
  unfold tailWord_810293
  simp only [CollatzResearch.WordTrace]
  refine ⟨29553813653454322871955533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19702542435636215247970355 29553813653454322871955533)
  ·
    refine ⟨11082680120045371076983325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29553813653454322871955533 11082680120045371076983325)
    ·
      refine ⟨4156005045017014153868747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11082680120045371076983325 4156005045017014153868747)
      ·
        refine ⟨6234007567525521230803121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4156005045017014153868747 6234007567525521230803121)
        ·
          refine ⟨4675505675644140923102341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6234007567525521230803121 4675505675644140923102341)
          ·
            refine ⟨876657314183276423081689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4675505675644140923102341 876657314183276423081689)
            ·
              refine ⟨657492985637457317311267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 876657314183276423081689 657492985637457317311267)
              ·
                refine ⟨986239478456185975966901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 657492985637457317311267 986239478456185975966901)
                ·
                  refine ⟨92459951105267435246897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 986239478456185975966901 92459951105267435246897)
                  ·
                    rfl

theorem cell22_810293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 5].length) (baseStart_810293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810293 prefixEnd_810293 := by exact prefixLift 810293
  have htrace : WordTrace (prefixWord ++ tailWord_810293) baseStart_810293 baseEnd_810293 := by
    simpa [prefixWord, tailWord_810293, baseEnd_810293] using wordTrace_append hprefix tailTrace_810293
  have hstable : (prefixWord ++ tailWord_810293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810293).length < 2 ^ (prefixWord ++ tailWord_810293).sum := by decide
  have hdescent : baseEnd_810293 < baseStart_810293 := by decide
  rcases family_descends (prefixWord ++ tailWord_810293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810321 : List Nat := [1, 2, 2, 1, 4, 1, 2, 5, 4]
def baseStart_810321 : Nat := 118140960795 + 810321 * 2 ^ 59
def prefixEnd_810321 : Nat := 4983230072969 + 3 ^ 40 * 810321 * 2
def baseEnd_810321 : Nat := 92463146096006522013535

theorem tailTrace_810321 : CollatzResearch.WordTrace tailWord_810321 prefixEnd_810321 92463146096006522013535 := by
  unfold tailWord_810321
  simp only [CollatzResearch.WordTrace]
  refine ⟨29554834897352883653974817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19703223264901922435983211 29554834897352883653974817)
  ·
    refine ⟨22166126173014662740481113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29554834897352883653974817 22166126173014662740481113)
    ·
      refine ⟨16624594629760997055360835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22166126173014662740481113 16624594629760997055360835)
      ·
        refine ⟨24936891944641495583041253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16624594629760997055360835 24936891944641495583041253)
        ·
          refine ⟨4675667239620280421820235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24936891944641495583041253 4675667239620280421820235)
          ·
            refine ⟨7013500859430420632730353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4675667239620280421820235 7013500859430420632730353)
            ·
              refine ⟨5260125644572815474547765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7013500859430420632730353 5260125644572815474547765)
              ·
                refine ⟨493136779178701450738853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5260125644572815474547765 493136779178701450738853)
                ·
                  refine ⟨92463146096006522013535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 493136779178701450738853 92463146096006522013535)
                  ·
                    rfl

theorem cell22_810321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5, 4].length) (baseStart_810321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810321 prefixEnd_810321 := by exact prefixLift 810321
  have htrace : WordTrace (prefixWord ++ tailWord_810321) baseStart_810321 baseEnd_810321 := by
    simpa [prefixWord, tailWord_810321, baseEnd_810321] using wordTrace_append hprefix tailTrace_810321
  have hstable : (prefixWord ++ tailWord_810321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810321).length < 2 ^ (prefixWord ++ tailWord_810321).sum := by decide
  have hdescent : baseEnd_810321 < baseStart_810321 := by decide
  rcases family_descends (prefixWord ++ tailWord_810321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810338 : List Nat := [3, 3, 2, 1, 1, 1, 3, 4, 4]
def baseStart_810338 : Nat := 118140960795 + 810338 * 2 ^ 59
def prefixEnd_810338 : Nat := 4983230072969 + 3 ^ 40 * 810338 * 2
def baseEnd_810338 : Nat := 92465085911812396121851

theorem tailTrace_810338 : CollatzResearch.WordTrace tailWord_810338 prefixEnd_810338 92465085911812396121851 := by
  unfold tailWord_810338
  simp only [CollatzResearch.WordTrace]
  refine ⟨7388863734572823889335917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19703636625527530371562445 7388863734572823889335917)
  ·
    refine ⟨2770823900464808958500969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7388863734572823889335917 2770823900464808958500969)
    ·
      refine ⟨2078117925348606718875727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2770823900464808958500969 2078117925348606718875727)
      ·
        refine ⟨3117176888022910078313591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2078117925348606718875727 3117176888022910078313591)
        ·
          refine ⟨4675765332034365117470387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3117176888022910078313591 4675765332034365117470387)
          ·
            refine ⟨7013647998051547676205581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4675765332034365117470387 7013647998051547676205581)
            ·
              refine ⟨2630117999269330378577093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7013647998051547676205581 2630117999269330378577093)
              ·
                refine ⟨493147124862999445983205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2630117999269330378577093 493147124862999445983205)
                ·
                  refine ⟨92465085911812396121851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 493147124862999445983205 92465085911812396121851)
                  ·
                    rfl

theorem cell22_810338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_810338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810338 prefixEnd_810338 := by exact prefixLift 810338
  have htrace : WordTrace (prefixWord ++ tailWord_810338) baseStart_810338 baseEnd_810338 := by
    simpa [prefixWord, tailWord_810338, baseEnd_810338] using wordTrace_append hprefix tailTrace_810338
  have hstable : (prefixWord ++ tailWord_810338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810338).length < 2 ^ (prefixWord ++ tailWord_810338).sum := by decide
  have hdescent : baseEnd_810338 < baseStart_810338 := by decide
  rcases family_descends (prefixWord ++ tailWord_810338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810434 : List Nat := [3, 5, 2, 1, 2, 1, 8]
def baseStart_810434 : Nat := 118140960795 + 810434 * 2 ^ 59
def prefixEnd_810434 : Nat := 4983230072969 + 3 ^ 40 * 810434 * 2
def baseEnd_810434 : Nat := 10275115573974997702417

theorem tailTrace_810434 : CollatzResearch.WordTrace tailWord_810434 prefixEnd_810434 10275115573974997702417 := by
  unfold tailWord_810434
  simp only [CollatzResearch.WordTrace]
  refine ⟨7389739086485875988209589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19705970897295669301892237 7389739086485875988209589)
  ·
    refine ⟨692788039358050873894649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7389739086485875988209589 692788039358050873894649)
    ·
      refine ⟨519591029518538155420987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 692788039358050873894649 519591029518538155420987)
      ·
        refine ⟨779386544277807233131481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519591029518538155420987 779386544277807233131481)
        ·
          refine ⟨584539908208355424848611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 779386544277807233131481 584539908208355424848611)
          ·
            refine ⟨876809862312533137272917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 584539908208355424848611 876809862312533137272917)
            ·
              refine ⟨10275115573974997702417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 876809862312533137272917 10275115573974997702417)
              ·
                rfl

theorem cell22_810434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 8].length) (baseStart_810434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810434 prefixEnd_810434 := by exact prefixLift 810434
  have htrace : WordTrace (prefixWord ++ tailWord_810434) baseStart_810434 baseEnd_810434 := by
    simpa [prefixWord, tailWord_810434, baseEnd_810434] using wordTrace_append hprefix tailTrace_810434
  have hstable : (prefixWord ++ tailWord_810434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810434).length < 2 ^ (prefixWord ++ tailWord_810434).sum := by decide
  have hdescent : baseEnd_810434 < baseStart_810434 := by decide
  rcases family_descends (prefixWord ++ tailWord_810434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810456 : List Nat := [2, 1, 2, 2, 2, 1, 5, 1, 6]
def baseStart_810456 : Nat := 118140960795 + 810456 * 2 ^ 59
def prefixEnd_810456 : Nat := 4983230072969 + 3 ^ 40 * 810456 * 2
def baseEnd_810456 : Nat := 92478550515641404638397

theorem tailTrace_810456 : CollatzResearch.WordTrace tailWord_810456 prefixEnd_810456 92478550515641404638397 := by
  unfold tailWord_810456
  simp only [CollatzResearch.WordTrace]
  refine ⟨14779879375931900855069611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19706505834575867806759481 14779879375931900855069611)
  ·
    refine ⟨22169819063897851282604417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14779879375931900855069611 22169819063897851282604417)
    ·
      refine ⟨16627364297923388461953313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22169819063897851282604417 16627364297923388461953313)
      ·
        refine ⟨12470523223442541346464985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16627364297923388461953313 12470523223442541346464985)
        ·
          refine ⟨9352892417581906009848739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12470523223442541346464985 9352892417581906009848739)
          ·
            refine ⟨14029338626372859014773109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9352892417581906009848739 14029338626372859014773109)
            ·
              refine ⟨1315250496222455532634979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14029338626372859014773109 1315250496222455532634979)
              ·
                refine ⟨1972875744333683298952469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1315250496222455532634979 1972875744333683298952469)
                ·
                  refine ⟨92478550515641404638397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1972875744333683298952469 92478550515641404638397)
                  ·
                    rfl

theorem cell22_810456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 6].length) (baseStart_810456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810456 prefixEnd_810456 := by exact prefixLift 810456
  have htrace : WordTrace (prefixWord ++ tailWord_810456) baseStart_810456 baseEnd_810456 := by
    simpa [prefixWord, tailWord_810456, baseEnd_810456] using wordTrace_append hprefix tailTrace_810456
  have hstable : (prefixWord ++ tailWord_810456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810456).length < 2 ^ (prefixWord ++ tailWord_810456).sum := by decide
  have hdescent : baseEnd_810456 < baseStart_810456 := by decide
  rcases family_descends (prefixWord ++ tailWord_810456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810503 : List Nat := [1, 1, 4, 3, 2, 1, 2, 2, 2, 4]
def baseStart_810503 : Nat := 118140960795 + 810503 * 2 ^ 59
def prefixEnd_810503 : Nat := 4983230072969 + 3 ^ 40 * 810503 * 2
def baseEnd_810503 : Nat := 277451740607431757990047

theorem tailTrace_810503 : CollatzResearch.WordTrace tailWord_810503 prefixEnd_810503 277451740607431757990047 := by
  unfold tailWord_810503
  simp only [CollatzResearch.WordTrace]
  refine ⟨29561472982693528737100163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19707648655129019158066775 29561472982693528737100163)
  ·
    refine ⟨44342209474040293105650245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29561472982693528737100163 44342209474040293105650245)
    ·
      refine ⟨8314164276382554957309421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44342209474040293105650245 8314164276382554957309421)
      ·
        refine ⟨3117811603643458108991033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8314164276382554957309421 3117811603643458108991033)
        ·
          refine ⟨2338358702732593581743275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3117811603643458108991033 2338358702732593581743275)
          ·
            refine ⟨3507538054098890372614913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2338358702732593581743275 3507538054098890372614913)
            ·
              refine ⟨2630653540574167779461185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3507538054098890372614913 2630653540574167779461185)
              ·
                refine ⟨1972990155430625834595889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2630653540574167779461185 1972990155430625834595889)
                ·
                  refine ⟨1479742616572969375946917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1972990155430625834595889 1479742616572969375946917)
                  ·
                    refine ⟨277451740607431757990047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1479742616572969375946917 277451740607431757990047)
                    ·
                      rfl

theorem cell22_810503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_810503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810503 prefixEnd_810503 := by exact prefixLift 810503
  have htrace : WordTrace (prefixWord ++ tailWord_810503) baseStart_810503 baseEnd_810503 := by
    simpa [prefixWord, tailWord_810503, baseEnd_810503] using wordTrace_append hprefix tailTrace_810503
  have hstable : (prefixWord ++ tailWord_810503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810503).length < 2 ^ (prefixWord ++ tailWord_810503).sum := by decide
  have hdescent : baseEnd_810503 < baseStart_810503 := by decide
  rcases family_descends (prefixWord ++ tailWord_810503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810507 : List Nat := [1, 1, 1, 1, 8, 2, 2, 2, 4]
def baseStart_810507 : Nat := 118140960795 + 810507 * 2 ^ 59
def prefixEnd_810507 : Nat := 4983230072969 + 3 ^ 40 * 810507 * 2
def baseEnd_810507 : Nat := 92484369963059026963345

theorem tailTrace_810507 : CollatzResearch.WordTrace tailWord_810507 prefixEnd_810507 92484369963059026963345 := by
  unfold tailWord_810507
  simp only [CollatzResearch.WordTrace]
  refine ⟨29561618874679037420245775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19707745916452691613497183 29561618874679037420245775)
  ·
    refine ⟨44342428312018556130368663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29561618874679037420245775 44342428312018556130368663)
    ·
      refine ⟨66513642468027834195552995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44342428312018556130368663 66513642468027834195552995)
      ·
        refine ⟨99770463702041751293329493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66513642468027834195552995 99770463702041751293329493)
        ·
          refine ⟨1169185121508301772968705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 99770463702041751293329493 1169185121508301772968705)
          ·
            refine ⟨876888841131226329726529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1169185121508301772968705 876888841131226329726529)
            ·
              refine ⟨657666630848419747294897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 876888841131226329726529 657666630848419747294897)
              ·
                refine ⟨493249973136314810471173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 657666630848419747294897 493249973136314810471173)
                ·
                  refine ⟨92484369963059026963345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 493249973136314810471173 92484369963059026963345)
                  ·
                    rfl

theorem cell22_810507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2, 4].length) (baseStart_810507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810507 prefixEnd_810507 := by exact prefixLift 810507
  have htrace : WordTrace (prefixWord ++ tailWord_810507) baseStart_810507 baseEnd_810507 := by
    simpa [prefixWord, tailWord_810507, baseEnd_810507] using wordTrace_append hprefix tailTrace_810507
  have hstable : (prefixWord ++ tailWord_810507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810507).length < 2 ^ (prefixWord ++ tailWord_810507).sum := by decide
  have hdescent : baseEnd_810507 < baseStart_810507 := by decide
  rcases family_descends (prefixWord ++ tailWord_810507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810546 : List Nat := [3, 2, 1, 1, 2, 1, 1, 4, 7]
def baseStart_810546 : Nat := 118140960795 + 810546 * 2 ^ 59
def prefixEnd_810546 : Nat := 4983230072969 + 3 ^ 40 * 810546 * 2
def baseEnd_810546 : Nat := 92488820128731326388305

theorem tailTrace_810546 : CollatzResearch.WordTrace tailWord_810546 prefixEnd_810546 92488820128731326388305 := by
  unfold tailWord_810546
  simp only [CollatzResearch.WordTrace]
  refine ⟨7390760330384436770228873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19708694214358498053943661 7390760330384436770228873)
  ·
    refine ⟨5543070247788327577671655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7390760330384436770228873 5543070247788327577671655)
    ·
      refine ⟨8314605371682491366507483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5543070247788327577671655 8314605371682491366507483)
      ·
        refine ⟨12471908057523737049761225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8314605371682491366507483 12471908057523737049761225)
        ·
          refine ⟨9353931043142802787320919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12471908057523737049761225 9353931043142802787320919)
          ·
            refine ⟨14030896564714204180981379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9353931043142802787320919 14030896564714204180981379)
            ·
              refine ⟨21046344847071306271472069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14030896564714204180981379 21046344847071306271472069)
              ·
                refine ⟨3946189658825869925901013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21046344847071306271472069 3946189658825869925901013)
                ·
                  refine ⟨92488820128731326388305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3946189658825869925901013 92488820128731326388305)
                  ·
                    rfl

theorem cell22_810546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_810546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810546 prefixEnd_810546 := by exact prefixLift 810546
  have htrace : WordTrace (prefixWord ++ tailWord_810546) baseStart_810546 baseEnd_810546 := by
    simpa [prefixWord, tailWord_810546, baseEnd_810546] using wordTrace_append hprefix tailTrace_810546
  have hstable : (prefixWord ++ tailWord_810546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810546).length < 2 ^ (prefixWord ++ tailWord_810546).sum := by decide
  have hdescent : baseEnd_810546 < baseStart_810546 := by decide
  rcases family_descends (prefixWord ++ tailWord_810546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810578 : List Nat := [3, 2, 2, 1, 2, 2, 2, 1, 2, 5]
def baseStart_810578 : Nat := 118140960795 + 810578 * 2 ^ 59
def prefixEnd_810578 : Nat := 4983230072969 + 3 ^ 40 * 810578 * 2
def baseEnd_810578 : Nat := 277477414640156562364817

theorem tailTrace_810578 : CollatzResearch.WordTrace tailWord_810578 prefixEnd_810578 277477414640156562364817 := by
  unfold tailWord_810578
  simp only [CollatzResearch.WordTrace]
  refine ⟨7391052114355454136520097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19709472304947877697386925 7391052114355454136520097)
  ·
    refine ⟨5543289085766590602390073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7391052114355454136520097 5543289085766590602390073)
    ·
      refine ⟨4157466814324942951792555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5543289085766590602390073 4157466814324942951792555)
      ·
        refine ⟨6236200221487414427688833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4157466814324942951792555 6236200221487414427688833)
        ·
          refine ⟨4677150166115560820766625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6236200221487414427688833 4677150166115560820766625)
          ·
            refine ⟨3507862624586670615574969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4677150166115560820766625 3507862624586670615574969)
            ·
              refine ⟨2630896968440002961681227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3507862624586670615574969 2630896968440002961681227)
              ·
                refine ⟨3946345452660004442521841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2630896968440002961681227 3946345452660004442521841)
                ·
                  refine ⟨2959759089495003331891381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3946345452660004442521841 2959759089495003331891381)
                  ·
                    refine ⟨277477414640156562364817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2959759089495003331891381 277477414640156562364817)
                    ·
                      rfl

theorem cell22_810578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_810578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810578 prefixEnd_810578 := by exact prefixLift 810578
  have htrace : WordTrace (prefixWord ++ tailWord_810578) baseStart_810578 baseEnd_810578 := by
    simpa [prefixWord, tailWord_810578, baseEnd_810578] using wordTrace_append hprefix tailTrace_810578
  have hstable : (prefixWord ++ tailWord_810578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810578).length < 2 ^ (prefixWord ++ tailWord_810578).sum := by decide
  have hdescent : baseEnd_810578 < baseStart_810578 := by decide
  rcases family_descends (prefixWord ++ tailWord_810578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810580 : List Nat := [2, 4, 1, 1, 1, 2, 5, 1, 5]
def baseStart_810580 : Nat := 118140960795 + 810580 * 2 ^ 59
def prefixEnd_810580 : Nat := 4983230072969 + 3 ^ 40 * 810580 * 2
def baseEnd_810580 : Nat := 92492699760343074604937

theorem tailTrace_810580 : CollatzResearch.WordTrace tailWord_810580 prefixEnd_810580 92492699760343074604937 := by
  unfold tailWord_810580
  simp only [CollatzResearch.WordTrace]
  refine ⟨14782140701707285443826597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19709520935609713925102129 14782140701707285443826597)
  ·
    refine ⟨2771651381570116020717487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14782140701707285443826597 2771651381570116020717487)
    ·
      refine ⟨4157477072355174031076231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2771651381570116020717487 4157477072355174031076231)
      ·
        refine ⟨6236215608532761046614347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4157477072355174031076231 6236215608532761046614347)
        ·
          refine ⟨9354323412799141569921521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6236215608532761046614347 9354323412799141569921521)
          ·
            refine ⟨7015742559599356177441141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9354323412799141569921521 7015742559599356177441141)
            ·
              refine ⟨657725864962439641635107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7015742559599356177441141 657725864962439641635107)
              ·
                refine ⟨986588797443659462452661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 657725864962439641635107 986588797443659462452661)
                ·
                  refine ⟨92492699760343074604937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 986588797443659462452661 92492699760343074604937)
                  ·
                    rfl

theorem cell22_810580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_810580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810580 prefixEnd_810580 := by exact prefixLift 810580
  have htrace : WordTrace (prefixWord ++ tailWord_810580) baseStart_810580 baseEnd_810580 := by
    simpa [prefixWord, tailWord_810580, baseEnd_810580] using wordTrace_append hprefix tailTrace_810580
  have hstable : (prefixWord ++ tailWord_810580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810580).length < 2 ^ (prefixWord ++ tailWord_810580).sum := by decide
  have hdescent : baseEnd_810580 < baseStart_810580 := by decide
  rcases family_descends (prefixWord ++ tailWord_810580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810610 : List Nat := [3, 2, 1, 2, 3, 1, 2, 3, 1, 4]
def baseStart_810610 : Nat := 118140960795 + 810610 * 2 ^ 59
def prefixEnd_810610 : Nat := 4983230072969 + 3 ^ 40 * 810610 * 2
def baseEnd_810610 : Nat := 277488368894119145564719

theorem tailTrace_810610 : CollatzResearch.WordTrace tailWord_810610 prefixEnd_810610 277488368894119145564719 := by
  unfold tailWord_810610
  simp only [CollatzResearch.WordTrace]
  refine ⟨7391343898326471502811321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19710250395537257340830189 7391343898326471502811321)
  ·
    refine ⟨5543507923744853627108491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7391343898326471502811321 5543507923744853627108491)
    ·
      refine ⟨8315261885617280440662737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5543507923744853627108491 8315261885617280440662737)
      ·
        refine ⟨6236446414212960330497053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8315261885617280440662737 6236446414212960330497053)
        ·
          refine ⟨2338667405329860123936395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6236446414212960330497053 2338667405329860123936395)
          ·
            refine ⟨3508001107994790185904593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2338667405329860123936395 3508001107994790185904593)
            ·
              refine ⟨2631000830996092639428445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3508001107994790185904593 2631000830996092639428445)
              ·
                refine ⟨986625311623534739785667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2631000830996092639428445 986625311623534739785667)
                ·
                  refine ⟨1479937967435302109678501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 986625311623534739785667 1479937967435302109678501)
                  ·
                    refine ⟨277488368894119145564719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1479937967435302109678501 277488368894119145564719)
                    ·
                      rfl

theorem cell22_810610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_810610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810610 prefixEnd_810610 := by exact prefixLift 810610
  have htrace : WordTrace (prefixWord ++ tailWord_810610) baseStart_810610 baseEnd_810610 := by
    simpa [prefixWord, tailWord_810610, baseEnd_810610] using wordTrace_append hprefix tailTrace_810610
  have hstable : (prefixWord ++ tailWord_810610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810610).length < 2 ^ (prefixWord ++ tailWord_810610).sum := by decide
  have hdescent : baseEnd_810610 < baseStart_810610 := by decide
  rcases family_descends (prefixWord ++ tailWord_810610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810625 : List Nat := [1, 2, 4, 2, 1, 4, 1, 1, 6]
def baseStart_810625 : Nat := 118140960795 + 810625 * 2 ^ 59
def prefixEnd_810625 : Nat := 4983230072969 + 3 ^ 40 * 810625 * 2
def baseEnd_810625 : Nat := 92497834566888035479891

theorem tailTrace_810625 : CollatzResearch.WordTrace tailWord_810625 prefixEnd_810625 92497834566888035479891 := by
  unfold tailWord_810625
  simp only [CollatzResearch.WordTrace]
  refine ⟨29565922688251543573041329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19710615125501029048694219 29565922688251543573041329)
  ·
    refine ⟨22174442016188657679780997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29565922688251543573041329 22174442016188657679780997)
    ·
      refine ⟨4157707878035373314958937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22174442016188657679780997 4157707878035373314958937)
      ·
        refine ⟨3118280908526529986219203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4157707878035373314958937 3118280908526529986219203)
        ·
          refine ⟨4677421362789794979328805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3118280908526529986219203 4677421362789794979328805)
          ·
            refine ⟨877016505523086558624151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4677421362789794979328805 877016505523086558624151)
            ·
              refine ⟨1315524758284629837936227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 877016505523086558624151 1315524758284629837936227)
              ·
                refine ⟨1973287137426944756904341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1315524758284629837936227 1973287137426944756904341)
                ·
                  refine ⟨92497834566888035479891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1973287137426944756904341 92497834566888035479891)
                  ·
                    rfl

theorem cell22_810625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 6].length) (baseStart_810625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810625 prefixEnd_810625 := by exact prefixLift 810625
  have htrace : WordTrace (prefixWord ++ tailWord_810625) baseStart_810625 baseEnd_810625 := by
    simpa [prefixWord, tailWord_810625, baseEnd_810625] using wordTrace_append hprefix tailTrace_810625
  have hstable : (prefixWord ++ tailWord_810625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810625).length < 2 ^ (prefixWord ++ tailWord_810625).sum := by decide
  have hdescent : baseEnd_810625 < baseStart_810625 := by decide
  rcases family_descends (prefixWord ++ tailWord_810625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810644 : List Nat := [2, 4, 2, 2, 2, 2, 1, 2, 1, 4]
def baseStart_810644 : Nat := 118140960795 + 810644 * 2 ^ 59
def prefixEnd_810644 : Nat := 4983230072969 + 3 ^ 40 * 810644 * 2
def baseEnd_810644 : Nat := 277500007788954390214615

theorem tailTrace_810644 : CollatzResearch.WordTrace tailWord_810644 prefixEnd_810644 277500007788954390214615 := by
  unfold tailWord_810644
  simp only [CollatzResearch.WordTrace]
  refine ⟨14783307837591354908991493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19711077116788473211988657 14783307837591354908991493)
  ·
    refine ⟨2771870219548379045435905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14783307837591354908991493 2771870219548379045435905)
    ·
      refine ⟨2078902664661284284076929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2771870219548379045435905 2078902664661284284076929)
      ·
        refine ⟨1559176998495963213057697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2078902664661284284076929 1559176998495963213057697)
        ·
          refine ⟨1169382748871972409793273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1559176998495963213057697 1169382748871972409793273)
          ·
            refine ⟨877037061653979307344955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1169382748871972409793273 877037061653979307344955)
            ·
              refine ⟨1315555592480968961017433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 877037061653979307344955 1315555592480968961017433)
              ·
                refine ⟨986666694360726720763075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1315555592480968961017433 986666694360726720763075)
                ·
                  refine ⟨1480000041541090081144613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 986666694360726720763075 1480000041541090081144613)
                  ·
                    refine ⟨277500007788954390214615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1480000041541090081144613 277500007788954390214615)
                    ·
                      rfl

theorem cell22_810644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_810644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810644 prefixEnd_810644 := by exact prefixLift 810644
  have htrace : WordTrace (prefixWord ++ tailWord_810644) baseStart_810644 baseEnd_810644 := by
    simpa [prefixWord, tailWord_810644, baseEnd_810644] using wordTrace_append hprefix tailTrace_810644
  have hstable : (prefixWord ++ tailWord_810644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810644).length < 2 ^ (prefixWord ++ tailWord_810644).sum := by decide
  have hdescent : baseEnd_810644 < baseStart_810644 := by decide
  rcases family_descends (prefixWord ++ tailWord_810644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810670 : List Nat := [4, 1, 4, 1, 2, 10]
def baseStart_810670 : Nat := 118140960795 + 810670 * 2 ^ 59
def prefixEnd_810670 : Nat := 4983230072969 + 3 ^ 40 * 810670 * 2
def baseEnd_810670 : Nat := 3426035902719740605735

theorem tailTrace_810670 : CollatzResearch.WordTrace tailWord_810670 prefixEnd_810670 3426035902719740605735 := by
  unfold tailWord_810670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3695945496636064532303683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19711709315392344172286309 3695945496636064532303683)
  ·
    refine ⟨5543918244954096798455525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3695945496636064532303683 5543918244954096798455525)
    ·
      refine ⟨1039484670928893149710411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5543918244954096798455525 1039484670928893149710411)
      ·
        refine ⟨1559227006393339724565617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1039484670928893149710411 1559227006393339724565617)
        ·
          refine ⟨1169420254795004793424213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1559227006393339724565617 1169420254795004793424213)
          ·
            refine ⟨3426035902719740605735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1169420254795004793424213 3426035902719740605735)
            ·
              rfl

theorem cell22_810670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 10].length) (baseStart_810670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810670 prefixEnd_810670 := by exact prefixLift 810670
  have htrace : WordTrace (prefixWord ++ tailWord_810670) baseStart_810670 baseEnd_810670 := by
    simpa [prefixWord, tailWord_810670, baseEnd_810670] using wordTrace_append hprefix tailTrace_810670
  have hstable : (prefixWord ++ tailWord_810670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810670).length < 2 ^ (prefixWord ++ tailWord_810670).sum := by decide
  have hdescent : baseEnd_810670 < baseStart_810670 := by decide
  rcases family_descends (prefixWord ++ tailWord_810670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810685 : List Nat := [1, 4, 1, 2, 1, 2, 2, 3, 3, 3]
def baseStart_810685 : Nat := 118140960795 + 810685 * 2 ^ 59
def prefixEnd_810685 : Nat := 4983230072969 + 3 ^ 40 * 810685 * 2
def baseEnd_810685 : Nat := 277514042926843949939489

theorem tailTrace_810685 : CollatzResearch.WordTrace tailWord_810685 prefixEnd_810685 277514042926843949939489 := by
  unfold tailWord_810685
  simp only [CollatzResearch.WordTrace]
  refine ⟨29568111068034173820225509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19712074045356115880150339 29568111068034173820225509)
  ·
    refine ⟨5544020825256407591292283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29568111068034173820225509 5544020825256407591292283)
    ·
      refine ⟨8316031237884611386938425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5544020825256407591292283 8316031237884611386938425)
      ·
        refine ⟨6237023428413458540203819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8316031237884611386938425 6237023428413458540203819)
        ·
          refine ⟨9355535142620187810305729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6237023428413458540203819 9355535142620187810305729)
          ·
            refine ⟨7016651356965140857729297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9355535142620187810305729 7016651356965140857729297)
            ·
              refine ⟨5262488517723855643296973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7016651356965140857729297 5262488517723855643296973)
              ·
                refine ⟨1973433194146445866236365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5262488517723855643296973 1973433194146445866236365)
                ·
                  refine ⟨740037447804917199838637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1973433194146445866236365 740037447804917199838637)
                  ·
                    refine ⟨277514042926843949939489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 740037447804917199838637 277514042926843949939489)
                    ·
                      rfl

theorem cell22_810685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_810685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810685 prefixEnd_810685 := by exact prefixLift 810685
  have htrace : WordTrace (prefixWord ++ tailWord_810685) baseStart_810685 baseEnd_810685 := by
    simpa [prefixWord, tailWord_810685, baseEnd_810685] using wordTrace_append hprefix tailTrace_810685
  have hstable : (prefixWord ++ tailWord_810685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810685).length < 2 ^ (prefixWord ++ tailWord_810685).sum := by decide
  have hdescent : baseEnd_810685 < baseStart_810685 := by decide
  rcases family_descends (prefixWord ++ tailWord_810685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810743 : List Nat := [1, 1, 3, 1, 1, 1, 5, 3, 6]
def baseStart_810743 : Nat := 118140960795 + 810743 * 2 ^ 59
def prefixEnd_810743 : Nat := 4983230072969 + 3 ^ 40 * 810743 * 2
def baseEnd_810743 : Nat := 92511299170717043996437

theorem tailTrace_810743 : CollatzResearch.WordTrace tailWord_810743 prefixEnd_810743 92511299170717043996437 := by
  unfold tailWord_810743
  simp only [CollatzResearch.WordTrace]
  refine ⟨29570226501824049725836883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19713484334549366483891255 29570226501824049725836883)
  ·
    refine ⟨44355339752736074588755325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29570226501824049725836883 44355339752736074588755325)
    ·
      refine ⟨16633252407276027970783247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44355339752736074588755325 16633252407276027970783247)
      ·
        refine ⟨24949878610914041956174871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16633252407276027970783247 24949878610914041956174871)
        ·
          refine ⟨37424817916371062934262307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24949878610914041956174871 37424817916371062934262307)
          ·
            refine ⟨56137226874556594401393461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37424817916371062934262307 56137226874556594401393461)
            ·
              refine ⟨5262865019489680725130637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56137226874556594401393461 5262865019489680725130637)
              ·
                refine ⟨1973574382308630271923989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5262865019489680725130637 1973574382308630271923989)
                ·
                  refine ⟨92511299170717043996437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1973574382308630271923989 92511299170717043996437)
                  ·
                    rfl

theorem cell22_810743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 6].length) (baseStart_810743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810743 prefixEnd_810743 := by exact prefixLift 810743
  have htrace : WordTrace (prefixWord ++ tailWord_810743) baseStart_810743 baseEnd_810743 := by
    simpa [prefixWord, tailWord_810743, baseEnd_810743] using wordTrace_append hprefix tailTrace_810743
  have hstable : (prefixWord ++ tailWord_810743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810743).length < 2 ^ (prefixWord ++ tailWord_810743).sum := by decide
  have hdescent : baseEnd_810743 < baseStart_810743 := by decide
  rcases family_descends (prefixWord ++ tailWord_810743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810762 : List Nat := [3, 1, 2, 2, 1, 4, 2, 2, 1, 4]
def baseStart_810762 : Nat := 118140960795 + 810762 * 2 ^ 59
def prefixEnd_810762 : Nat := 4983230072969 + 3 ^ 40 * 810762 * 2
def baseEnd_810762 : Nat := 277540401600441415764253

theorem tailTrace_810762 : CollatzResearch.WordTrace tailWord_810762 prefixEnd_810762 277540401600441415764253 := by
  unfold tailWord_810762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7392729872188803992694635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19713946325836810647185693 7392729872188803992694635)
  ·
    refine ⟨11089094808283205989041953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7392729872188803992694635 11089094808283205989041953)
    ·
      refine ⟨8316821106212404491781465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11089094808283205989041953 8316821106212404491781465)
      ·
        refine ⟨6237615829659303368836099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8316821106212404491781465 6237615829659303368836099)
        ·
          refine ⟨9356423744488955053254149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6237615829659303368836099 9356423744488955053254149)
          ·
            refine ⟨1754329452091679072485153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9356423744488955053254149 1754329452091679072485153)
            ·
              refine ⟨1315747089068759304363865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1754329452091679072485153 1315747089068759304363865)
              ·
                refine ⟨986810316801569478272899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1315747089068759304363865 986810316801569478272899)
                ·
                  refine ⟨1480215475202354217409349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 986810316801569478272899 1480215475202354217409349)
                  ·
                    refine ⟨277540401600441415764253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1480215475202354217409349 277540401600441415764253)
                    ·
                      rfl

theorem cell22_810762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_810762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810762 prefixEnd_810762 := by exact prefixLift 810762
  have htrace : WordTrace (prefixWord ++ tailWord_810762) baseStart_810762 baseEnd_810762 := by
    simpa [prefixWord, tailWord_810762, baseEnd_810762] using wordTrace_append hprefix tailTrace_810762
  have hstable : (prefixWord ++ tailWord_810762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810762).length < 2 ^ (prefixWord ++ tailWord_810762).sum := by decide
  have hdescent : baseEnd_810762 < baseStart_810762 := by decide
  rcases family_descends (prefixWord ++ tailWord_810762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810792 : List Nat := [2, 1, 5, 1, 1, 2, 2, 1, 4, 3]
def baseStart_810792 : Nat := 118140960795 + 810792 * 2 ^ 59
def prefixEnd_810792 : Nat := 4983230072969 + 3 ^ 40 * 810792 * 2
def baseEnd_810792 : Nat := 277550671213531337514161

theorem tailTrace_810792 : CollatzResearch.WordTrace tailWord_810792 prefixEnd_810792 277550671213531337514161 := by
  unfold tailWord_810792
  simp only [CollatzResearch.WordTrace]
  refine ⟨14786006839323265547185315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19714675785764354062913753 14786006839323265547185315)
  ·
    refine ⟨22179010258984898320777973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14786006839323265547185315 22179010258984898320777973)
    ·
      refine ⟨2079282211779834217572935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22179010258984898320777973 2079282211779834217572935)
      ·
        refine ⟨3118923317669751326359403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2079282211779834217572935 3118923317669751326359403)
        ·
          refine ⟨4678384976504626989539105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3118923317669751326359403 4678384976504626989539105)
          ·
            refine ⟨3508788732378470242154329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4678384976504626989539105 3508788732378470242154329)
            ·
              refine ⟨2631591549283852681615747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3508788732378470242154329 2631591549283852681615747)
              ·
                refine ⟨3947387323925779022423621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2631591549283852681615747 3947387323925779022423621)
                ·
                  refine ⟨740135123236083566704429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3947387323925779022423621 740135123236083566704429)
                  ·
                    refine ⟨277550671213531337514161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 740135123236083566704429 277550671213531337514161)
                    ·
                      rfl

theorem cell22_810792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_810792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810792 prefixEnd_810792 := by exact prefixLift 810792
  have htrace : WordTrace (prefixWord ++ tailWord_810792) baseStart_810792 baseEnd_810792 := by
    simpa [prefixWord, tailWord_810792, baseEnd_810792] using wordTrace_append hprefix tailTrace_810792
  have hstable : (prefixWord ++ tailWord_810792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810792).length < 2 ^ (prefixWord ++ tailWord_810792).sum := by decide
  have hdescent : baseEnd_810792 < baseStart_810792 := by decide
  rcases family_descends (prefixWord ++ tailWord_810792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810865 : List Nat := [1, 2, 2, 2, 1, 3, 3, 1, 2, 5]
def baseStart_810865 : Nat := 118140960795 + 810865 * 2 ^ 59
def prefixEnd_810865 : Nat := 4983230072969 + 3 ^ 40 * 810865 * 2
def baseEnd_810865 : Nat := 277575660605383480438937

theorem tailTrace_810865 : CollatzResearch.WordTrace tailWord_810865 prefixEnd_810865 277575660605383480438937 := by
  unfold tailWord_810865
  simp only [CollatzResearch.WordTrace]
  refine ⟨29574676207382064561778049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19716450804921376374518699 29574676207382064561778049)
  ·
    refine ⟨22181007155536548421333537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29574676207382064561778049 22181007155536548421333537)
    ·
      refine ⟨16635755366652411316000153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22181007155536548421333537 16635755366652411316000153)
      ·
        refine ⟨12476816524989308487000115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16635755366652411316000153 12476816524989308487000115)
        ·
          refine ⟨18715224787483962730500173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12476816524989308487000115 18715224787483962730500173)
          ·
            refine ⟨7018209295306486023937565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18715224787483962730500173 7018209295306486023937565)
            ·
              refine ⟨2631828485739932258976587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7018209295306486023937565 2631828485739932258976587)
              ·
                refine ⟨3947742728609898388464881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2631828485739932258976587 3947742728609898388464881)
                ·
                  refine ⟨2960807046457423791348661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3947742728609898388464881 2960807046457423791348661)
                  ·
                    refine ⟨277575660605383480438937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2960807046457423791348661 277575660605383480438937)
                    ·
                      rfl

theorem cell22_810865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_810865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810865 prefixEnd_810865 := by exact prefixLift 810865
  have htrace : WordTrace (prefixWord ++ tailWord_810865) baseStart_810865 baseEnd_810865 := by
    simpa [prefixWord, tailWord_810865, baseEnd_810865] using wordTrace_append hprefix tailTrace_810865
  have hstable : (prefixWord ++ tailWord_810865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810865).length < 2 ^ (prefixWord ++ tailWord_810865).sum := by decide
  have hdescent : baseEnd_810865 < baseStart_810865 := by decide
  rcases family_descends (prefixWord ++ tailWord_810865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810880 : List Nat := [2, 1, 1, 2, 1, 2, 3, 3, 3, 4]
def baseStart_810880 : Nat := 118140960795 + 810880 * 2 ^ 59
def prefixEnd_810880 : Nat := 4983230072969 + 3 ^ 40 * 810880 * 2
def baseEnd_810880 : Nat := 277580795411928441313891

theorem tailTrace_810880 : CollatzResearch.WordTrace tailWord_810880 prefixEnd_810880 277580795411928441313891 := by
  unfold tailWord_810880
  simp only [CollatzResearch.WordTrace]
  refine ⟨14787611651163861061787047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19716815534885148082382729 14787611651163861061787047)
  ·
    refine ⟨22181417476745791592680571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14787611651163861061787047 22181417476745791592680571)
    ·
      refine ⟨33272126215118687389020857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22181417476745791592680571 33272126215118687389020857)
      ·
        refine ⟨24954094661339015541765643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33272126215118687389020857 24954094661339015541765643)
        ·
          refine ⟨37431141992008523312648465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24954094661339015541765643 37431141992008523312648465)
          ·
            refine ⟨28073356494006392484486349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37431141992008523312648465 28073356494006392484486349)
            ·
              refine ⟨10527508685252397181682381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28073356494006392484486349 10527508685252397181682381)
              ·
                refine ⟨3947815756969648943130893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10527508685252397181682381 3947815756969648943130893)
                ·
                  refine ⟨1480430908863618353674085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3947815756969648943130893 1480430908863618353674085)
                  ·
                    refine ⟨277580795411928441313891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1480430908863618353674085 277580795411928441313891)
                    ·
                      rfl

theorem cell22_810880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 3, 4].length) (baseStart_810880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810880 prefixEnd_810880 := by exact prefixLift 810880
  have htrace : WordTrace (prefixWord ++ tailWord_810880) baseStart_810880 baseEnd_810880 := by
    simpa [prefixWord, tailWord_810880, baseEnd_810880] using wordTrace_append hprefix tailTrace_810880
  have hstable : (prefixWord ++ tailWord_810880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810880).length < 2 ^ (prefixWord ++ tailWord_810880).sum := by decide
  have hdescent : baseEnd_810880 < baseStart_810880 := by decide
  rcases family_descends (prefixWord ++ tailWord_810880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810942 : List Nat := [4, 2, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_810942 : Nat := 118140960795 + 810942 * 2 ^ 59
def prefixEnd_810942 : Nat := 4983230072969 + 3 ^ 40 * 810942 * 2
def baseEnd_810942 : Nat := 277602019278980946263701

theorem tailTrace_810942 : CollatzResearch.WordTrace tailWord_810942 prefixEnd_810942 277602019278980946263701 := by
  unfold tailWord_810942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3697185578512888339041385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19718323085402071141554053 3697185578512888339041385)
  ·
    refine ⟨2772889183884666254281039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3697185578512888339041385 2772889183884666254281039)
    ·
      refine ⟨4159333775826999381421559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2772889183884666254281039 4159333775826999381421559)
      ·
        refine ⟨6239000663740499072132339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4159333775826999381421559 6239000663740499072132339)
        ·
          refine ⟨9358500995610748608198509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6239000663740499072132339 9358500995610748608198509)
          ·
            refine ⟨3509437873354030728074441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9358500995610748608198509 3509437873354030728074441)
            ·
              refine ⟨2632078405015523046055831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3509437873354030728074441 2632078405015523046055831)
              ·
                refine ⟨3948117607523284569083747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2632078405015523046055831 3948117607523284569083747)
                ·
                  refine ⟨5922176411284926853625621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3948117607523284569083747 5922176411284926853625621)
                  ·
                    refine ⟨277602019278980946263701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5922176411284926853625621 277602019278980946263701)
                    ·
                      rfl

theorem cell22_810942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_810942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810942 prefixEnd_810942 := by exact prefixLift 810942
  have htrace : WordTrace (prefixWord ++ tailWord_810942) baseStart_810942 baseEnd_810942 := by
    simpa [prefixWord, tailWord_810942, baseEnd_810942] using wordTrace_append hprefix tailTrace_810942
  have hstable : (prefixWord ++ tailWord_810942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810942).length < 2 ^ (prefixWord ++ tailWord_810942).sum := by decide
  have hdescent : baseEnd_810942 < baseStart_810942 := by decide
  rcases family_descends (prefixWord ++ tailWord_810942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_810978 : List Nat := [3, 3, 3, 1, 2, 1, 1, 3, 2, 3]
def baseStart_810978 : Nat := 118140960795 + 810978 * 2 ^ 59
def prefixEnd_810978 : Nat := 4983230072969 + 3 ^ 40 * 810978 * 2
def baseEnd_810978 : Nat := 277614342814688852363591

theorem tailTrace_810978 : CollatzResearch.WordTrace tailWord_810978 prefixEnd_810978 277614342814688852363591 := by
  unfold tailWord_810978
  simp only [CollatzResearch.WordTrace]
  refine ⟨7394699413993171215160397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19719198437315123240427725 7394699413993171215160397)
  ·
    refine ⟨2773012280247439205685149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7394699413993171215160397 2773012280247439205685149)
    ·
      refine ⟨1039879605092789702131931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2773012280247439205685149 1039879605092789702131931)
      ·
        refine ⟨1559819407639184553197897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1039879605092789702131931 1559819407639184553197897)
        ·
          refine ⟨1169864555729388414898423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1559819407639184553197897 1169864555729388414898423)
          ·
            refine ⟨1754796833594082622347635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1169864555729388414898423 1754796833594082622347635)
            ·
              refine ⟨2632195250391123933521453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1754796833594082622347635 2632195250391123933521453)
              ·
                refine ⟨987073218896671475070545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2632195250391123933521453 987073218896671475070545)
                ·
                  refine ⟨740304914172503606302909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 987073218896671475070545 740304914172503606302909)
                  ·
                    refine ⟨277614342814688852363591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 740304914172503606302909 277614342814688852363591)
                    ·
                      rfl

theorem cell22_810978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_810978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_810978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_810978 prefixEnd_810978 := by exact prefixLift 810978
  have htrace : WordTrace (prefixWord ++ tailWord_810978) baseStart_810978 baseEnd_810978 := by
    simpa [prefixWord, tailWord_810978, baseEnd_810978] using wordTrace_append hprefix tailTrace_810978
  have hstable : (prefixWord ++ tailWord_810978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_810978).length < 2 ^ (prefixWord ++ tailWord_810978).sum := by decide
  have hdescent : baseEnd_810978 < baseStart_810978 := by decide
  rcases family_descends (prefixWord ++ tailWord_810978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811014 : List Nat := [6, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_811014 : Nat := 118140960795 + 811014 * 2 ^ 59
def prefixEnd_811014 : Nat := 4983230072969 + 3 ^ 40 * 811014 * 2
def baseEnd_811014 : Nat := 92542222116798919487827

theorem tailTrace_811014 : CollatzResearch.WordTrace tailWord_811014 prefixEnd_811014 92542222116798919487827 := by
  unfold tailWord_811014
  simp only [CollatzResearch.WordTrace]
  refine ⟨924378458870070719029753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19720073789228175339301397 924378458870070719029753)
  ·
    refine ⟨693283844152553039272315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 924378458870070719029753 693283844152553039272315)
    ·
      refine ⟨1039925766228829558908473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 693283844152553039272315 1039925766228829558908473)
      ·
        refine ⟨779944324671622169181355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1039925766228829558908473 779944324671622169181355)
        ·
          refine ⟨1169916487007433253772033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 779944324671622169181355 1169916487007433253772033)
          ·
            refine ⟨877437365255574940329025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1169916487007433253772033 877437365255574940329025)
            ·
              refine ⟨658078023941681205246769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 877437365255574940329025 658078023941681205246769)
              ·
                refine ⟨493558517956260903935077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 658078023941681205246769 493558517956260903935077)
                ·
                  refine ⟨92542222116798919487827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 493558517956260903935077 92542222116798919487827)
                  ·
                    rfl

theorem cell22_811014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_811014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_811014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_811014 prefixEnd_811014 := by exact prefixLift 811014
  have htrace : WordTrace (prefixWord ++ tailWord_811014) baseStart_811014 baseEnd_811014 := by
    simpa [prefixWord, tailWord_811014, baseEnd_811014] using wordTrace_append hprefix tailTrace_811014
  have hstable : (prefixWord ++ tailWord_811014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811014).length < 2 ^ (prefixWord ++ tailWord_811014).sum := by decide
  have hdescent : baseEnd_811014 < baseStart_811014 := by decide
  rcases family_descends (prefixWord ++ tailWord_811014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811032 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 5, 4]
def baseStart_811032 : Nat := 118140960795 + 811032 * 2 ^ 59
def prefixEnd_811032 : Nat := 4983230072969 + 3 ^ 40 * 811032 * 2
def baseEnd_811032 : Nat := 277632828118250711513425

theorem tailTrace_811032 : CollatzResearch.WordTrace tailWord_811032 prefixEnd_811032 277632828118250711513425 := by
  unfold tailWord_811032
  simp only [CollatzResearch.WordTrace]
  refine ⟨14790383598888526041553675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19720511465184701388738233 14790383598888526041553675)
  ·
    refine ⟨22185575398332789062330513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14790383598888526041553675 22185575398332789062330513)
    ·
      refine ⟨16639181548749591796747885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22185575398332789062330513 16639181548749591796747885)
      ·
        refine ⟨6239693080781096923780457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16639181548749591796747885 6239693080781096923780457)
        ·
          refine ⟨4679769810585822692835343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6239693080781096923780457 4679769810585822692835343)
          ·
            refine ⟨7019654715878734039253015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4679769810585822692835343 7019654715878734039253015)
            ·
              refine ⟨10529482073818101058879523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7019654715878734039253015 10529482073818101058879523)
              ·
                refine ⟨15794223110727151588319285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10529482073818101058879523 15794223110727151588319285)
                ·
                  refine ⟨1480708416630670461404933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15794223110727151588319285 1480708416630670461404933)
                  ·
                    refine ⟨277632828118250711513425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1480708416630670461404933 277632828118250711513425)
                    ·
                      rfl

theorem cell22_811032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_811032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_811032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_811032 prefixEnd_811032 := by exact prefixLift 811032
  have htrace : WordTrace (prefixWord ++ tailWord_811032) baseStart_811032 baseEnd_811032 := by
    simpa [prefixWord, tailWord_811032, baseEnd_811032] using wordTrace_append hprefix tailTrace_811032
  have hstable : (prefixWord ++ tailWord_811032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811032).length < 2 ^ (prefixWord ++ tailWord_811032).sum := by decide
  have hdescent : baseEnd_811032 < baseStart_811032 := by decide
  rcases family_descends (prefixWord ++ tailWord_811032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811077 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 4, 4]
def baseStart_811077 : Nat := 118140960795 + 811077 * 2 ^ 59
def prefixEnd_811077 : Nat := 4983230072969 + 3 ^ 40 * 811077 * 2
def baseEnd_811077 : Nat := 277648232537885594138287

theorem tailTrace_811077 : CollatzResearch.WordTrace tailWord_811077 prefixEnd_811077 277648232537885594138287 := by
  unfold tailWord_811077
  simp only [CollatzResearch.WordTrace]
  refine ⟨29582408482614024768495485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19721605655076016512330323 29582408482614024768495485)
  ·
    refine ⟨11093403180980259288185807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29582408482614024768495485 11093403180980259288185807)
    ·
      refine ⟨16640104771470388932278711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11093403180980259288185807 16640104771470388932278711)
      ·
        refine ⟨24960157157205583398418067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16640104771470388932278711 24960157157205583398418067)
        ·
          refine ⟨37440235735808375097627101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24960157157205583398418067 37440235735808375097627101)
          ·
            refine ⟨14040088400928140661610163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37440235735808375097627101 14040088400928140661610163)
            ·
              refine ⟨21060132601392210992415245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14040088400928140661610163 21060132601392210992415245)
              ·
                refine ⟨7897549725522079122155717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21060132601392210992415245 7897549725522079122155717)
                ·
                  refine ⟨1480790573535389835404197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7897549725522079122155717 1480790573535389835404197)
                  ·
                    refine ⟨277648232537885594138287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1480790573535389835404197 277648232537885594138287)
                    ·
                      rfl

theorem cell22_811077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_811077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_811077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_811077 prefixEnd_811077 := by exact prefixLift 811077
  have htrace : WordTrace (prefixWord ++ tailWord_811077) baseStart_811077 baseEnd_811077 := by
    simpa [prefixWord, tailWord_811077, baseEnd_811077] using wordTrace_append hprefix tailTrace_811077
  have hstable : (prefixWord ++ tailWord_811077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811077).length < 2 ^ (prefixWord ++ tailWord_811077).sum := by decide
  have hdescent : baseEnd_811077 < baseStart_811077 := by decide
  rcases family_descends (prefixWord ++ tailWord_811077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811079 : List Nat := [1, 1, 4, 1, 3, 1, 3, 1, 4, 3]
def baseStart_811079 : Nat := 118140960795 + 811079 * 2 ^ 59
def prefixEnd_811079 : Nat := 4983230072969 + 3 ^ 40 * 811079 * 2
def baseEnd_811079 : Nat := 277648917178758255588281

theorem tailTrace_811079 : CollatzResearch.WordTrace tailWord_811079 prefixEnd_811079 277648917178758255588281 := by
  unfold tailWord_811079
  simp only [CollatzResearch.WordTrace]
  refine ⟨29582481428606779110068291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19721654285737852740045527 29582481428606779110068291)
  ·
    refine ⟨44373722142910168665102437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29582481428606779110068291 44373722142910168665102437)
    ·
      refine ⟨8320072901795656624706707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44373722142910168665102437 8320072901795656624706707)
      ·
        refine ⟨12480109352693484937060061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8320072901795656624706707 12480109352693484937060061)
        ·
          refine ⟨4680041007260056851397523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12480109352693484937060061 4680041007260056851397523)
          ·
            refine ⟨7020061510890085277096285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4680041007260056851397523 7020061510890085277096285)
            ·
              refine ⟨2632523066583781978911107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7020061510890085277096285 2632523066583781978911107)
              ·
                refine ⟨3948784599875672968366661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2632523066583781978911107 3948784599875672968366661)
                ·
                  refine ⟨740397112476688681568749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3948784599875672968366661 740397112476688681568749)
                  ·
                    refine ⟨277648917178758255588281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 740397112476688681568749 277648917178758255588281)
                    ·
                      rfl

theorem cell22_811079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_811079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_811079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_811079 prefixEnd_811079 := by exact prefixLift 811079
  have htrace : WordTrace (prefixWord ++ tailWord_811079) baseStart_811079 baseEnd_811079 := by
    simpa [prefixWord, tailWord_811079, baseEnd_811079] using wordTrace_append hprefix tailTrace_811079
  have hstable : (prefixWord ++ tailWord_811079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811079).length < 2 ^ (prefixWord ++ tailWord_811079).sum := by decide
  have hdescent : baseEnd_811079 < baseStart_811079 := by decide
  rcases family_descends (prefixWord ++ tailWord_811079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811092 : List Nat := [2, 4, 1, 1, 1, 1, 1, 11]
def baseStart_811092 : Nat := 118140960795 + 811092 * 2 ^ 59
def prefixEnd_811092 : Nat := 4983230072969 + 3 ^ 40 * 811092 * 2
def baseEnd_811092 : Nat := 30850374149381172779249

theorem tailTrace_811092 : CollatzResearch.WordTrace tailWord_811092 prefixEnd_811092 30850374149381172779249 := by
  unfold tailWord_811092
  simp only [CollatzResearch.WordTrace]
  refine ⟨14791477788779841165145765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19721970385039788220194353 14791477788779841165145765)
  ·
    refine ⟨2773402085396220218464831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14791477788779841165145765 2773402085396220218464831)
    ·
      refine ⟨4160103128094330327697247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2773402085396220218464831 4160103128094330327697247)
      ·
        refine ⟨6240154692141495491545871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4160103128094330327697247 6240154692141495491545871)
        ·
          refine ⟨9360232038212243237318807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6240154692141495491545871 9360232038212243237318807)
          ·
            refine ⟨14040348057318364855978211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9360232038212243237318807 14040348057318364855978211)
            ·
              refine ⟨21060522085977547283967317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14040348057318364855978211 21060522085977547283967317)
              ·
                refine ⟨30850374149381172779249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 21060522085977547283967317 30850374149381172779249)
                ·
                  rfl

theorem cell22_811092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 11].length) (baseStart_811092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_811092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_811092 prefixEnd_811092 := by exact prefixLift 811092
  have htrace : WordTrace (prefixWord ++ tailWord_811092) baseStart_811092 baseEnd_811092 := by
    simpa [prefixWord, tailWord_811092, baseEnd_811092] using wordTrace_append hprefix tailTrace_811092
  have hstable : (prefixWord ++ tailWord_811092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811092).length < 2 ^ (prefixWord ++ tailWord_811092).sum := by decide
  have hdescent : baseEnd_811092 < baseStart_811092 := by decide
  rcases family_descends (prefixWord ++ tailWord_811092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811109 : List Nat := [1, 3, 1, 3, 2, 2, 4, 6]
def baseStart_811109 : Nat := 118140960795 + 811109 * 2 ^ 59
def prefixEnd_811109 : Nat := 4983230072969 + 3 ^ 40 * 811109 * 2
def baseEnd_811109 : Nat := 30851020754649797482021

theorem tailTrace_811109 : CollatzResearch.WordTrace tailWord_811109 prefixEnd_811109 30851020754649797482021 := by
  unfold tailWord_811109
  simp only [CollatzResearch.WordTrace]
  refine ⟨29583575618498094233660381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19722383745665396155773587 29583575618498094233660381)
  ·
    refine ⟨11093840856936785337622643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29583575618498094233660381 11093840856936785337622643)
    ·
      refine ⟨16640761285405178006433965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11093840856936785337622643 16640761285405178006433965)
      ·
        refine ⟨6240285482026941752412737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16640761285405178006433965 6240285482026941752412737)
        ·
          refine ⟨4680214111520206314309553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6240285482026941752412737 4680214111520206314309553)
          ·
            refine ⟨3510160583640154735732165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4680214111520206314309553 3510160583640154735732165)
            ·
              refine ⟨658155109432529012949781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3510160583640154735732165 658155109432529012949781)
              ·
                refine ⟨30851020754649797482021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 658155109432529012949781 30851020754649797482021)
                ·
                  rfl

theorem cell22_811109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 6].length) (baseStart_811109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_811109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_811109 prefixEnd_811109 := by exact prefixLift 811109
  have htrace : WordTrace (prefixWord ++ tailWord_811109) baseStart_811109 baseEnd_811109 := by
    simpa [prefixWord, tailWord_811109, baseEnd_811109] using wordTrace_append hprefix tailTrace_811109
  have hstable : (prefixWord ++ tailWord_811109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811109).length < 2 ^ (prefixWord ++ tailWord_811109).sum := by decide
  have hdescent : baseEnd_811109 < baseStart_811109 := by decide
  rcases family_descends (prefixWord ++ tailWord_811109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811141 : List Nat := [1, 3, 1, 1, 5, 1, 3, 1, 3, 3]
def baseStart_811141 : Nat := 118140960795 + 811141 * 2 ^ 59
def prefixEnd_811141 : Nat := 4983230072969 + 3 ^ 40 * 811141 * 2
def baseEnd_811141 : Nat := 277670141045810760538091

theorem tailTrace_811141 : CollatzResearch.WordTrace tailWord_811141 prefixEnd_811141 277670141045810760538091 := by
  unfold tailWord_811141
  simp only [CollatzResearch.WordTrace]
  refine ⟨29584742754382163698825277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19723161836254775799216851 29584742754382163698825277)
  ·
    refine ⟨11094278532893311387059479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29584742754382163698825277 11094278532893311387059479)
    ·
      refine ⟨16641417799339967080589219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11094278532893311387059479 16641417799339967080589219)
      ·
        refine ⟨24962126699009950620883829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16641417799339967080589219 24962126699009950620883829)
        ·
          refine ⟨2340199378032182870707859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24962126699009950620883829 2340199378032182870707859)
          ·
            refine ⟨3510299067048274306061789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2340199378032182870707859 3510299067048274306061789)
            ·
              refine ⟨1316362150143102864773171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3510299067048274306061789 1316362150143102864773171)
              ·
                refine ⟨1974543225214654297159757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1316362150143102864773171 1974543225214654297159757)
                ·
                  refine ⟨740453709455495361434909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1974543225214654297159757 740453709455495361434909)
                  ·
                    refine ⟨277670141045810760538091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 740453709455495361434909 277670141045810760538091)
                    ·
                      rfl

theorem cell22_811141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3, 3].length) (baseStart_811141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_811141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_811141 prefixEnd_811141 := by exact prefixLift 811141
  have htrace : WordTrace (prefixWord ++ tailWord_811141) baseStart_811141 baseEnd_811141 := by
    simpa [prefixWord, tailWord_811141, baseEnd_811141] using wordTrace_append hprefix tailTrace_811141
  have hstable : (prefixWord ++ tailWord_811141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811141).length < 2 ^ (prefixWord ++ tailWord_811141).sum := by decide
  have hdescent : baseEnd_811141 < baseStart_811141 := by decide
  rcases family_descends (prefixWord ++ tailWord_811141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811152 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 1, 7]
def baseStart_811152 : Nat := 118140960795 + 811152 * 2 ^ 59
def prefixEnd_811152 : Nat := 4983230072969 + 3 ^ 40 * 811152 * 2
def baseEnd_811152 : Nat := 277673906570610398513057

theorem tailTrace_811152 : CollatzResearch.WordTrace tailWord_811152 prefixEnd_811152 277673906570610398513057 := by
  unfold tailWord_811152
  simp only [CollatzResearch.WordTrace]
  refine ⟨14792571978671156288737855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19723429304894875051650473 14792571978671156288737855)
  ·
    refine ⟨22188857968006734433106783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14792571978671156288737855 22188857968006734433106783)
    ·
      refine ⟨33283286952010101649660175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22188857968006734433106783 33283286952010101649660175)
      ·
        refine ⟨49924930428015152474490263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33283286952010101649660175 49924930428015152474490263)
        ·
          refine ⟨74887395642022728711735395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49924930428015152474490263 74887395642022728711735395)
          ·
            refine ⟨112331093463034093067603093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74887395642022728711735395 112331093463034093067603093)
            ·
              refine ⟨5265520006079723112543895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112331093463034093067603093 5265520006079723112543895)
              ·
                refine ⟨7898280009119584668815843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5265520006079723112543895 7898280009119584668815843)
                ·
                  refine ⟨11847420013679377003223765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7898280009119584668815843 11847420013679377003223765)
                  ·
                    refine ⟨277673906570610398513057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11847420013679377003223765 277673906570610398513057)
                    ·
                      rfl

theorem cell22_811152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 1, 7].length) (baseStart_811152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_811152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_811152 prefixEnd_811152 := by exact prefixLift 811152
  have htrace : WordTrace (prefixWord ++ tailWord_811152) baseStart_811152 baseEnd_811152 := by
    simpa [prefixWord, tailWord_811152, baseEnd_811152] using wordTrace_append hprefix tailTrace_811152
  have hstable : (prefixWord ++ tailWord_811152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811152).length < 2 ^ (prefixWord ++ tailWord_811152).sum := by decide
  have hdescent : baseEnd_811152 < baseStart_811152 := by decide
  rcases family_descends (prefixWord ++ tailWord_811152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811274 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 2, 6]
def baseStart_811274 : Nat := 118140960795 + 811274 * 2 ^ 59
def prefixEnd_811274 : Nat := 4983230072969 + 3 ^ 40 * 811274 * 2
def baseEnd_811274 : Nat := 277715669663842746962683

theorem tailTrace_811274 : CollatzResearch.WordTrace tailWord_811274 prefixEnd_811274 277715669663842746962683 := by
  unfold tailWord_811274
  simp only [CollatzResearch.WordTrace]
  refine ⟨7397398415725081853354219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19726395775266884942277917 7397398415725081853354219)
  ·
    refine ⟨11096097623587622780031329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7397398415725081853354219 11096097623587622780031329)
    ·
      refine ⟨8322073217690717085023497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11096097623587622780031329 8322073217690717085023497)
      ·
        refine ⟨6241554913268037813767623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8322073217690717085023497 6241554913268037813767623)
        ·
          refine ⟨9362332369902056720651435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6241554913268037813767623 9362332369902056720651435)
          ·
            refine ⟨14043498554853085080977153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9362332369902056720651435 14043498554853085080977153)
            ·
              refine ⟨10532623916139813810732865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14043498554853085080977153 10532623916139813810732865)
              ·
                refine ⟨7899467937104860358049649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10532623916139813810732865 7899467937104860358049649)
                ·
                  refine ⟨5924600952828645268537237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7899467937104860358049649 5924600952828645268537237)
                  ·
                    refine ⟨277715669663842746962683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5924600952828645268537237 277715669663842746962683)
                    ·
                      rfl

theorem cell22_811274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_811274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_811274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_811274 prefixEnd_811274 := by exact prefixLift 811274
  have htrace : WordTrace (prefixWord ++ tailWord_811274) baseStart_811274 baseEnd_811274 := by
    simpa [prefixWord, tailWord_811274, baseEnd_811274] using wordTrace_append hprefix tailTrace_811274
  have hstable : (prefixWord ++ tailWord_811274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811274).length < 2 ^ (prefixWord ++ tailWord_811274).sum := by decide
  have hdescent : baseEnd_811274 < baseStart_811274 := by decide
  rcases family_descends (prefixWord ++ tailWord_811274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811276 : List Nat := [2, 2, 1, 2, 2, 2, 1, 4, 3, 3]
def baseStart_811276 : Nat := 118140960795 + 811276 * 2 ^ 59
def prefixEnd_811276 : Nat := 4983230072969 + 3 ^ 40 * 811276 * 2
def baseEnd_811276 : Nat := 277716354304715408412677

theorem tailTrace_811276 : CollatzResearch.WordTrace tailWord_811276 prefixEnd_811276 277716354304715408412677 := by
  unfold tailWord_811276
  simp only [CollatzResearch.WordTrace]
  refine ⟨14794833304446540877494841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19726444405928721169993121 14794833304446540877494841)
  ·
    refine ⟨11096124978334905658121131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14794833304446540877494841 11096124978334905658121131)
    ·
      refine ⟨16644187467502358487181697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11096124978334905658121131 16644187467502358487181697)
      ·
        refine ⟨12483140600626768865386273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16644187467502358487181697 12483140600626768865386273)
        ·
          refine ⟨9362355450470076649039705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12483140600626768865386273 9362355450470076649039705)
          ·
            refine ⟨7021766587852557486779779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9362355450470076649039705 7021766587852557486779779)
            ·
              refine ⟨10532649881778836230169669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7021766587852557486779779 10532649881778836230169669)
              ·
                refine ⟨1974871852833531793156813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10532649881778836230169669 1974871852833531793156813)
                ·
                  refine ⟨740576944812574422433805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1974871852833531793156813 740576944812574422433805)
                  ·
                    refine ⟨277716354304715408412677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 740576944812574422433805 277716354304715408412677)
                    ·
                      rfl

theorem cell22_811276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 3, 3].length) (baseStart_811276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_811276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_811276 prefixEnd_811276 := by exact prefixLift 811276
  have htrace : WordTrace (prefixWord ++ tailWord_811276) baseStart_811276 baseEnd_811276 := by
    simpa [prefixWord, tailWord_811276, baseEnd_811276] using wordTrace_append hprefix tailTrace_811276
  have hstable : (prefixWord ++ tailWord_811276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811276).length < 2 ^ (prefixWord ++ tailWord_811276).sum := by decide
  have hdescent : baseEnd_811276 < baseStart_811276 := by decide
  rcases family_descends (prefixWord ++ tailWord_811276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811402 : List Nat := [3, 1, 2, 5, 1, 1, 2, 3, 4]
def baseStart_811402 : Nat := 118140960795 + 811402 * 2 ^ 59
def prefixEnd_811402 : Nat := 4983230072969 + 3 ^ 40 * 811402 * 2
def baseEnd_811402 : Nat := 92586495559897693254097

theorem tailTrace_811402 : CollatzResearch.WordTrace tailWord_811402 prefixEnd_811402 92586495559897693254097 := by
  unfold tailWord_811402
  simp only [CollatzResearch.WordTrace]
  refine ⟨7398565551609151318519115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19729508137624403516050973 7398565551609151318519115)
  ·
    refine ⟨11097848327413726977778673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7398565551609151318519115 11097848327413726977778673)
    ·
      refine ⟨8323386245560295233334005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11097848327413726977778673 8323386245560295233334005)
      ·
        refine ⟨780317460521277678125063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8323386245560295233334005 780317460521277678125063)
        ·
          refine ⟨1170476190781916517187595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 780317460521277678125063 1170476190781916517187595)
          ·
            refine ⟨1755714286172874775781393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1170476190781916517187595 1755714286172874775781393)
            ·
              refine ⟨1316785714629656081836045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1755714286172874775781393 1316785714629656081836045)
              ·
                refine ⟨493794642986121030688517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1316785714629656081836045 493794642986121030688517)
                ·
                  refine ⟨92586495559897693254097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 493794642986121030688517 92586495559897693254097)
                  ·
                    rfl

theorem cell22_811402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3, 4].length) (baseStart_811402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_811402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_811402 prefixEnd_811402 := by exact prefixLift 811402
  have htrace : WordTrace (prefixWord ++ tailWord_811402) baseStart_811402 baseEnd_811402 := by
    simpa [prefixWord, tailWord_811402, baseEnd_811402] using wordTrace_append hprefix tailTrace_811402
  have hstable : (prefixWord ++ tailWord_811402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811402).length < 2 ^ (prefixWord ++ tailWord_811402).sum := by decide
  have hdescent : baseEnd_811402 < baseStart_811402 := by decide
  rcases family_descends (prefixWord ++ tailWord_811402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811428 : List Nat := [2, 3, 1, 2, 1, 1, 3, 3, 3, 3]
def baseStart_811428 : Nat := 118140960795 + 811428 * 2 ^ 59
def prefixEnd_811428 : Nat := 4983230072969 + 3 ^ 40 * 811428 * 2
def baseEnd_811428 : Nat := 277768387011037678612211

theorem tailTrace_811428 : CollatzResearch.WordTrace tailWord_811428 prefixEnd_811428 277768387011037678612211 := by
  unfold tailWord_811428
  simp only [CollatzResearch.WordTrace]
  refine ⟨14797605252171205857261469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19730140336228274476348625 14797605252171205857261469)
  ·
    refine ⟨5549101969564202196473051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14797605252171205857261469 5549101969564202196473051)
    ·
      refine ⟨8323652954346303294709577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5549101969564202196473051 8323652954346303294709577)
      ·
        refine ⟨6242739715759727471032183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8323652954346303294709577 6242739715759727471032183)
        ·
          refine ⟨9364109573639591206548275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6242739715759727471032183 9364109573639591206548275)
          ·
            refine ⟨14046164360459386809822413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9364109573639591206548275 14046164360459386809822413)
            ·
              refine ⟨5267311635172270053683405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14046164360459386809822413 5267311635172270053683405)
              ·
                refine ⟨1975241863189601270131277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5267311635172270053683405 1975241863189601270131277)
                ·
                  refine ⟨740715698696100476299229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1975241863189601270131277 740715698696100476299229)
                  ·
                    refine ⟨277768387011037678612211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 740715698696100476299229 277768387011037678612211)
                    ·
                      rfl

theorem cell22_811428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_811428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_811428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_811428 prefixEnd_811428 := by exact prefixLift 811428
  have htrace : WordTrace (prefixWord ++ tailWord_811428) baseStart_811428 baseEnd_811428 := by
    simpa [prefixWord, tailWord_811428, baseEnd_811428] using wordTrace_append hprefix tailTrace_811428
  have hstable : (prefixWord ++ tailWord_811428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811428).length < 2 ^ (prefixWord ++ tailWord_811428).sum := by decide
  have hdescent : baseEnd_811428 < baseStart_811428 := by decide
  rcases family_descends (prefixWord ++ tailWord_811428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811434 : List Nat := [3, 1, 6, 1, 1, 2, 1, 1, 1, 5]
def baseStart_811434 : Nat := 118140960795 + 811434 * 2 ^ 59
def prefixEnd_811434 : Nat := 4983230072969 + 3 ^ 40 * 811434 * 2
def baseEnd_811434 : Nat := 277770440933655662962193

theorem tailTrace_811434 : CollatzResearch.WordTrace tailWord_811434 prefixEnd_811434 277770440933655662962193 := by
  unfold tailWord_811434
  simp only [CollatzResearch.WordTrace]
  refine ⟨7398857335580168684810339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19730286228213783159494237 7398857335580168684810339)
  ·
    refine ⟨11098286003370253027215509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7398857335580168684810339 11098286003370253027215509)
    ·
      refine ⟨520232156407980610650727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11098286003370253027215509 520232156407980610650727)
      ·
        refine ⟨780348234611970915976091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520232156407980610650727 780348234611970915976091)
        ·
          refine ⟨1170522351917956373964137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 780348234611970915976091 1170522351917956373964137)
          ·
            refine ⟨877891763938467280473103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1170522351917956373964137 877891763938467280473103)
            ·
              refine ⟨1316837645907700920709655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 877891763938467280473103 1316837645907700920709655)
              ·
                refine ⟨1975256468861551381064483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1316837645907700920709655 1975256468861551381064483)
                ·
                  refine ⟨2962884703292327071596725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1975256468861551381064483 2962884703292327071596725)
                  ·
                    refine ⟨277770440933655662962193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2962884703292327071596725 277770440933655662962193)
                    ·
                      rfl

theorem cell22_811434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_811434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_811434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_811434 prefixEnd_811434 := by exact prefixLift 811434
  have htrace : WordTrace (prefixWord ++ tailWord_811434) baseStart_811434 baseEnd_811434 := by
    simpa [prefixWord, tailWord_811434, baseEnd_811434] using wordTrace_append hprefix tailTrace_811434
  have hstable : (prefixWord ++ tailWord_811434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811434).length < 2 ^ (prefixWord ++ tailWord_811434).sum := by decide
  have hdescent : baseEnd_811434 < baseStart_811434 := by decide
  rcases family_descends (prefixWord ++ tailWord_811434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811471 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 5, 4]
def baseStart_811471 : Nat := 118140960795 + 811471 * 2 ^ 59
def prefixEnd_811471 : Nat := 4983230072969 + 3 ^ 40 * 811471 * 2
def baseEnd_811471 : Nat := 277783106789799899787079

theorem tailTrace_811471 : CollatzResearch.WordTrace tailWord_811471 prefixEnd_811471 277783106789799899787079 := by
  unfold tailWord_811471
  simp only [CollatzResearch.WordTrace]
  refine ⟨29596778843186630058338267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19731185895457753372225511 29596778843186630058338267)
  ·
    refine ⟨44395168264779945087507401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29596778843186630058338267 44395168264779945087507401)
    ·
      refine ⟨33296376198584958815630551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44395168264779945087507401 33296376198584958815630551)
      ·
        refine ⟨49944564297877438223445827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33296376198584958815630551 49944564297877438223445827)
        ·
          refine ⟨74916846446816157335168741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49944564297877438223445827 74916846446816157335168741)
          ·
            refine ⟨14046908708778029500344139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74916846446816157335168741 14046908708778029500344139)
            ·
              refine ⟨21070363063167044250516209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14046908708778029500344139 21070363063167044250516209)
              ·
                refine ⟨15802772297375283187887157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21070363063167044250516209 15802772297375283187887157)
                ·
                  refine ⟨1481509902878932798864421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15802772297375283187887157 1481509902878932798864421)
                  ·
                    refine ⟨277783106789799899787079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1481509902878932798864421 277783106789799899787079)
                    ·
                      rfl

theorem cell22_811471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 4].length) (baseStart_811471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_811471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_811471 prefixEnd_811471 := by exact prefixLift 811471
  have htrace : WordTrace (prefixWord ++ tailWord_811471) baseStart_811471 baseEnd_811471 := by
    simpa [prefixWord, tailWord_811471, baseEnd_811471] using wordTrace_append hprefix tailTrace_811471
  have hstable : (prefixWord ++ tailWord_811471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811471).length < 2 ^ (prefixWord ++ tailWord_811471).sum := by decide
  have hdescent : baseEnd_811471 < baseStart_811471 := by decide
  rcases family_descends (prefixWord ++ tailWord_811471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811531 : List Nat := [1, 1, 1, 1, 7, 11]
def baseStart_811531 : Nat := 118140960795 + 811531 * 2 ^ 59
def prefixEnd_811531 : Nat := 4983230072969 + 3 ^ 40 * 811531 * 2
def baseEnd_811531 : Nat := 3429674642172589423295

theorem tailTrace_811531 : CollatzResearch.WordTrace tailWord_811531 prefixEnd_811531 3429674642172589423295 := by
  unfold tailWord_811531
  simp only [CollatzResearch.WordTrace]
  refine ⟨29598967222969260305522447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19732644815312840203681631 29598967222969260305522447)
  ·
    refine ⟨44398450834453890458283671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29598967222969260305522447 44398450834453890458283671)
    ·
      refine ⟨66597676251680835687425507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44398450834453890458283671 66597676251680835687425507)
      ·
        refine ⟨99896514377521253531138261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66597676251680835687425507 99896514377521253531138261)
        ·
          refine ⟨2341324555723154379636053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 99896514377521253531138261 2341324555723154379636053)
          ·
            refine ⟨3429674642172589423295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2341324555723154379636053 3429674642172589423295)
            ·
              rfl

theorem cell22_811531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 11].length) (baseStart_811531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_811531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_811531 prefixEnd_811531 := by exact prefixLift 811531
  have htrace : WordTrace (prefixWord ++ tailWord_811531) baseStart_811531 baseEnd_811531 := by
    simpa [prefixWord, tailWord_811531, baseEnd_811531] using wordTrace_append hprefix tailTrace_811531
  have hstable : (prefixWord ++ tailWord_811531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811531).length < 2 ^ (prefixWord ++ tailWord_811531).sum := by decide
  have hdescent : baseEnd_811531 < baseStart_811531 := by decide
  rcases family_descends (prefixWord ++ tailWord_811531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811548 : List Nat := [2, 2, 3, 1, 2, 2, 3, 7]
def baseStart_811548 : Nat := 118140960795 + 811548 * 2 ^ 59
def prefixEnd_811548 : Nat := 4983230072969 + 3 ^ 40 * 811548 * 2
def baseEnd_811548 : Nat := 30867718384821929512427

theorem tailTrace_811548 : CollatzResearch.WordTrace tailWord_811548 prefixEnd_811548 30867718384821929512427 := by
  unfold tailWord_811548
  simp only [CollatzResearch.WordTrace]
  refine ⟨14799793631953836104445649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19733058175938448139260865 14799793631953836104445649)
  ·
    refine ⟨11099845223965377078334237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14799793631953836104445649 11099845223965377078334237)
    ·
      refine ⟨4162441958987016404375339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11099845223965377078334237 4162441958987016404375339)
      ·
        refine ⟨6243662938480524606563009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4162441958987016404375339 6243662938480524606563009)
        ·
          refine ⟨4682747203860393454922257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6243662938480524606563009 4682747203860393454922257)
          ·
            refine ⟨3512060402895295091191693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4682747203860393454922257 3512060402895295091191693)
            ·
              refine ⟨1317022651085735659196885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3512060402895295091191693 1317022651085735659196885)
              ·
                refine ⟨30867718384821929512427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1317022651085735659196885 30867718384821929512427)
                ·
                  rfl

theorem cell22_811548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 7].length) (baseStart_811548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_811548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_811548 prefixEnd_811548 := by exact prefixLift 811548
  have htrace : WordTrace (prefixWord ++ tailWord_811548) baseStart_811548 baseEnd_811548 := by
    simpa [prefixWord, tailWord_811548, baseEnd_811548] using wordTrace_append hprefix tailTrace_811548
  have hstable : (prefixWord ++ tailWord_811548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811548).length < 2 ^ (prefixWord ++ tailWord_811548).sum := by decide
  have hdescent : baseEnd_811548 < baseStart_811548 := by decide
  rcases family_descends (prefixWord ++ tailWord_811548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811597 : List Nat := [1, 6, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_811597 : Nat := 118140960795 + 811597 * 2 ^ 59
def prefixEnd_811597 : Nat := 4983230072969 + 3 ^ 40 * 811597 * 2
def baseEnd_811597 : Nat := 277826239164777571136693

theorem tailTrace_811597 : CollatzResearch.WordTrace tailWord_811597 prefixEnd_811597 277826239164777571136693 := by
  unfold tailWord_811597
  simp only [CollatzResearch.WordTrace]
  refine ⟨29601374440730153577425045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19734249627153435718283363 29601374440730153577425045)
  ·
    refine ⟨1387564426909225948941799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29601374440730153577425045 1387564426909225948941799)
    ·
      refine ⟨2081346640363838923412699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1387564426909225948941799 2081346640363838923412699)
      ·
        refine ⟨3122019960545758385119049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2081346640363838923412699 3122019960545758385119049)
        ·
          refine ⟨2341514970409318788839287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3122019960545758385119049 2341514970409318788839287)
          ·
            refine ⟨3512272455613978183258931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2341514970409318788839287 3512272455613978183258931)
            ·
              refine ⟨5268408683420967274888397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3512272455613978183258931 5268408683420967274888397)
              ·
                refine ⟨1975653256282862728083149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5268408683420967274888397 1975653256282862728083149)
                ·
                  refine ⟨740869971106073523031181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1975653256282862728083149 740869971106073523031181)
                  ·
                    refine ⟨277826239164777571136693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 740869971106073523031181 277826239164777571136693)
                    ·
                      rfl

theorem cell22_811597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_811597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_811597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_811597 prefixEnd_811597 := by exact prefixLift 811597
  have htrace : WordTrace (prefixWord ++ tailWord_811597) baseStart_811597 baseEnd_811597 := by
    simpa [prefixWord, tailWord_811597, baseEnd_811597] using wordTrace_append hprefix tailTrace_811597
  have hstable : (prefixWord ++ tailWord_811597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811597).length < 2 ^ (prefixWord ++ tailWord_811597).sum := by decide
  have hdescent : baseEnd_811597 < baseStart_811597 := by decide
  rcases family_descends (prefixWord ++ tailWord_811597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811608 : List Nat := [2, 1, 2, 2, 1, 2, 4, 1, 2, 5]
def baseStart_811608 : Nat := 118140960795 + 811608 * 2 ^ 59
def prefixEnd_811608 : Nat := 4983230072969 + 3 ^ 40 * 811608 * 2
def baseEnd_811608 : Nat := 277830004689577209111659

theorem tailTrace_811608 : CollatzResearch.WordTrace tailWord_811608 prefixEnd_811608 277830004689577209111659 := by
  unfold tailWord_811608
  simp only [CollatzResearch.WordTrace]
  refine ⟨14800887821845151228037739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19734517095793534970716985 14800887821845151228037739)
  ·
    refine ⟨22201331732767726842056609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14800887821845151228037739 22201331732767726842056609)
    ·
      refine ⟨16650998799575795131542457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22201331732767726842056609 16650998799575795131542457)
      ·
        refine ⟨12488249099681846348656843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16650998799575795131542457 12488249099681846348656843)
        ·
          refine ⟨18732373649522769522985265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12488249099681846348656843 18732373649522769522985265)
          ·
            refine ⟨14049280237142077142238949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18732373649522769522985265 14049280237142077142238949)
            ·
              refine ⟨2634240044464139464169803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14049280237142077142238949 2634240044464139464169803)
              ·
                refine ⟨3951360066696209196254705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2634240044464139464169803 3951360066696209196254705)
                ·
                  refine ⟨2963520050022156897191029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3951360066696209196254705 2963520050022156897191029)
                  ·
                    refine ⟨277830004689577209111659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2963520050022156897191029 277830004689577209111659)
                    ·
                      rfl

theorem cell22_811608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_811608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_811608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_811608 prefixEnd_811608 := by exact prefixLift 811608
  have htrace : WordTrace (prefixWord ++ tailWord_811608) baseStart_811608 baseEnd_811608 := by
    simpa [prefixWord, tailWord_811608, baseEnd_811608] using wordTrace_append hprefix tailTrace_811608
  have hstable : (prefixWord ++ tailWord_811608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811608).length < 2 ^ (prefixWord ++ tailWord_811608).sum := by decide
  have hdescent : baseEnd_811608 < baseStart_811608 := by decide
  rcases family_descends (prefixWord ++ tailWord_811608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811749 : List Nat := [1, 3, 1, 4, 1, 2, 1, 5, 1, 3]
def baseStart_811749 : Nat := 118140960795 + 811749 * 2 ^ 59
def prefixEnd_811749 : Nat := 4983230072969 + 3 ^ 40 * 811749 * 2
def baseEnd_811749 : Nat := 277878271871099841336227

theorem tailTrace_811749 : CollatzResearch.WordTrace tailWord_811749 prefixEnd_811749 277878271871099841336227 := by
  unfold tailWord_811749
  simp only [CollatzResearch.WordTrace]
  refine ⟨29606918336179483536958301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19737945557452989024638867 29606918336179483536958301)
  ·
    refine ⟨11102594376067306326359363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29606918336179483536958301 11102594376067306326359363)
    ·
      refine ⟨16653891564100959489539045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11102594376067306326359363 16653891564100959489539045)
      ·
        refine ⟨3122604668268929904288571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16653891564100959489539045 3122604668268929904288571)
        ·
          refine ⟨4683907002403394856432857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3122604668268929904288571 4683907002403394856432857)
          ·
            refine ⟨3512930251802546142324643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4683907002403394856432857 3512930251802546142324643)
            ·
              refine ⟨5269395377703819213486965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3512930251802546142324643 5269395377703819213486965)
              ·
                refine ⟨494005816659733051264403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5269395377703819213486965 494005816659733051264403)
                ·
                  refine ⟨741008724989599576896605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 494005816659733051264403 741008724989599576896605)
                  ·
                    refine ⟨277878271871099841336227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 741008724989599576896605 277878271871099841336227)
                    ·
                      rfl

theorem cell22_811749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5, 1, 3].length) (baseStart_811749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_811749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_811749 prefixEnd_811749 := by exact prefixLift 811749
  have htrace : WordTrace (prefixWord ++ tailWord_811749) baseStart_811749 baseEnd_811749 := by
    simpa [prefixWord, tailWord_811749, baseEnd_811749] using wordTrace_append hprefix tailTrace_811749
  have hstable : (prefixWord ++ tailWord_811749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811749).length < 2 ^ (prefixWord ++ tailWord_811749).sum := by decide
  have hdescent : baseEnd_811749 < baseStart_811749 := by decide
  rcases family_descends (prefixWord ++ tailWord_811749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811762 : List Nat := [3, 2, 1, 3, 1, 2, 3, 2, 5]
def baseStart_811762 : Nat := 118140960795 + 811762 * 2 ^ 59
def prefixEnd_811762 : Nat := 4983230072969 + 3 ^ 40 * 811762 * 2
def baseEnd_811762 : Nat := 92627574012257380253729

theorem tailTrace_811762 : CollatzResearch.WordTrace tailWord_811762 prefixEnd_811762 92627574012257380253729 := by
  unfold tailWord_811762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7401848121283096689295385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19738261656754924504787693 7401848121283096689295385)
  ·
    refine ⟨5551386090962322516971539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7401848121283096689295385 5551386090962322516971539)
    ·
      refine ⟨8327079136443483775457309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5551386090962322516971539 8327079136443483775457309)
      ·
        refine ⟨3122654676166306415796491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8327079136443483775457309 3122654676166306415796491)
        ·
          refine ⟨4683982014249459623694737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3122654676166306415796491 4683982014249459623694737)
          ·
            refine ⟨3512986510687094717771053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4683982014249459623694737 3512986510687094717771053)
            ·
              refine ⟨1317369941507660519164145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3512986510687094717771053 1317369941507660519164145)
              ·
                refine ⟨988027456130745389373109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1317369941507660519164145 988027456130745389373109)
                ·
                  refine ⟨92627574012257380253729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 988027456130745389373109 92627574012257380253729)
                  ·
                    rfl

theorem cell22_811762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_811762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_811762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_811762 prefixEnd_811762 := by exact prefixLift 811762
  have htrace : WordTrace (prefixWord ++ tailWord_811762) baseStart_811762 baseEnd_811762 := by
    simpa [prefixWord, tailWord_811762, baseEnd_811762] using wordTrace_append hprefix tailTrace_811762
  have hstable : (prefixWord ++ tailWord_811762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811762).length < 2 ^ (prefixWord ++ tailWord_811762).sum := by decide
  have hdescent : baseEnd_811762 < baseStart_811762 := by decide
  rcases family_descends (prefixWord ++ tailWord_811762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811839 : List Nat := [1, 1, 2, 2, 5, 2, 1, 3, 2, 3]
def baseStart_811839 : Nat := 118140960795 + 811839 * 2 ^ 59
def prefixEnd_811839 : Nat := 4983230072969 + 3 ^ 40 * 811839 * 2
def baseEnd_811839 : Nat := 277909080710369606585951

theorem tailTrace_811839 : CollatzResearch.WordTrace tailWord_811839 prefixEnd_811839 277909080710369606585951 := by
  unfold tailWord_811839
  simp only [CollatzResearch.WordTrace]
  refine ⟨29610200905853428907734571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19740133937235619271823047 29610200905853428907734571)
  ·
    refine ⟨44415301358780143361601857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29610200905853428907734571 44415301358780143361601857)
    ·
      refine ⟨33311476019085107521201393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44415301358780143361601857 33311476019085107521201393)
      ·
        refine ⟨24983607014313830640901045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33311476019085107521201393 24983607014313830640901045)
        ·
          refine ⟨2342213157591921622584473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24983607014313830640901045 2342213157591921622584473)
          ·
            refine ⟨1756659868193941216938355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2342213157591921622584473 1756659868193941216938355)
            ·
              refine ⟨2634989802290911825407533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1756659868193941216938355 2634989802290911825407533)
              ·
                refine ⟨988121175859091934527825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2634989802290911825407533 988121175859091934527825)
                ·
                  refine ⟨741090881894318950895869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 988121175859091934527825 741090881894318950895869)
                  ·
                    refine ⟨277909080710369606585951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 741090881894318950895869 277909080710369606585951)
                    ·
                      rfl

theorem cell22_811839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2, 3].length) (baseStart_811839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_811839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_811839 prefixEnd_811839 := by exact prefixLift 811839
  have htrace : WordTrace (prefixWord ++ tailWord_811839) baseStart_811839 baseEnd_811839 := by
    simpa [prefixWord, tailWord_811839, baseEnd_811839] using wordTrace_append hprefix tailTrace_811839
  have hstable : (prefixWord ++ tailWord_811839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811839).length < 2 ^ (prefixWord ++ tailWord_811839).sum := by decide
  have hdescent : baseEnd_811839 < baseStart_811839 := by decide
  rcases family_descends (prefixWord ++ tailWord_811839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811886 : List Nat := [4, 1, 2, 3, 3, 1, 1, 7]
def baseStart_811886 : Nat := 118140960795 + 811886 * 2 ^ 59
def prefixEnd_811886 : Nat := 4983230072969 + 3 ^ 40 * 811886 * 2
def baseEnd_811886 : Nat := 30880574418986350073423

theorem tailTrace_811886 : CollatzResearch.WordTrace tailWord_811886 prefixEnd_811886 30880574418986350073423 := by
  unfold tailWord_811886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3701489392085394491836939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19741276757788770623130341 3701489392085394491836939)
  ·
    refine ⟨5552234088128091737755409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3701489392085394491836939 5552234088128091737755409)
    ·
      refine ⟨4164175566096068803316557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5552234088128091737755409 4164175566096068803316557)
      ·
        refine ⟨1561565837286025801243709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4164175566096068803316557 1561565837286025801243709)
        ·
          refine ⟨585587188982259675466391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1561565837286025801243709 585587188982259675466391)
          ·
            refine ⟨878380783473389513199587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585587188982259675466391 878380783473389513199587)
            ·
              refine ⟨1317571175210084269799381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 878380783473389513199587 1317571175210084269799381)
              ·
                refine ⟨30880574418986350073423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1317571175210084269799381 30880574418986350073423)
                ·
                  rfl

theorem cell22_811886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 7].length) (baseStart_811886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_811886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_811886 prefixEnd_811886 := by exact prefixLift 811886
  have htrace : WordTrace (prefixWord ++ tailWord_811886) baseStart_811886 baseEnd_811886 := by
    simpa [prefixWord, tailWord_811886, baseEnd_811886] using wordTrace_append hprefix tailTrace_811886
  have hstable : (prefixWord ++ tailWord_811886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811886).length < 2 ^ (prefixWord ++ tailWord_811886).sum := by decide
  have hdescent : baseEnd_811886 < baseStart_811886 := by decide
  rcases family_descends (prefixWord ++ tailWord_811886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_811897 : List Nat := [1, 2, 1, 3, 2, 3, 2, 3, 5]
def baseStart_811897 : Nat := 118140960795 + 811897 * 2 ^ 59
def prefixEnd_811897 : Nat := 4983230072969 + 3 ^ 40 * 811897 * 2
def baseEnd_811897 : Nat := 92642978431892262878591

theorem tailTrace_811897 : CollatzResearch.WordTrace tailWord_811897 prefixEnd_811897 92642978431892262878591 := by
  unfold tailWord_811897
  simp only [CollatzResearch.WordTrace]
  refine ⟨29612316339643304813345945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19741544226428869875563963 29612316339643304813345945)
  ·
    refine ⟨22209237254732478610009459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29612316339643304813345945 22209237254732478610009459)
    ·
      refine ⟨33313855882098717915014189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22209237254732478610009459 33313855882098717915014189)
      ·
        refine ⟨12492695955787019218130321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33313855882098717915014189 12492695955787019218130321)
        ·
          refine ⟨9369521966840264413597741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12492695955787019218130321 9369521966840264413597741)
          ·
            refine ⟨3513570737565099155099153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9369521966840264413597741 3513570737565099155099153)
            ·
              refine ⟨2635178053173824366324365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3513570737565099155099153 2635178053173824366324365)
              ·
                refine ⟨988191769940184137371637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2635178053173824366324365 988191769940184137371637)
                ·
                  refine ⟨92642978431892262878591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 988191769940184137371637 92642978431892262878591)
                  ·
                    rfl

theorem cell22_811897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 5].length) (baseStart_811897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_811897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_811897 prefixEnd_811897 := by exact prefixLift 811897
  have htrace : WordTrace (prefixWord ++ tailWord_811897) baseStart_811897 baseEnd_811897 := by
    simpa [prefixWord, tailWord_811897, baseEnd_811897] using wordTrace_append hprefix tailTrace_811897
  have hstable : (prefixWord ++ tailWord_811897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_811897).length < 2 ^ (prefixWord ++ tailWord_811897).sum := by decide
  have hdescent : baseEnd_811897 < baseStart_811897 := by decide
  rcases family_descends (prefixWord ++ tailWord_811897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812053 : List Nat := [1, 3, 2, 1, 4, 2, 1, 4, 1, 3]
def baseStart_812053 : Nat := 118140960795 + 812053 * 2 ^ 59
def prefixEnd_812053 : Nat := 4983230072969 + 3 ^ 40 * 812053 * 2
def baseEnd_812053 : Nat := 277982337283744381735295

theorem tailTrace_812053 : CollatzResearch.WordTrace tailWord_812053 prefixEnd_812053 277982337283744381735295 := by
  unfold tailWord_812053
  simp only [CollatzResearch.WordTrace]
  refine ⟨29618006127078143456024813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19745337418052095637349875 29618006127078143456024813)
  ·
    refine ⟨11106752297654303796009305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29618006127078143456024813 11106752297654303796009305)
    ·
      refine ⟨8330064223240727847006979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11106752297654303796009305 8330064223240727847006979)
      ·
        refine ⟨12495096334861091770510469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8330064223240727847006979 12495096334861091770510469)
        ·
          refine ⟨2342830562786454706970713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12495096334861091770510469 2342830562786454706970713)
          ·
            refine ⟨1757122922089841030228035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2342830562786454706970713 1757122922089841030228035)
            ·
              refine ⟨2635684383134761545342053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1757122922089841030228035 2635684383134761545342053)
              ·
                refine ⟨494190821837767789751635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2635684383134761545342053 494190821837767789751635)
                ·
                  refine ⟨741286232756651684627453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 494190821837767789751635 741286232756651684627453)
                  ·
                    refine ⟨277982337283744381735295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 741286232756651684627453 277982337283744381735295)
                    ·
                      rfl

theorem cell22_812053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_812053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_812053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_812053 prefixEnd_812053 := by exact prefixLift 812053
  have htrace : WordTrace (prefixWord ++ tailWord_812053) baseStart_812053 baseEnd_812053 := by
    simpa [prefixWord, tailWord_812053, baseEnd_812053] using wordTrace_append hprefix tailTrace_812053
  have hstable : (prefixWord ++ tailWord_812053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812053).length < 2 ^ (prefixWord ++ tailWord_812053).sum := by decide
  have hdescent : baseEnd_812053 < baseStart_812053 := by decide
  rcases family_descends (prefixWord ++ tailWord_812053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812107 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 5, 6]
def baseStart_812107 : Nat := 118140960795 + 812107 * 2 ^ 59
def prefixEnd_812107 : Nat := 4983230072969 + 3 ^ 40 * 812107 * 2
def baseEnd_812107 : Nat := 278000822587306240885129

theorem tailTrace_812107 : CollatzResearch.WordTrace tailWord_812107 prefixEnd_812107 278000822587306240885129 := by
  unfold tailWord_812107
  simp only [CollatzResearch.WordTrace]
  refine ⟨29619975668882510678490575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19746650445921673785660383 29619975668882510678490575)
  ·
    refine ⟨44429963503323766017735863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29619975668882510678490575 44429963503323766017735863)
    ·
      refine ⟨66644945254985649026603795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44429963503323766017735863 66644945254985649026603795)
      ·
        refine ⟨99967417882478473539905693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66644945254985649026603795 99967417882478473539905693)
        ·
          refine ⟨37487781705929427577464635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99967417882478473539905693 37487781705929427577464635)
          ·
            refine ⟨56231672558894141366196953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37487781705929427577464635 56231672558894141366196953)
            ·
              refine ⟨42173754419170606024647715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56231672558894141366196953 42173754419170606024647715)
              ·
                refine ⟨63260631628755909036971573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42173754419170606024647715 63260631628755909036971573)
                ·
                  refine ⟨5930684215195866472216085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63260631628755909036971573 5930684215195866472216085)
                  ·
                    refine ⟨278000822587306240885129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5930684215195866472216085 278000822587306240885129)
                    ·
                      rfl

theorem cell22_812107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 6].length) (baseStart_812107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_812107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_812107 prefixEnd_812107 := by exact prefixLift 812107
  have htrace : WordTrace (prefixWord ++ tailWord_812107) baseStart_812107 baseEnd_812107 := by
    simpa [prefixWord, tailWord_812107, baseEnd_812107] using wordTrace_append hprefix tailTrace_812107
  have hstable : (prefixWord ++ tailWord_812107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812107).length < 2 ^ (prefixWord ++ tailWord_812107).sum := by decide
  have hdescent : baseEnd_812107 < baseStart_812107 := by decide
  rcases family_descends (prefixWord ++ tailWord_812107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812124 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 3, 6]
def baseStart_812124 : Nat := 118140960795 + 812124 * 2 ^ 59
def prefixEnd_812124 : Nat := 4983230072969 + 3 ^ 40 * 812124 * 2
def baseEnd_812124 : Nat := 278006642034723863210077

theorem tailTrace_812124 : CollatzResearch.WordTrace tailWord_812124 prefixEnd_812124 278006642034723863210077 := by
  unfold tailWord_812124
  simp only [CollatzResearch.WordTrace]
  refine ⟨14810297854910461290929713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19747063806547281721239617 14810297854910461290929713)
  ·
    refine ⟨11107723391182845968197285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14810297854910461290929713 11107723391182845968197285)
    ·
      refine ⟨2082698135846783619036991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11107723391182845968197285 2082698135846783619036991)
      ·
        refine ⟨3124047203770175428555487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2082698135846783619036991 3124047203770175428555487)
        ·
          refine ⟨4686070805655263142833231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3124047203770175428555487 4686070805655263142833231)
          ·
            refine ⟨7029106208482894714249847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4686070805655263142833231 7029106208482894714249847)
            ·
              refine ⟨10543659312724342071374771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7029106208482894714249847 10543659312724342071374771)
              ·
                refine ⟨15815488969086513107062157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10543659312724342071374771 15815488969086513107062157)
                ·
                  refine ⟨5930808363407442415148309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15815488969086513107062157 5930808363407442415148309)
                  ·
                    refine ⟨278006642034723863210077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5930808363407442415148309 278006642034723863210077)
                    ·
                      rfl

theorem cell22_812124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_812124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_812124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_812124 prefixEnd_812124 := by exact prefixLift 812124
  have htrace : WordTrace (prefixWord ++ tailWord_812124) baseStart_812124 baseEnd_812124 := by
    simpa [prefixWord, tailWord_812124, baseEnd_812124] using wordTrace_append hprefix tailTrace_812124
  have hstable : (prefixWord ++ tailWord_812124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812124).length < 2 ^ (prefixWord ++ tailWord_812124).sum := by decide
  have hdescent : baseEnd_812124 < baseStart_812124 := by decide
  rcases family_descends (prefixWord ++ tailWord_812124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812222 : List Nat := [4, 2, 1, 1, 3, 1, 4, 2, 1, 3]
def baseStart_812222 : Nat := 118140960795 + 812222 * 2 ^ 59
def prefixEnd_812222 : Nat := 4983230072969 + 3 ^ 40 * 812222 * 2
def baseEnd_812222 : Nat := 278040189437484274259777

theorem tailTrace_812222 : CollatzResearch.WordTrace tailWord_812222 prefixEnd_812222 278040189437484274259777 := by
  unfold tailWord_812222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3703021257933235664865865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19749446708977256879284613 3703021257933235664865865)
  ·
    refine ⟨2777265943449926748649399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3703021257933235664865865 2777265943449926748649399)
    ·
      refine ⟨4165898915174890122974099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2777265943449926748649399 4165898915174890122974099)
      ·
        refine ⟨6248848372762335184461149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4165898915174890122974099 6248848372762335184461149)
        ·
          refine ⟨2343318139785875694172931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6248848372762335184461149 2343318139785875694172931)
          ·
            refine ⟨3514977209678813541259397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2343318139785875694172931 3514977209678813541259397)
            ·
              refine ⟨659058226814777538986137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3514977209678813541259397 659058226814777538986137)
              ·
                refine ⟨494293670111083154239603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 659058226814777538986137 494293670111083154239603)
                ·
                  refine ⟨741440505166624731359405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 494293670111083154239603 741440505166624731359405)
                  ·
                    refine ⟨278040189437484274259777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 741440505166624731359405 278040189437484274259777)
                    ·
                      rfl

theorem cell22_812222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_812222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_812222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_812222 prefixEnd_812222 := by exact prefixLift 812222
  have htrace : WordTrace (prefixWord ++ tailWord_812222) baseStart_812222 baseEnd_812222 := by
    simpa [prefixWord, tailWord_812222, baseEnd_812222] using wordTrace_append hprefix tailTrace_812222
  have hstable : (prefixWord ++ tailWord_812222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812222).length < 2 ^ (prefixWord ++ tailWord_812222).sum := by decide
  have hdescent : baseEnd_812222 < baseStart_812222 := by decide
  rcases family_descends (prefixWord ++ tailWord_812222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812229 : List Nat := [1, 3, 1, 1, 1, 1, 3, 5, 6]
def baseStart_812229 : Nat := 118140960795 + 812229 * 2 ^ 59
def prefixEnd_812229 : Nat := 4983230072969 + 3 ^ 40 * 812229 * 2
def baseEnd_812229 : Nat := 92680861893512863111585

theorem tailTrace_812229 : CollatzResearch.WordTrace tailWord_812229 prefixEnd_812229 92680861893512863111585 := by
  unfold tailWord_812229
  simp only [CollatzResearch.WordTrace]
  refine ⟨29624425374440525514431741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19749616916293683676287827 29624425374440525514431741)
  ·
    refine ⟨11109159515415197067911903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29624425374440525514431741 11109159515415197067911903)
    ·
      refine ⟨16663739273122795601867855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11109159515415197067911903 16663739273122795601867855)
      ·
        refine ⟨24995608909684193402801783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16663739273122795601867855 24995608909684193402801783)
        ·
          refine ⟨37493413364526290104202675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24995608909684193402801783 37493413364526290104202675)
          ·
            refine ⟨56240120046789435156304013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37493413364526290104202675 56240120046789435156304013)
            ·
              refine ⟨21090045017546038183614005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56240120046789435156304013 21090045017546038183614005)
              ·
                refine ⟨1977191720394941079713813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21090045017546038183614005 1977191720394941079713813)
                ·
                  refine ⟨92680861893512863111585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1977191720394941079713813 92680861893512863111585)
                  ·
                    rfl

theorem cell22_812229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 6].length) (baseStart_812229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_812229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_812229 prefixEnd_812229 := by exact prefixLift 812229
  have htrace : WordTrace (prefixWord ++ tailWord_812229) baseStart_812229 baseEnd_812229 := by
    simpa [prefixWord, tailWord_812229, baseEnd_812229] using wordTrace_append hprefix tailTrace_812229
  have hstable : (prefixWord ++ tailWord_812229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812229).length < 2 ^ (prefixWord ++ tailWord_812229).sum := by decide
  have hdescent : baseEnd_812229 < baseStart_812229 := by decide
  rcases family_descends (prefixWord ++ tailWord_812229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812304 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 5, 8]
def baseStart_812304 : Nat := 118140960795 + 812304 * 2 ^ 59
def prefixEnd_812304 : Nat := 4983230072969 + 3 ^ 40 * 812304 * 2
def baseEnd_812304 : Nat := 278068259713263393709525

theorem tailTrace_812304 : CollatzResearch.WordTrace tailWord_812304 prefixEnd_812304 278068259713263393709525 := by
  unfold tailWord_812304
  simp only [CollatzResearch.WordTrace]
  refine ⟨14813580424584406661705983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19751440566112542215607977 14813580424584406661705983)
  ·
    refine ⟨22220370636876609992558975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14813580424584406661705983 22220370636876609992558975)
    ·
      refine ⟨33330555955314914988838463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22220370636876609992558975 33330555955314914988838463)
      ·
        refine ⟨49995833932972372483257695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33330555955314914988838463 49995833932972372483257695)
        ·
          refine ⟨74993750899458558724886543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49995833932972372483257695 74993750899458558724886543)
          ·
            refine ⟨112490626349187838087329815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74993750899458558724886543 112490626349187838087329815)
            ·
              refine ⟨168735939523781757130994723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112490626349187838087329815 168735939523781757130994723)
              ·
                refine ⟨253103909285672635696492085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168735939523781757130994723 253103909285672635696492085)
                ·
                  refine ⟨23728491495531809596546133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 253103909285672635696492085 23728491495531809596546133)
                  ·
                    refine ⟨278068259713263393709525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23728491495531809596546133 278068259713263393709525)
                    ·
                      rfl

theorem cell22_812304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 8].length) (baseStart_812304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_812304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_812304 prefixEnd_812304 := by exact prefixLift 812304
  have htrace : WordTrace (prefixWord ++ tailWord_812304) baseStart_812304 baseEnd_812304 := by
    simpa [prefixWord, tailWord_812304, baseEnd_812304] using wordTrace_append hprefix tailTrace_812304
  have hstable : (prefixWord ++ tailWord_812304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812304).length < 2 ^ (prefixWord ++ tailWord_812304).sum := by decide
  have hdescent : baseEnd_812304 < baseStart_812304 := by decide
  rcases family_descends (prefixWord ++ tailWord_812304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812336 : List Nat := [2, 1, 1, 1, 2, 2, 4, 4, 5]
def baseStart_812336 : Nat := 118140960795 + 812336 * 2 ^ 59
def prefixEnd_812336 : Nat := 4983230072969 + 3 ^ 40 * 812336 * 2
def baseEnd_812336 : Nat := 92693071322408658969809

theorem tailTrace_812336 : CollatzResearch.WordTrace tailWord_812336 prefixEnd_812336 92693071322408658969809 := by
  unfold tailWord_812336
  simp only [CollatzResearch.WordTrace]
  refine ⟨14814163992526441394288431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19752218656701921859051241 14814163992526441394288431)
  ·
    refine ⟨22221245988789662091432647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14814163992526441394288431 22221245988789662091432647)
    ·
      refine ⟨33331868983184493137148971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22221245988789662091432647 33331868983184493137148971)
      ·
        refine ⟨49997803474776739705723457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33331868983184493137148971 49997803474776739705723457)
        ·
          refine ⟨37498352606082554779292593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49997803474776739705723457 37498352606082554779292593)
          ·
            refine ⟨28123764454561916084469445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37498352606082554779292593 28123764454561916084469445)
            ·
              refine ⟨5273205835230359265838021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28123764454561916084469445 5273205835230359265838021)
              ·
                refine ⟨988726094105692362344629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5273205835230359265838021 988726094105692362344629)
                ·
                  refine ⟨92693071322408658969809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 988726094105692362344629 92693071322408658969809)
                  ·
                    rfl

theorem cell22_812336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 5].length) (baseStart_812336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_812336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_812336 prefixEnd_812336 := by exact prefixLift 812336
  have htrace : WordTrace (prefixWord ++ tailWord_812336) baseStart_812336 baseEnd_812336 := by
    simpa [prefixWord, tailWord_812336, baseEnd_812336] using wordTrace_append hprefix tailTrace_812336
  have hstable : (prefixWord ++ tailWord_812336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812336).length < 2 ^ (prefixWord ++ tailWord_812336).sum := by decide
  have hdescent : baseEnd_812336 < baseStart_812336 := by decide
  rcases family_descends (prefixWord ++ tailWord_812336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812391 : List Nat := [1, 1, 5, 1, 5, 1, 2, 2, 1, 3]
def baseStart_812391 : Nat := 118140960795 + 812391 * 2 ^ 59
def prefixEnd_812391 : Nat := 4983230072969 + 3 ^ 40 * 812391 * 2
def baseEnd_812391 : Nat := 278098041591224166784259

theorem tailTrace_812391 : CollatzResearch.WordTrace tailWord_812391 prefixEnd_812391 278098041591224166784259 := by
  unfold tailWord_812391
  simp only [CollatzResearch.WordTrace]
  refine ⟨29630333999853627181829027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19753555999902418121219351 29630333999853627181829027)
  ·
    refine ⟨44445500999780440772743541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29630333999853627181829027 44445500999780440772743541)
    ·
      refine ⟨4166765718729416322444707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44445500999780440772743541 4166765718729416322444707)
      ·
        refine ⟨6250148578094124483667061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4166765718729416322444707 6250148578094124483667061)
        ·
          refine ⟨585951429196324170343787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6250148578094124483667061 585951429196324170343787)
          ·
            refine ⟨878927143794486255515681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585951429196324170343787 878927143794486255515681)
            ·
              refine ⟨659195357845864691636761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 878927143794486255515681 659195357845864691636761)
              ·
                refine ⟨494396518384398518727571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 659195357845864691636761 494396518384398518727571)
                ·
                  refine ⟨741594777576597778091357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 494396518384398518727571 741594777576597778091357)
                  ·
                    refine ⟨278098041591224166784259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 741594777576597778091357 278098041591224166784259)
                    ·
                      rfl

theorem cell22_812391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_812391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_812391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_812391 prefixEnd_812391 := by exact prefixLift 812391
  have htrace : WordTrace (prefixWord ++ tailWord_812391) baseStart_812391 baseEnd_812391 := by
    simpa [prefixWord, tailWord_812391, baseEnd_812391] using wordTrace_append hprefix tailTrace_812391
  have hstable : (prefixWord ++ tailWord_812391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812391).length < 2 ^ (prefixWord ++ tailWord_812391).sum := by decide
  have hdescent : baseEnd_812391 < baseStart_812391 := by decide
  rcases family_descends (prefixWord ++ tailWord_812391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812411 : List Nat := [1, 1, 1, 1, 1, 6, 2, 2, 1, 6]
def baseStart_812411 : Nat := 118140960795 + 812411 * 2 ^ 59
def prefixEnd_812411 : Nat := 4983230072969 + 3 ^ 40 * 812411 * 2
def baseEnd_812411 : Nat := 278104887999950781284197

theorem tailTrace_812411 : CollatzResearch.WordTrace tailWord_812411 prefixEnd_812411 278104887999950781284197 := by
  unfold tailWord_812411
  simp only [CollatzResearch.WordTrace]
  refine ⟨29631063459781170597557087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19754042306520780398371391 29631063459781170597557087)
  ·
    refine ⟨44446595189671755896335631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29631063459781170597557087 44446595189671755896335631)
    ·
      refine ⟨66669892784507633844503447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44446595189671755896335631 66669892784507633844503447)
      ·
        refine ⟨100004839176761450766755171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66669892784507633844503447 100004839176761450766755171)
        ·
          refine ⟨150007258765142176150132757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100004839176761450766755171 150007258765142176150132757)
          ·
            refine ⟨7031590254616039507037473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 150007258765142176150132757 7031590254616039507037473)
            ·
              refine ⟨5273692690962029630278105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7031590254616039507037473 5273692690962029630278105)
              ·
                refine ⟨3955269518221522222708579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5273692690962029630278105 3955269518221522222708579)
                ·
                  refine ⟨5932904277332283334062869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3955269518221522222708579 5932904277332283334062869)
                  ·
                    refine ⟨278104887999950781284197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5932904277332283334062869 278104887999950781284197)
                    ·
                      rfl

theorem cell22_812411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 6].length) (baseStart_812411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_812411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_812411 prefixEnd_812411 := by exact prefixLift 812411
  have htrace : WordTrace (prefixWord ++ tailWord_812411) baseStart_812411 baseEnd_812411 := by
    simpa [prefixWord, tailWord_812411, baseEnd_812411] using wordTrace_append hprefix tailTrace_812411
  have hstable : (prefixWord ++ tailWord_812411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812411).length < 2 ^ (prefixWord ++ tailWord_812411).sum := by decide
  have hdescent : baseEnd_812411 < baseStart_812411 := by decide
  rcases family_descends (prefixWord ++ tailWord_812411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812413 : List Nat := [1, 4, 1, 1, 2, 2, 4, 1, 1, 5]
def baseStart_812413 : Nat := 118140960795 + 812413 * 2 ^ 59
def prefixEnd_812413 : Nat := 4983230072969 + 3 ^ 40 * 812413 * 2
def baseEnd_812413 : Nat := 278105572640823442734191

theorem tailTrace_812413 : CollatzResearch.WordTrace tailWord_812413 prefixEnd_812413 278105572640823442734191 := by
  unfold tailWord_812413
  simp only [CollatzResearch.WordTrace]
  refine ⟨29631136405773924939129893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19754090937182616626086595 29631136405773924939129893)
  ·
    refine ⟨5555838076082610926086855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29631136405773924939129893 5555838076082610926086855)
    ·
      refine ⟨8333757114123916389130283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5555838076082610926086855 8333757114123916389130283)
      ·
        refine ⟨12500635671185874583695425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8333757114123916389130283 12500635671185874583695425)
        ·
          refine ⟨9375476753389405937771569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12500635671185874583695425 9375476753389405937771569)
          ·
            refine ⟨7031607565042054453328677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9375476753389405937771569 7031607565042054453328677)
            ·
              refine ⟨1318426418445385209999127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7031607565042054453328677 1318426418445385209999127)
              ·
                refine ⟨1977639627668077814998691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1318426418445385209999127 1977639627668077814998691)
                ·
                  refine ⟨2966459441502116722498037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1977639627668077814998691 2966459441502116722498037)
                  ·
                    refine ⟨278105572640823442734191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2966459441502116722498037 278105572640823442734191)
                    ·
                      rfl

theorem cell22_812413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_812413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_812413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_812413 prefixEnd_812413 := by exact prefixLift 812413
  have htrace : WordTrace (prefixWord ++ tailWord_812413) baseStart_812413 baseEnd_812413 := by
    simpa [prefixWord, tailWord_812413, baseEnd_812413] using wordTrace_append hprefix tailTrace_812413
  have hstable : (prefixWord ++ tailWord_812413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812413).length < 2 ^ (prefixWord ++ tailWord_812413).sum := by decide
  have hdescent : baseEnd_812413 < baseStart_812413 := by decide
  rcases family_descends (prefixWord ++ tailWord_812413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812447 : List Nat := [1, 1, 2, 5, 1, 4, 1, 2, 2, 3]
def baseStart_812447 : Nat := 118140960795 + 812447 * 2 ^ 59
def prefixEnd_812447 : Nat := 4983230072969 + 3 ^ 40 * 812447 * 2
def baseEnd_812447 : Nat := 278117211535658687384087

theorem tailTrace_812447 : CollatzResearch.WordTrace tailWord_812447 prefixEnd_812447 278117211535658687384087 := by
  unfold tailWord_812447
  simp only [CollatzResearch.WordTrace]
  refine ⟨29632376487650748745867595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19754917658433832497245063 29632376487650748745867595)
  ·
    refine ⟨44448564731476123118801393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29632376487650748745867595 44448564731476123118801393)
    ·
      refine ⟨33336423548607092339101045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44448564731476123118801393 33336423548607092339101045)
      ·
        refine ⟨3125289707681914906790723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33336423548607092339101045 3125289707681914906790723)
        ·
          refine ⟨4687934561522872360186085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3125289707681914906790723 4687934561522872360186085)
          ·
            refine ⟨878987730285538567534891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4687934561522872360186085 878987730285538567534891)
            ·
              refine ⟨1318481595428307851302337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 878987730285538567534891 1318481595428307851302337)
              ·
                refine ⟨988861196571230888476753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1318481595428307851302337 988861196571230888476753)
                ·
                  refine ⟨741645897428423166357565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 988861196571230888476753 741645897428423166357565)
                  ·
                    refine ⟨278117211535658687384087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 741645897428423166357565 278117211535658687384087)
                    ·
                      rfl

theorem cell22_812447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2, 3].length) (baseStart_812447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_812447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_812447 prefixEnd_812447 := by exact prefixLift 812447
  have htrace : WordTrace (prefixWord ++ tailWord_812447) baseStart_812447 baseEnd_812447 := by
    simpa [prefixWord, tailWord_812447, baseEnd_812447] using wordTrace_append hprefix tailTrace_812447
  have hstable : (prefixWord ++ tailWord_812447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812447).length < 2 ^ (prefixWord ++ tailWord_812447).sum := by decide
  have hdescent : baseEnd_812447 < baseStart_812447 := by decide
  rcases family_descends (prefixWord ++ tailWord_812447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812595 : List Nat := [1, 1, 1, 2, 4, 4, 3, 6]
def baseStart_812595 : Nat := 118140960795 + 812595 * 2 ^ 59
def prefixEnd_812595 : Nat := 4983230072969 + 3 ^ 40 * 812595 * 2
def baseEnd_812595 : Nat := 30907541662248403853737

theorem tailTrace_812595 : CollatzResearch.WordTrace tailWord_812595 prefixEnd_812595 30907541662248403853737 := by
  unfold tailWord_812595
  simp only [CollatzResearch.WordTrace]
  refine ⟨29637774491114570022255239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19758516327409713348170159 29637774491114570022255239)
  ·
    refine ⟨44456661736671855033382859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29637774491114570022255239 44456661736671855033382859)
    ·
      refine ⟨66684992605007782550074289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44456661736671855033382859 66684992605007782550074289)
      ·
        refine ⟨50013744453755836912555717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66684992605007782550074289 50013744453755836912555717)
        ·
          refine ⟨9377577085079219421104197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50013744453755836912555717 9377577085079219421104197)
          ·
            refine ⟨1758295703452353641457037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9377577085079219421104197 1758295703452353641457037)
            ·
              refine ⟨659360888794632615546389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1758295703452353641457037 659360888794632615546389)
              ·
                refine ⟨30907541662248403853737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 659360888794632615546389 30907541662248403853737)
                ·
                  rfl

theorem cell22_812595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 6].length) (baseStart_812595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_812595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_812595 prefixEnd_812595 := by exact prefixLift 812595
  have htrace : WordTrace (prefixWord ++ tailWord_812595) baseStart_812595 baseEnd_812595 := by
    simpa [prefixWord, tailWord_812595, baseEnd_812595] using wordTrace_append hprefix tailTrace_812595
  have hstable : (prefixWord ++ tailWord_812595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812595).length < 2 ^ (prefixWord ++ tailWord_812595).sum := by decide
  have hdescent : baseEnd_812595 < baseStart_812595 := by decide
  rcases family_descends (prefixWord ++ tailWord_812595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812597 : List Nat := [1, 3, 3, 1, 1, 5, 1, 1, 2, 4]
def baseStart_812597 : Nat := 118140960795 + 812597 * 2 ^ 59
def prefixEnd_812597 : Nat := 4983230072969 + 3 ^ 40 * 812597 * 2
def baseEnd_812597 : Nat := 278168559601108296133627

theorem tailTrace_812597 : CollatzResearch.WordTrace tailWord_812597 prefixEnd_812597 278168559601108296133627 := by
  unfold tailWord_812597
  simp only [CollatzResearch.WordTrace]
  refine ⟨29637847437107324363828045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19758564958071549575885363 29637847437107324363828045)
  ·
    refine ⟨11114192788915246636435517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29637847437107324363828045 11114192788915246636435517)
    ·
      refine ⟨4167822295843217488663319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11114192788915246636435517 4167822295843217488663319)
      ·
        refine ⟨6251733443764826232994979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4167822295843217488663319 6251733443764826232994979)
        ·
          refine ⟨9377600165647239349492469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6251733443764826232994979 9377600165647239349492469)
          ·
            refine ⟨879150015529428689014919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9377600165647239349492469 879150015529428689014919)
            ·
              refine ⟨1318725023294143033522379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 879150015529428689014919 1318725023294143033522379)
              ·
                refine ⟨1978087534941214550283569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1318725023294143033522379 1978087534941214550283569)
                ·
                  refine ⟨1483565651205910912712677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1978087534941214550283569 1483565651205910912712677)
                  ·
                    refine ⟨278168559601108296133627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1483565651205910912712677 278168559601108296133627)
                    ·
                      rfl

theorem cell22_812597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_812597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_812597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_812597 prefixEnd_812597 := by exact prefixLift 812597
  have htrace : WordTrace (prefixWord ++ tailWord_812597) baseStart_812597 baseEnd_812597 := by
    simpa [prefixWord, tailWord_812597, baseEnd_812597] using wordTrace_append hprefix tailTrace_812597
  have hstable : (prefixWord ++ tailWord_812597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812597).length < 2 ^ (prefixWord ++ tailWord_812597).sum := by decide
  have hdescent : baseEnd_812597 < baseStart_812597 := by decide
  rcases family_descends (prefixWord ++ tailWord_812597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812661 : List Nat := [1, 3, 4, 2, 1, 1, 3, 3, 1, 3]
def baseStart_812661 : Nat := 118140960795 + 812661 * 2 ^ 59
def prefixEnd_812661 : Nat := 4983230072969 + 3 ^ 40 * 812661 * 2
def baseEnd_812661 : Nat := 278190468109033462533431

theorem tailTrace_812661 : CollatzResearch.WordTrace tailWord_812661 prefixEnd_812661 278190468109033462533431 := by
  unfold tailWord_812661
  simp only [CollatzResearch.WordTrace]
  refine ⟨29640181708875463294157837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19760121139250308862771891 29640181708875463294157837)
  ·
    refine ⟨11115068140828298735309189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29640181708875463294157837 11115068140828298735309189)
    ·
      refine ⟨2084075276405306012870473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11115068140828298735309189 2084075276405306012870473)
      ·
        refine ⟨1563056457303979509652855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2084075276405306012870473 1563056457303979509652855)
        ·
          refine ⟨2344584685955969264479283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1563056457303979509652855 2344584685955969264479283)
          ·
            refine ⟨3516877028933953896718925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2344584685955969264479283 3516877028933953896718925)
            ·
              refine ⟨1318828885850232711269597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3516877028933953896718925 1318828885850232711269597)
              ·
                refine ⟨494560832193837266726099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1318828885850232711269597 494560832193837266726099)
                ·
                  refine ⟨741841248290755900089149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 494560832193837266726099 741841248290755900089149)
                  ·
                    refine ⟨278190468109033462533431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 741841248290755900089149 278190468109033462533431)
                    ·
                      rfl

theorem cell22_812661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_812661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_812661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_812661 prefixEnd_812661 := by exact prefixLift 812661
  have htrace : WordTrace (prefixWord ++ tailWord_812661) baseStart_812661 baseEnd_812661 := by
    simpa [prefixWord, tailWord_812661, baseEnd_812661] using wordTrace_append hprefix tailTrace_812661
  have hstable : (prefixWord ++ tailWord_812661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812661).length < 2 ^ (prefixWord ++ tailWord_812661).sum := by decide
  have hdescent : baseEnd_812661 < baseStart_812661 := by decide
  rcases family_descends (prefixWord ++ tailWord_812661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812704 : List Nat := [2, 1, 1, 4, 3, 3, 1, 2, 1, 4]
def baseStart_812704 : Nat := 118140960795 + 812704 * 2 ^ 59
def prefixEnd_812704 : Nat := 4983230072969 + 3 ^ 40 * 812704 * 2
def baseEnd_812704 : Nat := 278205187887795683708299

theorem tailTrace_812704 : CollatzResearch.WordTrace tailWord_812704 prefixEnd_812704 278205187887795683708299 := by
  unfold tailWord_812704
  simp only [CollatzResearch.WordTrace]
  refine ⟨14820875023859840818986583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19761166698479787758648777 14820875023859840818986583)
  ·
    refine ⟨22231312535789761228479875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14820875023859840818986583 22231312535789761228479875)
    ·
      refine ⟨33346968803684641842719813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22231312535789761228479875 33346968803684641842719813)
      ·
        refine ⟨6252556650690870345509965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33346968803684641842719813 6252556650690870345509965)
        ·
          refine ⟨2344708744009076379566237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6252556650690870345509965 2344708744009076379566237)
          ·
            refine ⟨879265779003403642337339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2344708744009076379566237 879265779003403642337339)
            ·
              refine ⟨1318898668505105463506009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 879265779003403642337339 1318898668505105463506009)
              ·
                refine ⟨989174001378829097629507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1318898668505105463506009 989174001378829097629507)
                ·
                  refine ⟨1483761002068243646444261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 989174001378829097629507 1483761002068243646444261)
                  ·
                    refine ⟨278205187887795683708299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1483761002068243646444261 278205187887795683708299)
                    ·
                      rfl

theorem cell22_812704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 1, 4].length) (baseStart_812704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_812704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_812704 prefixEnd_812704 := by exact prefixLift 812704
  have htrace : WordTrace (prefixWord ++ tailWord_812704) baseStart_812704 baseEnd_812704 := by
    simpa [prefixWord, tailWord_812704, baseEnd_812704] using wordTrace_append hprefix tailTrace_812704
  have hstable : (prefixWord ++ tailWord_812704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812704).length < 2 ^ (prefixWord ++ tailWord_812704).sum := by decide
  have hdescent : baseEnd_812704 < baseStart_812704 := by decide
  rcases family_descends (prefixWord ++ tailWord_812704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812717 : List Nat := [1, 5, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_812717 : Nat := 118140960795 + 812717 * 2 ^ 59
def prefixEnd_812717 : Nat := 4983230072969 + 3 ^ 40 * 812717 * 2
def baseEnd_812717 : Nat := 278209638053467983133259

theorem tailTrace_812717 : CollatzResearch.WordTrace tailWord_812717 prefixEnd_812717 278209638053467983133259 := by
  unfold tailWord_812717
  simp only [CollatzResearch.WordTrace]
  refine ⟨29642224196672584858196405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19761482797781723238797603 29642224196672584858196405)
  ·
    refine ⟨2778958518438054830455913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29642224196672584858196405 2778958518438054830455913)
    ·
      refine ⟨2084218888828541122841935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2778958518438054830455913 2084218888828541122841935)
      ·
        refine ⟨3126328333242811684262903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2084218888828541122841935 3126328333242811684262903)
        ·
          refine ⟨4689492499864217526394355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3126328333242811684262903 4689492499864217526394355)
          ·
            refine ⟨7034238749796326289591533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4689492499864217526394355 7034238749796326289591533)
            ·
              refine ⟨2637839531173622358596825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7034238749796326289591533 2637839531173622358596825)
              ·
                refine ⟨1978379648380216768947619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2637839531173622358596825 1978379648380216768947619)
                ·
                  refine ⟨2967569472570325153421429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1978379648380216768947619 2967569472570325153421429)
                  ·
                    refine ⟨278209638053467983133259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2967569472570325153421429 278209638053467983133259)
                    ·
                      rfl

theorem cell22_812717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_812717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_812717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_812717 prefixEnd_812717 := by exact prefixLift 812717
  have htrace : WordTrace (prefixWord ++ tailWord_812717) baseStart_812717 baseEnd_812717 := by
    simpa [prefixWord, tailWord_812717, baseEnd_812717] using wordTrace_append hprefix tailTrace_812717
  have hstable : (prefixWord ++ tailWord_812717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812717).length < 2 ^ (prefixWord ++ tailWord_812717).sum := by decide
  have hdescent : baseEnd_812717 < baseStart_812717 := by decide
  rcases family_descends (prefixWord ++ tailWord_812717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812732 : List Nat := [2, 2, 2, 3, 1, 2, 2, 2, 2, 4]
def baseStart_812732 : Nat := 118140960795 + 812732 * 2 ^ 59
def prefixEnd_812732 : Nat := 4983230072969 + 3 ^ 40 * 812732 * 2
def baseEnd_812732 : Nat := 278214772860012944008213

theorem tailTrace_812732 : CollatzResearch.WordTrace tailWord_812732 prefixEnd_812732 278214772860012944008213 := by
  unfold tailWord_812732
  simp only [CollatzResearch.WordTrace]
  refine ⟨14821385645809121209996225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19761847527745494946661633 14821385645809121209996225)
  ·
    refine ⟨11116039234356840907497169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14821385645809121209996225 11116039234356840907497169)
    ·
      refine ⟨8337029425767630680622877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11116039234356840907497169 8337029425767630680622877)
      ·
        refine ⟨3126386034662861505233579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8337029425767630680622877 3126386034662861505233579)
        ·
          refine ⟨4689579051994292257850369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3126386034662861505233579 4689579051994292257850369)
          ·
            refine ⟨3517184288995719193387777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4689579051994292257850369 3517184288995719193387777)
            ·
              refine ⟨2637888216746789395040833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3517184288995719193387777 2637888216746789395040833)
              ·
                refine ⟨1978416162560092046280625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2637888216746789395040833 1978416162560092046280625)
                ·
                  refine ⟨1483812121920069034710469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1978416162560092046280625 1483812121920069034710469)
                  ·
                    refine ⟨278214772860012944008213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1483812121920069034710469 278214772860012944008213)
                    ·
                      rfl

theorem cell22_812732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_812732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_812732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_812732 prefixEnd_812732 := by exact prefixLift 812732
  have htrace : WordTrace (prefixWord ++ tailWord_812732) baseStart_812732 baseEnd_812732 := by
    simpa [prefixWord, tailWord_812732, baseEnd_812732] using wordTrace_append hprefix tailTrace_812732
  have hstable : (prefixWord ++ tailWord_812732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812732).length < 2 ^ (prefixWord ++ tailWord_812732).sum := by decide
  have hdescent : baseEnd_812732 < baseStart_812732 := by decide
  rcases family_descends (prefixWord ++ tailWord_812732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812734 : List Nat := [4, 2, 1, 1, 2, 2, 1, 4, 2, 3]
def baseStart_812734 : Nat := 118140960795 + 812734 * 2 ^ 59
def prefixEnd_812734 : Nat := 4983230072969 + 3 ^ 40 * 812734 * 2
def baseEnd_812734 : Nat := 278215457500885605458207

theorem tailTrace_812734 : CollatzResearch.WordTrace tailWord_812734 prefixEnd_812734 278215457500885605458207 := by
  unfold tailWord_812734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3705355529701374595195657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19761896158407331174376837 3705355529701374595195657)
  ·
    refine ⟨2779016647276030946396743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3705355529701374595195657 2779016647276030946396743)
    ·
      refine ⟨4168524970914046419595115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2779016647276030946396743 4168524970914046419595115)
      ·
        refine ⟨6252787456371069629392673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4168524970914046419595115 6252787456371069629392673)
        ·
          refine ⟨4689590592278302222044505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6252787456371069629392673 4689590592278302222044505)
          ·
            refine ⟨3517192944208726666533379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4689590592278302222044505 3517192944208726666533379)
            ·
              refine ⟨5275789416313089999800069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3517192944208726666533379 5275789416313089999800069)
              ·
                refine ⟨989210515558704374962513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5275789416313089999800069 989210515558704374962513)
                ·
                  refine ⟨741907886669028281221885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 989210515558704374962513 741907886669028281221885)
                  ·
                    refine ⟨278215457500885605458207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 741907886669028281221885 278215457500885605458207)
                    ·
                      rfl

theorem cell22_812734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_812734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_812734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_812734 prefixEnd_812734 := by exact prefixLift 812734
  have htrace : WordTrace (prefixWord ++ tailWord_812734) baseStart_812734 baseEnd_812734 := by
    simpa [prefixWord, tailWord_812734, baseEnd_812734] using wordTrace_append hprefix tailTrace_812734
  have hstable : (prefixWord ++ tailWord_812734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812734).length < 2 ^ (prefixWord ++ tailWord_812734).sum := by decide
  have hdescent : baseEnd_812734 < baseStart_812734 := by decide
  rcases family_descends (prefixWord ++ tailWord_812734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812760 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 2, 6]
def baseStart_812760 : Nat := 118140960795 + 812760 * 2 ^ 59
def prefixEnd_812760 : Nat := 4983230072969 + 3 ^ 40 * 812760 * 2
def baseEnd_812760 : Nat := 278224357832230204308127

theorem tailTrace_812760 : CollatzResearch.WordTrace tailWord_812760 prefixEnd_812760 278224357832230204308127 := by
  unfold tailWord_812760
  simp only [CollatzResearch.WordTrace]
  refine ⟨14821896267758401601005867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19762528357011202134674489 14821896267758401601005867)
  ·
    refine ⟨22232844401637602401508801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14821896267758401601005867 22232844401637602401508801)
    ·
      refine ⟨16674633301228201801131601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22232844401637602401508801 16674633301228201801131601)
      ·
        refine ⟨12505974975921151350848701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16674633301228201801131601 12505974975921151350848701)
        ·
          refine ⟨4689740615970431756568263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12505974975921151350848701 4689740615970431756568263)
          ·
            refine ⟨7034610923955647634852395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4689740615970431756568263 7034610923955647634852395)
            ·
              refine ⟨10551916385933471452278593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7034610923955647634852395 10551916385933471452278593)
              ·
                refine ⟨7913937289450103589208945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10551916385933471452278593 7913937289450103589208945)
                ·
                  refine ⟨5935452967087577691906709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7913937289450103589208945 5935452967087577691906709)
                  ·
                    refine ⟨278224357832230204308127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5935452967087577691906709 278224357832230204308127)
                    ·
                      rfl

theorem cell22_812760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_812760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_812760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_812760 prefixEnd_812760 := by exact prefixLift 812760
  have htrace : WordTrace (prefixWord ++ tailWord_812760) baseStart_812760 baseEnd_812760 := by
    simpa [prefixWord, tailWord_812760, baseEnd_812760] using wordTrace_append hprefix tailTrace_812760
  have hstable : (prefixWord ++ tailWord_812760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812760).length < 2 ^ (prefixWord ++ tailWord_812760).sum := by decide
  have hdescent : baseEnd_812760 < baseStart_812760 := by decide
  rcases family_descends (prefixWord ++ tailWord_812760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812762 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 5, 3]
def baseStart_812762 : Nat := 118140960795 + 812762 * 2 ^ 59
def prefixEnd_812762 : Nat := 4983230072969 + 3 ^ 40 * 812762 * 2
def baseEnd_812762 : Nat := 278225042473102865758121

theorem tailTrace_812762 : CollatzResearch.WordTrace tailWord_812762 prefixEnd_812762 278225042473102865758121 := by
  unfold tailWord_812762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7410966370377389385896135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19762576987673038362389693 7410966370377389385896135)
  ·
    refine ⟨11116449555566084078844203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7410966370377389385896135 11116449555566084078844203)
    ·
      refine ⟨16674674333349126118266305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11116449555566084078844203 16674674333349126118266305)
      ·
        refine ⟨12506005750011844588699729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16674674333349126118266305 12506005750011844588699729)
        ·
          refine ⟨9379504312508883441524797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12506005750011844588699729 9379504312508883441524797)
          ·
            refine ⟨3517314117190831290571799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9379504312508883441524797 3517314117190831290571799)
            ·
              refine ⟨5275971175786246935857699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3517314117190831290571799 5275971175786246935857699)
              ·
                refine ⟨7913956763679370403786549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5275971175786246935857699 7913956763679370403786549)
                ·
                  refine ⟨741933446594940975354989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7913956763679370403786549 741933446594940975354989)
                  ·
                    refine ⟨278225042473102865758121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 741933446594940975354989 278225042473102865758121)
                    ·
                      rfl

theorem cell22_812762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 5, 3].length) (baseStart_812762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_812762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_812762 prefixEnd_812762 := by exact prefixLift 812762
  have htrace : WordTrace (prefixWord ++ tailWord_812762) baseStart_812762 baseEnd_812762 := by
    simpa [prefixWord, tailWord_812762, baseEnd_812762] using wordTrace_append hprefix tailTrace_812762
  have hstable : (prefixWord ++ tailWord_812762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812762).length < 2 ^ (prefixWord ++ tailWord_812762).sum := by decide
  have hdescent : baseEnd_812762 < baseStart_812762 := by decide
  rcases family_descends (prefixWord ++ tailWord_812762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812779 : List Nat := [1, 1, 1, 1, 2, 4, 3, 5, 1, 3]
def baseStart_812779 : Nat := 118140960795 + 812779 * 2 ^ 59
def prefixEnd_812779 : Nat := 4983230072969 + 3 ^ 40 * 812779 * 2
def baseEnd_812779 : Nat := 278230861920520488083069

theorem tailTrace_812779 : CollatzResearch.WordTrace tailWord_812779 prefixEnd_812779 278230861920520488083069 := by
  unfold tailWord_812779
  simp only [CollatzResearch.WordTrace]
  refine ⟨29644485522447969446953391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19762990348298646297968927 29644485522447969446953391)
  ·
    refine ⟨44466728283671954170430087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29644485522447969446953391 44466728283671954170430087)
    ·
      refine ⟨66700092425507931255645131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44466728283671954170430087 66700092425507931255645131)
      ·
        refine ⟨100050138638261896883467697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66700092425507931255645131 100050138638261896883467697)
        ·
          refine ⟨75037603978696422662600773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100050138638261896883467697 75037603978696422662600773)
          ·
            refine ⟨14069550746005579249237645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75037603978696422662600773 14069550746005579249237645)
            ·
              refine ⟨5276081529752092218464117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14069550746005579249237645 5276081529752092218464117)
              ·
                refine ⟨494632643414258645481011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5276081529752092218464117 494632643414258645481011)
                ·
                  refine ⟨741948965121387968221517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 494632643414258645481011 741948965121387968221517)
                  ·
                    refine ⟨278230861920520488083069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 741948965121387968221517 278230861920520488083069)
                    ·
                      rfl

theorem cell22_812779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5, 1, 3].length) (baseStart_812779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_812779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_812779 prefixEnd_812779 := by exact prefixLift 812779
  have htrace : WordTrace (prefixWord ++ tailWord_812779) baseStart_812779 baseEnd_812779 := by
    simpa [prefixWord, tailWord_812779, baseEnd_812779] using wordTrace_append hprefix tailTrace_812779
  have hstable : (prefixWord ++ tailWord_812779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812779).length < 2 ^ (prefixWord ++ tailWord_812779).sum := by decide
  have hdescent : baseEnd_812779 < baseStart_812779 := by decide
  rcases family_descends (prefixWord ++ tailWord_812779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812869 : List Nat := [1, 3, 1, 1, 1, 2, 5, 3, 2, 3]
def baseStart_812869 : Nat := 118140960795 + 812869 * 2 ^ 59
def prefixEnd_812869 : Nat := 4983230072969 + 3 ^ 40 * 812869 * 2
def baseEnd_812869 : Nat := 278261670759790253332793

theorem tailTrace_812869 : CollatzResearch.WordTrace tailWord_812869 prefixEnd_812869 278261670759790253332793 := by
  unfold tailWord_812869
  simp only [CollatzResearch.WordTrace]
  refine ⟨29647768092121914817729661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19765178728081276545153107 29647768092121914817729661)
  ·
    refine ⟨11117913034545718056648623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29647768092121914817729661 11117913034545718056648623)
    ·
      refine ⟨16676869551818577084972935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11117913034545718056648623 16676869551818577084972935)
      ·
        refine ⟨25015304327727865627459403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16676869551818577084972935 25015304327727865627459403)
        ·
          refine ⟨37522956491591798441189105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25015304327727865627459403 37522956491591798441189105)
          ·
            refine ⟨28142217368693848830891829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37522956491591798441189105 28142217368693848830891829)
            ·
              refine ⟨2638332878315048327896109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28142217368693848830891829 2638332878315048327896109)
              ·
                refine ⟨989374829368143122961041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2638332878315048327896109 989374829368143122961041)
                ·
                  refine ⟨742031122026107342220781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 989374829368143122961041 742031122026107342220781)
                  ·
                    refine ⟨278261670759790253332793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 742031122026107342220781 278261670759790253332793)
                    ·
                      rfl

theorem cell22_812869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2, 3].length) (baseStart_812869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_812869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_812869 prefixEnd_812869 := by exact prefixLift 812869
  have htrace : WordTrace (prefixWord ++ tailWord_812869) baseStart_812869 baseEnd_812869 := by
    simpa [prefixWord, tailWord_812869, baseEnd_812869] using wordTrace_append hprefix tailTrace_812869
  have hstable : (prefixWord ++ tailWord_812869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812869).length < 2 ^ (prefixWord ++ tailWord_812869).sum := by decide
  have hdescent : baseEnd_812869 < baseStart_812869 := by decide
  rcases family_descends (prefixWord ++ tailWord_812869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812882 : List Nat := [3, 2, 2, 1, 1, 3, 2, 8]
def baseStart_812882 : Nat := 118140960795 + 812882 * 2 ^ 59
def prefixEnd_812882 : Nat := 4983230072969 + 3 ^ 40 * 812882 * 2
def baseEnd_812882 : Nat := 30918457880606950306417

theorem tailTrace_812882 : CollatzResearch.WordTrace tailWord_812882 prefixEnd_812882 30918457880606950306417 := by
  unfold tailWord_812882
  simp only [CollatzResearch.WordTrace]
  refine ⟨7412060560268704509488225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19765494827383212025301933 7412060560268704509488225)
  ·
    refine ⟨5559045420201528382116169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7412060560268704509488225 5559045420201528382116169)
    ·
      refine ⟨4169284065151146286587127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5559045420201528382116169 4169284065151146286587127)
      ·
        refine ⟨6253926097726719429880691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4169284065151146286587127 6253926097726719429880691)
        ·
          refine ⟨9380889146590079144821037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6253926097726719429880691 9380889146590079144821037)
          ·
            refine ⟨3517833429971279679307889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9380889146590079144821037 3517833429971279679307889)
            ·
              refine ⟨2638375072478459759480917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3517833429971279679307889 2638375072478459759480917)
              ·
                refine ⟨30918457880606950306417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2638375072478459759480917 30918457880606950306417)
                ·
                  rfl

theorem cell22_812882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 8].length) (baseStart_812882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_812882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_812882 prefixEnd_812882 := by exact prefixLift 812882
  have htrace : WordTrace (prefixWord ++ tailWord_812882) baseStart_812882 baseEnd_812882 := by
    simpa [prefixWord, tailWord_812882, baseEnd_812882] using wordTrace_append hprefix tailTrace_812882
  have hstable : (prefixWord ++ tailWord_812882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812882).length < 2 ^ (prefixWord ++ tailWord_812882).sum := by decide
  have hdescent : baseEnd_812882 < baseStart_812882 := by decide
  rcases family_descends (prefixWord ++ tailWord_812882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812884 : List Nat := [2, 4, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_812884 : Nat := 118140960795 + 812884 * 2 ^ 59
def prefixEnd_812884 : Nat := 4983230072969 + 3 ^ 40 * 812884 * 2
def baseEnd_812884 : Nat := 278266805566335214207747

theorem tailTrace_812884 : CollatzResearch.WordTrace tailWord_812884 prefixEnd_812884 278266805566335214207747 := by
  unfold tailWord_812884
  simp only [CollatzResearch.WordTrace]
  refine ⟨14824157593533786189762853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19765543458045048253017137 14824157593533786189762853)
  ·
    refine ⟨2779529548787584910580535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14824157593533786189762853 2779529548787584910580535)
    ·
      refine ⟨4169294323181377365870803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2779529548787584910580535 4169294323181377365870803)
      ·
        refine ⟨6253941484772066048806205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4169294323181377365870803 6253941484772066048806205)
        ·
          refine ⟨2345228056789524768302327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6253941484772066048806205 2345228056789524768302327)
          ·
            refine ⟨3517842085184287152453491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2345228056789524768302327 3517842085184287152453491)
            ·
              refine ⟨5276763127776430728680237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3517842085184287152453491 5276763127776430728680237)
              ·
                refine ⟨1978786172916161523255089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5276763127776430728680237 1978786172916161523255089)
                ·
                  refine ⟨1484089629687121142441317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1978786172916161523255089 1484089629687121142441317)
                  ·
                    refine ⟨278266805566335214207747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1484089629687121142441317 278266805566335214207747)
                    ·
                      rfl

theorem cell22_812884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_812884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_812884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_812884 prefixEnd_812884 := by exact prefixLift 812884
  have htrace : WordTrace (prefixWord ++ tailWord_812884) baseStart_812884 baseEnd_812884 := by
    simpa [prefixWord, tailWord_812884, baseEnd_812884] using wordTrace_append hprefix tailTrace_812884
  have hstable : (prefixWord ++ tailWord_812884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812884).length < 2 ^ (prefixWord ++ tailWord_812884).sum := by decide
  have hdescent : baseEnd_812884 < baseStart_812884 := by decide
  rcases family_descends (prefixWord ++ tailWord_812884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812914 : List Nat := [3, 2, 1, 2, 1, 1, 1, 5, 3, 3]
def baseStart_812914 : Nat := 118140960795 + 812914 * 2 ^ 59
def prefixEnd_812914 : Nat := 4983230072969 + 3 ^ 40 * 812914 * 2
def baseEnd_812914 : Nat := 278277075179425135957655

theorem tailTrace_812914 : CollatzResearch.WordTrace tailWord_812914 prefixEnd_812914 278277075179425135957655 := by
  unfold tailWord_812914
  simp only [CollatzResearch.WordTrace]
  refine ⟨7412352344239721875779449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19766272917972591668745197 7412352344239721875779449)
  ·
    refine ⟨5559264258179791406834587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7412352344239721875779449 5559264258179791406834587)
    ·
      refine ⟨8338896387269687110251881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5559264258179791406834587 8338896387269687110251881)
      ·
        refine ⟨6254172290452265332688911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8338896387269687110251881 6254172290452265332688911)
        ·
          refine ⟨9381258435678397999033367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6254172290452265332688911 9381258435678397999033367)
          ·
            refine ⟨14071887653517596998550051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9381258435678397999033367 14071887653517596998550051)
            ·
              refine ⟨21107831480276395497825077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14071887653517596998550051 21107831480276395497825077)
              ·
                refine ⟨1978859201275912077921101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21107831480276395497825077 1978859201275912077921101)
                ·
                  refine ⟨742072200478467029220413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1978859201275912077921101 742072200478467029220413)
                  ·
                    refine ⟨278277075179425135957655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 742072200478467029220413 278277075179425135957655)
                    ·
                      rfl

theorem cell22_812914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_812914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_812914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_812914 prefixEnd_812914 := by exact prefixLift 812914
  have htrace : WordTrace (prefixWord ++ tailWord_812914) baseStart_812914 baseEnd_812914 := by
    simpa [prefixWord, tailWord_812914, baseEnd_812914] using wordTrace_append hprefix tailTrace_812914
  have hstable : (prefixWord ++ tailWord_812914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812914).length < 2 ^ (prefixWord ++ tailWord_812914).sum := by decide
  have hdescent : baseEnd_812914 < baseStart_812914 := by decide
  rcases family_descends (prefixWord ++ tailWord_812914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812948 : List Nat := [2, 4, 2, 1, 1, 2, 1, 5, 1, 3]
def baseStart_812948 : Nat := 118140960795 + 812948 * 2 ^ 59
def prefixEnd_812948 : Nat := 4983230072969 + 3 ^ 40 * 812948 * 2
def baseEnd_812948 : Nat := 278288714074260380607551

theorem tailTrace_812948 : CollatzResearch.WordTrace tailWord_812948 prefixEnd_812948 278288714074260380607551 := by
  unfold tailWord_812948
  simp only [CollatzResearch.WordTrace]
  refine ⟨14825324729417855654927749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19767099639223807539903665 14825324729417855654927749)
  ·
    refine ⟨2779748386765847935298953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14825324729417855654927749 2779748386765847935298953)
    ·
      refine ⟨2084811290074385951474215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2779748386765847935298953 2084811290074385951474215)
      ·
        refine ⟨3127216935111578927211323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2084811290074385951474215 3127216935111578927211323)
        ·
          refine ⟨4690825402667368390816985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3127216935111578927211323 4690825402667368390816985)
          ·
            refine ⟨3518119052000526293112739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4690825402667368390816985 3518119052000526293112739)
            ·
              refine ⟨5277178578000789439669109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3518119052000526293112739 5277178578000789439669109)
              ·
                refine ⟨494735491687574009968979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5277178578000789439669109 494735491687574009968979)
                ·
                  refine ⟨742103237531361014953469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 494735491687574009968979 742103237531361014953469)
                  ·
                    refine ⟨278288714074260380607551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 742103237531361014953469 278288714074260380607551)
                    ·
                      rfl

theorem cell22_812948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_812948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_812948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_812948 prefixEnd_812948 := by exact prefixLift 812948
  have htrace : WordTrace (prefixWord ++ tailWord_812948) baseStart_812948 baseEnd_812948 := by
    simpa [prefixWord, tailWord_812948, baseEnd_812948] using wordTrace_append hprefix tailTrace_812948
  have hstable : (prefixWord ++ tailWord_812948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812948).length < 2 ^ (prefixWord ++ tailWord_812948).sum := by decide
  have hdescent : baseEnd_812948 < baseStart_812948 := by decide
  rcases family_descends (prefixWord ++ tailWord_812948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_812989 : List Nat := [1, 4, 1, 2, 3, 1, 2, 2, 6]
def baseStart_812989 : Nat := 118140960795 + 812989 * 2 ^ 59
def prefixEnd_812989 : Nat := 4983230072969 + 3 ^ 40 * 812989 * 2
def baseEnd_812989 : Nat := 92767583070716646777475

theorem tailTrace_812989 : CollatzResearch.WordTrace tailWord_812989 prefixEnd_812989 92767583070716646777475 := by
  unfold tailWord_812989
  simp only [CollatzResearch.WordTrace]
  refine ⟨29652144851687175312098021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19768096567791450208065347 29652144851687175312098021)
  ·
    refine ⟨5559777159691345371018379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29652144851687175312098021 5559777159691345371018379)
    ·
      refine ⟨8339665739537018056527569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5559777159691345371018379 8339665739537018056527569)
      ·
        refine ⟨6254749304652763542395677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8339665739537018056527569 6254749304652763542395677)
        ·
          refine ⟨2345530989244786328398379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6254749304652763542395677 2345530989244786328398379)
          ·
            refine ⟨3518296483867179492597569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2345530989244786328398379 3518296483867179492597569)
            ·
              refine ⟨2638722362900384619448177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3518296483867179492597569 2638722362900384619448177)
              ·
                refine ⟨1979041772175288464586133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2638722362900384619448177 1979041772175288464586133)
                ·
                  refine ⟨92767583070716646777475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1979041772175288464586133 92767583070716646777475)
                  ·
                    rfl

theorem cell22_812989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_812989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_812989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_812989 prefixEnd_812989 := by exact prefixLift 812989
  have htrace : WordTrace (prefixWord ++ tailWord_812989) baseStart_812989 baseEnd_812989 := by
    simpa [prefixWord, tailWord_812989, baseEnd_812989] using wordTrace_append hprefix tailTrace_812989
  have hstable : (prefixWord ++ tailWord_812989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_812989).length < 2 ^ (prefixWord ++ tailWord_812989).sum := by decide
  have hdescent : baseEnd_812989 < baseStart_812989 := by decide
  rcases family_descends (prefixWord ++ tailWord_812989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813023 : List Nat := [1, 1, 2, 3, 4, 2, 3, 2, 4]
def baseStart_813023 : Nat := 118140960795 + 813023 * 2 ^ 59
def prefixEnd_813023 : Nat := 4983230072969 + 3 ^ 40 * 813023 * 2
def baseEnd_813023 : Nat := 92771462702328394994107

theorem tailTrace_813023 : CollatzResearch.WordTrace tailWord_813023 prefixEnd_813023 92771462702328394994107 := by
  unfold tailWord_813023
  simp only [CollatzResearch.WordTrace]
  refine ⟨29653384933563999118835723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19768923289042666079223815 29653384933563999118835723)
  ·
    refine ⟨44480077400345998678253585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29653384933563999118835723 44480077400345998678253585)
    ·
      refine ⟨33360058050259499008690189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44480077400345998678253585 33360058050259499008690189)
      ·
        refine ⟨12510021768847312128258821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33360058050259499008690189 12510021768847312128258821)
        ·
          refine ⟨2345629081658871024048529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12510021768847312128258821 2345629081658871024048529)
          ·
            refine ⟨1759221811244153268036397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2345629081658871024048529 1759221811244153268036397)
            ·
              refine ⟨659708179216557475513649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1759221811244153268036397 659708179216557475513649)
              ·
                refine ⟨494781134412418106635237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 659708179216557475513649 494781134412418106635237)
                ·
                  refine ⟨92771462702328394994107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 494781134412418106635237 92771462702328394994107)
                  ·
                    rfl

theorem cell22_813023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2, 4].length) (baseStart_813023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813023 prefixEnd_813023 := by exact prefixLift 813023
  have htrace : WordTrace (prefixWord ++ tailWord_813023) baseStart_813023 baseEnd_813023 := by
    simpa [prefixWord, tailWord_813023, baseEnd_813023] using wordTrace_append hprefix tailTrace_813023
  have hstable : (prefixWord ++ tailWord_813023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813023).length < 2 ^ (prefixWord ++ tailWord_813023).sum := by decide
  have hdescent : baseEnd_813023 < baseStart_813023 := by decide
  rcases family_descends (prefixWord ++ tailWord_813023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813034 : List Nat := [3, 1, 3, 1, 2, 1, 4, 7]
def baseStart_813034 : Nat := 118140960795 + 813034 * 2 ^ 59
def prefixEnd_813034 : Nat := 4983230072969 + 3 ^ 40 * 813034 * 2
def baseEnd_813034 : Nat := 30924239292420535884143

theorem tailTrace_813034 : CollatzResearch.WordTrace tailWord_813034 prefixEnd_813034 30924239292420535884143 := by
  unfold tailWord_813034
  simp only [CollatzResearch.WordTrace]
  refine ⟨7413446534131036999371539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19769190757682765331657437 7413446534131036999371539)
  ·
    refine ⟨11120169801196555499057309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7413446534131036999371539 11120169801196555499057309)
    ·
      refine ⟨4170063675448708312146491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11120169801196555499057309 4170063675448708312146491)
      ·
        refine ⟨6255095513173062468219737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4170063675448708312146491 6255095513173062468219737)
        ·
          refine ⟨4691321634879796851164803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6255095513173062468219737 4691321634879796851164803)
          ·
            refine ⟨7036982452319695276747205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4691321634879796851164803 7036982452319695276747205)
            ·
              refine ⟨1319434209809942864390101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7036982452319695276747205 1319434209809942864390101)
              ·
                refine ⟨30924239292420535884143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1319434209809942864390101 30924239292420535884143)
                ·
                  rfl

theorem cell22_813034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 7].length) (baseStart_813034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813034 prefixEnd_813034 := by exact prefixLift 813034
  have htrace : WordTrace (prefixWord ++ tailWord_813034) baseStart_813034 baseEnd_813034 := by
    simpa [prefixWord, tailWord_813034, baseEnd_813034] using wordTrace_append hprefix tailTrace_813034
  have hstable : (prefixWord ++ tailWord_813034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813034).length < 2 ^ (prefixWord ++ tailWord_813034).sum := by decide
  have hdescent : baseEnd_813034 < baseStart_813034 := by decide
  rcases family_descends (prefixWord ++ tailWord_813034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813038 : List Nat := [4, 1, 2, 1, 3, 2, 1, 3, 2, 3]
def baseStart_813038 : Nat := 118140960795 + 813038 * 2 ^ 59
def prefixEnd_813038 : Nat := 4983230072969 + 3 ^ 40 * 813038 * 2
def baseEnd_813038 : Nat := 278319522913530145857275

theorem tailTrace_813038 : CollatzResearch.WordTrace tailWord_813038 prefixEnd_813038 278319522913530145857275 := by
  unfold tailWord_813038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3706741503563707085078971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19769288019006437787087845 3706741503563707085078971)
  ·
    refine ⟨5560112255345560627618457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3706741503563707085078971 5560112255345560627618457)
    ·
      refine ⟨4170084191509170470713843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5560112255345560627618457 4170084191509170470713843)
      ·
        refine ⟨6255126287263755706070765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4170084191509170470713843 6255126287263755706070765)
        ·
          refine ⟨2345672357723908389776537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6255126287263755706070765 2345672357723908389776537)
          ·
            refine ⟨1759254268292931292332403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2345672357723908389776537 1759254268292931292332403)
            ·
              refine ⟨2638881402439396938498605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1759254268292931292332403 2638881402439396938498605)
              ·
                refine ⟨989580525914773851936977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2638881402439396938498605 989580525914773851936977)
                ·
                  refine ⟨742185394436080388952733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 989580525914773851936977 742185394436080388952733)
                  ·
                    refine ⟨278319522913530145857275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 742185394436080388952733 278319522913530145857275)
                    ·
                      rfl

theorem cell22_813038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_813038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813038 prefixEnd_813038 := by exact prefixLift 813038
  have htrace : WordTrace (prefixWord ++ tailWord_813038) baseStart_813038 baseEnd_813038 := by
    simpa [prefixWord, tailWord_813038, baseEnd_813038] using wordTrace_append hprefix tailTrace_813038
  have hstable : (prefixWord ++ tailWord_813038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813038).length < 2 ^ (prefixWord ++ tailWord_813038).sum := by decide
  have hdescent : baseEnd_813038 < baseStart_813038 := by decide
  rcases family_descends (prefixWord ++ tailWord_813038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813141 : List Nat := [1, 3, 2, 2, 1, 4, 2, 1, 6]
def baseStart_813141 : Nat := 118140960795 + 813141 * 2 ^ 59
def prefixEnd_813141 : Nat := 4983230072969 + 3 ^ 40 * 813141 * 2
def baseEnd_813141 : Nat := 92784927306157403510653

theorem tailTrace_813141 : CollatzResearch.WordTrace tailWord_813141 prefixEnd_813141 92784927306157403510653 := by
  unfold tailWord_813141
  simp only [CollatzResearch.WordTrace]
  refine ⟨29657688747136505271631277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19771792498091003514420851 29657688747136505271631277)
  ·
    refine ⟨11121633280176189476861729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29657688747136505271631277 11121633280176189476861729)
    ·
      refine ⟨8341224960132142107646297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11121633280176189476861729 8341224960132142107646297)
      ·
        refine ⟨6255918720099106580734723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8341224960132142107646297 6255918720099106580734723)
        ·
          refine ⟨9383878080148659871102085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6255918720099106580734723 9383878080148659871102085)
          ·
            refine ⟨1759477140027873725831641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9383878080148659871102085 1759477140027873725831641)
            ·
              refine ⟨1319607855020905294373731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1759477140027873725831641 1319607855020905294373731)
              ·
                refine ⟨1979411782531357941560597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1319607855020905294373731 1979411782531357941560597)
                ·
                  refine ⟨92784927306157403510653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1979411782531357941560597 92784927306157403510653)
                  ·
                    rfl

theorem cell22_813141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 6].length) (baseStart_813141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813141 prefixEnd_813141 := by exact prefixLift 813141
  have htrace : WordTrace (prefixWord ++ tailWord_813141) baseStart_813141 baseEnd_813141 := by
    simpa [prefixWord, tailWord_813141, baseEnd_813141] using wordTrace_append hprefix tailTrace_813141
  have hstable : (prefixWord ++ tailWord_813141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813141).length < 2 ^ (prefixWord ++ tailWord_813141).sum := by decide
  have hdescent : baseEnd_813141 < baseStart_813141 := by decide
  rcases family_descends (prefixWord ++ tailWord_813141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813156 : List Nat := [2, 3, 1, 1, 2, 1, 5, 1, 1, 5]
def baseStart_813156 : Nat := 118140960795 + 813156 * 2 ^ 59
def prefixEnd_813156 : Nat := 4983230072969 + 3 ^ 40 * 813156 * 2
def baseEnd_813156 : Nat := 278359916725017171406913

theorem tailTrace_813156 : CollatzResearch.WordTrace tailWord_813156 prefixEnd_813156 278359916725017171406913 := by
  unfold tailWord_813156
  simp only [CollatzResearch.WordTrace]
  refine ⟨14829117921041081416713661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19772157228054775222284881 14829117921041081416713661)
  ·
    refine ⟨5560919220390405531267623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14829117921041081416713661 5560919220390405531267623)
    ·
      refine ⟨8341378830585608296901435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5560919220390405531267623 8341378830585608296901435)
      ·
        refine ⟨12512068245878412445352153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8341378830585608296901435 12512068245878412445352153)
        ·
          refine ⟨9384051184408809334014115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12512068245878412445352153 9384051184408809334014115)
          ·
            refine ⟨14076076776613214001021173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9384051184408809334014115 14076076776613214001021173)
            ·
              refine ⟨1319632197807488812595735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14076076776613214001021173 1319632197807488812595735)
              ·
                refine ⟨1979448296711233218893603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1319632197807488812595735 1979448296711233218893603)
                ·
                  refine ⟨2969172445066849828340405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1979448296711233218893603 2969172445066849828340405)
                  ·
                    refine ⟨278359916725017171406913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2969172445066849828340405 278359916725017171406913)
                    ·
                      rfl

theorem cell22_813156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_813156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813156 prefixEnd_813156 := by exact prefixLift 813156
  have htrace : WordTrace (prefixWord ++ tailWord_813156) baseStart_813156 baseEnd_813156 := by
    simpa [prefixWord, tailWord_813156, baseEnd_813156] using wordTrace_append hprefix tailTrace_813156
  have hstable : (prefixWord ++ tailWord_813156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813156).length < 2 ^ (prefixWord ++ tailWord_813156).sum := by decide
  have hdescent : baseEnd_813156 < baseStart_813156 := by decide
  rcases family_descends (prefixWord ++ tailWord_813156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813169 : List Nat := [1, 2, 2, 2, 1, 1, 5, 8]
def baseStart_813169 : Nat := 118140960795 + 813169 * 2 ^ 59
def prefixEnd_813169 : Nat := 4983230072969 + 3 ^ 40 * 813169 * 2
def baseEnd_813169 : Nat := 30929374098965496759097

theorem tailTrace_813169 : CollatzResearch.WordTrace tailWord_813169 prefixEnd_813169 30929374098965496759097 := by
  unfold tailWord_813169
  simp only [CollatzResearch.WordTrace]
  refine ⟨29658709991035066053650561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19772473327356710702433707 29658709991035066053650561)
  ·
    refine ⟨22244032493276299540237921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29658709991035066053650561 22244032493276299540237921)
    ·
      refine ⟨16683024369957224655178441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22244032493276299540237921 16683024369957224655178441)
      ·
        refine ⟨12512268277467918491383831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16683024369957224655178441 12512268277467918491383831)
        ·
          refine ⟨18768402416201877737075747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12512268277467918491383831 18768402416201877737075747)
          ·
            refine ⟨28152603624302816605613621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18768402416201877737075747 28152603624302816605613621)
            ·
              refine ⟨2639306589778389056776277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28152603624302816605613621 2639306589778389056776277)
              ·
                refine ⟨30929374098965496759097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2639306589778389056776277 30929374098965496759097)
                ·
                  rfl

theorem cell22_813169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 8].length) (baseStart_813169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813169 prefixEnd_813169 := by exact prefixLift 813169
  have htrace : WordTrace (prefixWord ++ tailWord_813169) baseStart_813169 baseEnd_813169 := by
    simpa [prefixWord, tailWord_813169, baseEnd_813169] using wordTrace_append hprefix tailTrace_813169
  have hstable : (prefixWord ++ tailWord_813169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813169).length < 2 ^ (prefixWord ++ tailWord_813169).sum := by decide
  have hdescent : baseEnd_813169 < baseStart_813169 := by decide
  rcases family_descends (prefixWord ++ tailWord_813169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813207 : List Nat := [1, 1, 3, 3, 4, 2, 2, 1, 2, 3]
def baseStart_813207 : Nat := 118140960795 + 813207 * 2 ^ 59
def prefixEnd_813207 : Nat := 4983230072969 + 3 ^ 40 * 813207 * 2
def baseEnd_813207 : Nat := 278377375067270038381757

theorem tailTrace_813207 : CollatzResearch.WordTrace tailWord_813207 prefixEnd_813207 278377375067270038381757 := by
  unfold tailWord_813207
  simp only [CollatzResearch.WordTrace]
  refine ⟨29660095964897398543533875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19773397309931599029022583 29660095964897398543533875)
  ·
    refine ⟨44490143947346097815300813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29660095964897398543533875 44490143947346097815300813)
    ·
      refine ⟨16683803980254786680737805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44490143947346097815300813 16683803980254786680737805)
      ·
        refine ⟨6256426492595545005276677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16683803980254786680737805 6256426492595545005276677)
        ·
          refine ⟨1173079967361664688489377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6256426492595545005276677 1173079967361664688489377)
          ·
            refine ⟨879809975521248516367033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1173079967361664688489377 879809975521248516367033)
            ·
              refine ⟨659857481640936387275275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 879809975521248516367033 659857481640936387275275)
              ·
                refine ⟨989786222461404580912913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 659857481640936387275275 989786222461404580912913)
                ·
                  refine ⟨742339666846053435684685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 989786222461404580912913 742339666846053435684685)
                  ·
                    refine ⟨278377375067270038381757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 742339666846053435684685 278377375067270038381757)
                    ·
                      rfl

theorem cell22_813207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 2, 3].length) (baseStart_813207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813207 prefixEnd_813207 := by exact prefixLift 813207
  have htrace : WordTrace (prefixWord ++ tailWord_813207) baseStart_813207 baseEnd_813207 := by
    simpa [prefixWord, tailWord_813207, baseEnd_813207] using wordTrace_append hprefix tailTrace_813207
  have hstable : (prefixWord ++ tailWord_813207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813207).length < 2 ^ (prefixWord ++ tailWord_813207).sum := by decide
  have hdescent : baseEnd_813207 < baseStart_813207 := by decide
  rcases family_descends (prefixWord ++ tailWord_813207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813248 : List Nat := [2, 1, 1, 2, 5, 2, 2, 2, 5]
def baseStart_813248 : Nat := 118140960795 + 813248 * 2 ^ 59
def prefixEnd_813248 : Nat := 4983230072969 + 3 ^ 40 * 813248 * 2
def baseEnd_813248 : Nat := 92797136735053199368877

theorem tailTrace_813248 : CollatzResearch.WordTrace tailWord_813248 prefixEnd_813248 92797136735053199368877 := by
  unfold tailWord_813248
  simp only [CollatzResearch.WordTrace]
  refine ⟨14830795678874431272888199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19774394238499241697184265 14830795678874431272888199)
  ·
    refine ⟨22246193518311646909332299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14830795678874431272888199 22246193518311646909332299)
    ·
      refine ⟨33369290277467470363998449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22246193518311646909332299 33369290277467470363998449)
      ·
        refine ⟨25026967708100602772998837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33369290277467470363998449 25026967708100602772998837)
        ·
          refine ⟨2346278222634431509968641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25026967708100602772998837 2346278222634431509968641)
          ·
            refine ⟨1759708666975823632476481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2346278222634431509968641 1759708666975823632476481)
            ·
              refine ⟨1319781500231867724357361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1759708666975823632476481 1319781500231867724357361)
              ·
                refine ⟨989836125173900793268021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1319781500231867724357361 989836125173900793268021)
                ·
                  refine ⟨92797136735053199368877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 989836125173900793268021 92797136735053199368877)
                  ·
                    rfl

theorem cell22_813248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 5].length) (baseStart_813248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813248 prefixEnd_813248 := by exact prefixLift 813248
  have htrace : WordTrace (prefixWord ++ tailWord_813248) baseStart_813248 baseEnd_813248 := by
    simpa [prefixWord, tailWord_813248, baseEnd_813248] using wordTrace_append hprefix tailTrace_813248
  have hstable : (prefixWord ++ tailWord_813248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813248).length < 2 ^ (prefixWord ++ tailWord_813248).sum := by decide
  have hdescent : baseEnd_813248 < baseStart_813248 := by decide
  rcases family_descends (prefixWord ++ tailWord_813248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813250 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_813250 : Nat := 118140960795 + 813250 * 2 ^ 59
def prefixEnd_813250 : Nat := 4983230072969 + 3 ^ 40 * 813250 * 2
def baseEnd_813250 : Nat := 278392094846032259556625

theorem tailTrace_813250 : CollatzResearch.WordTrace tailWord_813250 prefixEnd_813250 278392094846032259556625 := by
  unfold tailWord_813250
  simp only [CollatzResearch.WordTrace]
  refine ⟨7415416075935404221837301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19774442869161077924899469 7415416075935404221837301)
  ·
    refine ⟨695195257118944145797247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7415416075935404221837301 695195257118944145797247)
    ·
      refine ⟨1042792885678416218695871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 695195257118944145797247 1042792885678416218695871)
      ·
        refine ⟨1564189328517624328043807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1042792885678416218695871 1564189328517624328043807)
        ·
          refine ⟨2346283992776436492065711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1564189328517624328043807 2346283992776436492065711)
          ·
            refine ⟨3519425989164654738098567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2346283992776436492065711 3519425989164654738098567)
            ·
              refine ⟨5279138983746982107147851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3519425989164654738098567 5279138983746982107147851)
              ·
                refine ⟨7918708475620473160721777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5279138983746982107147851 7918708475620473160721777)
                ·
                  refine ⟨5939031356715354870541333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7918708475620473160721777 5939031356715354870541333)
                  ·
                    refine ⟨278392094846032259556625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5939031356715354870541333 278392094846032259556625)
                    ·
                      rfl

theorem cell22_813250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_813250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813250 prefixEnd_813250 := by exact prefixLift 813250
  have htrace : WordTrace (prefixWord ++ tailWord_813250) baseStart_813250 baseEnd_813250 := by
    simpa [prefixWord, tailWord_813250, baseEnd_813250] using wordTrace_append hprefix tailTrace_813250
  have hstable : (prefixWord ++ tailWord_813250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813250).length < 2 ^ (prefixWord ++ tailWord_813250).sum := by decide
  have hdescent : baseEnd_813250 < baseStart_813250 := by decide
  rcases family_descends (prefixWord ++ tailWord_813250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813252 : List Nat := [2, 3, 3, 1, 2, 2, 1, 4, 1, 3]
def baseStart_813252 : Nat := 118140960795 + 813252 * 2 ^ 59
def prefixEnd_813252 : Nat := 4983230072969 + 3 ^ 40 * 813252 * 2
def baseEnd_813252 : Nat := 278392779486904921006619

theorem tailTrace_813252 : CollatzResearch.WordTrace tailWord_813252 prefixEnd_813252 278392779486904921006619 := by
  unfold tailWord_813252
  simp only [CollatzResearch.WordTrace]
  refine ⟨14830868624867185614461005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19774491499822914152614673 14830868624867185614461005)
  ·
    refine ⟨5561575734325194605422877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14830868624867185614461005 5561575734325194605422877)
    ·
      refine ⟨2085590900371947977033579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5561575734325194605422877 2085590900371947977033579)
      ·
        refine ⟨3128386350557921965550369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2085590900371947977033579 3128386350557921965550369)
        ·
          refine ⟨2346289762918441474162777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3128386350557921965550369 2346289762918441474162777)
          ·
            refine ⟨1759717322188831105622083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2346289762918441474162777 1759717322188831105622083)
            ·
              refine ⟨2639575983283246658433125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1759717322188831105622083 2639575983283246658433125)
              ·
                refine ⟨494920496865608748456211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2639575983283246658433125 494920496865608748456211)
                ·
                  refine ⟨742380745298413122684317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 494920496865608748456211 742380745298413122684317)
                  ·
                    refine ⟨278392779486904921006619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 742380745298413122684317 278392779486904921006619)
                    ·
                      rfl

theorem cell22_813252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_813252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813252 prefixEnd_813252 := by exact prefixLift 813252
  have htrace : WordTrace (prefixWord ++ tailWord_813252) baseStart_813252 baseEnd_813252 := by
    simpa [prefixWord, tailWord_813252, baseEnd_813252] using wordTrace_append hprefix tailTrace_813252
  have hstable : (prefixWord ++ tailWord_813252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813252).length < 2 ^ (prefixWord ++ tailWord_813252).sum := by decide
  have hdescent : baseEnd_813252 < baseStart_813252 := by decide
  rcases family_descends (prefixWord ++ tailWord_813252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813291 : List Nat := [1, 1, 1, 1, 2, 5, 1, 4, 1, 5]
def baseStart_813291 : Nat := 118140960795 + 813291 * 2 ^ 59
def prefixEnd_813291 : Nat := 4983230072969 + 3 ^ 40 * 813291 * 2
def baseEnd_813291 : Nat := 278406129983921819281499

theorem tailTrace_813291 : CollatzResearch.WordTrace tailWord_813291 prefixEnd_813291 278406129983921819281499 := by
  unfold tailWord_813291
  simp only [CollatzResearch.WordTrace]
  refine ⟨29663159696593080889591727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19775439797728720593061151 29663159696593080889591727)
  ·
    refine ⟨44494739544889621334387591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29663159696593080889591727 44494739544889621334387591)
    ·
      refine ⟨66742109317334432001581387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44494739544889621334387591 66742109317334432001581387)
      ·
        refine ⟨100113163976001648002372081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66742109317334432001581387 100113163976001648002372081)
        ·
          refine ⟨75084872982001236001779061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100113163976001648002372081 75084872982001236001779061)
          ·
            refine ⟨7039206842062615875166787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75084872982001236001779061 7039206842062615875166787)
            ·
              refine ⟨10558810263093923812750181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7039206842062615875166787 10558810263093923812750181)
              ·
                refine ⟨1979776924330110714890659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10558810263093923812750181 1979776924330110714890659)
                ·
                  refine ⟨2969665386495166072335989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1979776924330110714890659 2969665386495166072335989)
                  ·
                    refine ⟨278406129983921819281499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2969665386495166072335989 278406129983921819281499)
                    ·
                      rfl

theorem cell22_813291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 5].length) (baseStart_813291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813291 prefixEnd_813291 := by exact prefixLift 813291
  have htrace : WordTrace (prefixWord ++ tailWord_813291) baseStart_813291 baseEnd_813291 := by
    simpa [prefixWord, tailWord_813291, baseEnd_813291] using wordTrace_append hprefix tailTrace_813291
  have hstable : (prefixWord ++ tailWord_813291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813291).length < 2 ^ (prefixWord ++ tailWord_813291).sum := by decide
  have hdescent : baseEnd_813291 < baseStart_813291 := by decide
  rcases family_descends (prefixWord ++ tailWord_813291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813295 : List Nat := [1, 1, 2, 1, 6, 1, 4, 1, 1, 4]
def baseStart_813295 : Nat := 118140960795 + 813295 * 2 ^ 59
def prefixEnd_813295 : Nat := 4983230072969 + 3 ^ 40 * 813295 * 2
def baseEnd_813295 : Nat := 278407499265667142181487

theorem tailTrace_813295 : CollatzResearch.WordTrace tailWord_813295 prefixEnd_813295 278407499265667142181487 := by
  unfold tailWord_813295
  simp only [CollatzResearch.WordTrace]
  refine ⟨29663305588578589572737339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19775537059052393048491559 29663305588578589572737339)
  ·
    refine ⟨44494958382867884359106009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29663305588578589572737339 44494958382867884359106009)
    ·
      refine ⟨33371218787150913269329507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44494958382867884359106009 33371218787150913269329507)
      ·
        refine ⟨50056828180726369903994261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33371218787150913269329507 50056828180726369903994261)
        ·
          refine ⟨2346413820971548589249731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50056828180726369903994261 2346413820971548589249731)
          ·
            refine ⟨3519620731457322883874597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2346413820971548589249731 3519620731457322883874597)
            ·
              refine ⟨659928887148248040726487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3519620731457322883874597 659928887148248040726487)
              ·
                refine ⟨989893330722372061089731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 659928887148248040726487 989893330722372061089731)
                ·
                  refine ⟨1484839996083558091634597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 989893330722372061089731 1484839996083558091634597)
                  ·
                    refine ⟨278407499265667142181487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1484839996083558091634597 278407499265667142181487)
                    ·
                      rfl

theorem cell22_813295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 1, 4].length) (baseStart_813295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813295 prefixEnd_813295 := by exact prefixLift 813295
  have htrace : WordTrace (prefixWord ++ tailWord_813295) baseStart_813295 baseEnd_813295 := by
    simpa [prefixWord, tailWord_813295, baseEnd_813295] using wordTrace_append hprefix tailTrace_813295
  have hstable : (prefixWord ++ tailWord_813295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813295).length < 2 ^ (prefixWord ++ tailWord_813295).sum := by decide
  have hdescent : baseEnd_813295 < baseStart_813295 := by decide
  rcases family_descends (prefixWord ++ tailWord_813295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813310 : List Nat := [4, 2, 2, 1, 1, 1, 1, 6, 4]
def baseStart_813310 : Nat := 118140960795 + 813310 * 2 ^ 59
def prefixEnd_813310 : Nat := 4983230072969 + 3 ^ 40 * 813310 * 2
def baseEnd_813310 : Nat := 92804211357404034352147

theorem tailTrace_813310 : CollatzResearch.WordTrace tailWord_813310 prefixEnd_813310 92804211357404034352147 := by
  unfold tailWord_813310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3707981585440530891816673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19775901789016164756355589 3707981585440530891816673)
  ·
    refine ⟨2780986189080398168862505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3707981585440530891816673 2780986189080398168862505)
    ·
      refine ⟨2085739641810298626646879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2780986189080398168862505 2085739641810298626646879)
      ·
        refine ⟨3128609462715447939970319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2085739641810298626646879 3128609462715447939970319)
        ·
          refine ⟨4692914194073171909955479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3128609462715447939970319 4692914194073171909955479)
          ·
            refine ⟨7039371291109757864933219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4692914194073171909955479 7039371291109757864933219)
            ·
              refine ⟨10559056936664636797399829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7039371291109757864933219 10559056936664636797399829)
              ·
                refine ⟨494955793906154849878117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10559056936664636797399829 494955793906154849878117)
                ·
                  refine ⟨92804211357404034352147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 494955793906154849878117 92804211357404034352147)
                  ·
                    rfl

theorem cell22_813310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_813310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813310 prefixEnd_813310 := by exact prefixLift 813310
  have htrace : WordTrace (prefixWord ++ tailWord_813310) baseStart_813310 baseEnd_813310 := by
    simpa [prefixWord, tailWord_813310, baseEnd_813310] using wordTrace_append hprefix tailTrace_813310
  have hstable : (prefixWord ++ tailWord_813310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813310).length < 2 ^ (prefixWord ++ tailWord_813310).sum := by decide
  have hdescent : baseEnd_813310 < baseStart_813310 := by decide
  rcases family_descends (prefixWord ++ tailWord_813310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813336 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 2, 7]
def baseStart_813336 : Nat := 118140960795 + 813336 * 2 ^ 59
def prefixEnd_813336 : Nat := 4983230072969 + 3 ^ 40 * 813336 * 2
def baseEnd_813336 : Nat := 278421534403556701906361

theorem tailTrace_813336 : CollatzResearch.WordTrace tailWord_813336 prefixEnd_813336 278421534403556701906361 := by
  unfold tailWord_813336
  simp only [CollatzResearch.WordTrace]
  refine ⟨14832400490715026787489931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19776533987620035716653241 14832400490715026787489931)
  ·
    refine ⟨22248600736072540181234897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14832400490715026787489931 22248600736072540181234897)
    ·
      refine ⟨16686450552054405135926173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22248600736072540181234897 16686450552054405135926173)
      ·
        refine ⟨6257418957020401925972315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16686450552054405135926173 6257418957020401925972315)
        ·
          refine ⟨9386128435530602888958473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6257418957020401925972315 9386128435530602888958473)
          ·
            refine ⟨7039596326647952166718855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9386128435530602888958473 7039596326647952166718855)
            ·
              refine ⟨10559394489971928250078283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7039596326647952166718855 10559394489971928250078283)
              ·
                refine ⟨15839091734957892375117425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10559394489971928250078283 15839091734957892375117425)
                ·
                  refine ⟨11879318801218419281338069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15839091734957892375117425 11879318801218419281338069)
                  ·
                    refine ⟨278421534403556701906361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11879318801218419281338069 278421534403556701906361)
                    ·
                      rfl

theorem cell22_813336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_813336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813336 prefixEnd_813336 := by exact prefixLift 813336
  have htrace : WordTrace (prefixWord ++ tailWord_813336) baseStart_813336 baseEnd_813336 := by
    simpa [prefixWord, tailWord_813336, baseEnd_813336] using wordTrace_append hprefix tailTrace_813336
  have hstable : (prefixWord ++ tailWord_813336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813336).length < 2 ^ (prefixWord ++ tailWord_813336).sum := by decide
  have hdescent : baseEnd_813336 < baseStart_813336 := by decide
  rcases family_descends (prefixWord ++ tailWord_813336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813338 : List Nat := [3, 1, 1, 3, 4, 1, 1, 8]
def baseStart_813338 : Nat := 118140960795 + 813338 * 2 ^ 59
def prefixEnd_813338 : Nat := 4983230072969 + 3 ^ 40 * 813338 * 2
def baseEnd_813338 : Nat := 30935802116047707039595

theorem tailTrace_813338 : CollatzResearch.WordTrace tailWord_813338 prefixEnd_813338 30935802116047707039595 := by
  unfold tailWord_813338
  simp only [CollatzResearch.WordTrace]
  refine ⟨7416218481855701979138167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19776582618281871944368445 7416218481855701979138167)
  ·
    refine ⟨11124327722783552968707251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7416218481855701979138167 11124327722783552968707251)
    ·
      refine ⟨16686491584175329453060877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11124327722783552968707251 16686491584175329453060877)
      ·
        refine ⟨6257434344065748544897829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16686491584175329453060877 6257434344065748544897829)
        ·
          refine ⟨1173268939512327852168343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6257434344065748544897829 1173268939512327852168343)
          ·
            refine ⟨1759903409268491778252515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173268939512327852168343 1759903409268491778252515)
            ·
              refine ⟨2639855113902737667378773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1759903409268491778252515 2639855113902737667378773)
              ·
                refine ⟨30935802116047707039595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2639855113902737667378773 30935802116047707039595)
                ·
                  rfl

theorem cell22_813338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 8].length) (baseStart_813338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813338 prefixEnd_813338 := by exact prefixLift 813338
  have htrace : WordTrace (prefixWord ++ tailWord_813338) baseStart_813338 baseEnd_813338 := by
    simpa [prefixWord, tailWord_813338, baseEnd_813338] using wordTrace_append hprefix tailTrace_813338
  have hstable : (prefixWord ++ tailWord_813338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813338).length < 2 ^ (prefixWord ++ tailWord_813338).sum := by decide
  have hdescent : baseEnd_813338 < baseStart_813338 := by decide
  rcases family_descends (prefixWord ++ tailWord_813338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813342 : List Nat := [4, 3, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_813342 : Nat := 118140960795 + 813342 * 2 ^ 59
def prefixEnd_813342 : Nat := 4983230072969 + 3 ^ 40 * 813342 * 2
def baseEnd_813342 : Nat := 278423588326174686256343

theorem tailTrace_813342 : CollatzResearch.WordTrace tailWord_813342 prefixEnd_813342 278423588326174686256343 := by
  unfold tailWord_813342
  simp only [CollatzResearch.WordTrace]
  refine ⟨3708127477426039574962285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19776679879605544399798853 3708127477426039574962285)
  ·
    refine ⟨1390547804034764840610857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3708127477426039574962285 1390547804034764840610857)
    ·
      refine ⟨1042910853026073630458143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1390547804034764840610857 1042910853026073630458143)
      ·
        refine ⟨1564366279539110445687215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1042910853026073630458143 1564366279539110445687215)
        ·
          refine ⟨2346549419308665668530823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1564366279539110445687215 2346549419308665668530823)
          ·
            refine ⟨3519824128962998502796235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2346549419308665668530823 3519824128962998502796235)
            ·
              refine ⟨5279736193444497754194353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3519824128962998502796235 5279736193444497754194353)
              ·
                refine ⟨3959802145083373315645765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5279736193444497754194353 3959802145083373315645765)
                ·
                  refine ⟨742462902203132496683581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3959802145083373315645765 742462902203132496683581)
                  ·
                    refine ⟨278423588326174686256343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 742462902203132496683581 278423588326174686256343)
                    ·
                      rfl

theorem cell22_813342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_813342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813342 prefixEnd_813342 := by exact prefixLift 813342
  have htrace : WordTrace (prefixWord ++ tailWord_813342) baseStart_813342 baseEnd_813342 := by
    simpa [prefixWord, tailWord_813342, baseEnd_813342] using wordTrace_append hprefix tailTrace_813342
  have hstable : (prefixWord ++ tailWord_813342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813342).length < 2 ^ (prefixWord ++ tailWord_813342).sum := by decide
  have hdescent : baseEnd_813342 < baseStart_813342 := by decide
  rcases family_descends (prefixWord ++ tailWord_813342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813357 : List Nat := [1, 5, 3, 1, 2, 1, 1, 2, 2, 4]
def baseStart_813357 : Nat := 118140960795 + 813357 * 2 ^ 59
def prefixEnd_813357 : Nat := 4983230072969 + 3 ^ 40 * 813357 * 2
def baseEnd_813357 : Nat := 278428723132719647131297

theorem tailTrace_813357 : CollatzResearch.WordTrace tailWord_813357 prefixEnd_813357 278428723132719647131297 := by
  unfold tailWord_813357
  simp only [CollatzResearch.WordTrace]
  refine ⟨29665566914353974161494325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19777044609569316107662883 29665566914353974161494325)
  ·
    refine ⟨2781146898220685077640093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29665566914353974161494325 2781146898220685077640093)
    ·
      refine ⟨1042930086832756904115035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2781146898220685077640093 1042930086832756904115035)
      ·
        refine ⟨1564395130249135356172553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1042930086832756904115035 1564395130249135356172553)
        ·
          refine ⟨1173296347686851517129415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1564395130249135356172553 1173296347686851517129415)
          ·
            refine ⟨1759944521530277275694123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173296347686851517129415 1759944521530277275694123)
            ·
              refine ⟨2639916782295415913541185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1759944521530277275694123 2639916782295415913541185)
              ·
                refine ⟨1979937586721561935155889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2639916782295415913541185 1979937586721561935155889)
                ·
                  refine ⟨1484953190041171451366917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1979937586721561935155889 1484953190041171451366917)
                  ·
                    refine ⟨278428723132719647131297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1484953190041171451366917 278428723132719647131297)
                    ·
                      rfl

theorem cell22_813357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_813357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813357 prefixEnd_813357 := by exact prefixLift 813357
  have htrace : WordTrace (prefixWord ++ tailWord_813357) baseStart_813357 baseEnd_813357 := by
    simpa [prefixWord, tailWord_813357, baseEnd_813357] using wordTrace_append hprefix tailTrace_813357
  have hstable : (prefixWord ++ tailWord_813357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813357).length < 2 ^ (prefixWord ++ tailWord_813357).sum := by decide
  have hdescent : baseEnd_813357 < baseStart_813357 := by decide
  rcases family_descends (prefixWord ++ tailWord_813357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813370 : List Nat := [3, 1, 1, 1, 4, 2, 3, 1, 3, 3]
def baseStart_813370 : Nat := 118140960795 + 813370 * 2 ^ 59
def prefixEnd_813370 : Nat := 4983230072969 + 3 ^ 40 * 813370 * 2
def baseEnd_813370 : Nat := 278433173298391946556257

theorem tailTrace_813370 : CollatzResearch.WordTrace tailWord_813370 prefixEnd_813370 278433173298391946556257 := by
  unfold tailWord_813370
  simp only [CollatzResearch.WordTrace]
  refine ⟨7416510265826719345429391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19777360708871251587811709 7416510265826719345429391)
  ·
    refine ⟨11124765398740079018144087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7416510265826719345429391 11124765398740079018144087)
    ·
      refine ⟨16687148098110118527216131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11124765398740079018144087 16687148098110118527216131)
      ·
        refine ⟨25030722147165177790824197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16687148098110118527216131 25030722147165177790824197)
        ·
          refine ⟨4693260402593470835779537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25030722147165177790824197 4693260402593470835779537)
          ·
            refine ⟨3519945301945103126834653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4693260402593470835779537 3519945301945103126834653)
            ·
              refine ⟨1319979488229413672562995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3519945301945103126834653 1319979488229413672562995)
              ·
                refine ⟨1979969232344120508844493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1319979488229413672562995 1979969232344120508844493)
                ·
                  refine ⟨742488462129045190816685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1979969232344120508844493 742488462129045190816685)
                  ·
                    refine ⟨278433173298391946556257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 742488462129045190816685 278433173298391946556257)
                    ·
                      rfl

theorem cell22_813370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 3, 3].length) (baseStart_813370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813370 prefixEnd_813370 := by exact prefixLift 813370
  have htrace : WordTrace (prefixWord ++ tailWord_813370) baseStart_813370 baseEnd_813370 := by
    simpa [prefixWord, tailWord_813370, baseEnd_813370] using wordTrace_append hprefix tailTrace_813370
  have hstable : (prefixWord ++ tailWord_813370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813370).length < 2 ^ (prefixWord ++ tailWord_813370).sum := by decide
  have hdescent : baseEnd_813370 < baseStart_813370 := by decide
  rcases family_descends (prefixWord ++ tailWord_813370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813383 : List Nat := [1, 1, 4, 1, 2, 2, 3, 3, 5]
def baseStart_813383 : Nat := 118140960795 + 813383 * 2 ^ 59
def prefixEnd_813383 : Nat := 4983230072969 + 3 ^ 40 * 813383 * 2
def baseEnd_813383 : Nat := 92812541154688081993739

theorem tailTrace_813383 : CollatzResearch.WordTrace tailWord_813383 prefixEnd_813383 92812541154688081993739 := by
  unfold tailWord_813383
  simp only [CollatzResearch.WordTrace]
  refine ⟨29666515212259780601940803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19777676808173187067960535 29666515212259780601940803)
  ·
    refine ⟨44499772818389670902911205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29666515212259780601940803 44499772818389670902911205)
    ·
      refine ⟨8343707403448063294295851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44499772818389670902911205 8343707403448063294295851)
      ·
        refine ⟨12515561105172094941443777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8343707403448063294295851 12515561105172094941443777)
        ·
          refine ⟨9386670828879071206082833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12515561105172094941443777 9386670828879071206082833)
          ·
            refine ⟨7040003121659303404562125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9386670828879071206082833 7040003121659303404562125)
            ·
              refine ⟨2640001170622238776710797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7040003121659303404562125 2640001170622238776710797)
              ·
                refine ⟨990000438983339541266549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2640001170622238776710797 990000438983339541266549)
                ·
                  refine ⟨92812541154688081993739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 990000438983339541266549 92812541154688081993739)
                  ·
                    rfl

theorem cell22_813383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 5].length) (baseStart_813383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813383 prefixEnd_813383 := by exact prefixLift 813383
  have htrace : WordTrace (prefixWord ++ tailWord_813383) baseStart_813383 baseEnd_813383 := by
    simpa [prefixWord, tailWord_813383, baseEnd_813383] using wordTrace_append hprefix tailTrace_813383
  have hstable : (prefixWord ++ tailWord_813383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813383).length < 2 ^ (prefixWord ++ tailWord_813383).sum := by decide
  have hdescent : baseEnd_813383 < baseStart_813383 := by decide
  rcases family_descends (prefixWord ++ tailWord_813383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813464 : List Nat := [2, 1, 2, 5, 1, 3, 2, 1, 1, 4]
def baseStart_813464 : Nat := 118140960795 + 813464 * 2 ^ 59
def prefixEnd_813464 : Nat := 4983230072969 + 3 ^ 40 * 813464 * 2
def baseEnd_813464 : Nat := 278465351419407034705969

theorem tailTrace_813464 : CollatzResearch.WordTrace tailWord_813464 prefixEnd_813464 278465351419407034705969 := by
  unfold tailWord_813464
  simp only [CollatzResearch.WordTrace]
  refine ⟨14834734762483165717819723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19779646349977554290426297 14834734762483165717819723)
  ·
    refine ⟨22252102143724748576729585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14834734762483165717819723 22252102143724748576729585)
    ·
      refine ⟨16689076607793561432547189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22252102143724748576729585 16689076607793561432547189)
      ·
        refine ⟨1564600931980646384301299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16689076607793561432547189 1564600931980646384301299)
        ·
          refine ⟨2346901397970969576451949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1564600931980646384301299 2346901397970969576451949)
          ·
            refine ⟨880088024239113591169481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2346901397970969576451949 880088024239113591169481)
            ·
              refine ⟨660066018179335193377111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 880088024239113591169481 660066018179335193377111)
              ·
                refine ⟨990099027269002790065667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 660066018179335193377111 990099027269002790065667)
                ·
                  refine ⟨1485148540903504185098501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 990099027269002790065667 1485148540903504185098501)
                  ·
                    refine ⟨278465351419407034705969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1485148540903504185098501 278465351419407034705969)
                    ·
                      rfl

theorem cell22_813464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 1, 4].length) (baseStart_813464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813464 prefixEnd_813464 := by exact prefixLift 813464
  have htrace : WordTrace (prefixWord ++ tailWord_813464) baseStart_813464 baseEnd_813464 := by
    simpa [prefixWord, tailWord_813464, baseEnd_813464] using wordTrace_append hprefix tailTrace_813464
  have hstable : (prefixWord ++ tailWord_813464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813464).length < 2 ^ (prefixWord ++ tailWord_813464).sum := by decide
  have hdescent : baseEnd_813464 < baseStart_813464 := by decide
  rcases family_descends (prefixWord ++ tailWord_813464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813539 : List Nat := [1, 1, 1, 6, 3, 2, 1, 1, 3, 3]
def baseStart_813539 : Nat := 118140960795 + 813539 * 2 ^ 59
def prefixEnd_813539 : Nat := 4983230072969 + 3 ^ 40 * 813539 * 2
def baseEnd_813539 : Nat := 278491025452131839080739

theorem tailTrace_813539 : CollatzResearch.WordTrace tailWord_813539 prefixEnd_813539 278491025452131839080739 := by
  unfold tailWord_813539
  simp only [CollatzResearch.WordTrace]
  refine ⟨29672204999694619244619671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19781469999796412829746447 29672204999694619244619671)
  ·
    refine ⟨44508307499541928866929507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29672204999694619244619671 44508307499541928866929507)
    ·
      refine ⟨66762461249312893300394261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44508307499541928866929507 66762461249312893300394261)
      ·
        refine ⟨3129490371061541873455981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 66762461249312893300394261 3129490371061541873455981)
        ·
          refine ⟨1173558889148078202545993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3129490371061541873455981 1173558889148078202545993)
          ·
            refine ⟨880169166861058651909495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1173558889148078202545993 880169166861058651909495)
            ·
              refine ⟨1320253750291587977864243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 880169166861058651909495 1320253750291587977864243)
              ·
                refine ⟨1980380625437381966796365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1320253750291587977864243 1980380625437381966796365)
                ·
                  refine ⟨742642734539018237548637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1980380625437381966796365 742642734539018237548637)
                  ·
                    refine ⟨278491025452131839080739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 742642734539018237548637 278491025452131839080739)
                    ·
                      rfl

theorem cell22_813539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3, 3].length) (baseStart_813539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813539 prefixEnd_813539 := by exact prefixLift 813539
  have htrace : WordTrace (prefixWord ++ tailWord_813539) baseStart_813539 baseEnd_813539 := by
    simpa [prefixWord, tailWord_813539, baseEnd_813539] using wordTrace_append hprefix tailTrace_813539
  have hstable : (prefixWord ++ tailWord_813539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813539).length < 2 ^ (prefixWord ++ tailWord_813539).sum := by decide
  have hdescent : baseEnd_813539 < baseStart_813539 := by decide
  rcases family_descends (prefixWord ++ tailWord_813539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813565 : List Nat := [1, 4, 1, 1, 1, 3, 3, 1, 3, 4]
def baseStart_813565 : Nat := 118140960795 + 813565 * 2 ^ 59
def prefixEnd_813565 : Nat := 4983230072969 + 3 ^ 40 * 813565 * 2
def baseEnd_813565 : Nat := 278499925783476437930659

theorem tailTrace_813565 : CollatzResearch.WordTrace tailWord_813565 prefixEnd_813565 278499925783476437930659 := by
  unfold tailWord_813565
  simp only [CollatzResearch.WordTrace]
  refine ⟨29673153297600425685066149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19782102198400283790044099 29673153297600425685066149)
  ·
    refine ⟨5563716243300079815949903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29673153297600425685066149 5563716243300079815949903)
    ·
      refine ⟨8345574364950119723924855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5563716243300079815949903 8345574364950119723924855)
      ·
        refine ⟨12518361547425179585887283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8345574364950119723924855 12518361547425179585887283)
        ·
          refine ⟨18777542321137769378830925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12518361547425179585887283 18777542321137769378830925)
          ·
            refine ⟨7041578370426663517061597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18777542321137769378830925 7041578370426663517061597)
            ·
              refine ⟨2640591888909998818898099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7041578370426663517061597 2640591888909998818898099)
              ·
                refine ⟨3960887833364998228347149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2640591888909998818898099 3960887833364998228347149)
                ·
                  refine ⟨1485332937511874335630181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3960887833364998228347149 1485332937511874335630181)
                  ·
                    refine ⟨278499925783476437930659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1485332937511874335630181 278499925783476437930659)
                    ·
                      rfl

theorem cell22_813565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_813565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813565 prefixEnd_813565 := by exact prefixLift 813565
  have htrace : WordTrace (prefixWord ++ tailWord_813565) baseStart_813565 baseEnd_813565 := by
    simpa [prefixWord, tailWord_813565, baseEnd_813565] using wordTrace_append hprefix tailTrace_813565
  have hstable : (prefixWord ++ tailWord_813565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813565).length < 2 ^ (prefixWord ++ tailWord_813565).sum := by decide
  have hdescent : baseEnd_813565 < baseStart_813565 := by decide
  rcases family_descends (prefixWord ++ tailWord_813565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813747 : List Nat := [1, 1, 1, 2, 3, 5, 1, 2, 1, 5]
def baseStart_813747 : Nat := 118140960795 + 813747 * 2 ^ 59
def prefixEnd_813747 : Nat := 4983230072969 + 3 ^ 40 * 813747 * 2
def baseEnd_813747 : Nat := 278562228102888629880101

theorem tailTrace_813747 : CollatzResearch.WordTrace tailWord_813747 prefixEnd_813747 278562228102888629880101 := by
  unfold tailWord_813747
  simp only [CollatzResearch.WordTrace]
  refine ⟨29679791382941070768191495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19786527588627380512127663 29679791382941070768191495)
  ·
    refine ⟨44519687074411606152287243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29679791382941070768191495 44519687074411606152287243)
    ·
      refine ⟨66779530611617409228430865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44519687074411606152287243 66779530611617409228430865)
      ·
        refine ⟨50084647958713056921323149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66779530611617409228430865 50084647958713056921323149)
        ·
          refine ⟨18781742984517396345496181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50084647958713056921323149 18781742984517396345496181)
          ·
            refine ⟨1760788404798505907390267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18781742984517396345496181 1760788404798505907390267)
            ·
              refine ⟨2641182607197758861085401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1760788404798505907390267 2641182607197758861085401)
              ·
                refine ⟨1980886955398319145814051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2641182607197758861085401 1980886955398319145814051)
                ·
                  refine ⟨2971330433097478718721077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1980886955398319145814051 2971330433097478718721077)
                  ·
                    refine ⟨278562228102888629880101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2971330433097478718721077 278562228102888629880101)
                    ·
                      rfl

theorem cell22_813747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 5].length) (baseStart_813747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813747 prefixEnd_813747 := by exact prefixLift 813747
  have htrace : WordTrace (prefixWord ++ tailWord_813747) baseStart_813747 baseEnd_813747 := by
    simpa [prefixWord, tailWord_813747, baseEnd_813747] using wordTrace_append hprefix tailTrace_813747
  have hstable : (prefixWord ++ tailWord_813747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813747).length < 2 ^ (prefixWord ++ tailWord_813747).sum := by decide
  have hdescent : baseEnd_813747 < baseStart_813747 := by decide
  rcases family_descends (prefixWord ++ tailWord_813747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813751 : List Nat := [1, 1, 3, 1, 6, 1, 3, 1, 1, 4]
def baseStart_813751 : Nat := 118140960795 + 813751 * 2 ^ 59
def prefixEnd_813751 : Nat := 4983230072969 + 3 ^ 40 * 813751 * 2
def baseEnd_813751 : Nat := 278563597384633952780089

theorem tailTrace_813751 : CollatzResearch.WordTrace tailWord_813751 prefixEnd_813751 278563597384633952780089 := by
  unfold tailWord_813751
  simp only [CollatzResearch.WordTrace]
  refine ⟨29679937274926579451337107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19786624849951052967558071 29679937274926579451337107)
  ·
    refine ⟨44519905912389869177005661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29679937274926579451337107 44519905912389869177005661)
    ·
      refine ⟨16694964717146200941377123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44519905912389869177005661 16694964717146200941377123)
      ·
        refine ⟨25042447075719301412065685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16694964717146200941377123 25042447075719301412065685)
        ·
          refine ⟨1173864706674342253690579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25042447075719301412065685 1173864706674342253690579)
          ·
            refine ⟨1760797060011513380535869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173864706674342253690579 1760797060011513380535869)
            ·
              refine ⟨660298897504317517700951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1760797060011513380535869 660298897504317517700951)
              ·
                refine ⟨990448346256476276551427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 660298897504317517700951 990448346256476276551427)
                ·
                  refine ⟨1485672519384714414827141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 990448346256476276551427 1485672519384714414827141)
                  ·
                    refine ⟨278563597384633952780089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1485672519384714414827141 278563597384633952780089)
                    ·
                      rfl

theorem cell22_813751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 1, 4].length) (baseStart_813751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813751 prefixEnd_813751 := by exact prefixLift 813751
  have htrace : WordTrace (prefixWord ++ tailWord_813751) baseStart_813751 baseEnd_813751 := by
    simpa [prefixWord, tailWord_813751, baseEnd_813751] using wordTrace_append hprefix tailTrace_813751
  have hstable : (prefixWord ++ tailWord_813751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813751).length < 2 ^ (prefixWord ++ tailWord_813751).sum := by decide
  have hdescent : baseEnd_813751 < baseStart_813751 := by decide
  rcases family_descends (prefixWord ++ tailWord_813751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813760 : List Nat := [2, 1, 1, 2, 4, 12]
def baseStart_813760 : Nat := 118140960795 + 813760 * 2 ^ 59
def prefixEnd_813760 : Nat := 4983230072969 + 3 ^ 40 * 813760 * 2
def baseEnd_813760 : Nat := 3439094793439023818581

theorem tailTrace_813760 : CollatzResearch.WordTrace tailWord_813760 prefixEnd_813760 3439094793439023818581 := by
  unfold tailWord_813760
  simp only [CollatzResearch.WordTrace]
  refine ⟨14840132765946986994207367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19786843687929315992276489 14840132765946986994207367)
  ·
    refine ⟨22260199148920480491311051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14840132765946986994207367 22260199148920480491311051)
    ·
      refine ⟨33390298723380720736966577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22260199148920480491311051 33390298723380720736966577)
      ·
        refine ⟨25042724042535540552724933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33390298723380720736966577 25042724042535540552724933)
        ·
          refine ⟨4695510757975413853635925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25042724042535540552724933 4695510757975413853635925)
          ·
            refine ⟨3439094793439023818581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 4695510757975413853635925 3439094793439023818581)
            ·
              rfl

theorem cell22_813760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 12].length) (baseStart_813760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813760 prefixEnd_813760 := by exact prefixLift 813760
  have htrace : WordTrace (prefixWord ++ tailWord_813760) baseStart_813760 baseEnd_813760 := by
    simpa [prefixWord, tailWord_813760, baseEnd_813760] using wordTrace_append hprefix tailTrace_813760
  have hstable : (prefixWord ++ tailWord_813760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813760).length < 2 ^ (prefixWord ++ tailWord_813760).sum := by decide
  have hdescent : baseEnd_813760 < baseStart_813760 := by decide
  rcases family_descends (prefixWord ++ tailWord_813760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813775 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 4, 7]
def baseStart_813775 : Nat := 118140960795 + 813775 * 2 ^ 59
def prefixEnd_813775 : Nat := 4983230072969 + 3 ^ 40 * 813775 * 2
def baseEnd_813775 : Nat := 278571813075105890180015

theorem tailTrace_813775 : CollatzResearch.WordTrace tailWord_813775 prefixEnd_813775 278571813075105890180015 := by
  unfold tailWord_813775
  simp only [CollatzResearch.WordTrace]
  refine ⟨29680812626839631550210779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19787208417893087700140519 29680812626839631550210779)
  ·
    refine ⟨44521218940259447325316169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29680812626839631550210779 44521218940259447325316169)
    ·
      refine ⟨33390914205194585493987127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44521218940259447325316169 33390914205194585493987127)
      ·
        refine ⟨50086371307791878240980691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33390914205194585493987127 50086371307791878240980691)
        ·
          refine ⟨75129556961687817361471037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50086371307791878240980691 75129556961687817361471037)
          ·
            refine ⟨28173583860632931510551639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75129556961687817361471037 28173583860632931510551639)
            ·
              refine ⟨42260375790949397265827459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28173583860632931510551639 42260375790949397265827459)
              ·
                refine ⟨63390563686424095898741189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42260375790949397265827459 63390563686424095898741189)
                ·
                  refine ⟨11885730691204517981013973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63390563686424095898741189 11885730691204517981013973)
                  ·
                    refine ⟨278571813075105890180015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11885730691204517981013973 278571813075105890180015)
                    ·
                      rfl

theorem cell22_813775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 7].length) (baseStart_813775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813775 prefixEnd_813775 := by exact prefixLift 813775
  have htrace : WordTrace (prefixWord ++ tailWord_813775) baseStart_813775 baseEnd_813775 := by
    simpa [prefixWord, tailWord_813775, baseEnd_813775] using wordTrace_append hprefix tailTrace_813775
  have hstable : (prefixWord ++ tailWord_813775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813775).length < 2 ^ (prefixWord ++ tailWord_813775).sum := by decide
  have hdescent : baseEnd_813775 < baseStart_813775 := by decide
  rcases family_descends (prefixWord ++ tailWord_813775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813781 : List Nat := [1, 3, 2, 5, 1, 1, 2, 1, 1, 5]
def baseStart_813781 : Nat := 118140960795 + 813781 * 2 ^ 59
def prefixEnd_813781 : Nat := 4983230072969 + 3 ^ 40 * 813781 * 2
def baseEnd_813781 : Nat := 278573866997723874529997

theorem tailTrace_813781 : CollatzResearch.WordTrace tailWord_813781 prefixEnd_813781 278573866997723874529997 := by
  unfold tailWord_813781
  simp only [CollatzResearch.WordTrace]
  refine ⟨29681031464817894574929197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19787354309878596383286131 29681031464817894574929197)
  ·
    refine ⟨11130386799306710465598449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29681031464817894574929197 11130386799306710465598449)
    ·
      refine ⟨8347790099480032849198837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11130386799306710465598449 8347790099480032849198837)
      ·
        refine ⟨782605321826253079612391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8347790099480032849198837 782605321826253079612391)
        ·
          refine ⟨1173907982739379619418587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782605321826253079612391 1173907982739379619418587)
          ·
            refine ⟨1760861974109069429127881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173907982739379619418587 1760861974109069429127881)
            ·
              refine ⟨1320646480581802071845911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1760861974109069429127881 1320646480581802071845911)
              ·
                refine ⟨1980969720872703107768867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1320646480581802071845911 1980969720872703107768867)
                ·
                  refine ⟨2971454581309054661653301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1980969720872703107768867 2971454581309054661653301)
                  ·
                    refine ⟨278573866997723874529997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2971454581309054661653301 278573866997723874529997)
                    ·
                      rfl

theorem cell22_813781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_813781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813781 prefixEnd_813781 := by exact prefixLift 813781
  have htrace : WordTrace (prefixWord ++ tailWord_813781) baseStart_813781 baseEnd_813781 := by
    simpa [prefixWord, tailWord_813781, baseEnd_813781] using wordTrace_append hprefix tailTrace_813781
  have hstable : (prefixWord ++ tailWord_813781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813781).length < 2 ^ (prefixWord ++ tailWord_813781).sum := by decide
  have hdescent : baseEnd_813781 < baseStart_813781 := by decide
  rcases family_descends (prefixWord ++ tailWord_813781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813826 : List Nat := [3, 4, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_813826 : Nat := 118140960795 + 813826 * 2 ^ 59
def prefixEnd_813826 : Nat := 4983230072969 + 3 ^ 40 * 813826 * 2
def baseEnd_813826 : Nat := 278589271417358757154859

theorem tailTrace_813826 : CollatzResearch.WordTrace tailWord_813826 prefixEnd_813826 278589271417358757154859 := by
  unfold tailWord_813826
  simp only [CollatzResearch.WordTrace]
  refine ⟨7420668187413716815079333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19788448499769911506878221 7420668187413716815079333)
  ·
    refine ⟨1391375285140071902827375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7420668187413716815079333 1391375285140071902827375)
    ·
      refine ⟨2087062927710107854241063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1391375285140071902827375 2087062927710107854241063)
      ·
        refine ⟨3130594391565161781361595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2087062927710107854241063 3130594391565161781361595)
        ·
          refine ⟨4695891587347742672042393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3130594391565161781361595 4695891587347742672042393)
          ·
            refine ⟨3521918690510807004031795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4695891587347742672042393 3521918690510807004031795)
            ·
              refine ⟨5282878035766210506047693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3521918690510807004031795 5282878035766210506047693)
              ·
                refine ⟨1981079263412328939767885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5282878035766210506047693 1981079263412328939767885)
                ·
                  refine ⟨742904723779623352412957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1981079263412328939767885 742904723779623352412957)
                  ·
                    refine ⟨278589271417358757154859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 742904723779623352412957 278589271417358757154859)
                    ·
                      rfl

theorem cell22_813826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_813826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813826 prefixEnd_813826 := by exact prefixLift 813826
  have htrace : WordTrace (prefixWord ++ tailWord_813826) baseStart_813826 baseEnd_813826 := by
    simpa [prefixWord, tailWord_813826, baseEnd_813826] using wordTrace_append hprefix tailTrace_813826
  have hstable : (prefixWord ++ tailWord_813826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813826).length < 2 ^ (prefixWord ++ tailWord_813826).sum := by decide
  have hdescent : baseEnd_813826 < baseStart_813826 := by decide
  rcases family_descends (prefixWord ++ tailWord_813826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813839 : List Nat := [1, 1, 2, 1, 1, 1, 9, 1, 5]
def baseStart_813839 : Nat := 118140960795 + 813839 * 2 ^ 59
def prefixEnd_813839 : Nat := 4983230072969 + 3 ^ 40 * 813839 * 2
def baseEnd_813839 : Nat := 92864573861010352193273

theorem tailTrace_813839 : CollatzResearch.WordTrace tailWord_813839 prefixEnd_813839 92864573861010352193273 := by
  unfold tailWord_813839
  simp only [CollatzResearch.WordTrace]
  refine ⟨29683146898607770480540571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19788764599071846987027047 29683146898607770480540571)
  ·
    refine ⟨44524720347911655720810857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29683146898607770480540571 44524720347911655720810857)
    ·
      refine ⟨33393540260933741790608143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44524720347911655720810857 33393540260933741790608143)
      ·
        refine ⟨50090310391400612685912215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33393540260933741790608143 50090310391400612685912215)
        ·
          refine ⟨75135465587100919028868323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50090310391400612685912215 75135465587100919028868323)
          ·
            refine ⟨112703198380651378543302485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75135465587100919028868323 112703198380651378543302485)
            ·
              refine ⟨660370303011629171152163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 112703198380651378543302485 660370303011629171152163)
              ·
                refine ⟨990555454517443756728245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 660370303011629171152163 990555454517443756728245)
                ·
                  refine ⟨92864573861010352193273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 990555454517443756728245 92864573861010352193273)
                  ·
                    rfl

theorem cell22_813839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 5].length) (baseStart_813839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813839 prefixEnd_813839 := by exact prefixLift 813839
  have htrace : WordTrace (prefixWord ++ tailWord_813839) baseStart_813839 baseEnd_813839 := by
    simpa [prefixWord, tailWord_813839, baseEnd_813839] using wordTrace_append hprefix tailTrace_813839
  have hstable : (prefixWord ++ tailWord_813839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813839).length < 2 ^ (prefixWord ++ tailWord_813839).sum := by decide
  have hdescent : baseEnd_813839 < baseStart_813839 := by decide
  rcases family_descends (prefixWord ++ tailWord_813839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813860 : List Nat := [2, 3, 1, 3, 3, 2, 1, 3, 1, 3]
def baseStart_813860 : Nat := 118140960795 + 813860 * 2 ^ 59
def prefixEnd_813860 : Nat := 4983230072969 + 3 ^ 40 * 813860 * 2
def baseEnd_813860 : Nat := 278600910312194001804755

theorem tailTrace_813860 : CollatzResearch.WordTrace tailWord_813860 prefixEnd_813860 278600910312194001804755 := by
  unfold tailWord_813860
  simp only [CollatzResearch.WordTrace]
  refine ⟨14841956415765845533527517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19789275221021127378036689 14841956415765845533527517)
  ·
    refine ⟨5565733655912192075072819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14841956415765845533527517 5565733655912192075072819)
    ·
      refine ⟨8348600483868288112609229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5565733655912192075072819 8348600483868288112609229)
      ·
        refine ⟨3130725181450608042228461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8348600483868288112609229 3130725181450608042228461)
        ·
          refine ⟨1174021943043978015835673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3130725181450608042228461 1174021943043978015835673)
          ·
            refine ⟨880516457282983511876755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1174021943043978015835673 880516457282983511876755)
            ·
              refine ⟨1320774685924475267815133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 880516457282983511876755 1320774685924475267815133)
              ·
                refine ⟨495290507221678225430675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1320774685924475267815133 495290507221678225430675)
                ·
                  refine ⟨742935760832517338146013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 495290507221678225430675 742935760832517338146013)
                  ·
                    refine ⟨278600910312194001804755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 742935760832517338146013 278600910312194001804755)
                    ·
                      rfl

theorem cell22_813860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_813860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813860 prefixEnd_813860 := by exact prefixLift 813860
  have htrace : WordTrace (prefixWord ++ tailWord_813860) baseStart_813860 baseEnd_813860 := by
    simpa [prefixWord, tailWord_813860, baseEnd_813860] using wordTrace_append hprefix tailTrace_813860
  have hstable : (prefixWord ++ tailWord_813860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813860).length < 2 ^ (prefixWord ++ tailWord_813860).sum := by decide
  have hdescent : baseEnd_813860 < baseStart_813860 := by decide
  rcases family_descends (prefixWord ++ tailWord_813860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813914 : List Nat := [3, 1, 1, 2, 1, 4, 1, 3, 2, 4]
def baseStart_813914 : Nat := 118140960795 + 813914 * 2 ^ 59
def prefixEnd_813914 : Nat := 4983230072969 + 3 ^ 40 * 813914 * 2
def baseEnd_813914 : Nat := 278619395615755860954589

theorem tailTrace_813914 : CollatzResearch.WordTrace tailWord_813914 prefixEnd_813914 278619395615755860954589 := by
  unfold tailWord_813914
  simp only [CollatzResearch.WordTrace]
  refine ⟨7421470593334014572380199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19790588248890705526347197 7421470593334014572380199)
  ·
    refine ⟨11132205890001021858570299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7421470593334014572380199 11132205890001021858570299)
    ·
      refine ⟨16698308835001532787855449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11132205890001021858570299 16698308835001532787855449)
      ·
        refine ⟨12523731626251149590891587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16698308835001532787855449 12523731626251149590891587)
        ·
          refine ⟨18785597439376724386337381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12523731626251149590891587 18785597439376724386337381)
          ·
            refine ⟨3522299519883135822438259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18785597439376724386337381 3522299519883135822438259)
            ·
              refine ⟨5283449279824703733657389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3522299519883135822438259 5283449279824703733657389)
              ·
                refine ⟨1981293479934263900121521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5283449279824703733657389 1981293479934263900121521)
                ·
                  refine ⟨1485970109950697925091141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1981293479934263900121521 1485970109950697925091141)
                  ·
                    refine ⟨278619395615755860954589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1485970109950697925091141 278619395615755860954589)
                    ·
                      rfl

theorem cell22_813914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_813914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813914 prefixEnd_813914 := by exact prefixLift 813914
  have htrace : WordTrace (prefixWord ++ tailWord_813914) baseStart_813914 baseEnd_813914 := by
    simpa [prefixWord, tailWord_813914, baseEnd_813914] using wordTrace_append hprefix tailTrace_813914
  have hstable : (prefixWord ++ tailWord_813914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813914).length < 2 ^ (prefixWord ++ tailWord_813914).sum := by decide
  have hdescent : baseEnd_813914 < baseStart_813914 := by decide
  rcases family_descends (prefixWord ++ tailWord_813914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813916 : List Nat := [2, 2, 4, 2, 1, 2, 1, 2, 1, 5]
def baseStart_813916 : Nat := 118140960795 + 813916 * 2 ^ 59
def prefixEnd_813916 : Nat := 4983230072969 + 3 ^ 40 * 813916 * 2
def baseEnd_813916 : Nat := 278620080256628522404583

theorem tailTrace_813916 : CollatzResearch.WordTrace tailWord_813916 prefixEnd_813916 278620080256628522404583 := by
  unfold tailWord_813916
  simp only [CollatzResearch.WordTrace]
  refine ⟨14842977659664406315546801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19790636879552541754062401 14842977659664406315546801)
  ·
    refine ⟨11132233244748304736660101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14842977659664406315546801 11132233244748304736660101)
    ·
      refine ⟨2087293733390307138123769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11132233244748304736660101 2087293733390307138123769)
      ·
        refine ⟨1565470300042730353592827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2087293733390307138123769 1565470300042730353592827)
        ·
          refine ⟨2348205450064095530389241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1565470300042730353592827 2348205450064095530389241)
          ·
            refine ⟨1761154087548071647791931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2348205450064095530389241 1761154087548071647791931)
            ·
              refine ⟨2641731131322107471687897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1761154087548071647791931 2641731131322107471687897)
              ·
                refine ⟨1981298348491580603765923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2641731131322107471687897 1981298348491580603765923)
                ·
                  refine ⟨2971947522737370905648885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1981298348491580603765923 2971947522737370905648885)
                  ·
                    refine ⟨278620080256628522404583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2971947522737370905648885 278620080256628522404583)
                    ·
                      rfl

theorem cell22_813916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_813916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813916 prefixEnd_813916 := by exact prefixLift 813916
  have htrace : WordTrace (prefixWord ++ tailWord_813916) baseStart_813916 baseEnd_813916 := by
    simpa [prefixWord, tailWord_813916, baseEnd_813916] using wordTrace_append hprefix tailTrace_813916
  have hstable : (prefixWord ++ tailWord_813916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813916).length < 2 ^ (prefixWord ++ tailWord_813916).sum := by decide
  have hdescent : baseEnd_813916 < baseStart_813916 := by decide
  rcases family_descends (prefixWord ++ tailWord_813916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813961 : List Nat := [1, 2, 1, 1, 5, 3, 1, 2, 3, 3]
def baseStart_813961 : Nat := 118140960795 + 813961 * 2 ^ 59
def prefixEnd_813961 : Nat := 4983230072969 + 3 ^ 40 * 813961 * 2
def baseEnd_813961 : Nat := 278635484676263405029445

theorem tailTrace_813961 : CollatzResearch.WordTrace tailWord_813961 prefixEnd_813961 278635484676263405029445 := by
  unfold tailWord_813961
  simp only [CollatzResearch.WordTrace]
  refine ⟨29687596604165785316481737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19791731069443856877654491 29687596604165785316481737)
  ·
    refine ⟨22265697453124338987361303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29687596604165785316481737 22265697453124338987361303)
    ·
      refine ⟨33398546179686508481041955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22265697453124338987361303 33398546179686508481041955)
      ·
        refine ⟨50097819269529762721562933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33398546179686508481041955 50097819269529762721562933)
        ·
          refine ⟨4696670556518415255146525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50097819269529762721562933 4696670556518415255146525)
          ·
            refine ⟨1761251458694405720679947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4696670556518415255146525 1761251458694405720679947)
            ·
              refine ⟨2641877188041608581019921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1761251458694405720679947 2641877188041608581019921)
              ·
                refine ⟨1981407891031206435764941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2641877188041608581019921 1981407891031206435764941)
                ·
                  refine ⟨743027959136702413411853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1981407891031206435764941 743027959136702413411853)
                  ·
                    refine ⟨278635484676263405029445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 743027959136702413411853 278635484676263405029445)
                    ·
                      rfl

theorem cell22_813961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3, 3].length) (baseStart_813961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813961 prefixEnd_813961 := by exact prefixLift 813961
  have htrace : WordTrace (prefixWord ++ tailWord_813961) baseStart_813961 baseEnd_813961 := by
    simpa [prefixWord, tailWord_813961, baseEnd_813961] using wordTrace_append hprefix tailTrace_813961
  have hstable : (prefixWord ++ tailWord_813961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813961).length < 2 ^ (prefixWord ++ tailWord_813961).sum := by decide
  have hdescent : baseEnd_813961 < baseStart_813961 := by decide
  rcases family_descends (prefixWord ++ tailWord_813961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813991 : List Nat := [1, 1, 6, 1, 3, 1, 1, 1, 7]
def baseStart_813991 : Nat := 118140960795 + 813991 * 2 ^ 59
def prefixEnd_813991 : Nat := 4983230072969 + 3 ^ 40 * 813991 * 2
def baseEnd_813991 : Nat := 92881918096451108926451

theorem tailTrace_813991 : CollatzResearch.WordTrace tailWord_813991 prefixEnd_813991 92881918096451108926451 := by
  unfold tailWord_813991
  simp only [CollatzResearch.WordTrace]
  refine ⟨29688690794057100440073827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19792460529371400293382551 29688690794057100440073827)
  ·
    refine ⟨44533036191085650660110741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29688690794057100440073827 44533036191085650660110741)
    ·
      refine ⟨2087486071457139874692691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44533036191085650660110741 2087486071457139874692691)
      ·
        refine ⟨3131229107185709812039037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2087486071457139874692691 3131229107185709812039037)
        ·
          refine ⟨1174210915194641179514639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3131229107185709812039037 1174210915194641179514639)
          ·
            refine ⟨1761316372791961769271959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1174210915194641179514639 1761316372791961769271959)
            ·
              refine ⟨2641974559187942653907939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1761316372791961769271959 2641974559187942653907939)
              ·
                refine ⟨3962961838781913980861909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2641974559187942653907939 3962961838781913980861909)
                ·
                  refine ⟨92881918096451108926451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3962961838781913980861909 92881918096451108926451)
                  ·
                    rfl

theorem cell22_813991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 7].length) (baseStart_813991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_813991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_813991 prefixEnd_813991 := by exact prefixLift 813991
  have htrace : WordTrace (prefixWord ++ tailWord_813991) baseStart_813991 baseEnd_813991 := by
    simpa [prefixWord, tailWord_813991, baseEnd_813991] using wordTrace_append hprefix tailTrace_813991
  have hstable : (prefixWord ++ tailWord_813991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813991).length < 2 ^ (prefixWord ++ tailWord_813991).sum := by decide
  have hdescent : baseEnd_813991 < baseStart_813991 := by decide
  rcases family_descends (prefixWord ++ tailWord_813991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814051 : List Nat := [1, 1, 1, 6, 1, 1, 1, 3, 4, 3]
def baseStart_814051 : Nat := 118140960795 + 814051 * 2 ^ 59
def prefixEnd_814051 : Nat := 4983230072969 + 3 ^ 40 * 814051 * 2
def baseEnd_814051 : Nat := 278666293515533170279169

theorem tailTrace_814051 : CollatzResearch.WordTrace tailWord_814051 prefixEnd_814051 278666293515533170279169 := by
  unfold tailWord_814051
  simp only [CollatzResearch.WordTrace]
  refine ⟨29690879173839730687258007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19793919449226487124838671 29690879173839730687258007)
  ·
    refine ⟨44536318760759596030887011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29690879173839730687258007 44536318760759596030887011)
    ·
      refine ⟨66804478141139394046330517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44536318760759596030887011 66804478141139394046330517)
      ·
        refine ⟨3131459912865909095921743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 66804478141139394046330517 3131459912865909095921743)
        ·
          refine ⟨4697189869298863643882615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3131459912865909095921743 4697189869298863643882615)
          ·
            refine ⟨7045784803948295465823923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4697189869298863643882615 7045784803948295465823923)
            ·
              refine ⟨10568677205922443198735885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7045784803948295465823923 10568677205922443198735885)
              ·
                refine ⟨3963253952220916199525957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10568677205922443198735885 3963253952220916199525957)
                ·
                  refine ⟨743110116041421787411117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3963253952220916199525957 743110116041421787411117)
                  ·
                    refine ⟨278666293515533170279169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 743110116041421787411117 278666293515533170279169)
                    ·
                      rfl

theorem cell22_814051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4, 3].length) (baseStart_814051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814051 prefixEnd_814051 := by exact prefixLift 814051
  have htrace : WordTrace (prefixWord ++ tailWord_814051) baseStart_814051 baseEnd_814051 := by
    simpa [prefixWord, tailWord_814051, baseEnd_814051] using wordTrace_append hprefix tailTrace_814051
  have hstable : (prefixWord ++ tailWord_814051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814051).length < 2 ^ (prefixWord ++ tailWord_814051).sum := by decide
  have hdescent : baseEnd_814051 < baseStart_814051 := by decide
  rcases family_descends (prefixWord ++ tailWord_814051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814098 : List Nat := [3, 2, 5, 1, 11]
def baseStart_814098 : Nat := 118140960795 + 814098 * 2 ^ 59
def prefixEnd_814098 : Nat := 4983230072969 + 3 ^ 40 * 814098 * 2
def baseEnd_814098 : Nat := 1146841080559838330675

theorem tailTrace_814098 : CollatzResearch.WordTrace tailWord_814098 prefixEnd_814098 1146841080559838330675 := by
  unfold tailWord_814098
  simp only [CollatzResearch.WordTrace]
  refine ⟨7423148351167364428554737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19795062269779638476145965 7423148351167364428554737)
  ·
    refine ⟨5567361263375523321416053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7423148351167364428554737 5567361263375523321416053)
    ·
      refine ⟨521940118441455311382755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5567361263375523321416053 521940118441455311382755)
      ·
        refine ⟨782910177662182967074133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521940118441455311382755 782910177662182967074133)
        ·
          refine ⟨1146841080559838330675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 782910177662182967074133 1146841080559838330675)
          ·
            rfl

theorem cell22_814098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 11].length) (baseStart_814098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814098 prefixEnd_814098 := by exact prefixLift 814098
  have htrace : WordTrace (prefixWord ++ tailWord_814098) baseStart_814098 baseEnd_814098 := by
    simpa [prefixWord, tailWord_814098, baseEnd_814098] using wordTrace_append hprefix tailTrace_814098
  have hstable : (prefixWord ++ tailWord_814098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814098).length < 2 ^ (prefixWord ++ tailWord_814098).sum := by decide
  have hdescent : baseEnd_814098 < baseStart_814098 := by decide
  rcases family_descends (prefixWord ++ tailWord_814098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814190 : List Nat := [4, 1, 2, 2, 1, 3, 2, 2, 1, 4]
def baseStart_814190 : Nat := 118140960795 + 814190 * 2 ^ 59
def prefixEnd_814190 : Nat := 4983230072969 + 3 ^ 40 * 814190 * 2
def baseEnd_814190 : Nat := 278713876056183141053743

theorem tailTrace_814190 : CollatzResearch.WordTrace tailWord_814190 prefixEnd_814190 278713876056183141053743 := by
  unfold tailWord_814190
  simp only [CollatzResearch.WordTrace]
  refine ⟨3711993615042019678321003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19797299280224104951045349 3711993615042019678321003)
  ·
    refine ⟨5567990422563029517481505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3711993615042019678321003 5567990422563029517481505)
    ·
      refine ⟨4175992816922272138111129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5567990422563029517481505 4175992816922272138111129)
      ·
        refine ⟨3131994612691704103583347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4175992816922272138111129 3131994612691704103583347)
        ·
          refine ⟨4697991919037556155375021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3131994612691704103583347 4697991919037556155375021)
          ·
            refine ⟨1761746969639083558265633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4697991919037556155375021 1761746969639083558265633)
            ·
              refine ⟨1321310227229312668699225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1761746969639083558265633 1321310227229312668699225)
              ·
                refine ⟨990982670421984501524419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1321310227229312668699225 990982670421984501524419)
                ·
                  refine ⟨1486474005632976752286629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 990982670421984501524419 1486474005632976752286629)
                  ·
                    refine ⟨278713876056183141053743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1486474005632976752286629 278713876056183141053743)
                    ·
                      rfl

theorem cell22_814190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_814190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814190 prefixEnd_814190 := by exact prefixLift 814190
  have htrace : WordTrace (prefixWord ++ tailWord_814190) baseStart_814190 baseEnd_814190 := by
    simpa [prefixWord, tailWord_814190, baseEnd_814190] using wordTrace_append hprefix tailTrace_814190
  have hstable : (prefixWord ++ tailWord_814190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814190).length < 2 ^ (prefixWord ++ tailWord_814190).sum := by decide
  have hdescent : baseEnd_814190 < baseStart_814190 := by decide
  rcases family_descends (prefixWord ++ tailWord_814190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814218 : List Nat := [3, 1, 2, 3, 1, 1, 3, 2, 2, 4]
def baseStart_814218 : Nat := 118140960795 + 814218 * 2 ^ 59
def prefixEnd_814218 : Nat := 4983230072969 + 3 ^ 40 * 814218 * 2
def baseEnd_814218 : Nat := 278723461028400401353657

theorem tailTrace_814218 : CollatzResearch.WordTrace tailWord_814218 prefixEnd_814218 278723461028400401353657 := by
  unfold tailWord_814218
  simp only [CollatzResearch.WordTrace]
  refine ⟨7424242541058679552146827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19797980109489812139058205 7424242541058679552146827)
  ·
    refine ⟨11136363811588019328220241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7424242541058679552146827 11136363811588019328220241)
    ·
      refine ⟨8352272858691014496165181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11136363811588019328220241 8352272858691014496165181)
      ·
        refine ⟨3132102322009130436061943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8352272858691014496165181 3132102322009130436061943)
        ·
          refine ⟨4698153483013695654092915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3132102322009130436061943 4698153483013695654092915)
          ·
            refine ⟨7047230224520543481139373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4698153483013695654092915 7047230224520543481139373)
            ·
              refine ⟨2642711334195203805427265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7047230224520543481139373 2642711334195203805427265)
              ·
                refine ⟨1982033500646402854070449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2642711334195203805427265 1982033500646402854070449)
                ·
                  refine ⟨1486525125484802140552837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1982033500646402854070449 1486525125484802140552837)
                  ·
                    refine ⟨278723461028400401353657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1486525125484802140552837 278723461028400401353657)
                    ·
                      rfl

theorem cell22_814218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_814218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814218 prefixEnd_814218 := by exact prefixLift 814218
  have htrace : WordTrace (prefixWord ++ tailWord_814218) baseStart_814218 baseEnd_814218 := by
    simpa [prefixWord, tailWord_814218, baseEnd_814218] using wordTrace_append hprefix tailTrace_814218
  have hstable : (prefixWord ++ tailWord_814218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814218).length < 2 ^ (prefixWord ++ tailWord_814218).sum := by decide
  have hdescent : baseEnd_814218 < baseStart_814218 := by decide
  rcases family_descends (prefixWord ++ tailWord_814218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814222 : List Nat := [4, 1, 1, 3, 2, 2, 3, 2, 4]
def baseStart_814222 : Nat := 118140960795 + 814222 * 2 ^ 59
def prefixEnd_814222 : Nat := 4983230072969 + 3 ^ 40 * 814222 * 2
def baseEnd_814222 : Nat := 92908276770048574751215

theorem tailTrace_814222 : CollatzResearch.WordTrace tailWord_814222 prefixEnd_814222 92908276770048574751215 := by
  unfold tailWord_814222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3712139507027528361466615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19798077370813484594488613 3712139507027528361466615)
  ·
    refine ⟨5568209260541292542199923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3712139507027528361466615 5568209260541292542199923)
    ·
      refine ⟨8352313890811938813299885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5568209260541292542199923 8352313890811938813299885)
      ·
        refine ⟨3132117709054477054987457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8352313890811938813299885 3132117709054477054987457)
        ·
          refine ⟨2349088281790857791240593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3132117709054477054987457 2349088281790857791240593)
          ·
            refine ⟨1761816211343143343430445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2349088281790857791240593 1761816211343143343430445)
            ·
              refine ⟨660681079253678753786417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1761816211343143343430445 660681079253678753786417)
              ·
                refine ⟨495510809440259065339813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 660681079253678753786417 495510809440259065339813)
                ·
                  refine ⟨92908276770048574751215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 495510809440259065339813 92908276770048574751215)
                  ·
                    rfl

theorem cell22_814222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_814222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814222 prefixEnd_814222 := by exact prefixLift 814222
  have htrace : WordTrace (prefixWord ++ tailWord_814222) baseStart_814222 baseEnd_814222 := by
    simpa [prefixWord, tailWord_814222, baseEnd_814222] using wordTrace_append hprefix tailTrace_814222
  have hstable : (prefixWord ++ tailWord_814222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814222).length < 2 ^ (prefixWord ++ tailWord_814222).sum := by decide
  have hdescent : baseEnd_814222 < baseStart_814222 := by decide
  rcases family_descends (prefixWord ++ tailWord_814222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814282 : List Nat := [3, 1, 2, 1, 3, 3, 1, 4, 1, 3]
def baseStart_814282 : Nat := 118140960795 + 814282 * 2 ^ 59
def prefixEnd_814282 : Nat := 4983230072969 + 3 ^ 40 * 814282 * 2
def baseEnd_814282 : Nat := 278745369536325567753461

theorem tailTrace_814282 : CollatzResearch.WordTrace tailWord_814282 prefixEnd_814282 278745369536325567753461 := by
  unfold tailWord_814282
  simp only [CollatzResearch.WordTrace]
  refine ⟨7424826109000714284729275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19799536290668571425944733 7424826109000714284729275)
  ·
    refine ⟨11137239163501071427093913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7424826109000714284729275 11137239163501071427093913)
    ·
      refine ⟨8352929372625803570320435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11137239163501071427093913 8352929372625803570320435)
      ·
        refine ⟨12529394058938705355480653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8352929372625803570320435 12529394058938705355480653)
        ·
          refine ⟨4698522772102014508305245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12529394058938705355480653 4698522772102014508305245)
          ·
            refine ⟨1761946039538255440614467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4698522772102014508305245 1761946039538255440614467)
            ·
              refine ⟨2642919059307383160921701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1761946039538255440614467 2642919059307383160921701)
              ·
                refine ⟨495547323620134342672819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2642919059307383160921701 495547323620134342672819)
                ·
                  refine ⟨743320985430201514009229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 495547323620134342672819 743320985430201514009229)
                  ·
                    refine ⟨278745369536325567753461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 743320985430201514009229 278745369536325567753461)
                    ·
                      rfl

theorem cell22_814282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_814282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814282 prefixEnd_814282 := by exact prefixLift 814282
  have htrace : WordTrace (prefixWord ++ tailWord_814282) baseStart_814282 baseEnd_814282 := by
    simpa [prefixWord, tailWord_814282, baseEnd_814282] using wordTrace_append hprefix tailTrace_814282
  have hstable : (prefixWord ++ tailWord_814282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814282).length < 2 ^ (prefixWord ++ tailWord_814282).sum := by decide
  have hdescent : baseEnd_814282 < baseStart_814282 := by decide
  rcases family_descends (prefixWord ++ tailWord_814282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814293 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 1, 7]
def baseStart_814293 : Nat := 118140960795 + 814293 * 2 ^ 59
def prefixEnd_814293 : Nat := 4983230072969 + 3 ^ 40 * 814293 * 2
def baseEnd_814293 : Nat := 278749135061125205728427

theorem tailTrace_814293 : CollatzResearch.WordTrace tailWord_814293 prefixEnd_814293 278749135061125205728427 := by
  unfold tailWord_814293
  simp only [CollatzResearch.WordTrace]
  refine ⟨29699705638963006017567533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19799803759308670678378355 29699705638963006017567533)
  ·
    refine ⟨11137389614611127256587825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29699705638963006017567533 11137389614611127256587825)
    ·
      refine ⟨8353042210958345442440869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11137389614611127256587825 8353042210958345442440869)
      ·
        refine ⟨1566195414554689770457663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8353042210958345442440869 1566195414554689770457663)
        ·
          refine ⟨2349293121832034655686495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1566195414554689770457663 2349293121832034655686495)
          ·
            refine ⟨3523939682748051983529743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2349293121832034655686495 3523939682748051983529743)
            ·
              refine ⟨5285909524122077975294615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3523939682748051983529743 5285909524122077975294615)
              ·
                refine ⟨7928864286183116962941923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5285909524122077975294615 7928864286183116962941923)
                ·
                  refine ⟨11893296429274675444412885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7928864286183116962941923 11893296429274675444412885)
                  ·
                    refine ⟨278749135061125205728427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11893296429274675444412885 278749135061125205728427)
                    ·
                      rfl

theorem cell22_814293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_814293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814293 prefixEnd_814293 := by exact prefixLift 814293
  have htrace : WordTrace (prefixWord ++ tailWord_814293) baseStart_814293 baseEnd_814293 := by
    simpa [prefixWord, tailWord_814293, baseEnd_814293] using wordTrace_append hprefix tailTrace_814293
  have hstable : (prefixWord ++ tailWord_814293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814293).length < 2 ^ (prefixWord ++ tailWord_814293).sum := by decide
  have hdescent : baseEnd_814293 < baseStart_814293 := by decide
  rcases family_descends (prefixWord ++ tailWord_814293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814308 : List Nat := [2, 3, 1, 1, 1, 2, 4, 1, 3, 4]
def baseStart_814308 : Nat := 118140960795 + 814308 * 2 ^ 59
def prefixEnd_814308 : Nat := 4983230072969 + 3 ^ 40 * 814308 * 2
def baseEnd_814308 : Nat := 278754269867670166603381

theorem tailTrace_814308 : CollatzResearch.WordTrace tailWord_814308 prefixEnd_814308 278754269867670166603381 := by
  unfold tailWord_814308
  simp only [CollatzResearch.WordTrace]
  refine ⟨14850126366954331789681789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19800168489272442386242385 14850126366954331789681789)
  ·
    refine ⟨5568797387607874421130671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14850126366954331789681789 5568797387607874421130671)
    ·
      refine ⟨8353196081411811631696007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5568797387607874421130671 8353196081411811631696007)
      ·
        refine ⟨12529794122117717447544011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8353196081411811631696007 12529794122117717447544011)
        ·
          refine ⟨18794691183176576171316017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12529794122117717447544011 18794691183176576171316017)
          ·
            refine ⟨14096018387382432128487013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18794691183176576171316017 14096018387382432128487013)
            ·
              refine ⟨2643003447634206024091315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14096018387382432128487013 2643003447634206024091315)
              ·
                refine ⟨3964505171451309036136973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2643003447634206024091315 3964505171451309036136973)
                ·
                  refine ⟨1486689439294240888551365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3964505171451309036136973 1486689439294240888551365)
                  ·
                    refine ⟨278754269867670166603381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1486689439294240888551365 278754269867670166603381)
                    ·
                      rfl

theorem cell22_814308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_814308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814308 prefixEnd_814308 := by exact prefixLift 814308
  have htrace : WordTrace (prefixWord ++ tailWord_814308) baseStart_814308 baseEnd_814308 := by
    simpa [prefixWord, tailWord_814308, baseEnd_814308] using wordTrace_append hprefix tailTrace_814308
  have hstable : (prefixWord ++ tailWord_814308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814308).length < 2 ^ (prefixWord ++ tailWord_814308).sum := by decide
  have hdescent : baseEnd_814308 < baseStart_814308 := by decide
  rcases family_descends (prefixWord ++ tailWord_814308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814340 : List Nat := [2, 3, 2, 2, 2, 2, 2, 1, 6]
def baseStart_814340 : Nat := 118140960795 + 814340 * 2 ^ 59
def prefixEnd_814340 : Nat := 4983230072969 + 3 ^ 40 * 814340 * 2
def baseEnd_814340 : Nat := 92921741373877583267761

theorem tailTrace_814340 : CollatzResearch.WordTrace tailWord_814340 prefixEnd_814340 92921741373877583267761 := by
  unfold tailWord_814340
  simp only [CollatzResearch.WordTrace]
  refine ⟨14850709934896366522264237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19800946579861822029685649 14850709934896366522264237)
  ·
    refine ⟨5569016225586137445849089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14850709934896366522264237 5569016225586137445849089)
    ·
      refine ⟨4176762169189603084386817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5569016225586137445849089 4176762169189603084386817)
      ·
        refine ⟨3132571626892202313290113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4176762169189603084386817 3132571626892202313290113)
        ·
          refine ⟨2349428720169151734967585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3132571626892202313290113 2349428720169151734967585)
          ·
            refine ⟨1762071540126863801225689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2349428720169151734967585 1762071540126863801225689)
            ·
              refine ⟨1321553655095147850919267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1762071540126863801225689 1321553655095147850919267)
              ·
                refine ⟨1982330482642721776378901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1321553655095147850919267 1982330482642721776378901)
                ·
                  refine ⟨92921741373877583267761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1982330482642721776378901 92921741373877583267761)
                  ·
                    rfl

theorem cell22_814340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_814340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814340 prefixEnd_814340 := by exact prefixLift 814340
  have htrace : WordTrace (prefixWord ++ tailWord_814340) baseStart_814340 baseEnd_814340 := by
    simpa [prefixWord, tailWord_814340, baseEnd_814340] using wordTrace_append hprefix tailTrace_814340
  have hstable : (prefixWord ++ tailWord_814340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814340).length < 2 ^ (prefixWord ++ tailWord_814340).sum := by decide
  have hdescent : baseEnd_814340 < baseStart_814340 := by decide
  rcases family_descends (prefixWord ++ tailWord_814340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814434 : List Nat := [3, 3, 2, 1, 1, 1, 2, 5, 1, 3]
def baseStart_814434 : Nat := 118140960795 + 814434 * 2 ^ 59
def prefixEnd_814434 : Nat := 4983230072969 + 3 ^ 40 * 814434 * 2
def baseEnd_814434 : Nat := 278797402242647837952995

theorem tailTrace_814434 : CollatzResearch.WordTrace tailWord_814434 prefixEnd_814434 278797402242647837952995 := by
  unfold tailWord_814434
  simp only [CollatzResearch.WordTrace]
  refine ⟨7426212082863046774612589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19803232220968124732300237 7426212082863046774612589)
  ·
    refine ⟨2784829531073642540479721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7426212082863046774612589 2784829531073642540479721)
    ·
      refine ⟨2088622148305231905359791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2784829531073642540479721 2088622148305231905359791)
      ·
        refine ⟨3132933222457847858039687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2088622148305231905359791 3132933222457847858039687)
        ·
          refine ⟨4699399833686771787059531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3132933222457847858039687 4699399833686771787059531)
          ·
            refine ⟨7049099750530157680589297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4699399833686771787059531 7049099750530157680589297)
            ·
              refine ⟨5286824812897618260441973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7049099750530157680589297 5286824812897618260441973)
              ·
                refine ⟨495639826209151711916435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5286824812897618260441973 495639826209151711916435)
                ·
                  refine ⟨743459739313727567874653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 495639826209151711916435 743459739313727567874653)
                  ·
                    refine ⟨278797402242647837952995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 743459739313727567874653 278797402242647837952995)
                    ·
                      rfl

theorem cell22_814434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_814434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814434 prefixEnd_814434 := by exact prefixLift 814434
  have htrace : WordTrace (prefixWord ++ tailWord_814434) baseStart_814434 baseEnd_814434 := by
    simpa [prefixWord, tailWord_814434, baseEnd_814434] using wordTrace_append hprefix tailTrace_814434
  have hstable : (prefixWord ++ tailWord_814434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814434).length < 2 ^ (prefixWord ++ tailWord_814434).sum := by decide
  have hdescent : baseEnd_814434 < baseStart_814434 := by decide
  rcases family_descends (prefixWord ++ tailWord_814434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814443 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 7, 4]
def baseStart_814443 : Nat := 118140960795 + 814443 * 2 ^ 59
def prefixEnd_814443 : Nat := 4983230072969 + 3 ^ 40 * 814443 * 2
def baseEnd_814443 : Nat := 278800483126574814477967

theorem tailTrace_814443 : CollatzResearch.WordTrace tailWord_814443 prefixEnd_814443 278800483126574814477967 := by
  unfold tailWord_814443
  simp only [CollatzResearch.WordTrace]
  refine ⟨29705176588419581635527983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19803451058946387757018655 29705176588419581635527983)
  ·
    refine ⟨44557764882629372453291975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29705176588419581635527983 44557764882629372453291975)
    ·
      refine ⟨66836647323944058679937963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44557764882629372453291975 66836647323944058679937963)
      ·
        refine ⟨100254970985916088019906945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66836647323944058679937963 100254970985916088019906945)
        ·
          refine ⟨75191228239437066014930209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100254970985916088019906945 75191228239437066014930209)
          ·
            refine ⟨56393421179577799511197657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75191228239437066014930209 56393421179577799511197657)
            ·
              refine ⟨42295065884683349633398243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56393421179577799511197657 42295065884683349633398243)
              ·
                refine ⟨63442598827025024450097365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42295065884683349633398243 63442598827025024450097365)
                ·
                  refine ⟨1486935910008399010549157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 63442598827025024450097365 1486935910008399010549157)
                  ·
                    refine ⟨278800483126574814477967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1486935910008399010549157 278800483126574814477967)
                    ·
                      rfl

theorem cell22_814443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 4].length) (baseStart_814443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814443 prefixEnd_814443 := by exact prefixLift 814443
  have htrace : WordTrace (prefixWord ++ tailWord_814443) baseStart_814443 baseEnd_814443 := by
    simpa [prefixWord, tailWord_814443, baseEnd_814443] using wordTrace_append hprefix tailTrace_814443
  have hstable : (prefixWord ++ tailWord_814443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814443).length < 2 ^ (prefixWord ++ tailWord_814443).sum := by decide
  have hdescent : baseEnd_814443 < baseStart_814443 := by decide
  rcases family_descends (prefixWord ++ tailWord_814443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814490 : List Nat := [3, 1, 1, 4, 1, 1, 1, 4, 1, 5]
def baseStart_814490 : Nat := 118140960795 + 814490 * 2 ^ 59
def prefixEnd_814490 : Nat := 4983230072969 + 3 ^ 40 * 814490 * 2
def baseEnd_814490 : Nat := 278816572187082358552823

theorem tailTrace_814490 : CollatzResearch.WordTrace tailWord_814490 prefixEnd_814490 278816572187082358552823 := by
  unfold tailWord_814490
  simp only [CollatzResearch.WordTrace]
  refine ⟨7426722704812327165622231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19804593879499539108325949 7426722704812327165622231)
  ·
    refine ⟨11140084057218490748433347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7426722704812327165622231 11140084057218490748433347)
    ·
      refine ⟨16710126085827736122650021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11140084057218490748433347 16710126085827736122650021)
      ·
        refine ⟨3133148641092700522996879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16710126085827736122650021 3133148641092700522996879)
        ·
          refine ⟨4699722961639050784495319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3133148641092700522996879 4699722961639050784495319)
          ·
            refine ⟨7049584442458576176742979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4699722961639050784495319 7049584442458576176742979)
            ·
              refine ⟨10574376663687864265114469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7049584442458576176742979 10574376663687864265114469)
              ·
                refine ⟨1982695624441474549708963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10574376663687864265114469 1982695624441474549708963)
                ·
                  refine ⟨2974043436662211824563445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1982695624441474549708963 2974043436662211824563445)
                  ·
                    refine ⟨278816572187082358552823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2974043436662211824563445 278816572187082358552823)
                    ·
                      rfl

theorem cell22_814490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_814490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814490 prefixEnd_814490 := by exact prefixLift 814490
  have htrace : WordTrace (prefixWord ++ tailWord_814490) baseStart_814490 baseEnd_814490 := by
    simpa [prefixWord, tailWord_814490, baseEnd_814490] using wordTrace_append hprefix tailTrace_814490
  have hstable : (prefixWord ++ tailWord_814490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814490).length < 2 ^ (prefixWord ++ tailWord_814490).sum := by decide
  have hdescent : baseEnd_814490 < baseStart_814490 := by decide
  rcases family_descends (prefixWord ++ tailWord_814490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814509 : List Nat := [1, 5, 2, 2, 1, 1, 2, 4, 4]
def baseStart_814509 : Nat := 118140960795 + 814509 * 2 ^ 59
def prefixEnd_814509 : Nat := 4983230072969 + 3 ^ 40 * 814509 * 2
def baseEnd_814509 : Nat := 92941025425124214109255

theorem tailTrace_814509 : CollatzResearch.WordTrace tailWord_814509 prefixEnd_814509 92941025425124214109255 := by
  unfold tailWord_814509
  simp only [CollatzResearch.WordTrace]
  refine ⟨29707583806180474907430581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19805055870786983271620387 29707583806180474907430581)
  ·
    refine ⟨2785085981829419522571617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29707583806180474907430581 2785085981829419522571617)
    ·
      refine ⟨2088814486372064641928713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2785085981829419522571617 2088814486372064641928713)
      ·
        refine ⟨1566610864779048481446535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2088814486372064641928713 1566610864779048481446535)
        ·
          refine ⟨2349916297168572722169803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1566610864779048481446535 2349916297168572722169803)
          ·
            refine ⟨3524874445752859083254705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2349916297168572722169803 3524874445752859083254705)
            ·
              refine ⟨2643655834314644312441029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3524874445752859083254705 2643655834314644312441029)
              ·
                refine ⟨495685468933995808582693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2643655834314644312441029 495685468933995808582693)
                ·
                  refine ⟨92941025425124214109255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 495685468933995808582693 92941025425124214109255)
                  ·
                    rfl

theorem cell22_814509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_814509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814509 prefixEnd_814509 := by exact prefixLift 814509
  have htrace : WordTrace (prefixWord ++ tailWord_814509) baseStart_814509 baseEnd_814509 := by
    simpa [prefixWord, tailWord_814509, baseEnd_814509] using wordTrace_append hprefix tailTrace_814509
  have hstable : (prefixWord ++ tailWord_814509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814509).length < 2 ^ (prefixWord ++ tailWord_814509).sum := by decide
  have hdescent : baseEnd_814509 < baseStart_814509 := by decide
  rcases family_descends (prefixWord ++ tailWord_814509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814524 : List Nat := [2, 2, 2, 4, 2, 2, 1, 1, 1, 5]
def baseStart_814524 : Nat := 118140960795 + 814524 * 2 ^ 59
def prefixEnd_814524 : Nat := 4983230072969 + 3 ^ 40 * 814524 * 2
def baseEnd_814524 : Nat := 278828211081917603202719

theorem tailTrace_814524 : CollatzResearch.WordTrace tailWord_814524 prefixEnd_814524 278828211081917603202719 := by
  unfold tailWord_814524
  simp only [CollatzResearch.WordTrace]
  refine ⟨14854065450563066234613313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19805420600750754979484417 14854065450563066234613313)
  ·
    refine ⟨11140549087922299675959985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14854065450563066234613313 11140549087922299675959985)
    ·
      refine ⟨8355411815941724756969989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11140549087922299675959985 8355411815941724756969989)
      ·
        refine ⟨1566639715489073391931873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8355411815941724756969989 1566639715489073391931873)
        ·
          refine ⟨1174979786616805043948905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1566639715489073391931873 1174979786616805043948905)
          ·
            refine ⟨881234839962603782961679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1174979786616805043948905 881234839962603782961679)
            ·
              refine ⟨1321852259943905674442519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 881234839962603782961679 1321852259943905674442519)
              ·
                refine ⟨1982778389915858511663779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1321852259943905674442519 1982778389915858511663779)
                ·
                  refine ⟨2974167584873787767495669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1982778389915858511663779 2974167584873787767495669)
                  ·
                    refine ⟨278828211081917603202719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2974167584873787767495669 278828211081917603202719)
                    ·
                      rfl

theorem cell22_814524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_814524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814524 prefixEnd_814524 := by exact prefixLift 814524
  have htrace : WordTrace (prefixWord ++ tailWord_814524) baseStart_814524 baseEnd_814524 := by
    simpa [prefixWord, tailWord_814524, baseEnd_814524] using wordTrace_append hprefix tailTrace_814524
  have hstable : (prefixWord ++ tailWord_814524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814524).length < 2 ^ (prefixWord ++ tailWord_814524).sum := by decide
  have hdescent : baseEnd_814524 < baseStart_814524 := by decide
  rcases family_descends (prefixWord ++ tailWord_814524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814640 : List Nat := [2, 1, 1, 1, 2, 3, 1, 4, 1, 6]
def baseStart_814640 : Nat := 118140960795 + 814640 * 2 ^ 59
def prefixEnd_814640 : Nat := 4983230072969 + 3 ^ 40 * 814640 * 2
def baseEnd_814640 : Nat := 278867920252531967302363

theorem tailTrace_814640 : CollatzResearch.WordTrace tailWord_814640 prefixEnd_814640 278867920252531967302363 := by
  unfold tailWord_814640
  simp only [CollatzResearch.WordTrace]
  refine ⟨14856180884352942140224687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19808241179137256186966249 14856180884352942140224687)
  ·
    refine ⟨22284271326529413210337031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14856180884352942140224687 22284271326529413210337031)
    ·
      refine ⟨33426406989794119815505547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22284271326529413210337031 33426406989794119815505547)
      ·
        refine ⟨50139610484691179723258321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33426406989794119815505547 50139610484691179723258321)
        ·
          refine ⟨37604707863518384792443741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50139610484691179723258321 37604707863518384792443741)
          ·
            refine ⟨14101765448819394297166403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37604707863518384792443741 14101765448819394297166403)
            ·
              refine ⟨21152648173229091445749605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14101765448819394297166403 21152648173229091445749605)
              ·
                refine ⟨3966121532480454646078051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21152648173229091445749605 3966121532480454646078051)
                ·
                  refine ⟨5949182298720681969117077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3966121532480454646078051 5949182298720681969117077)
                  ·
                    refine ⟨278867920252531967302363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5949182298720681969117077 278867920252531967302363)
                    ·
                      rfl

theorem cell22_814640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 1, 6].length) (baseStart_814640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814640 prefixEnd_814640 := by exact prefixLift 814640
  have htrace : WordTrace (prefixWord ++ tailWord_814640) baseStart_814640 baseEnd_814640 := by
    simpa [prefixWord, tailWord_814640, baseEnd_814640] using wordTrace_append hprefix tailTrace_814640
  have hstable : (prefixWord ++ tailWord_814640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814640).length < 2 ^ (prefixWord ++ tailWord_814640).sum := by decide
  have hdescent : baseEnd_814640 < baseStart_814640 := by decide
  rcases family_descends (prefixWord ++ tailWord_814640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814642 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 6, 3]
def baseStart_814642 : Nat := 118140960795 + 814642 * 2 ^ 59
def prefixEnd_814642 : Nat := 4983230072969 + 3 ^ 40 * 814642 * 2
def baseEnd_814642 : Nat := 278868604893404628752357

theorem tailTrace_814642 : CollatzResearch.WordTrace tailWord_814642 prefixEnd_814642 278868604893404628752357 := by
  unfold tailWord_814642
  simp only [CollatzResearch.WordTrace]
  refine ⟨7428108678674659655505545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19808289809799092414681453 7428108678674659655505545)
  ·
    refine ⟨5571081509005994741629159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7428108678674659655505545 5571081509005994741629159)
    ·
      refine ⟨8356622263508992112443739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5571081509005994741629159 8356622263508992112443739)
      ·
        refine ⟨12534933395263488168665609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8356622263508992112443739 12534933395263488168665609)
        ·
          refine ⟨9401200046447616126499207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12534933395263488168665609 9401200046447616126499207)
          ·
            refine ⟨14101800069671424189748811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9401200046447616126499207 14101800069671424189748811)
            ·
              refine ⟨21152700104507136284623217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14101800069671424189748811 21152700104507136284623217)
              ·
                refine ⟨15864525078380352213467413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21152700104507136284623217 15864525078380352213467413)
                ·
                  refine ⟨743649613049079010006285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15864525078380352213467413 743649613049079010006285)
                  ·
                    refine ⟨278868604893404628752357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 743649613049079010006285 278868604893404628752357)
                    ·
                      rfl

theorem cell22_814642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_814642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814642 prefixEnd_814642 := by exact prefixLift 814642
  have htrace : WordTrace (prefixWord ++ tailWord_814642) baseStart_814642 baseEnd_814642 := by
    simpa [prefixWord, tailWord_814642, baseEnd_814642] using wordTrace_append hprefix tailTrace_814642
  have hstable : (prefixWord ++ tailWord_814642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814642).length < 2 ^ (prefixWord ++ tailWord_814642).sum := by decide
  have hdescent : baseEnd_814642 < baseStart_814642 := by decide
  rcases family_descends (prefixWord ++ tailWord_814642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814657 : List Nat := [1, 2, 5, 1, 1, 1, 3, 1, 1, 6]
def baseStart_814657 : Nat := 118140960795 + 814657 * 2 ^ 59
def prefixEnd_814657 : Nat := 4983230072969 + 3 ^ 40 * 814657 * 2
def baseEnd_814657 : Nat := 278873739699949589627311

theorem tailTrace_814657 : CollatzResearch.WordTrace tailWord_814657 prefixEnd_814657 278873739699949589627311 := by
  unfold tailWord_814657
  simp only [CollatzResearch.WordTrace]
  refine ⟨29712981809644296183818225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19808654539762864122545483 29712981809644296183818225)
  ·
    refine ⟨22284736357233222137863669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29712981809644296183818225 22284736357233222137863669)
    ·
      refine ⟨2089194033490614575424719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22284736357233222137863669 2089194033490614575424719)
      ·
        refine ⟨3133791050235921863137079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2089194033490614575424719 3133791050235921863137079)
        ·
          refine ⟨4700686575353882794705619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3133791050235921863137079 4700686575353882794705619)
          ·
            refine ⟨7051029863030824192058429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4700686575353882794705619 7051029863030824192058429)
            ·
              refine ⟨2644136198636559072021911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7051029863030824192058429 2644136198636559072021911)
              ·
                refine ⟨3966204297954838608032867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2644136198636559072021911 3966204297954838608032867)
                ·
                  refine ⟨5949306446932257912049301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3966204297954838608032867 5949306446932257912049301)
                  ·
                    refine ⟨278873739699949589627311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5949306446932257912049301 278873739699949589627311)
                    ·
                      rfl

theorem cell22_814657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_814657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814657 prefixEnd_814657 := by exact prefixLift 814657
  have htrace : WordTrace (prefixWord ++ tailWord_814657) baseStart_814657 baseEnd_814657 := by
    simpa [prefixWord, tailWord_814657, baseEnd_814657] using wordTrace_append hprefix tailTrace_814657
  have hstable : (prefixWord ++ tailWord_814657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814657).length < 2 ^ (prefixWord ++ tailWord_814657).sum := by decide
  have hdescent : baseEnd_814657 < baseStart_814657 := by decide
  rcases family_descends (prefixWord ++ tailWord_814657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814663 : List Nat := [1, 1, 4, 1, 6, 1, 2, 1, 1, 4]
def baseStart_814663 : Nat := 118140960795 + 814663 * 2 ^ 59
def prefixEnd_814663 : Nat := 4983230072969 + 3 ^ 40 * 814663 * 2
def baseEnd_814663 : Nat := 278875793622567573977293

theorem tailTrace_814663 : CollatzResearch.WordTrace tailWord_814663 prefixEnd_814663 278875793622567573977293 := by
  unfold tailWord_814663
  simp only [CollatzResearch.WordTrace]
  refine ⟨29713200647622559208536643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19808800431748372805691095 29713200647622559208536643)
  ·
    refine ⟨44569800971433838812804965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29713200647622559208536643 44569800971433838812804965)
    ·
      refine ⟨8356837682143844777400931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44569800971433838812804965 8356837682143844777400931)
      ·
        refine ⟨12535256523215767166101397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8356837682143844777400931 12535256523215767166101397)
        ·
          refine ⟨587590149525739085911003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12535256523215767166101397 587590149525739085911003)
          ·
            refine ⟨881385224288608628866505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587590149525739085911003 881385224288608628866505)
            ·
              refine ⟨661038918216456471649879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 881385224288608628866505 661038918216456471649879)
              ·
                refine ⟨991558377324684707474819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 661038918216456471649879 991558377324684707474819)
                ·
                  refine ⟨1487337565987027061212229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 991558377324684707474819 1487337565987027061212229)
                  ·
                    refine ⟨278875793622567573977293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1487337565987027061212229 278875793622567573977293)
                    ·
                      rfl

theorem cell22_814663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_814663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814663 prefixEnd_814663 := by exact prefixLift 814663
  have htrace : WordTrace (prefixWord ++ tailWord_814663) baseStart_814663 baseEnd_814663 := by
    simpa [prefixWord, tailWord_814663, baseEnd_814663] using wordTrace_append hprefix tailTrace_814663
  have hstable : (prefixWord ++ tailWord_814663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814663).length < 2 ^ (prefixWord ++ tailWord_814663).sum := by decide
  have hdescent : baseEnd_814663 < baseStart_814663 := by decide
  rcases family_descends (prefixWord ++ tailWord_814663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814678 : List Nat := [5, 2, 2, 2, 1, 1, 2, 1, 6]
def baseStart_814678 : Nat := 118140960795 + 814678 * 2 ^ 59
def prefixEnd_814678 : Nat := 4983230072969 + 3 ^ 40 * 814678 * 2
def baseEnd_814678 : Nat := 92960309476370844950749

theorem tailTrace_814678 : CollatzResearch.WordTrace tailWord_814678 prefixEnd_814678 92960309476370844950749 := by
  unfold tailWord_814678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1857109233910513548145793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19809165161712144513555125 1857109233910513548145793)
  ·
    refine ⟨1392831925432885161109345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1857109233910513548145793 1392831925432885161109345)
    ·
      refine ⟨1044623944074663870832009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1392831925432885161109345 1044623944074663870832009)
      ·
        refine ⟨783467958055997903124007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1044623944074663870832009 783467958055997903124007)
        ·
          refine ⟨1175201937083996854686011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 783467958055997903124007 1175201937083996854686011)
          ·
            refine ⟨1762802905625995282029017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1175201937083996854686011 1762802905625995282029017)
            ·
              refine ⟨1322102179219496461521763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1762802905625995282029017 1322102179219496461521763)
              ·
                refine ⟨1983153268829244692282645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1322102179219496461521763 1983153268829244692282645)
                ·
                  refine ⟨92960309476370844950749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1983153268829244692282645 92960309476370844950749)
                  ·
                    rfl

theorem cell22_814678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_814678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814678 prefixEnd_814678 := by exact prefixLift 814678
  have htrace : WordTrace (prefixWord ++ tailWord_814678) baseStart_814678 baseEnd_814678 := by
    simpa [prefixWord, tailWord_814678, baseEnd_814678] using wordTrace_append hprefix tailTrace_814678
  have hstable : (prefixWord ++ tailWord_814678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814678).length < 2 ^ (prefixWord ++ tailWord_814678).sum := by decide
  have hdescent : baseEnd_814678 < baseStart_814678 := by decide
  rcases family_descends (prefixWord ++ tailWord_814678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814704 : List Nat := [2, 1, 1, 1, 6, 1, 2, 2, 3, 3]
def baseStart_814704 : Nat := 118140960795 + 814704 * 2 ^ 59
def prefixEnd_814704 : Nat := 4983230072969 + 3 ^ 40 * 814704 * 2
def baseEnd_814704 : Nat := 278889828760457133702167

theorem tailTrace_814704 : CollatzResearch.WordTrace tailWord_814704 prefixEnd_814704 278889828760457133702167 := by
  unfold tailWord_814704
  simp only [CollatzResearch.WordTrace]
  refine ⟨14857348020237011605389583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19809797360316015473852777 14857348020237011605389583)
  ·
    refine ⟨22286022030355517408084375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14857348020237011605389583 22286022030355517408084375)
    ·
      refine ⟨33429033045533276112126563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22286022030355517408084375 33429033045533276112126563)
      ·
        refine ⟨50143549568299914168189845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33429033045533276112126563 50143549568299914168189845)
        ·
          refine ⟨2350478886014058476633899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50143549568299914168189845 2350478886014058476633899)
          ·
            refine ⟨3525718329021087714950849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2350478886014058476633899 3525718329021087714950849)
            ·
              refine ⟨2644288746765815786213137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3525718329021087714950849 2644288746765815786213137)
              ·
                refine ⟨1983216560074361839659853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2644288746765815786213137 1983216560074361839659853)
                ·
                  refine ⟨743706210027885689872445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1983216560074361839659853 743706210027885689872445)
                  ·
                    refine ⟨278889828760457133702167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 743706210027885689872445 278889828760457133702167)
                    ·
                      rfl

theorem cell22_814704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 3, 3].length) (baseStart_814704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814704 prefixEnd_814704 := by exact prefixLift 814704
  have htrace : WordTrace (prefixWord ++ tailWord_814704) baseStart_814704 baseEnd_814704 := by
    simpa [prefixWord, tailWord_814704, baseEnd_814704] using wordTrace_append hprefix tailTrace_814704
  have hstable : (prefixWord ++ tailWord_814704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814704).length < 2 ^ (prefixWord ++ tailWord_814704).sum := by decide
  have hdescent : baseEnd_814704 < baseStart_814704 := by decide
  rcases family_descends (prefixWord ++ tailWord_814704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814717 : List Nat := [1, 4, 1, 1, 4, 1, 1, 2, 7]
def baseStart_814717 : Nat := 118140960795 + 814717 * 2 ^ 59
def prefixEnd_814717 : Nat := 4983230072969 + 3 ^ 40 * 814717 * 2
def baseEnd_814717 : Nat := 92964759642043144375709

theorem tailTrace_814717 : CollatzResearch.WordTrace tailWord_814717 prefixEnd_814717 92964759642043144375709 := by
  unfold tailWord_814717
  simp only [CollatzResearch.WordTrace]
  refine ⟨29715170189426926431002405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19810113459617950954001603 29715170189426926431002405)
  ·
    refine ⟨5571594410517548705812951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29715170189426926431002405 5571594410517548705812951)
    ·
      refine ⟨8357391615776323058719427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5571594410517548705812951 8357391615776323058719427)
      ·
        refine ⟨12536087423664484588079141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8357391615776323058719427 12536087423664484588079141)
        ·
          refine ⟨2350516391937090860264839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12536087423664484588079141 2350516391937090860264839)
          ·
            refine ⟨3525774587905636290397259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2350516391937090860264839 3525774587905636290397259)
            ·
              refine ⟨5288661881858454435595889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3525774587905636290397259 5288661881858454435595889)
              ·
                refine ⟨3966496411393840826696917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5288661881858454435595889 3966496411393840826696917)
                ·
                  refine ⟨92964759642043144375709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3966496411393840826696917 92964759642043144375709)
                  ·
                    rfl

theorem cell22_814717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_814717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814717 prefixEnd_814717 := by exact prefixLift 814717
  have htrace : WordTrace (prefixWord ++ tailWord_814717) baseStart_814717 baseEnd_814717 := by
    simpa [prefixWord, tailWord_814717, baseEnd_814717] using wordTrace_append hprefix tailTrace_814717
  have hstable : (prefixWord ++ tailWord_814717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814717).length < 2 ^ (prefixWord ++ tailWord_814717).sum := by decide
  have hdescent : baseEnd_814717 < baseStart_814717 := by decide
  rcases family_descends (prefixWord ++ tailWord_814717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814738 : List Nat := [3, 2, 3, 1, 3, 2, 1, 1, 3, 3]
def baseStart_814738 : Nat := 118140960795 + 814738 * 2 ^ 59
def prefixEnd_814738 : Nat := 4983230072969 + 3 ^ 40 * 814738 * 2
def baseEnd_814738 : Nat := 278901467655292378352063

theorem tailTrace_814738 : CollatzResearch.WordTrace tailWord_814738 prefixEnd_814738 278901467655292378352063 := by
  unfold tailWord_814738
  simp only [CollatzResearch.WordTrace]
  refine ⟨7428984030587711754379217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19810624081567231345011245 7428984030587711754379217)
  ·
    refine ⟨5571738022940783815784413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7428984030587711754379217 5571738022940783815784413)
    ·
      refine ⟨2089401758602793930919155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5571738022940783815784413 2089401758602793930919155)
      ·
        refine ⟨3134102637904190896378733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2089401758602793930919155 3134102637904190896378733)
        ·
          refine ⟨1175288489214071586142025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3134102637904190896378733 1175288489214071586142025)
          ·
            refine ⟨881466366910553689606519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1175288489214071586142025 881466366910553689606519)
            ·
              refine ⟨1322199550365830534409779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 881466366910553689606519 1322199550365830534409779)
              ·
                refine ⟨1983299325548745801614669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1322199550365830534409779 1983299325548745801614669)
                ·
                  refine ⟨743737247080779675605501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1983299325548745801614669 743737247080779675605501)
                  ·
                    refine ⟨278901467655292378352063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 743737247080779675605501 278901467655292378352063)
                    ·
                      rfl

theorem cell22_814738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_814738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814738 prefixEnd_814738 := by exact prefixLift 814738
  have htrace : WordTrace (prefixWord ++ tailWord_814738) baseStart_814738 baseEnd_814738 := by
    simpa [prefixWord, tailWord_814738, baseEnd_814738] using wordTrace_append hprefix tailTrace_814738
  have hstable : (prefixWord ++ tailWord_814738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814738).length < 2 ^ (prefixWord ++ tailWord_814738).sum := by decide
  have hdescent : baseEnd_814738 < baseStart_814738 := by decide
  rcases family_descends (prefixWord ++ tailWord_814738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814751 : List Nat := [1, 1, 2, 7, 1, 1, 1, 3, 5]
def baseStart_814751 : Nat := 118140960795 + 814751 * 2 ^ 59
def prefixEnd_814751 : Nat := 4983230072969 + 3 ^ 40 * 814751 * 2
def baseEnd_814751 : Nat := 92968639273654892592341

theorem tailTrace_814751 : CollatzResearch.WordTrace tailWord_814751 prefixEnd_814751 92968639273654892592341 := by
  unfold tailWord_814751
  simp only [CollatzResearch.WordTrace]
  refine ⟨29716410271303750237740107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19810940180869166825160071 29716410271303750237740107)
  ·
    refine ⟨44574615406955625356610161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29716410271303750237740107 44574615406955625356610161)
    ·
      refine ⟨33430961555216719017457621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44574615406955625356610161 33430961555216719017457621)
      ·
        refine ⟨783538161450391851971663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 33430961555216719017457621 783538161450391851971663)
        ·
          refine ⟨1175307242175587777957495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 783538161450391851971663 1175307242175587777957495)
          ·
            refine ⟨1762960863263381666936243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1175307242175587777957495 1762960863263381666936243)
            ·
              refine ⟨2644441294895072500404365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1762960863263381666936243 2644441294895072500404365)
              ·
                refine ⟨991665485585652187651637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2644441294895072500404365 991665485585652187651637)
                ·
                  refine ⟨92968639273654892592341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 991665485585652187651637 92968639273654892592341)
                  ·
                    rfl

theorem cell22_814751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 5].length) (baseStart_814751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814751 prefixEnd_814751 := by exact prefixLift 814751
  have htrace : WordTrace (prefixWord ++ tailWord_814751) baseStart_814751 baseEnd_814751 := by
    simpa [prefixWord, tailWord_814751, baseEnd_814751] using wordTrace_append hprefix tailTrace_814751
  have hstable : (prefixWord ++ tailWord_814751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814751).length < 2 ^ (prefixWord ++ tailWord_814751).sum := by decide
  have hdescent : baseEnd_814751 < baseStart_814751 := by decide
  rcases family_descends (prefixWord ++ tailWord_814751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814777 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 3, 5]
def baseStart_814777 : Nat := 118140960795 + 814777 * 2 ^ 59
def prefixEnd_814777 : Nat := 4983230072969 + 3 ^ 40 * 814777 * 2
def baseEnd_814777 : Nat := 278914818152309276626943

theorem tailTrace_814777 : CollatzResearch.WordTrace tailWord_814777 prefixEnd_814777 278914818152309276626943 := by
  unfold tailWord_814777
  simp only [CollatzResearch.WordTrace]
  refine ⟨29717358569209556678186585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19811572379473037785457723 29717358569209556678186585)
  ·
    refine ⟨22288018926907167508639939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29717358569209556678186585 22288018926907167508639939)
    ·
      refine ⟨33432028390360751262959909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22288018926907167508639939 33432028390360751262959909)
      ·
        refine ⟨6268505323192640861804983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33432028390360751262959909 6268505323192640861804983)
        ·
          refine ⟨9402757984788961292707475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6268505323192640861804983 9402757984788961292707475)
          ·
            refine ⟨14104136977183441939061213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9402757984788961292707475 14104136977183441939061213)
            ·
              refine ⟨5289051366443790727147955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14104136977183441939061213 5289051366443790727147955)
              ·
                refine ⟨7933577049665686090721933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5289051366443790727147955 7933577049665686090721933)
                ·
                  refine ⟨2975091393624632284020725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7933577049665686090721933 2975091393624632284020725)
                  ·
                    refine ⟨278914818152309276626943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2975091393624632284020725 278914818152309276626943)
                    ·
                      rfl

theorem cell22_814777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 5].length) (baseStart_814777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814777 prefixEnd_814777 := by exact prefixLift 814777
  have htrace : WordTrace (prefixWord ++ tailWord_814777) baseStart_814777 baseEnd_814777 := by
    simpa [prefixWord, tailWord_814777, baseEnd_814777] using wordTrace_append hprefix tailTrace_814777
  have hstable : (prefixWord ++ tailWord_814777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814777).length < 2 ^ (prefixWord ++ tailWord_814777).sum := by decide
  have hdescent : baseEnd_814777 < baseStart_814777 := by decide
  rcases family_descends (prefixWord ++ tailWord_814777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814781 : List Nat := [1, 4, 1, 2, 1, 2, 5, 1, 1, 4]
def baseStart_814781 : Nat := 118140960795 + 814781 * 2 ^ 59
def prefixEnd_814781 : Nat := 4983230072969 + 3 ^ 40 * 814781 * 2
def baseEnd_814781 : Nat := 278916187434054599526931

theorem tailTrace_814781 : CollatzResearch.WordTrace tailWord_814781 prefixEnd_814781 278916187434054599526931 := by
  unfold tailWord_814781
  simp only [CollatzResearch.WordTrace]
  refine ⟨29717504461195065361332197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19811669640796710240888131 29717504461195065361332197)
  ·
    refine ⟨5572032086474074755249787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29717504461195065361332197 5572032086474074755249787)
    ·
      refine ⟨8358048129711112132874681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5572032086474074755249787 8358048129711112132874681)
      ·
        refine ⟨6268536097283334099656011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8358048129711112132874681 6268536097283334099656011)
        ·
          refine ⟨9402804145925001149484017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6268536097283334099656011 9402804145925001149484017)
          ·
            refine ⟨7052103109443750862113013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9402804145925001149484017 7052103109443750862113013)
            ·
              refine ⟨661134666510351643323095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7052103109443750862113013 661134666510351643323095)
              ·
                refine ⟨991701999765527464984643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 661134666510351643323095 991701999765527464984643)
                ·
                  refine ⟨1487552999648291197476965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 991701999765527464984643 1487552999648291197476965)
                  ·
                    refine ⟨278916187434054599526931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1487552999648291197476965 278916187434054599526931)
                    ·
                      rfl

theorem cell22_814781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_814781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814781 prefixEnd_814781 := by exact prefixLift 814781
  have htrace : WordTrace (prefixWord ++ tailWord_814781) baseStart_814781 baseEnd_814781 := by
    simpa [prefixWord, tailWord_814781, baseEnd_814781] using wordTrace_append hprefix tailTrace_814781
  have hstable : (prefixWord ++ tailWord_814781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814781).length < 2 ^ (prefixWord ++ tailWord_814781).sum := by decide
  have hdescent : baseEnd_814781 < baseStart_814781 := by decide
  rcases family_descends (prefixWord ++ tailWord_814781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814856 : List Nat := [2, 1, 3, 2, 2, 1, 4, 1, 3, 3]
def baseStart_814856 : Nat := 118140960795 + 814856 * 2 ^ 59
def prefixEnd_814856 : Nat := 4983230072969 + 3 ^ 40 * 814856 * 2
def baseEnd_814856 : Nat := 278941861466779403901701

theorem tailTrace_814856 : CollatzResearch.WordTrace tailWord_814856 prefixEnd_814856 278941861466779403901701 := by
  unfold tailWord_814856
  simp only [CollatzResearch.WordTrace]
  refine ⟨14860119967961676585156211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19813493290615568780208281 14860119967961676585156211)
  ·
    refine ⟨22290179951942514877734317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14860119967961676585156211 22290179951942514877734317)
    ·
      refine ⟨8358817481978443079150369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22290179951942514877734317 8358817481978443079150369)
      ·
        refine ⟨6269113111483832309362777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8358817481978443079150369 6269113111483832309362777)
        ·
          refine ⟨4701834833612874232022083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6269113111483832309362777 4701834833612874232022083)
          ·
            refine ⟨7052752250419311348033125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4701834833612874232022083 7052752250419311348033125)
            ·
              refine ⟨1322391046953620877756211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7052752250419311348033125 1322391046953620877756211)
              ·
                refine ⟨1983586570430431316634317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1322391046953620877756211 1983586570430431316634317)
                ·
                  refine ⟨743844963911411743737869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1983586570430431316634317 743844963911411743737869)
                  ·
                    refine ⟨278941861466779403901701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 743844963911411743737869 278941861466779403901701)
                    ·
                      rfl

theorem cell22_814856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_814856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814856 prefixEnd_814856 := by exact prefixLift 814856
  have htrace : WordTrace (prefixWord ++ tailWord_814856) baseStart_814856 baseEnd_814856 := by
    simpa [prefixWord, tailWord_814856, baseEnd_814856] using wordTrace_append hprefix tailTrace_814856
  have hstable : (prefixWord ++ tailWord_814856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814856).length < 2 ^ (prefixWord ++ tailWord_814856).sum := by decide
  have hdescent : baseEnd_814856 < baseStart_814856 := by decide
  rcases family_descends (prefixWord ++ tailWord_814856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814867 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 1, 7]
def baseStart_814867 : Nat := 118140960795 + 814867 * 2 ^ 59
def prefixEnd_814867 : Nat := 4983230072969 + 3 ^ 40 * 814867 * 2
def baseEnd_814867 : Nat := 278945626991579041876667

theorem tailTrace_814867 : CollatzResearch.WordTrace tailWord_814867 prefixEnd_814867 278945626991579041876667 := by
  unfold tailWord_814867
  simp only [CollatzResearch.WordTrace]
  refine ⟨29720641138883502048962855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19813760759255668032641903 29720641138883502048962855)
  ·
    refine ⟨44580961708325253073444283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29720641138883502048962855 44580961708325253073444283)
    ·
      refine ⟨66871442562487879610166425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44580961708325253073444283 66871442562487879610166425)
      ·
        refine ⟨50153581921865909707624819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66871442562487879610166425 50153581921865909707624819)
        ·
          refine ⟨75230372882798864561437229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50153581921865909707624819 75230372882798864561437229)
          ·
            refine ⟨28211389831049574210538961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75230372882798864561437229 28211389831049574210538961)
            ·
              refine ⟨21158542373287180657904221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28211389831049574210538961 21158542373287180657904221)
              ·
                refine ⟨7934453389982692746714083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21158542373287180657904221 7934453389982692746714083)
                ·
                  refine ⟨11901680084974039120071125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7934453389982692746714083 11901680084974039120071125)
                  ·
                    refine ⟨278945626991579041876667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11901680084974039120071125 278945626991579041876667)
                    ·
                      rfl

theorem cell22_814867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 7].length) (baseStart_814867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814867 prefixEnd_814867 := by exact prefixLift 814867
  have htrace : WordTrace (prefixWord ++ tailWord_814867) baseStart_814867 baseEnd_814867 := by
    simpa [prefixWord, tailWord_814867, baseEnd_814867] using wordTrace_append hprefix tailTrace_814867
  have hstable : (prefixWord ++ tailWord_814867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814867).length < 2 ^ (prefixWord ++ tailWord_814867).sum := by decide
  have hdescent : baseEnd_814867 < baseStart_814867 := by decide
  rcases family_descends (prefixWord ++ tailWord_814867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814933 : List Nat := [1, 3, 2, 2, 2, 4, 1, 2, 1, 4]
def baseStart_814933 : Nat := 118140960795 + 814933 * 2 ^ 59
def prefixEnd_814933 : Nat := 4983230072969 + 3 ^ 40 * 814933 * 2
def baseEnd_814933 : Nat := 278968220140376869726465

theorem tailTrace_814933 : CollatzResearch.WordTrace tailWord_814933 prefixEnd_814933 278968220140376869726465 := by
  unfold tailWord_814933
  simp only [CollatzResearch.WordTrace]
  refine ⟨29723048356644395320865453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19815365571096263547243635 29723048356644395320865453)
  ·
    refine ⟨11146143133741648245324545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29723048356644395320865453 11146143133741648245324545)
    ·
      refine ⟨8359607350306236183993409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11146143133741648245324545 8359607350306236183993409)
      ·
        refine ⟨6269705512729677137995057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8359607350306236183993409 6269705512729677137995057)
        ·
          refine ⟨4702279134547257853496293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6269705512729677137995057 4702279134547257853496293)
          ·
            refine ⟨881677337727610847530555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4702279134547257853496293 881677337727610847530555)
            ·
              refine ⟨1322516006591416271295833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 881677337727610847530555 1322516006591416271295833)
              ·
                refine ⟨991887004943562203471875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1322516006591416271295833 991887004943562203471875)
                ·
                  refine ⟨1487830507415343305207813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 991887004943562203471875 1487830507415343305207813)
                  ·
                    refine ⟨278968220140376869726465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1487830507415343305207813 278968220140376869726465)
                    ·
                      rfl

theorem cell22_814933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_814933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814933 prefixEnd_814933 := by exact prefixLift 814933
  have htrace : WordTrace (prefixWord ++ tailWord_814933) baseStart_814933 baseEnd_814933 := by
    simpa [prefixWord, tailWord_814933, baseEnd_814933] using wordTrace_append hprefix tailTrace_814933
  have hstable : (prefixWord ++ tailWord_814933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814933).length < 2 ^ (prefixWord ++ tailWord_814933).sum := by decide
  have hdescent : baseEnd_814933 < baseStart_814933 := by decide
  rcases family_descends (prefixWord ++ tailWord_814933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814946 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_814946 : Nat := 118140960795 + 814946 * 2 ^ 59
def prefixEnd_814946 : Nat := 4983230072969 + 3 ^ 40 * 814946 * 2
def baseEnd_814946 : Nat := 278972670306049169151425

theorem tailTrace_814946 : CollatzResearch.WordTrace tailWord_814946 prefixEnd_814946 278972670306049169151425 := by
  unfold tailWord_814946
  simp only [CollatzResearch.WordTrace]
  refine ⟨7430880626399324635272173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19815681670398199027392461 7430880626399324635272173)
  ·
    refine ⟨2786580234899746738227065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7430880626399324635272173 2786580234899746738227065)
    ·
      refine ⟨2089935176174810053670299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2786580234899746738227065 2089935176174810053670299)
      ·
        refine ⟨3134902764262215080505449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2089935176174810053670299 3134902764262215080505449)
        ·
          refine ⟨2351177073196661310379087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3134902764262215080505449 2351177073196661310379087)
          ·
            refine ⟨3526765609794991965568631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2351177073196661310379087 3526765609794991965568631)
            ·
              refine ⟨5290148414692487948352947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3526765609794991965568631 5290148414692487948352947)
              ·
                refine ⟨7935222622038731922529421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5290148414692487948352947 7935222622038731922529421)
                ·
                  refine ⟨2975708483264524470948533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7935222622038731922529421 2975708483264524470948533)
                  ·
                    refine ⟨278972670306049169151425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2975708483264524470948533 278972670306049169151425)
                    ·
                      rfl

theorem cell22_814946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_814946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_814946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_814946 prefixEnd_814946 := by exact prefixLift 814946
  have htrace : WordTrace (prefixWord ++ tailWord_814946) baseStart_814946 baseEnd_814946 := by
    simpa [prefixWord, tailWord_814946, baseEnd_814946] using wordTrace_append hprefix tailTrace_814946
  have hstable : (prefixWord ++ tailWord_814946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814946).length < 2 ^ (prefixWord ++ tailWord_814946).sum := by decide
  have hdescent : baseEnd_814946 < baseStart_814946 := by decide
  rcases family_descends (prefixWord ++ tailWord_814946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815025 : List Nat := [1, 2, 2, 4, 2, 1, 2, 4, 1, 3]
def baseStart_815025 : Nat := 118140960795 + 815025 * 2 ^ 59
def prefixEnd_815025 : Nat := 4983230072969 + 3 ^ 40 * 815025 * 2
def baseEnd_815025 : Nat := 278999713620519296426183

theorem tailTrace_815025 : CollatzResearch.WordTrace tailWord_815025 prefixEnd_815025 278999713620519296426183 := by
  unfold tailWord_815025
  simp only [CollatzResearch.WordTrace]
  refine ⟨29726403872311095033214529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19817602581540730022143019 29726403872311095033214529)
  ·
    refine ⟨22294802904233321274910897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29726403872311095033214529 22294802904233321274910897)
    ·
      refine ⟨16721102178174990956183173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22294802904233321274910897 16721102178174990956183173)
      ·
        refine ⟨3135206658407810804284345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16721102178174990956183173 3135206658407810804284345)
        ·
          refine ⟨2351404993805858103213259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3135206658407810804284345 2351404993805858103213259)
          ·
            refine ⟨3527107490708787154819889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2351404993805858103213259 3527107490708787154819889)
            ·
              refine ⟨2645330618031590366114917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3527107490708787154819889 2645330618031590366114917)
              ·
                refine ⟨495999490880923193646547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2645330618031590366114917 495999490880923193646547)
                ·
                  refine ⟨743999236321384790469821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 495999490880923193646547 743999236321384790469821)
                  ·
                    refine ⟨278999713620519296426183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 743999236321384790469821 278999713620519296426183)
                    ·
                      rfl

theorem cell22_815025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4, 1, 3].length) (baseStart_815025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_815025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_815025 prefixEnd_815025 := by exact prefixLift 815025
  have htrace : WordTrace (prefixWord ++ tailWord_815025) baseStart_815025 baseEnd_815025 := by
    simpa [prefixWord, tailWord_815025, baseEnd_815025] using wordTrace_append hprefix tailTrace_815025
  have hstable : (prefixWord ++ tailWord_815025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815025).length < 2 ^ (prefixWord ++ tailWord_815025).sum := by decide
  have hdescent : baseEnd_815025 < baseStart_815025 := by decide
  rcases family_descends (prefixWord ++ tailWord_815025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815034 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 2, 8]
def baseStart_815034 : Nat := 118140960795 + 815034 * 2 ^ 59
def prefixEnd_815034 : Nat := 4983230072969 + 3 ^ 40 * 815034 * 2
def baseEnd_815034 : Nat := 279002794504446272951155

theorem tailTrace_815034 : CollatzResearch.WordTrace tailWord_815034 prefixEnd_815034 279002794504446272951155 := by
  unfold tailWord_815034
  simp only [CollatzResearch.WordTrace]
  refine ⟨7431683032319622392573039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19817821419518993046861437 7431683032319622392573039)
  ·
    refine ⟨11147524548479433588859559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7431683032319622392573039 11147524548479433588859559)
    ·
      refine ⟨16721286822719150383289339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11147524548479433588859559 16721286822719150383289339)
      ·
        refine ⟨25081930234078725574934009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16721286822719150383289339 25081930234078725574934009)
        ·
          refine ⟨18811447675559044181200507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25081930234078725574934009 18811447675559044181200507)
          ·
            refine ⟨28217171513338566271800761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18811447675559044181200507 28217171513338566271800761)
            ·
              refine ⟨21162878635003924703850571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28217171513338566271800761 21162878635003924703850571)
              ·
                refine ⟨31744317952505887055775857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21162878635003924703850571 31744317952505887055775857)
                ·
                  refine ⟨23808238464379415291831893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31744317952505887055775857 23808238464379415291831893)
                  ·
                    refine ⟨279002794504446272951155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23808238464379415291831893 279002794504446272951155)
                    ·
                      rfl

theorem cell22_815034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_815034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_815034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_815034 prefixEnd_815034 := by exact prefixLift 815034
  have htrace : WordTrace (prefixWord ++ tailWord_815034) baseStart_815034 baseEnd_815034 := by
    simpa [prefixWord, tailWord_815034, baseEnd_815034] using wordTrace_append hprefix tailTrace_815034
  have hstable : (prefixWord ++ tailWord_815034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815034).length < 2 ^ (prefixWord ++ tailWord_815034).sum := by decide
  have hdescent : baseEnd_815034 < baseStart_815034 := by decide
  rcases family_descends (prefixWord ++ tailWord_815034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815102 : List Nat := [4, 2, 2, 2, 1, 3, 1, 2, 1, 4]
def baseStart_815102 : Nat := 118140960795 + 815102 * 2 ^ 59
def prefixEnd_815102 : Nat := 4983230072969 + 3 ^ 40 * 815102 * 2
def baseEnd_815102 : Nat := 279026072294116762250947

theorem tailTrace_815102 : CollatzResearch.WordTrace tailWord_815102 prefixEnd_815102 279026072294116762250947 := by
  unfold tailWord_815102
  simp only [CollatzResearch.WordTrace]
  refine ⟨3716151536629017147970945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19819474862021424789178373 3716151536629017147970945)
  ·
    refine ⟨2787113652471762860978209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3716151536629017147970945 2787113652471762860978209)
    ·
      refine ⟨2090335239353822145733657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2787113652471762860978209 2090335239353822145733657)
      ·
        refine ⟨1567751429515366609300243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2090335239353822145733657 1567751429515366609300243)
        ·
          refine ⟨2351627144273049913950365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1567751429515366609300243 2351627144273049913950365)
          ·
            refine ⟨881860179102393717731387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2351627144273049913950365 881860179102393717731387)
            ·
              refine ⟨1322790268653590576597081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 881860179102393717731387 1322790268653590576597081)
              ·
                refine ⟨992092701490192932447811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1322790268653590576597081 992092701490192932447811)
                ·
                  refine ⟨1488139052235289398671717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 992092701490192932447811 1488139052235289398671717)
                  ·
                    refine ⟨279026072294116762250947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1488139052235289398671717 279026072294116762250947)
                    ·
                      rfl

theorem cell22_815102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_815102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_815102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_815102 prefixEnd_815102 := by exact prefixLift 815102
  have htrace : WordTrace (prefixWord ++ tailWord_815102) baseStart_815102 baseEnd_815102 := by
    simpa [prefixWord, tailWord_815102, baseEnd_815102] using wordTrace_append hprefix tailTrace_815102
  have hstable : (prefixWord ++ tailWord_815102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815102).length < 2 ^ (prefixWord ++ tailWord_815102).sum := by decide
  have hdescent : baseEnd_815102 < baseStart_815102 := by decide
  rcases family_descends (prefixWord ++ tailWord_815102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815111 : List Nat := [1, 1, 4, 3, 1, 2, 2, 8]
def baseStart_815111 : Nat := 118140960795 + 815111 * 2 ^ 59
def prefixEnd_815111 : Nat := 4983230072969 + 3 ^ 40 * 815111 * 2
def baseEnd_815111 : Nat := 31003239242004859863991

theorem tailTrace_815111 : CollatzResearch.WordTrace tailWord_815111 prefixEnd_815111 31003239242004859863991 := by
  unfold tailWord_815111
  simp only [CollatzResearch.WordTrace]
  refine ⟨29729540549999531720845187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19819693699999687813896791 29729540549999531720845187)
  ·
    refine ⟨44594310824999297581267781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29729540549999531720845187 44594310824999297581267781)
    ·
      refine ⟨8361433279687368296487709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44594310824999297581267781 8361433279687368296487709)
      ·
        refine ⟨3135537479882763111182891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8361433279687368296487709 3135537479882763111182891)
        ·
          refine ⟨4703306219824144666774337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3135537479882763111182891 4703306219824144666774337)
          ·
            refine ⟨3527479664868108500080753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4703306219824144666774337 3527479664868108500080753)
            ·
              refine ⟨2645609748651081375060565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3527479664868108500080753 2645609748651081375060565)
              ·
                refine ⟨31003239242004859863991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2645609748651081375060565 31003239242004859863991)
                ·
                  rfl

theorem cell22_815111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 8].length) (baseStart_815111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_815111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_815111 prefixEnd_815111 := by exact prefixLift 815111
  have htrace : WordTrace (prefixWord ++ tailWord_815111) baseStart_815111 baseEnd_815111 := by
    simpa [prefixWord, tailWord_815111, baseEnd_815111] using wordTrace_append hprefix tailTrace_815111
  have hstable : (prefixWord ++ tailWord_815111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815111).length < 2 ^ (prefixWord ++ tailWord_815111).sum := by decide
  have hdescent : baseEnd_815111 < baseStart_815111 := by decide
  rcases family_descends (prefixWord ++ tailWord_815111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815141 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 2, 6]
def baseStart_815141 : Nat := 118140960795 + 815141 * 2 ^ 59
def prefixEnd_815141 : Nat := 4983230072969 + 3 ^ 40 * 815141 * 2
def baseEnd_815141 : Nat := 279039422791133660525827

theorem tailTrace_815141 : CollatzResearch.WordTrace tailWord_815141 prefixEnd_815141 279039422791133660525827 := by
  unfold tailWord_815141
  simp only [CollatzResearch.WordTrace]
  refine ⟨29730634739890846844437277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19820423159927231229624851 29730634739890846844437277)
  ·
    refine ⟨11148988027459067566663979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29730634739890846844437277 11148988027459067566663979)
    ·
      refine ⟨16723482041188601349995969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11148988027459067566663979 16723482041188601349995969)
      ·
        refine ⟨12542611530891451012496977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16723482041188601349995969 12542611530891451012496977)
        ·
          refine ⟨9406958648168588259372733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12542611530891451012496977 9406958648168588259372733)
          ·
            refine ⟨3527609493063220597264775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9406958648168588259372733 3527609493063220597264775)
            ·
              refine ⟨5291414239594830895897163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3527609493063220597264775 5291414239594830895897163)
              ·
                refine ⟨7937121359392246343845745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5291414239594830895897163 7937121359392246343845745)
                ·
                  refine ⟨5952841019544184757884309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7937121359392246343845745 5952841019544184757884309)
                  ·
                    refine ⟨279039422791133660525827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5952841019544184757884309 279039422791133660525827)
                    ·
                      rfl

theorem cell22_815141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_815141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_815141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_815141 prefixEnd_815141 := by exact prefixLift 815141
  have htrace : WordTrace (prefixWord ++ tailWord_815141) baseStart_815141 baseEnd_815141 := by
    simpa [prefixWord, tailWord_815141, baseEnd_815141] using wordTrace_append hprefix tailTrace_815141
  have hstable : (prefixWord ++ tailWord_815141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815141).length < 2 ^ (prefixWord ++ tailWord_815141).sum := by decide
  have hdescent : baseEnd_815141 < baseStart_815141 := by decide
  rcases family_descends (prefixWord ++ tailWord_815141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815158 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_815158 : Nat := 118140960795 + 815158 * 2 ^ 59
def prefixEnd_815158 : Nat := 4983230072969 + 3 ^ 40 * 815158 * 2
def baseEnd_815158 : Nat := 279045242238551282850775

theorem tailTrace_815158 : CollatzResearch.WordTrace tailWord_815158 prefixEnd_815158 279045242238551282850775 := by
  unfold tailWord_815158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1858203423801828671737883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19820836520552839165204085 1858203423801828671737883)
  ·
    refine ⟨2787305135702743007606825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1858203423801828671737883 2787305135702743007606825)
    ·
      refine ⟨2090478851777057255705119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2787305135702743007606825 2090478851777057255705119)
      ·
        refine ⟨3135718277665585883557679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2090478851777057255705119 3135718277665585883557679)
        ·
          refine ⟨4703577416498378825336519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3135718277665585883557679 4703577416498378825336519)
          ·
            refine ⟨7055366124747568238004779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4703577416498378825336519 7055366124747568238004779)
            ·
              refine ⟨10583049187121352357007169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7055366124747568238004779 10583049187121352357007169)
              ·
                refine ⟨7937286890341014267755377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10583049187121352357007169 7937286890341014267755377)
                ·
                  refine ⟨5952965167755760700816533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7937286890341014267755377 5952965167755760700816533)
                  ·
                    refine ⟨279045242238551282850775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5952965167755760700816533 279045242238551282850775)
                    ·
                      rfl

theorem cell22_815158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_815158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_815158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_815158 prefixEnd_815158 := by exact prefixLift 815158
  have htrace : WordTrace (prefixWord ++ tailWord_815158) baseStart_815158 baseEnd_815158 := by
    simpa [prefixWord, tailWord_815158, baseEnd_815158] using wordTrace_append hprefix tailTrace_815158
  have hstable : (prefixWord ++ tailWord_815158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815158).length < 2 ^ (prefixWord ++ tailWord_815158).sum := by decide
  have hdescent : baseEnd_815158 < baseStart_815158 := by decide
  rcases family_descends (prefixWord ++ tailWord_815158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815160 : List Nat := [2, 1, 2, 1, 6, 1, 1, 2, 3, 3]
def baseStart_815160 : Nat := 118140960795 + 815160 * 2 ^ 59
def prefixEnd_815160 : Nat := 4983230072969 + 3 ^ 40 * 815160 * 2
def baseEnd_815160 : Nat := 279045926879423944300769

theorem tailTrace_815160 : CollatzResearch.WordTrace tailWord_815160 prefixEnd_815160 279045926879423944300769 := by
  unfold tailWord_815160
  simp only [CollatzResearch.WordTrace]
  refine ⟨14865663863411006544689467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19820885151214675392919289 14865663863411006544689467)
  ·
    refine ⟨22298495795116509817034201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14865663863411006544689467 22298495795116509817034201)
    ·
      refine ⟨16723871846337382362775651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22298495795116509817034201 16723871846337382362775651)
      ·
        refine ⟨25085807769506073544163477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16723871846337382362775651 25085807769506073544163477)
        ·
          refine ⟨1175897239195597197382663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25085807769506073544163477 1175897239195597197382663)
          ·
            refine ⟨1763845858793395796073995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1175897239195597197382663 1763845858793395796073995)
            ·
              refine ⟨2645768788190093694110993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1763845858793395796073995 2645768788190093694110993)
              ·
                refine ⟨1984326591142570270583245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2645768788190093694110993 1984326591142570270583245)
                ·
                  refine ⟨744122471678463851468717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1984326591142570270583245 744122471678463851468717)
                  ·
                    refine ⟨279045926879423944300769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 744122471678463851468717 279045926879423944300769)
                    ·
                      rfl

theorem cell22_815160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 3, 3].length) (baseStart_815160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_815160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_815160 prefixEnd_815160 := by exact prefixLift 815160
  have htrace : WordTrace (prefixWord ++ tailWord_815160) baseStart_815160 baseEnd_815160 := by
    simpa [prefixWord, tailWord_815160, baseEnd_815160] using wordTrace_append hprefix tailTrace_815160
  have hstable : (prefixWord ++ tailWord_815160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815160).length < 2 ^ (prefixWord ++ tailWord_815160).sum := by decide
  have hdescent : baseEnd_815160 < baseStart_815160 := by decide
  rcases family_descends (prefixWord ++ tailWord_815160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815218 : List Nat := [3, 2, 1, 2, 2, 2, 2, 2, 6]
def baseStart_815218 : Nat := 118140960795 + 815218 * 2 ^ 59
def prefixEnd_815218 : Nat := 4983230072969 + 3 ^ 40 * 815218 * 2
def baseEnd_815218 : Nat := 93021927154910375450197

theorem tailTrace_815218 : CollatzResearch.WordTrace tailWord_815218 prefixEnd_815218 93021927154910375450197 := by
  unfold tailWord_815218
  simp only [CollatzResearch.WordTrace]
  refine ⟨7433360790152972248747577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19822295440407925996660205 7433360790152972248747577)
  ·
    refine ⟨5575020592614729186560683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7433360790152972248747577 5575020592614729186560683)
    ·
      refine ⟨8362530888922093779841025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5575020592614729186560683 8362530888922093779841025)
      ·
        refine ⟨6271898166691570334880769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8362530888922093779841025 6271898166691570334880769)
        ·
          refine ⟨4703923625018677751160577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6271898166691570334880769 4703923625018677751160577)
          ·
            refine ⟨3527942718764008313370433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4703923625018677751160577 3527942718764008313370433)
            ·
              refine ⟨2645957039073006235027825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3527942718764008313370433 2645957039073006235027825)
              ·
                refine ⟨1984467779304754676270869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2645957039073006235027825 1984467779304754676270869)
                ·
                  refine ⟨93021927154910375450197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1984467779304754676270869 93021927154910375450197)
                  ·
                    rfl

theorem cell22_815218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_815218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_815218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_815218 prefixEnd_815218 := by exact prefixLift 815218
  have htrace : WordTrace (prefixWord ++ tailWord_815218) baseStart_815218 baseEnd_815218 := by
    simpa [prefixWord, tailWord_815218, baseEnd_815218] using wordTrace_append hprefix tailTrace_815218
  have hstable : (prefixWord ++ tailWord_815218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815218).length < 2 ^ (prefixWord ++ tailWord_815218).sum := by decide
  have hdescent : baseEnd_815218 < baseStart_815218 := by decide
  rcases family_descends (prefixWord ++ tailWord_815218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815235 : List Nat := [1, 1, 1, 3, 3, 3, 3, 3, 4]
def baseStart_815235 : Nat := 118140960795 + 815235 * 2 ^ 59
def prefixEnd_815235 : Nat := 4983230072969 + 3 ^ 40 * 815235 * 2
def baseEnd_815235 : Nat := 93023866970716249558513

theorem tailTrace_815235 : CollatzResearch.WordTrace tailWord_815235 prefixEnd_815235 93023866970716249558513 := by
  unfold tailWord_815235
  simp only [CollatzResearch.WordTrace]
  refine ⟨29734063201550300898359159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19822708801033533932239439 29734063201550300898359159)
  ·
    refine ⟨44601094802325451347538739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29734063201550300898359159 44601094802325451347538739)
    ·
      refine ⟨66901642203488177021308109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44601094802325451347538739 66901642203488177021308109)
      ·
        refine ⟨25088115826308066382990541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66901642203488177021308109 25088115826308066382990541)
        ·
          refine ⟨9408043434865524893621453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25088115826308066382990541 9408043434865524893621453)
          ·
            refine ⟨3528016288074571835108045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9408043434865524893621453 3528016288074571835108045)
            ·
              refine ⟨1323006108027964438165517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3528016288074571835108045 1323006108027964438165517)
              ·
                refine ⟨496127290510486664312069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1323006108027964438165517 496127290510486664312069)
                ·
                  refine ⟨93023866970716249558513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 496127290510486664312069 93023866970716249558513)
                  ·
                    rfl

theorem cell22_815235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 4].length) (baseStart_815235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_815235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_815235 prefixEnd_815235 := by exact prefixLift 815235
  have htrace : WordTrace (prefixWord ++ tailWord_815235) baseStart_815235 baseEnd_815235 := by
    simpa [prefixWord, tailWord_815235, baseEnd_815235] using wordTrace_append hprefix tailTrace_815235
  have hstable : (prefixWord ++ tailWord_815235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815235).length < 2 ^ (prefixWord ++ tailWord_815235).sum := by decide
  have hdescent : baseEnd_815235 < baseStart_815235 := by decide
  rcases family_descends (prefixWord ++ tailWord_815235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815248 : List Nat := [2, 1, 1, 1, 1, 1, 7, 2, 2, 4]
def baseStart_815248 : Nat := 118140960795 + 815248 * 2 ^ 59
def prefixEnd_815248 : Nat := 4983230072969 + 3 ^ 40 * 815248 * 2
def baseEnd_815248 : Nat := 279076051077821048100499

theorem tailTrace_815248 : CollatzResearch.WordTrace tailWord_815248 prefixEnd_815248 279076051077821048100499 := by
  unfold tailWord_815248
  simp only [CollatzResearch.WordTrace]
  refine ⟨14867268675251602059291199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19823024900335469412388265 14867268675251602059291199)
  ·
    refine ⟨22300903012877403088936799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14867268675251602059291199 22300903012877403088936799)
    ·
      refine ⟨33451354519316104633405199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22300903012877403088936799 33451354519316104633405199)
      ·
        refine ⟨50177031778974156950107799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33451354519316104633405199 50177031778974156950107799)
        ·
          refine ⟨75265547668461235425161699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50177031778974156950107799 75265547668461235425161699)
          ·
            refine ⟨112898321502691853137742549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75265547668461235425161699 112898321502691853137742549)
            ·
              refine ⟨2646054410219340307915841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 112898321502691853137742549 2646054410219340307915841)
              ·
                refine ⟨1984540807664505230936881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2646054410219340307915841 1984540807664505230936881)
                ·
                  refine ⟨1488405605748378923202661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1984540807664505230936881 1488405605748378923202661)
                  ·
                    refine ⟨279076051077821048100499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1488405605748378923202661 279076051077821048100499)
                    ·
                      rfl

theorem cell22_815248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 2, 4].length) (baseStart_815248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_815248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_815248 prefixEnd_815248 := by exact prefixLift 815248
  have htrace : WordTrace (prefixWord ++ tailWord_815248) baseStart_815248 baseEnd_815248 := by
    simpa [prefixWord, tailWord_815248, baseEnd_815248] using wordTrace_append hprefix tailTrace_815248
  have hstable : (prefixWord ++ tailWord_815248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815248).length < 2 ^ (prefixWord ++ tailWord_815248).sum := by decide
  have hdescent : baseEnd_815248 < baseStart_815248 := by decide
  rcases family_descends (prefixWord ++ tailWord_815248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815250 : List Nat := [3, 2, 3, 1, 1, 1, 1, 3, 4, 3]
def baseStart_815250 : Nat := 118140960795 + 815250 * 2 ^ 59
def prefixEnd_815250 : Nat := 4983230072969 + 3 ^ 40 * 815250 * 2
def baseEnd_815250 : Nat := 279076735718693709550493

theorem tailTrace_815250 : CollatzResearch.WordTrace tailWord_815250 prefixEnd_815250 279076735718693709550493 := by
  unfold tailWord_815250
  simp only [CollatzResearch.WordTrace]
  refine ⟨7433652574123989615038801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19823073530997305640103469 7433652574123989615038801)
  ·
    refine ⟨5575239430592992211279101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7433652574123989615038801 5575239430592992211279101)
    ·
      refine ⟨2090714786472372079229663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5575239430592992211279101 2090714786472372079229663)
      ·
        refine ⟨3136072179708558118844495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2090714786472372079229663 3136072179708558118844495)
        ·
          refine ⟨4704108269562837178266743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3136072179708558118844495 4704108269562837178266743)
          ·
            refine ⟨7056162404344255767400115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4704108269562837178266743 7056162404344255767400115)
            ·
              refine ⟨10584243606516383651100173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7056162404344255767400115 10584243606516383651100173)
              ·
                refine ⟨3969091352443643869162565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10584243606516383651100173 3969091352443643869162565)
                ·
                  refine ⟨744204628583183225467981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3969091352443643869162565 744204628583183225467981)
                  ·
                    refine ⟨279076735718693709550493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 744204628583183225467981 279076735718693709550493)
                    ·
                      rfl

theorem cell22_815250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_815250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_815250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_815250 prefixEnd_815250 := by exact prefixLift 815250
  have htrace : WordTrace (prefixWord ++ tailWord_815250) baseStart_815250 baseEnd_815250 := by
    simpa [prefixWord, tailWord_815250, baseEnd_815250] using wordTrace_append hprefix tailTrace_815250
  have hstable : (prefixWord ++ tailWord_815250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815250).length < 2 ^ (prefixWord ++ tailWord_815250).sum := by decide
  have hdescent : baseEnd_815250 < baseStart_815250 := by decide
  rcases family_descends (prefixWord ++ tailWord_815250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815263 : List Nat := [1, 1, 2, 6, 1, 1, 1, 9]
def baseStart_815263 : Nat := 118140960795 + 815263 * 2 ^ 59
def prefixEnd_815263 : Nat := 4983230072969 + 3 ^ 40 * 815263 * 2
def baseEnd_815263 : Nat := 31009020653818445441717

theorem tailTrace_815263 : CollatzResearch.WordTrace tailWord_815263 prefixEnd_815263 31009020653818445441717 := by
  unfold tailWord_815263
  simp only [CollatzResearch.WordTrace]
  refine ⟨29735084445448861680378443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19823389630299241120252295 29735084445448861680378443)
  ·
    refine ⟨44602626668173292520567665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29735084445448861680378443 44602626668173292520567665)
    ·
      refine ⟨33451970001129969390425749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44602626668173292520567665 33451970001129969390425749)
      ·
        refine ⟨1568061093802967315176207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33451970001129969390425749 1568061093802967315176207)
        ·
          refine ⟨2352091640704450972764311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1568061093802967315176207 2352091640704450972764311)
          ·
            refine ⟨3528137461056676459146467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2352091640704450972764311 3528137461056676459146467)
            ·
              refine ⟨5292206191585014688719701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3528137461056676459146467 5292206191585014688719701)
              ·
                refine ⟨31009020653818445441717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5292206191585014688719701 31009020653818445441717)
                ·
                  rfl

theorem cell22_815263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 9].length) (baseStart_815263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_815263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_815263 prefixEnd_815263 := by exact prefixLift 815263
  have htrace : WordTrace (prefixWord ++ tailWord_815263) baseStart_815263 baseEnd_815263 := by
    simpa [prefixWord, tailWord_815263, baseEnd_815263] using wordTrace_append hprefix tailTrace_815263
  have hstable : (prefixWord ++ tailWord_815263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815263).length < 2 ^ (prefixWord ++ tailWord_815263).sum := by decide
  have hdescent : baseEnd_815263 < baseStart_815263 := by decide
  rcases family_descends (prefixWord ++ tailWord_815263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815389 : List Nat := [1, 4, 2, 3, 2, 1, 2, 2, 1, 4]
def baseStart_815389 : Nat := 118140960795 + 815389 * 2 ^ 59
def prefixEnd_815389 : Nat := 4983230072969 + 3 ^ 40 * 815389 * 2
def baseEnd_815389 : Nat := 279124318259343680325067

theorem tailTrace_815389 : CollatzResearch.WordTrace tailWord_815389 prefixEnd_815389 279124318259343680325067 := by
  unfold tailWord_815389
  simp only [CollatzResearch.WordTrace]
  refine ⟨29739680042992385199465221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19826453361994923466310147 29739680042992385199465221)
  ·
    refine ⟨5576190008061072224899729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29739680042992385199465221 5576190008061072224899729)
    ·
      refine ⟨4182142506045804168674797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5576190008061072224899729 4182142506045804168674797)
      ·
        refine ⟨1568303439767176563253049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4182142506045804168674797 1568303439767176563253049)
        ·
          refine ⟨1176227579825382422439787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1568303439767176563253049 1176227579825382422439787)
          ·
            refine ⟨1764341369738073633659681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1176227579825382422439787 1764341369738073633659681)
            ·
              refine ⟨1323256027303555225244761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1764341369738073633659681 1323256027303555225244761)
              ·
                refine ⟨992442020477666418933571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1323256027303555225244761 992442020477666418933571)
                ·
                  refine ⟨1488663030716499628400357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 992442020477666418933571 1488663030716499628400357)
                  ·
                    refine ⟨279124318259343680325067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1488663030716499628400357 279124318259343680325067)
                    ·
                      rfl

theorem cell22_815389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_815389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_815389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_815389 prefixEnd_815389 := by exact prefixLift 815389
  have htrace : WordTrace (prefixWord ++ tailWord_815389) baseStart_815389 baseEnd_815389 := by
    simpa [prefixWord, tailWord_815389, baseEnd_815389] using wordTrace_append hprefix tailTrace_815389
  have hstable : (prefixWord ++ tailWord_815389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815389).length < 2 ^ (prefixWord ++ tailWord_815389).sum := by decide
  have hdescent : baseEnd_815389 < baseStart_815389 := by decide
  rcases family_descends (prefixWord ++ tailWord_815389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815417 : List Nat := [1, 2, 1, 6, 1, 2, 1, 2, 2, 4]
def baseStart_815417 : Nat := 118140960795 + 815417 * 2 ^ 59
def prefixEnd_815417 : Nat := 4983230072969 + 3 ^ 40 * 815417 * 2
def baseEnd_815417 : Nat := 279133903231560940624981

theorem tailTrace_815417 : CollatzResearch.WordTrace tailWord_815417 prefixEnd_815417 279133903231560940624981 := by
  unfold tailWord_815417
  simp only [CollatzResearch.WordTrace]
  refine ⟨29740701286890945981484505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19827134191260630654323003 29740701286890945981484505)
  ·
    refine ⟨22305525965168209486113379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29740701286890945981484505 22305525965168209486113379)
    ·
      refine ⟨33458288947752314229170069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22305525965168209486113379 33458288947752314229170069)
      ·
        refine ⟨1568357294425889729492347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33458288947752314229170069 1568357294425889729492347)
        ·
          refine ⟨2352535941638834594238521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1568357294425889729492347 2352535941638834594238521)
          ·
            refine ⟨1764401956229125945678891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2352535941638834594238521 1764401956229125945678891)
            ·
              refine ⟨2646602934343688918518337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1764401956229125945678891 2646602934343688918518337)
              ·
                refine ⟨1984952200757766688888753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2646602934343688918518337 1984952200757766688888753)
                ·
                  refine ⟨1488714150568325016666565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1984952200757766688888753 1488714150568325016666565)
                  ·
                    refine ⟨279133903231560940624981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1488714150568325016666565 279133903231560940624981)
                    ·
                      rfl

theorem cell22_815417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 4].length) (baseStart_815417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_815417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_815417 prefixEnd_815417 := by exact prefixLift 815417
  have htrace : WordTrace (prefixWord ++ tailWord_815417) baseStart_815417 baseEnd_815417 := by
    simpa [prefixWord, tailWord_815417, baseEnd_815417] using wordTrace_append hprefix tailTrace_815417
  have hstable : (prefixWord ++ tailWord_815417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815417).length < 2 ^ (prefixWord ++ tailWord_815417).sum := by decide
  have hdescent : baseEnd_815417 < baseStart_815417 := by decide
  rcases family_descends (prefixWord ++ tailWord_815417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815443 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 9]
def baseStart_815443 : Nat := 118140960795 + 815443 * 2 ^ 59
def prefixEnd_815443 : Nat := 4983230072969 + 3 ^ 40 * 815443 * 2
def baseEnd_815443 : Nat := 93047601187635179824967

theorem tailTrace_815443 : CollatzResearch.WordTrace tailWord_815443 prefixEnd_815443 93047601187635179824967 := by
  unfold tailWord_815443
  simp only [CollatzResearch.WordTrace]
  refine ⟨29741649584796752421930983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19827766389864501614620655 29741649584796752421930983)
  ·
    refine ⟨44612474377195128632896475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29741649584796752421930983 44612474377195128632896475)
    ·
      refine ⟨66918711565792692949344713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44612474377195128632896475 66918711565792692949344713)
      ·
        refine ⟨50189033674344519712008535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66918711565792692949344713 50189033674344519712008535)
        ·
          refine ⟨75283550511516779568012803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50189033674344519712008535 75283550511516779568012803)
          ·
            refine ⟨112925325767275169352019205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75283550511516779568012803 112925325767275169352019205)
            ·
              refine ⟨21173498581364094253503601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112925325767275169352019205 21173498581364094253503601)
              ·
                refine ⟨15880123936023070690127701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21173498581364094253503601 15880123936023070690127701)
                ·
                  refine ⟨93047601187635179824967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15880123936023070690127701 93047601187635179824967)
                  ·
                    rfl

theorem cell22_815443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 9].length) (baseStart_815443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_815443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_815443 prefixEnd_815443 := by exact prefixLift 815443
  have htrace : WordTrace (prefixWord ++ tailWord_815443) baseStart_815443 baseEnd_815443 := by
    simpa [prefixWord, tailWord_815443, baseEnd_815443] using wordTrace_append hprefix tailTrace_815443
  have hstable : (prefixWord ++ tailWord_815443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815443).length < 2 ^ (prefixWord ++ tailWord_815443).sum := by decide
  have hdescent : baseEnd_815443 < baseStart_815443 := by decide
  rcases family_descends (prefixWord ++ tailWord_815443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815477 : List Nat := [1, 3, 4, 1, 2, 1, 1, 4, 5]
def baseStart_815477 : Nat := 118140960795 + 815477 * 2 ^ 59
def prefixEnd_815477 : Nat := 4983230072969 + 3 ^ 40 * 815477 * 2
def baseEnd_815477 : Nat := 93051480819246928041599

theorem tailTrace_815477 : CollatzResearch.WordTrace tailWord_815477 prefixEnd_815477 93051480819246928041599 := by
  unfold tailWord_815477
  simp only [CollatzResearch.WordTrace]
  refine ⟨29742889666673576228668685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19828593111115717485779123 29742889666673576228668685)
  ·
    refine ⟨11153583625002591085750757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29742889666673576228668685 11153583625002591085750757)
    ·
      refine ⟨2091296929687985828578267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11153583625002591085750757 2091296929687985828578267)
      ·
        refine ⟨3136945394531978742867401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2091296929687985828578267 3136945394531978742867401)
        ·
          refine ⟨2352709045898984057150551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3136945394531978742867401 2352709045898984057150551)
          ·
            refine ⟨3529063568848476085725827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2352709045898984057150551 3529063568848476085725827)
            ·
              refine ⟨5293595353272714128588741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3529063568848476085725827 5293595353272714128588741)
              ·
                refine ⟨992549128738633899110389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5293595353272714128588741 992549128738633899110389)
                ·
                  refine ⟨93051480819246928041599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 992549128738633899110389 93051480819246928041599)
                  ·
                    rfl

theorem cell22_815477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 5].length) (baseStart_815477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_815477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_815477 prefixEnd_815477 := by exact prefixLift 815477
  have htrace : WordTrace (prefixWord ++ tailWord_815477) baseStart_815477 baseEnd_815477 := by
    simpa [prefixWord, tailWord_815477, baseEnd_815477] using wordTrace_append hprefix tailTrace_815477
  have hstable : (prefixWord ++ tailWord_815477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815477).length < 2 ^ (prefixWord ++ tailWord_815477).sum := by decide
  have hdescent : baseEnd_815477 < baseStart_815477 := by decide
  rcases family_descends (prefixWord ++ tailWord_815477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815524 : List Nat := [2, 3, 1, 2, 1, 1, 6, 1, 1, 4]
def baseStart_815524 : Nat := 118140960795 + 815524 * 2 ^ 59
def prefixEnd_815524 : Nat := 4983230072969 + 3 ^ 40 * 815524 * 2
def baseEnd_815524 : Nat := 279170531518248328199653

theorem tailTrace_815524 : CollatzResearch.WordTrace tailWord_815524 prefixEnd_815524 279170531518248328199653 := by
  unfold tailWord_815524
  simp only [CollatzResearch.WordTrace]
  refine ⟨14872301948751651627814813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19829735931668868837086417 14872301948751651627814813)
  ·
    refine ⟨5577113230781869360430555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14872301948751651627814813 5577113230781869360430555)
    ·
      refine ⟨8365669846172804040645833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5577113230781869360430555 8365669846172804040645833)
      ·
        refine ⟨6274252384629603030484375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8365669846172804040645833 6274252384629603030484375)
        ·
          refine ⟨9411378576944404545726563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6274252384629603030484375 9411378576944404545726563)
          ·
            refine ⟨14117067865416606818589845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9411378576944404545726563 14117067865416606818589845)
            ·
              refine ⟨661737556191403444621399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14117067865416606818589845 661737556191403444621399)
              ·
                refine ⟨992606334287105166932099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 661737556191403444621399 992606334287105166932099)
                ·
                  refine ⟨1488909501430657750398149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 992606334287105166932099 1488909501430657750398149)
                  ·
                    refine ⟨279170531518248328199653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1488909501430657750398149 279170531518248328199653)
                    ·
                      rfl

theorem cell22_815524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_815524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_815524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_815524 prefixEnd_815524 := by exact prefixLift 815524
  have htrace : WordTrace (prefixWord ++ tailWord_815524) baseStart_815524 baseEnd_815524 := by
    simpa [prefixWord, tailWord_815524, baseEnd_815524] using wordTrace_append hprefix tailTrace_815524
  have hstable : (prefixWord ++ tailWord_815524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815524).length < 2 ^ (prefixWord ++ tailWord_815524).sum := by decide
  have hdescent : baseEnd_815524 < baseStart_815524 := by decide
  rcases family_descends (prefixWord ++ tailWord_815524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815595 : List Nat := [1, 1, 1, 1, 2, 3, 3, 3, 7]
def baseStart_815595 : Nat := 118140960795 + 815595 * 2 ^ 59
def prefixEnd_815595 : Nat := 4983230072969 + 3 ^ 40 * 815595 * 2
def baseEnd_815595 : Nat := 93064945423075936558145

theorem tailTrace_815595 : CollatzResearch.WordTrace tailWord_815595 prefixEnd_815595 93064945423075936558145 := by
  unfold tailWord_815595
  simp only [CollatzResearch.WordTrace]
  refine ⟨29747193480246082381464239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19831462320164054920976159 29747193480246082381464239)
  ·
    refine ⟨44620790220369123572196359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29747193480246082381464239 44620790220369123572196359)
    ·
      refine ⟨66931185330553685358294539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44620790220369123572196359 66931185330553685358294539)
      ·
        refine ⟨100396777995830528037441809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66931185330553685358294539 100396777995830528037441809)
        ·
          refine ⟨75297583496872896028081357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100396777995830528037441809 75297583496872896028081357)
          ·
            refine ⟨28236593811327336010530509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75297583496872896028081357 28236593811327336010530509)
            ·
              refine ⟨10588722679247751003948941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28236593811327336010530509 10588722679247751003948941)
              ·
                refine ⟨3970771004717906626480853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10588722679247751003948941 3970771004717906626480853)
                ·
                  refine ⟨93064945423075936558145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3970771004717906626480853 93064945423075936558145)
                  ·
                    rfl

theorem cell22_815595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 7].length) (baseStart_815595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_815595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_815595 prefixEnd_815595 := by exact prefixLift 815595
  have htrace : WordTrace (prefixWord ++ tailWord_815595) baseStart_815595 baseEnd_815595 := by
    simpa [prefixWord, tailWord_815595, baseEnd_815595] using wordTrace_append hprefix tailTrace_815595
  have hstable : (prefixWord ++ tailWord_815595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815595).length < 2 ^ (prefixWord ++ tailWord_815595).sum := by decide
  have hdescent : baseEnd_815595 < baseStart_815595 := by decide
  rcases family_descends (prefixWord ++ tailWord_815595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815605 : List Nat := [1, 3, 5, 1, 2, 2, 2, 1, 2, 3]
def baseStart_815605 : Nat := 118140960795 + 815605 * 2 ^ 59
def prefixEnd_815605 : Nat := 4983230072969 + 3 ^ 40 * 815605 * 2
def baseEnd_815605 : Nat := 279198259473591116924405

theorem tailTrace_815605 : CollatzResearch.WordTrace tailWord_815605 prefixEnd_815605 279198259473591116924405 := by
  unfold tailWord_815605
  simp only [CollatzResearch.WordTrace]
  refine ⟨29747558210209854089328269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19831705473473236059552179 29747558210209854089328269)
  ·
    refine ⟨11155334328828695283498101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29747558210209854089328269 11155334328828695283498101)
    ·
      refine ⟨1045812593327690182827947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11155334328828695283498101 1045812593327690182827947)
      ·
        refine ⟨1568718889991535274241921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1045812593327690182827947 1568718889991535274241921)
        ·
          refine ⟨1176539167493651455681441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1568718889991535274241921 1176539167493651455681441)
          ·
            refine ⟨882404375620238591761081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1176539167493651455681441 882404375620238591761081)
            ·
              refine ⟨661803281715178943820811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 882404375620238591761081 661803281715178943820811)
              ·
                refine ⟨992704922572768415731217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 661803281715178943820811 992704922572768415731217)
                ·
                  refine ⟨744528691929576311798413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 992704922572768415731217 744528691929576311798413)
                  ·
                    refine ⟨279198259473591116924405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 744528691929576311798413 279198259473591116924405)
                    ·
                      rfl

theorem cell22_815605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_815605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_815605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_815605 prefixEnd_815605 := by exact prefixLift 815605
  have htrace : WordTrace (prefixWord ++ tailWord_815605) baseStart_815605 baseEnd_815605 := by
    simpa [prefixWord, tailWord_815605, baseEnd_815605] using wordTrace_append hprefix tailTrace_815605
  have hstable : (prefixWord ++ tailWord_815605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815605).length < 2 ^ (prefixWord ++ tailWord_815605).sum := by decide
  have hdescent : baseEnd_815605 < baseStart_815605 := by decide
  rcases family_descends (prefixWord ++ tailWord_815605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815693 : List Nat := [1, 6, 1, 1, 2, 1, 4, 1, 1, 4]
def baseStart_815693 : Nat := 118140960795 + 815693 * 2 ^ 59
def prefixEnd_815693 : Nat := 4983230072969 + 3 ^ 40 * 815693 * 2
def baseEnd_815693 : Nat := 279228383671988220724135

theorem tailTrace_815693 : CollatzResearch.WordTrace tailWord_815693 prefixEnd_815693 279228383671988220724135 := by
  unfold tailWord_815693
  simp only [CollatzResearch.WordTrace]
  refine ⟨29750767833891045118531733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19833845222594030079021155 29750767833891045118531733)
  ·
    refine ⟨1394567242213642739931175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29750767833891045118531733 1394567242213642739931175)
    ·
      refine ⟨2091850863320464109896763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1394567242213642739931175 2091850863320464109896763)
      ·
        refine ⟨3137776294980696164845145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2091850863320464109896763 3137776294980696164845145)
        ·
          refine ⟨2353332221235522123633859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3137776294980696164845145 2353332221235522123633859)
          ·
            refine ⟨3529998331853283185450789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2353332221235522123633859 3529998331853283185450789)
            ·
              refine ⟨661874687222490597272023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3529998331853283185450789 661874687222490597272023)
              ·
                refine ⟨992812030833735895908035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 661874687222490597272023 992812030833735895908035)
                ·
                  refine ⟨1489218046250603843862053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 992812030833735895908035 1489218046250603843862053)
                  ·
                    refine ⟨279228383671988220724135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1489218046250603843862053 279228383671988220724135)
                    ·
                      rfl

theorem cell22_815693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_815693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_815693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_815693 prefixEnd_815693 := by exact prefixLift 815693
  have htrace : WordTrace (prefixWord ++ tailWord_815693) baseStart_815693 baseEnd_815693 := by
    simpa [prefixWord, tailWord_815693, baseEnd_815693] using wordTrace_append hprefix tailTrace_815693
  have hstable : (prefixWord ++ tailWord_815693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815693).length < 2 ^ (prefixWord ++ tailWord_815693).sum := by decide
  have hdescent : baseEnd_815693 < baseStart_815693 := by decide
  rcases family_descends (prefixWord ++ tailWord_815693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815747 : List Nat := [1, 1, 1, 3, 3, 1, 3, 2, 7]
def baseStart_815747 : Nat := 118140960795 + 815747 * 2 ^ 59
def prefixEnd_815747 : Nat := 4983230072969 + 3 ^ 40 * 815747 * 2
def baseEnd_815747 : Nat := 93082289658516693291323

theorem tailTrace_815747 : CollatzResearch.WordTrace tailWord_815747 prefixEnd_815747 93082289658516693291323 := by
  unfold tailWord_815747
  simp only [CollatzResearch.WordTrace]
  refine ⟨29752737375695412340997495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19835158250463608227331663 29752737375695412340997495)
  ·
    refine ⟨44629106063543118511496243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29752737375695412340997495 44629106063543118511496243)
    ·
      refine ⟨66943659095314677767244365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44629106063543118511496243 66943659095314677767244365)
      ·
        refine ⟨25103872160743004162716637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66943659095314677767244365 25103872160743004162716637)
        ·
          refine ⟨9413952060278626561018739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25103872160743004162716637 9413952060278626561018739)
          ·
            refine ⟨14120928090417939841528109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9413952060278626561018739 14120928090417939841528109)
            ·
              refine ⟨5295348033906727440573041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14120928090417939841528109 5295348033906727440573041)
              ·
                refine ⟨3971511025430045580429781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5295348033906727440573041 3971511025430045580429781)
                ·
                  refine ⟨93082289658516693291323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3971511025430045580429781 93082289658516693291323)
                  ·
                    rfl

theorem cell22_815747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 7].length) (baseStart_815747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_815747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_815747 prefixEnd_815747 := by exact prefixLift 815747
  have htrace : WordTrace (prefixWord ++ tailWord_815747) baseStart_815747 baseEnd_815747 := by
    simpa [prefixWord, tailWord_815747, baseEnd_815747] using wordTrace_append hprefix tailTrace_815747
  have hstable : (prefixWord ++ tailWord_815747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815747).length < 2 ^ (prefixWord ++ tailWord_815747).sum := by decide
  have hdescent : baseEnd_815747 < baseStart_815747 := by decide
  rcases family_descends (prefixWord ++ tailWord_815747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815792 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 8]
def baseStart_815792 : Nat := 118140960795 + 815792 * 2 ^ 59
def prefixEnd_815792 : Nat := 4983230072969 + 3 ^ 40 * 815792 * 2
def baseEnd_815792 : Nat := 93087424465061654166277

theorem tailTrace_815792 : CollatzResearch.WordTrace tailWord_815792 prefixEnd_815792 93087424465061654166277 := by
  unfold tailWord_815792
  simp only [CollatzResearch.WordTrace]
  refine ⟨14877189330266192513192815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19836252440354923350923753 14877189330266192513192815)
  ·
    refine ⟨22315783995399288769789223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14877189330266192513192815 22315783995399288769789223)
    ·
      refine ⟨33473675993098933154683835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22315783995399288769789223 33473675993098933154683835)
      ·
        refine ⟨50210513989648399732025753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33473675993098933154683835 50210513989648399732025753)
        ·
          refine ⟨37657885492236299799019315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50210513989648399732025753 37657885492236299799019315)
          ·
            refine ⟨56486828238354449698528973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37657885492236299799019315 56486828238354449698528973)
            ·
              refine ⟨21182560589382918636948365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56486828238354449698528973 21182560589382918636948365)
              ·
                refine ⟨7943460221018594488855637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21182560589382918636948365 7943460221018594488855637)
                ·
                  refine ⟨93087424465061654166277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7943460221018594488855637 93087424465061654166277)
                  ·
                    rfl

theorem cell22_815792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 8].length) (baseStart_815792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_815792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_815792 prefixEnd_815792 := by exact prefixLift 815792
  have htrace : WordTrace (prefixWord ++ tailWord_815792) baseStart_815792 baseEnd_815792 := by
    simpa [prefixWord, tailWord_815792, baseEnd_815792] using wordTrace_append hprefix tailTrace_815792
  have hstable : (prefixWord ++ tailWord_815792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815792).length < 2 ^ (prefixWord ++ tailWord_815792).sum := by decide
  have hdescent : baseEnd_815792 < baseStart_815792 := by decide
  rcases family_descends (prefixWord ++ tailWord_815792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815824 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 8, 3]
def baseStart_815824 : Nat := 118140960795 + 815824 * 2 ^ 59
def prefixEnd_815824 : Nat := 4983230072969 + 3 ^ 40 * 815824 * 2
def baseEnd_815824 : Nat := 279273227649147545698733

theorem tailTrace_815824 : CollatzResearch.WordTrace tailWord_815824 prefixEnd_815824 279273227649147545698733 := by
  unfold tailWord_815824
  simp only [CollatzResearch.WordTrace]
  refine ⟨14877772898208227245775263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19837030530944302994367017 14877772898208227245775263)
  ·
    refine ⟨22316659347312340868662895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14877772898208227245775263 22316659347312340868662895)
    ·
      refine ⟨33474989020968511302994343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22316659347312340868662895 33474989020968511302994343)
      ·
        refine ⟨50212483531452766954491515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33474989020968511302994343 50212483531452766954491515)
        ·
          refine ⟨75318725297179150431737273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50212483531452766954491515 75318725297179150431737273)
          ·
            refine ⟨56489043972884362823802955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75318725297179150431737273 56489043972884362823802955)
            ·
              refine ⟨84733565959326544235704433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56489043972884362823802955 84733565959326544235704433)
              ·
                refine ⟨63550174469494908176778325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84733565959326544235704433 63550174469494908176778325)
                ·
                  refine ⟨744728607064393455196621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 63550174469494908176778325 744728607064393455196621)
                  ·
                    refine ⟨279273227649147545698733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 744728607064393455196621 279273227649147545698733)
                    ·
                      rfl

theorem cell22_815824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 8, 3].length) (baseStart_815824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_815824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_815824 prefixEnd_815824 := by exact prefixLift 815824
  have htrace : WordTrace (prefixWord ++ tailWord_815824) baseStart_815824 baseEnd_815824 := by
    simpa [prefixWord, tailWord_815824, baseEnd_815824] using wordTrace_append hprefix tailTrace_815824
  have hstable : (prefixWord ++ tailWord_815824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815824).length < 2 ^ (prefixWord ++ tailWord_815824).sum := by decide
  have hdescent : baseEnd_815824 < baseStart_815824 := by decide
  rcases family_descends (prefixWord ++ tailWord_815824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815841 : List Nat := [1, 2, 3, 1, 4, 2, 2, 1, 1, 5]
def baseStart_815841 : Nat := 118140960795 + 815841 * 2 ^ 59
def prefixEnd_815841 : Nat := 4983230072969 + 3 ^ 40 * 815841 * 2
def baseEnd_815841 : Nat := 279279047096565168023681

theorem tailTrace_815841 : CollatzResearch.WordTrace tailWord_815841 prefixEnd_815841 279279047096565168023681 := by
  unfold tailWord_815841
  simp only [CollatzResearch.WordTrace]
  refine ⟨29756165837354866394919377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19837443891569910929946251 29756165837354866394919377)
  ·
    refine ⟨22317124378016149796189533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29756165837354866394919377 22317124378016149796189533)
    ·
      refine ⟨8368921641756056173571075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22317124378016149796189533 8368921641756056173571075)
      ·
        refine ⟨12553382462634084260356613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8368921641756056173571075 12553382462634084260356613)
        ·
          refine ⟨2353759211743890798816865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12553382462634084260356613 2353759211743890798816865)
          ·
            refine ⟨1765319408807918099112649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2353759211743890798816865 1765319408807918099112649)
            ·
              refine ⟨1323989556605938574334487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1765319408807918099112649 1323989556605938574334487)
              ·
                refine ⟨1985984334908907861501731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1323989556605938574334487 1985984334908907861501731)
                ·
                  refine ⟨2978976502363361792252597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1985984334908907861501731 2978976502363361792252597)
                  ·
                    refine ⟨279279047096565168023681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2978976502363361792252597 279279047096565168023681)
                    ·
                      rfl

theorem cell22_815841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_815841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_815841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_815841 prefixEnd_815841 := by exact prefixLift 815841
  have htrace : WordTrace (prefixWord ++ tailWord_815841) baseStart_815841 baseEnd_815841 := by
    simpa [prefixWord, tailWord_815841, baseEnd_815841] using wordTrace_append hprefix tailTrace_815841
  have hstable : (prefixWord ++ tailWord_815841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815841).length < 2 ^ (prefixWord ++ tailWord_815841).sum := by decide
  have hdescent : baseEnd_815841 < baseStart_815841 := by decide
  rcases family_descends (prefixWord ++ tailWord_815841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815937 : List Nat := [1, 2, 5, 3, 1, 2, 1, 1, 3, 3]
def baseStart_815937 : Nat := 118140960795 + 815937 * 2 ^ 59
def prefixEnd_815937 : Nat := 4983230072969 + 3 ^ 40 * 815937 * 2
def baseEnd_815937 : Nat := 279311909858452917623387

theorem tailTrace_815937 : CollatzResearch.WordTrace tailWord_815937 prefixEnd_815937 279311909858452917623387 := by
  unfold tailWord_815937
  simp only [CollatzResearch.WordTrace]
  refine ⟨29759667245007074790414065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19839778163338049860276043 29759667245007074790414065)
  ·
    refine ⟨22319750433755306092810549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29759667245007074790414065 22319750433755306092810549)
    ·
      refine ⟨2092476603164559946200989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22319750433755306092810549 2092476603164559946200989)
      ·
        refine ⟨784678726186709979825371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2092476603164559946200989 784678726186709979825371)
        ·
          refine ⟨1177018089280064969738057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 784678726186709979825371 1177018089280064969738057)
          ·
            refine ⟨882763566960048727303543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1177018089280064969738057 882763566960048727303543)
            ·
              refine ⟨1324145350440073090955315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 882763566960048727303543 1324145350440073090955315)
              ·
                refine ⟨1986218025660109636432973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1324145350440073090955315 1986218025660109636432973)
                ·
                  refine ⟨744831759622541113662365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1986218025660109636432973 744831759622541113662365)
                  ·
                    refine ⟨279311909858452917623387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 744831759622541113662365 279311909858452917623387)
                    ·
                      rfl

theorem cell22_815937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_815937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_815937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_815937 prefixEnd_815937 := by exact prefixLift 815937
  have htrace : WordTrace (prefixWord ++ tailWord_815937) baseStart_815937 baseEnd_815937 := by
    simpa [prefixWord, tailWord_815937, baseEnd_815937] using wordTrace_append hprefix tailTrace_815937
  have hstable : (prefixWord ++ tailWord_815937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815937).length < 2 ^ (prefixWord ++ tailWord_815937).sum := by decide
  have hdescent : baseEnd_815937 < baseStart_815937 := by decide
  rcases family_descends (prefixWord ++ tailWord_815937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815976 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 3, 5]
def baseStart_815976 : Nat := 118140960795 + 815976 * 2 ^ 59
def prefixEnd_815976 : Nat := 4983230072969 + 3 ^ 40 * 815976 * 2
def baseEnd_815976 : Nat := 279325260355469815898267

theorem tailTrace_815976 : CollatzResearch.WordTrace tailWord_815976 prefixEnd_815976 279325260355469815898267 := by
  unfold tailWord_815976
  simp only [CollatzResearch.WordTrace]
  refine ⟨14880544845932892225541891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19840726461243856300722521 14880544845932892225541891)
  ·
    refine ⟨22320817268899338338312837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14880544845932892225541891 22320817268899338338312837)
    ·
      refine ⟨4185153237918625938433657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22320817268899338338312837 4185153237918625938433657)
      ·
        refine ⟨3138864928438969453825243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4185153237918625938433657 3138864928438969453825243)
        ·
          refine ⟨4708297392658454180737865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3138864928438969453825243 4708297392658454180737865)
          ·
            refine ⟨3531223044493840635553399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4708297392658454180737865 3531223044493840635553399)
            ·
              refine ⟨5296834566740760953330099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3531223044493840635553399 5296834566740760953330099)
              ·
                refine ⟨7945251850111141429995149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5296834566740760953330099 7945251850111141429995149)
                ·
                  refine ⟨2979469443791678036248181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7945251850111141429995149 2979469443791678036248181)
                  ·
                    refine ⟨279325260355469815898267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2979469443791678036248181 279325260355469815898267)
                    ·
                      rfl

theorem cell22_815976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_815976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_815976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_815976 prefixEnd_815976 := by exact prefixLift 815976
  have htrace : WordTrace (prefixWord ++ tailWord_815976) baseStart_815976 baseEnd_815976 := by
    simpa [prefixWord, tailWord_815976, baseEnd_815976] using wordTrace_append hprefix tailTrace_815976
  have hstable : (prefixWord ++ tailWord_815976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815976).length < 2 ^ (prefixWord ++ tailWord_815976).sum := by decide
  have hdescent : baseEnd_815976 < baseStart_815976 := by decide
  rcases family_descends (prefixWord ++ tailWord_815976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815993 : List Nat := [1, 2, 1, 3, 2, 3, 1, 4, 2, 3]
def baseStart_815993 : Nat := 118140960795 + 815993 * 2 ^ 59
def prefixEnd_815993 : Nat := 4983230072969 + 3 ^ 40 * 815993 * 2
def baseEnd_815993 : Nat := 279331079802887438223215

theorem tailTrace_815993 : CollatzResearch.WordTrace tailWord_815993 prefixEnd_815993 279331079802887438223215 := by
  unfold tailWord_815993
  simp only [CollatzResearch.WordTrace]
  refine ⟨29761709732804196354452633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19841139821869464236301755 29761709732804196354452633)
  ·
    refine ⟨22321282299603147265839475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29761709732804196354452633 22321282299603147265839475)
    ·
      refine ⟨33481923449404720898759213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22321282299603147265839475 33481923449404720898759213)
      ·
        refine ⟨12555721293526770337034705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33481923449404720898759213 12555721293526770337034705)
        ·
          refine ⟨9416790970145077752776029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12555721293526770337034705 9416790970145077752776029)
          ·
            refine ⟨3531296613804404157291011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9416790970145077752776029 3531296613804404157291011)
            ·
              refine ⟨5296944920706606235936517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3531296613804404157291011 5296944920706606235936517)
              ·
                refine ⟨993177172632488669238097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5296944920706606235936517 993177172632488669238097)
                ·
                  refine ⟨744882879474366501928573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 993177172632488669238097 744882879474366501928573)
                  ·
                    refine ⟨279331079802887438223215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 744882879474366501928573 279331079802887438223215)
                    ·
                      rfl

theorem cell22_815993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2, 3].length) (baseStart_815993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_815993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_815993 prefixEnd_815993 := by exact prefixLift 815993
  have htrace : WordTrace (prefixWord ++ tailWord_815993) baseStart_815993 baseEnd_815993 := by
    simpa [prefixWord, tailWord_815993, baseEnd_815993] using wordTrace_append hprefix tailTrace_815993
  have hstable : (prefixWord ++ tailWord_815993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815993).length < 2 ^ (prefixWord ++ tailWord_815993).sum := by decide
  have hdescent : baseEnd_815993 < baseStart_815993 := by decide
  rcases family_descends (prefixWord ++ tailWord_815993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816010 : List Nat := [3, 1, 2, 4, 1, 1, 2, 3, 2, 3]
def baseStart_816010 : Nat := 118140960795 + 816010 * 2 ^ 59
def prefixEnd_816010 : Nat := 4983230072969 + 3 ^ 40 * 816010 * 2
def baseEnd_816010 : Nat := 279336899250305060548163

theorem tailTrace_816010 : CollatzResearch.WordTrace tailWord_816010 prefixEnd_816010 279336899250305060548163 := by
  unfold tailWord_816010
  simp only [CollatzResearch.WordTrace]
  refine ⟨7440582443435652064455371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19841553182495072171880989 7440582443435652064455371)
  ·
    refine ⟨11160873665153478096683057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7440582443435652064455371 11160873665153478096683057)
    ·
      refine ⟨8370655248865108572512293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11160873665153478096683057 8370655248865108572512293)
      ·
        refine ⟨1569497859162207857346055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8370655248865108572512293 1569497859162207857346055)
        ·
          refine ⟨2354246788743311786019083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1569497859162207857346055 2354246788743311786019083)
          ·
            refine ⟨3531370183114967679028625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2354246788743311786019083 3531370183114967679028625)
            ·
              refine ⟨2648527637336225759271469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3531370183114967679028625 2648527637336225759271469)
              ·
                refine ⟨993197864001084659726801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2648527637336225759271469 993197864001084659726801)
                ·
                  refine ⟨744898398000813494795101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 993197864001084659726801 744898398000813494795101)
                  ·
                    refine ⟨279336899250305060548163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 744898398000813494795101 279336899250305060548163)
                    ·
                      rfl

theorem cell22_816010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_816010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816010 prefixEnd_816010 := by exact prefixLift 816010
  have htrace : WordTrace (prefixWord ++ tailWord_816010) baseStart_816010 baseEnd_816010 := by
    simpa [prefixWord, tailWord_816010, baseEnd_816010] using wordTrace_append hprefix tailTrace_816010
  have hstable : (prefixWord ++ tailWord_816010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816010).length < 2 ^ (prefixWord ++ tailWord_816010).sum := by decide
  have hdescent : baseEnd_816010 < baseStart_816010 := by decide
  rcases family_descends (prefixWord ++ tailWord_816010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816051 : List Nat := [1, 1, 1, 2, 3, 1, 2, 6, 5]
def baseStart_816051 : Nat := 118140960795 + 816051 * 2 ^ 59
def prefixEnd_816051 : Nat := 4983230072969 + 3 ^ 40 * 816051 * 2
def baseEnd_816051 : Nat := 93116978129398206757679

theorem tailTrace_816051 : CollatzResearch.WordTrace tailWord_816051 prefixEnd_816051 93116978129398206757679 := by
  unfold tailWord_816051
  simp only [CollatzResearch.WordTrace]
  refine ⟨29763825166594072260064007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19842550111062714840042671 29763825166594072260064007)
  ·
    refine ⟨44645737749891108390096011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29763825166594072260064007 44645737749891108390096011)
    ·
      refine ⟨66968606624836662585144017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44645737749891108390096011 66968606624836662585144017)
      ·
        refine ⟨50226454968627496938858013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66968606624836662585144017 50226454968627496938858013)
        ·
          refine ⟨18834920613235311352071755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50226454968627496938858013 18834920613235311352071755)
          ·
            refine ⟨28252380919852967028107633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18834920613235311352071755 28252380919852967028107633)
            ·
              refine ⟨21189285689889725271080725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28252380919852967028107633 21189285689889725271080725)
              ·
                refine ⟨993247766713580872081909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21189285689889725271080725 993247766713580872081909)
                ·
                  refine ⟨93116978129398206757679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 993247766713580872081909 93116978129398206757679)
                  ·
                    rfl

theorem cell22_816051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 5].length) (baseStart_816051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816051 prefixEnd_816051 := by exact prefixLift 816051
  have htrace : WordTrace (prefixWord ++ tailWord_816051) baseStart_816051 baseEnd_816051 := by
    simpa [prefixWord, tailWord_816051, baseEnd_816051] using wordTrace_append hprefix tailTrace_816051
  have hstable : (prefixWord ++ tailWord_816051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816051).length < 2 ^ (prefixWord ++ tailWord_816051).sum := by decide
  have hdescent : baseEnd_816051 < baseStart_816051 := by decide
  rcases family_descends (prefixWord ++ tailWord_816051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816055 : List Nat := [1, 1, 3, 1, 3, 1, 4, 4, 1, 3]
def baseStart_816055 : Nat := 118140960795 + 816055 * 2 ^ 59
def prefixEnd_816055 : Nat := 4983230072969 + 3 ^ 40 * 816055 * 2
def baseEnd_816055 : Nat := 279352303669939943173025

theorem tailTrace_816055 : CollatzResearch.WordTrace tailWord_816055 prefixEnd_816055 279352303669939943173025 := by
  unfold tailWord_816055
  simp only [CollatzResearch.WordTrace]
  refine ⟨29763971058579580943209619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19842647372386387295473079 29763971058579580943209619)
  ·
    refine ⟨44645956587869371414814429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29763971058579580943209619 44645956587869371414814429)
    ·
      refine ⟨16742233720451014280555411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44645956587869371414814429 16742233720451014280555411)
      ·
        refine ⟨25113350580676521420833117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16742233720451014280555411 25113350580676521420833117)
        ·
          refine ⟨9417506467753695532812419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25113350580676521420833117 9417506467753695532812419)
          ·
            refine ⟨14126259701630543299218629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9417506467753695532812419 14126259701630543299218629)
            ·
              refine ⟨2648673694055726868603493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14126259701630543299218629 2648673694055726868603493)
              ·
                refine ⟨496626317635448787863155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2648673694055726868603493 496626317635448787863155)
                ·
                  refine ⟨744939476453173181794733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 496626317635448787863155 744939476453173181794733)
                  ·
                    refine ⟨279352303669939943173025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 744939476453173181794733 279352303669939943173025)
                    ·
                      rfl

theorem cell22_816055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4, 1, 3].length) (baseStart_816055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816055 prefixEnd_816055 := by exact prefixLift 816055
  have htrace : WordTrace (prefixWord ++ tailWord_816055) baseStart_816055 baseEnd_816055 := by
    simpa [prefixWord, tailWord_816055, baseEnd_816055] using wordTrace_append hprefix tailTrace_816055
  have hstable : (prefixWord ++ tailWord_816055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816055).length < 2 ^ (prefixWord ++ tailWord_816055).sum := by decide
  have hdescent : baseEnd_816055 < baseStart_816055 := by decide
  rcases family_descends (prefixWord ++ tailWord_816055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816113 : List Nat := [1, 2, 2, 2, 4, 1, 3, 1, 6]
def baseStart_816113 : Nat := 118140960795 + 816113 * 2 ^ 59
def prefixEnd_816113 : Nat := 4983230072969 + 3 ^ 40 * 816113 * 2
def baseEnd_816113 : Nat := 93124052751749041740949

theorem tailTrace_816113 : CollatzResearch.WordTrace tailWord_816113 prefixEnd_816113 93124052751749041740949 := by
  unfold tailWord_816113
  simp only [CollatzResearch.WordTrace]
  refine ⟨29766086492369456848820993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19844057661579637899213995 29766086492369456848820993)
  ·
    refine ⟨22324564869277092636615745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29766086492369456848820993 22324564869277092636615745)
    ·
      refine ⟨16743423651957819477461809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22324564869277092636615745 16743423651957819477461809)
      ·
        refine ⟨12557567738968364608096357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16743423651957819477461809 12557567738968364608096357)
        ·
          refine ⟨2354543951056568364018067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12557567738968364608096357 2354543951056568364018067)
          ·
            refine ⟨3531815926584852546027101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2354543951056568364018067 3531815926584852546027101)
            ·
              refine ⟨1324430972469319704760163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3531815926584852546027101 1324430972469319704760163)
              ·
                refine ⟨1986646458703979557140245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1324430972469319704760163 1986646458703979557140245)
                ·
                  refine ⟨93124052751749041740949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1986646458703979557140245 93124052751749041740949)
                  ·
                    rfl

theorem cell22_816113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 6].length) (baseStart_816113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816113 prefixEnd_816113 := by exact prefixLift 816113
  have htrace : WordTrace (prefixWord ++ tailWord_816113) baseStart_816113 baseEnd_816113 := by
    simpa [prefixWord, tailWord_816113, baseEnd_816113] using wordTrace_append hprefix tailTrace_816113
  have hstable : (prefixWord ++ tailWord_816113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816113).length < 2 ^ (prefixWord ++ tailWord_816113).sum := by decide
  have hdescent : baseEnd_816113 < baseStart_816113 := by decide
  rcases family_descends (prefixWord ++ tailWord_816113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816162 : List Nat := [3, 3, 1, 1, 1, 4, 2, 2, 2, 3]
def baseStart_816162 : Nat := 118140960795 + 816162 * 2 ^ 59
def prefixEnd_816162 : Nat := 4983230072969 + 3 ^ 40 * 816162 * 2
def baseEnd_816162 : Nat := 279388931956627330747697

theorem tailTrace_816162 : CollatzResearch.WordTrace tailWord_816162 prefixEnd_816162 279388931956627330747697 := by
  unfold tailWord_816162
  simp only [CollatzResearch.WordTrace]
  refine ⟨7441968417297984554338685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19845249112794625478236493 7441968417297984554338685)
  ·
    refine ⟨2790738156486744207877007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7441968417297984554338685 2790738156486744207877007)
    ·
      refine ⟨4186107234730116311815511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2790738156486744207877007 4186107234730116311815511)
      ·
        refine ⟨6279160852095174467723267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4186107234730116311815511 6279160852095174467723267)
        ·
          refine ⟨9418741278142761701584901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6279160852095174467723267 9418741278142761701584901)
          ·
            refine ⟨1766013989651767819047169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9418741278142761701584901 1766013989651767819047169)
            ·
              refine ⟨1324510492238825864285377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1766013989651767819047169 1324510492238825864285377)
              ·
                refine ⟨993382869179119398214033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1324510492238825864285377 993382869179119398214033)
                ·
                  refine ⟨745037151884339548660525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 993382869179119398214033 745037151884339548660525)
                  ·
                    refine ⟨279388931956627330747697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 745037151884339548660525 279388931956627330747697)
                    ·
                      rfl

theorem cell22_816162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_816162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816162 prefixEnd_816162 := by exact prefixLift 816162
  have htrace : WordTrace (prefixWord ++ tailWord_816162) baseStart_816162 baseEnd_816162 := by
    simpa [prefixWord, tailWord_816162, baseEnd_816162] using wordTrace_append hprefix tailTrace_816162
  have hstable : (prefixWord ++ tailWord_816162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816162).length < 2 ^ (prefixWord ++ tailWord_816162).sum := by decide
  have hdescent : baseEnd_816162 < baseStart_816162 := by decide
  rcases family_descends (prefixWord ++ tailWord_816162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816164 : List Nat := [2, 3, 1, 4, 1, 3, 2, 2, 4]
def baseStart_816164 : Nat := 118140960795 + 816164 * 2 ^ 59
def prefixEnd_816164 : Nat := 4983230072969 + 3 ^ 40 * 816164 * 2
def baseEnd_816164 : Nat := 93129872199166664065897

theorem tailTrace_816164 : CollatzResearch.WordTrace tailWord_816164 prefixEnd_816164 93129872199166664065897 := by
  unfold tailWord_816164
  simp only [CollatzResearch.WordTrace]
  refine ⟨14883973307592346279463773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19845297743456461705951697 14883973307592346279463773)
  ·
    refine ⟨5581489990347129854798915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14883973307592346279463773 5581489990347129854798915)
    ·
      refine ⟨8372234985520694782198373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5581489990347129854798915 8372234985520694782198373)
      ·
        refine ⟨1569794059785130271662195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8372234985520694782198373 1569794059785130271662195)
        ·
          refine ⟨2354691089677695407493293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1569794059785130271662195 2354691089677695407493293)
          ·
            refine ⟨883009158629135777809985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2354691089677695407493293 883009158629135777809985)
            ·
              refine ⟨662256868971851833357489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 883009158629135777809985 662256868971851833357489)
              ·
                refine ⟨496692651728888875018117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 662256868971851833357489 496692651728888875018117)
                ·
                  refine ⟨93129872199166664065897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 496692651728888875018117 93129872199166664065897)
                  ·
                    rfl

theorem cell22_816164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_816164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816164 prefixEnd_816164 := by exact prefixLift 816164
  have htrace : WordTrace (prefixWord ++ tailWord_816164) baseStart_816164 baseEnd_816164 := by
    simpa [prefixWord, tailWord_816164, baseEnd_816164] using wordTrace_append hprefix tailTrace_816164
  have hstable : (prefixWord ++ tailWord_816164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816164).length < 2 ^ (prefixWord ++ tailWord_816164).sum := by decide
  have hdescent : baseEnd_816164 < baseStart_816164 := by decide
  rcases family_descends (prefixWord ++ tailWord_816164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816171 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 1, 8]
def baseStart_816171 : Nat := 118140960795 + 816171 * 2 ^ 59
def prefixEnd_816171 : Nat := 4983230072969 + 3 ^ 40 * 816171 * 2
def baseEnd_816171 : Nat := 279392012840554307272669

theorem tailTrace_816171 : CollatzResearch.WordTrace tailWord_816171 prefixEnd_816171 279392012840554307272669 := by
  unfold tailWord_816171
  simp only [CollatzResearch.WordTrace]
  refine ⟨29768201926159332754432367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19845467950772888502954911 29768201926159332754432367)
  ·
    refine ⟨44652302889238999131648551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29768201926159332754432367 44652302889238999131648551)
    ·
      refine ⟨66978454333858498697472827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44652302889238999131648551 66978454333858498697472827)
      ·
        refine ⟨100467681500787748046209241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66978454333858498697472827 100467681500787748046209241)
        ·
          refine ⟨75350761125590811034656931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100467681500787748046209241 75350761125590811034656931)
          ·
            refine ⟨113026141688386216551985397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75350761125590811034656931 113026141688386216551985397)
            ·
              refine ⟨10596200783286207801748631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113026141688386216551985397 10596200783286207801748631)
              ·
                refine ⟨15894301174929311702622947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10596200783286207801748631 15894301174929311702622947)
                ·
                  refine ⟨23841451762393967553934421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15894301174929311702622947 23841451762393967553934421)
                  ·
                    refine ⟨279392012840554307272669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23841451762393967553934421 279392012840554307272669)
                    ·
                      rfl

theorem cell22_816171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 8].length) (baseStart_816171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816171 prefixEnd_816171 := by exact prefixLift 816171
  have htrace : WordTrace (prefixWord ++ tailWord_816171) baseStart_816171 baseEnd_816171 := by
    simpa [prefixWord, tailWord_816171, baseEnd_816171] using wordTrace_append hprefix tailTrace_816171
  have hstable : (prefixWord ++ tailWord_816171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816171).length < 2 ^ (prefixWord ++ tailWord_816171).sum := by decide
  have hdescent : baseEnd_816171 < baseStart_816171 := by decide
  rcases family_descends (prefixWord ++ tailWord_816171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816237 : List Nat := [1, 5, 1, 1, 2, 3, 3, 1, 5]
def baseStart_816237 : Nat := 118140960795 + 816237 * 2 ^ 59
def prefixEnd_816237 : Nat := 4983230072969 + 3 ^ 40 * 816237 * 2
def baseEnd_816237 : Nat := 93138201996450711707489

theorem tailTrace_816237 : CollatzResearch.WordTrace tailWord_816237 prefixEnd_816237 93138201996450711707489 := by
  unfold tailWord_816237
  simp only [CollatzResearch.WordTrace]
  refine ⟨29770609143920226026334965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19847072762613484017556643 29770609143920226026334965)
  ·
    refine ⟨2790994607242521189968903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29770609143920226026334965 2790994607242521189968903)
    ·
      refine ⟨4186491910863781784953355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2790994607242521189968903 4186491910863781784953355)
      ·
        refine ⟨6279737866295672677430033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4186491910863781784953355 6279737866295672677430033)
        ·
          refine ⟨4709803399721754508072525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6279737866295672677430033 4709803399721754508072525)
          ·
            refine ⟨1766176274895657940527197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4709803399721754508072525 1766176274895657940527197)
            ·
              refine ⟨662316103085871727697699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1766176274895657940527197 662316103085871727697699)
              ·
                refine ⟨993474154628807591546549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 662316103085871727697699 993474154628807591546549)
                ·
                  refine ⟨93138201996450711707489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 993474154628807591546549 93138201996450711707489)
                  ·
                    rfl

theorem cell22_816237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_816237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816237 prefixEnd_816237 := by exact prefixLift 816237
  have htrace : WordTrace (prefixWord ++ tailWord_816237) baseStart_816237 baseEnd_816237 := by
    simpa [prefixWord, tailWord_816237, baseEnd_816237] using wordTrace_append hprefix tailTrace_816237
  have hstable : (prefixWord ++ tailWord_816237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816237).length < 2 ^ (prefixWord ++ tailWord_816237).sum := by decide
  have hdescent : baseEnd_816237 < baseStart_816237 := by decide
  rcases family_descends (prefixWord ++ tailWord_816237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816248 : List Nat := [2, 1, 2, 1, 1, 1, 6, 2, 6]
def baseStart_816248 : Nat := 118140960795 + 816248 * 2 ^ 59
def prefixEnd_816248 : Nat := 4983230072969 + 3 ^ 40 * 816248 * 2
def baseEnd_816248 : Nat := 93139457171383924365811

theorem tailTrace_816248 : CollatzResearch.WordTrace tailWord_816248 prefixEnd_816248 93139457171383924365811 := by
  unfold tailWord_816248
  simp only [CollatzResearch.WordTrace]
  refine ⟨14885505173440187452492699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19847340231253583269990265 14885505173440187452492699)
  ·
    refine ⟨22328257760160281178739049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14885505173440187452492699 22328257760160281178739049)
    ·
      refine ⟨16746193320120210884054287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22328257760160281178739049 16746193320120210884054287)
      ·
        refine ⟨25119289980180316326081431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16746193320120210884054287 25119289980180316326081431)
        ·
          refine ⟨37678934970270474489122147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25119289980180316326081431 37678934970270474489122147)
          ·
            refine ⟨56518402455405711733683221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37678934970270474489122147 56518402455405711733683221)
            ·
              refine ⟨2649300115097142737516401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56518402455405711733683221 2649300115097142737516401)
              ·
                refine ⟨1986975086322857053137301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2649300115097142737516401 1986975086322857053137301)
                ·
                  refine ⟨93139457171383924365811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1986975086322857053137301 93139457171383924365811)
                  ·
                    rfl

theorem cell22_816248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 6].length) (baseStart_816248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816248 prefixEnd_816248 := by exact prefixLift 816248
  have htrace : WordTrace (prefixWord ++ tailWord_816248) baseStart_816248 baseEnd_816248 := by
    simpa [prefixWord, tailWord_816248, baseEnd_816248] using wordTrace_append hprefix tailTrace_816248
  have hstable : (prefixWord ++ tailWord_816248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816248).length < 2 ^ (prefixWord ++ tailWord_816248).sum := by decide
  have hdescent : baseEnd_816248 < baseStart_816248 := by decide
  rcases family_descends (prefixWord ++ tailWord_816248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816263 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 3, 5]
def baseStart_816263 : Nat := 118140960795 + 816263 * 2 ^ 59
def prefixEnd_816263 : Nat := 4983230072969 + 3 ^ 40 * 816263 * 2
def baseEnd_816263 : Nat := 279423506320696733972387

theorem tailTrace_816263 : CollatzResearch.WordTrace tailWord_816263 prefixEnd_816263 279423506320696733972387 := by
  unfold tailWord_816263
  simp only [CollatzResearch.WordTrace]
  refine ⟨29771557441826032466781443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19847704961217354977854295 29771557441826032466781443)
  ·
    refine ⟨44657336162739048700172165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29771557441826032466781443 44657336162739048700172165)
    ·
      refine ⟨8373250530513571631282281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44657336162739048700172165 8373250530513571631282281)
      ·
        refine ⟨6279937897885178723461711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8373250530513571631282281 6279937897885178723461711)
        ·
          refine ⟨9419906846827768085192567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6279937897885178723461711 9419906846827768085192567)
          ·
            refine ⟨14129860270241652127788851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9419906846827768085192567 14129860270241652127788851)
            ·
              refine ⟨21194790405362478191683277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14129860270241652127788851 21194790405362478191683277)
              ·
                refine ⟨7948046402010929321881229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21194790405362478191683277 7948046402010929321881229)
                ·
                  refine ⟨2980517400754098495705461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7948046402010929321881229 2980517400754098495705461)
                  ·
                    refine ⟨279423506320696733972387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2980517400754098495705461 279423506320696733972387)
                    ·
                      rfl

theorem cell22_816263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_816263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816263 prefixEnd_816263 := by exact prefixLift 816263
  have htrace : WordTrace (prefixWord ++ tailWord_816263) baseStart_816263 baseEnd_816263 := by
    simpa [prefixWord, tailWord_816263, baseEnd_816263] using wordTrace_append hprefix tailTrace_816263
  have hstable : (prefixWord ++ tailWord_816263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816263).length < 2 ^ (prefixWord ++ tailWord_816263).sum := by decide
  have hdescent : baseEnd_816263 < baseStart_816263 := by decide
  rcases family_descends (prefixWord ++ tailWord_816263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816282 : List Nat := [3, 1, 1, 5, 1, 3, 1, 1, 6]
def baseStart_816282 : Nat := 118140960795 + 816282 * 2 ^ 59
def prefixEnd_816282 : Nat := 4983230072969 + 3 ^ 40 * 816282 * 2
def baseEnd_816282 : Nat := 93143336802995672582443

theorem tailTrace_816282 : CollatzResearch.WordTrace tailWord_816282 prefixEnd_816282 93143336802995672582443 := by
  unfold tailWord_816282
  simp only [CollatzResearch.WordTrace]
  refine ⟨7443062607189299677930775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19848166952504799141148733 7443062607189299677930775)
  ·
    refine ⟨11164593910783949516896163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7443062607189299677930775 11164593910783949516896163)
    ·
      refine ⟨16746890866175924275344245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11164593910783949516896163 16746890866175924275344245)
      ·
        refine ⟨1570021018703992900813523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16746890866175924275344245 1570021018703992900813523)
        ·
          refine ⟨2355031528055989351220285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1570021018703992900813523 2355031528055989351220285)
          ·
            refine ⟨883136823020996006707607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2355031528055989351220285 883136823020996006707607)
            ·
              refine ⟨1324705234531494010061411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 883136823020996006707607 1324705234531494010061411)
              ·
                refine ⟨1987057851797241015092117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1324705234531494010061411 1987057851797241015092117)
                ·
                  refine ⟨93143336802995672582443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1987057851797241015092117 93143336802995672582443)
                  ·
                    rfl

theorem cell22_816282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 6].length) (baseStart_816282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816282 prefixEnd_816282 := by exact prefixLift 816282
  have htrace : WordTrace (prefixWord ++ tailWord_816282) baseStart_816282 baseEnd_816282 := by
    simpa [prefixWord, tailWord_816282, baseEnd_816282] using wordTrace_append hprefix tailTrace_816282
  have hstable : (prefixWord ++ tailWord_816282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816282).length < 2 ^ (prefixWord ++ tailWord_816282).sum := by decide
  have hdescent : baseEnd_816282 < baseStart_816282 := by decide
  rcases family_descends (prefixWord ++ tailWord_816282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816293 : List Nat := [1, 3, 1, 2, 1, 4, 1, 9]
def baseStart_816293 : Nat := 118140960795 + 816293 * 2 ^ 59
def prefixEnd_816293 : Nat := 4983230072969 + 3 ^ 40 * 816293 * 2
def baseEnd_816293 : Nat := 31048197325976295080255

theorem tailTrace_816293 : CollatzResearch.WordTrace tailWord_816293 prefixEnd_816293 31048197325976295080255 := by
  unfold tailWord_816293
  simp only [CollatzResearch.WordTrace]
  refine ⟨29772651631717347590373533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19848434421144898393582355 29772651631717347590373533)
  ·
    refine ⟨11164744361894005346390075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29772651631717347590373533 11164744361894005346390075)
    ·
      refine ⟨16747116542841008019585113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11164744361894005346390075 16747116542841008019585113)
      ·
        refine ⟨12560337407130756014688835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16747116542841008019585113 12560337407130756014688835)
        ·
          refine ⟨18840506110696134022033253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12560337407130756014688835 18840506110696134022033253)
          ·
            refine ⟨3532594895755525129131235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18840506110696134022033253 3532594895755525129131235)
            ·
              refine ⟨5298892343633287693696853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3532594895755525129131235 5298892343633287693696853)
              ·
                refine ⟨31048197325976295080255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5298892343633287693696853 31048197325976295080255)
                ·
                  rfl

theorem cell22_816293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 9].length) (baseStart_816293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816293 prefixEnd_816293 := by exact prefixLift 816293
  have htrace : WordTrace (prefixWord ++ tailWord_816293) baseStart_816293 baseEnd_816293 := by
    simpa [prefixWord, tailWord_816293, baseEnd_816293] using wordTrace_append hprefix tailTrace_816293
  have hstable : (prefixWord ++ tailWord_816293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816293).length < 2 ^ (prefixWord ++ tailWord_816293).sum := by decide
  have hdescent : baseEnd_816293 < baseStart_816293 := by decide
  rcases family_descends (prefixWord ++ tailWord_816293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816301 : List Nat := [1, 5, 2, 1, 4, 1, 1, 2, 1, 4]
def baseStart_816301 : Nat := 118140960795 + 816301 * 2 ^ 59
def prefixEnd_816301 : Nat := 4983230072969 + 3 ^ 40 * 816301 * 2
def baseEnd_816301 : Nat := 279436514497277301522271

theorem tailTrace_816301 : CollatzResearch.WordTrace tailWord_816301 prefixEnd_816301 279436514497277301522271 := by
  unfold tailWord_816301
  simp only [CollatzResearch.WordTrace]
  refine ⟨29772943415688364956664757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19848628943792243304443171 29772943415688364956664757)
  ·
    refine ⟨2791213445220784214687321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29772943415688364956664757 2791213445220784214687321)
    ·
      refine ⟨2093410083915588161015491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2791213445220784214687321 2093410083915588161015491)
      ·
        refine ⟨3140115125873382241523237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2093410083915588161015491 3140115125873382241523237)
        ·
          refine ⟨588771586101259170285607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3140115125873382241523237 588771586101259170285607)
          ·
            refine ⟨883157379151888755428411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588771586101259170285607 883157379151888755428411)
            ·
              refine ⟨1324736068727833133142617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 883157379151888755428411 1324736068727833133142617)
              ·
                refine ⟨993552051545874849856963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1324736068727833133142617 993552051545874849856963)
                ·
                  refine ⟨1490328077318812274785445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 993552051545874849856963 1490328077318812274785445)
                  ·
                    refine ⟨279436514497277301522271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1490328077318812274785445 279436514497277301522271)
                    ·
                      rfl

theorem cell22_816301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_816301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816301 prefixEnd_816301 := by exact prefixLift 816301
  have htrace : WordTrace (prefixWord ++ tailWord_816301) baseStart_816301 baseEnd_816301 := by
    simpa [prefixWord, tailWord_816301, baseEnd_816301] using wordTrace_append hprefix tailTrace_816301
  have hstable : (prefixWord ++ tailWord_816301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816301).length < 2 ^ (prefixWord ++ tailWord_816301).sum := by decide
  have hdescent : baseEnd_816301 < baseStart_816301 := by decide
  rcases family_descends (prefixWord ++ tailWord_816301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816359 : List Nat := [1, 1, 5, 3, 2, 1, 1, 2, 3, 3]
def baseStart_816359 : Nat := 118140960795 + 816359 * 2 ^ 59
def prefixEnd_816359 : Nat := 4983230072969 + 3 ^ 40 * 816359 * 2
def baseEnd_816359 : Nat := 279456369082584483572093

theorem tailTrace_816359 : CollatzResearch.WordTrace tailWord_816359 prefixEnd_816359 279456369082584483572093 := by
  unfold tailWord_816359
  simp only [CollatzResearch.WordTrace]
  refine ⟨29775058849478240862276131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19850039232985493908184087 29775058849478240862276131)
  ·
    refine ⟨44662588274217361293414197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29775058849478240862276131 44662588274217361293414197)
    ·
      refine ⟨4187117650707877621257581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44662588274217361293414197 4187117650707877621257581)
      ·
        refine ⟨1570169119015454107971593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4187117650707877621257581 1570169119015454107971593)
        ·
          refine ⟨1177626839261590580978695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1570169119015454107971593 1177626839261590580978695)
          ·
            refine ⟨1766440258892385871468043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1177626839261590580978695 1766440258892385871468043)
            ·
              refine ⟨2649660388338578807202065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1766440258892385871468043 2649660388338578807202065)
              ·
                refine ⟨1987245291253934105401549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2649660388338578807202065 1987245291253934105401549)
                ·
                  refine ⟨745216984220225289525581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1987245291253934105401549 745216984220225289525581)
                  ·
                    refine ⟨279456369082584483572093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 745216984220225289525581 279456369082584483572093)
                    ·
                      rfl

theorem cell22_816359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_816359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816359 prefixEnd_816359 := by exact prefixLift 816359
  have htrace : WordTrace (prefixWord ++ tailWord_816359) baseStart_816359 baseEnd_816359 := by
    simpa [prefixWord, tailWord_816359, baseEnd_816359] using wordTrace_append hprefix tailTrace_816359
  have hstable : (prefixWord ++ tailWord_816359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816359).length < 2 ^ (prefixWord ++ tailWord_816359).sum := by decide
  have hdescent : baseEnd_816359 < baseStart_816359 := by decide
  rcases family_descends (prefixWord ++ tailWord_816359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816434 : List Nat := [3, 2, 1, 1, 4, 1, 3, 3, 4]
def baseStart_816434 : Nat := 118140960795 + 816434 * 2 ^ 59
def prefixEnd_816434 : Nat := 4983230072969 + 3 ^ 40 * 816434 * 2
def baseEnd_816434 : Nat := 93160681038436429315621

theorem tailTrace_816434 : CollatzResearch.WordTrace tailWord_816434 prefixEnd_816434 93160681038436429315621 := by
  unfold tailWord_816434
  simp only [CollatzResearch.WordTrace]
  refine ⟨7444448581051632167814089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19851862882804352447504237 7444448581051632167814089)
  ·
    refine ⟨5583336435788724125860567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7444448581051632167814089 5583336435788724125860567)
    ·
      refine ⟨8375004653683086188790851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5583336435788724125860567 8375004653683086188790851)
      ·
        refine ⟨12562506980524629283186277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8375004653683086188790851 12562506980524629283186277)
        ·
          refine ⟨2355470058848367990597427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12562506980524629283186277 2355470058848367990597427)
          ·
            refine ⟨3533205088272551985896141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2355470058848367990597427 3533205088272551985896141)
            ·
              refine ⟨1324951908102206994711053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3533205088272551985896141 1324951908102206994711053)
              ·
                refine ⟨496856965538327623016645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1324951908102206994711053 496856965538327623016645)
                ·
                  refine ⟨93160681038436429315621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 496856965538327623016645 93160681038436429315621)
                  ·
                    rfl

theorem cell22_816434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_816434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816434 prefixEnd_816434 := by exact prefixLift 816434
  have htrace : WordTrace (prefixWord ++ tailWord_816434) baseStart_816434 baseEnd_816434 := by
    simpa [prefixWord, tailWord_816434, baseEnd_816434] using wordTrace_append hprefix tailTrace_816434
  have hstable : (prefixWord ++ tailWord_816434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816434).length < 2 ^ (prefixWord ++ tailWord_816434).sum := by decide
  have hdescent : baseEnd_816434 < baseStart_816434 := by decide
  rcases family_descends (prefixWord ++ tailWord_816434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816447 : List Nat := [1, 1, 2, 2, 4, 3, 1, 2, 2, 4]
def baseStart_816447 : Nat := 118140960795 + 816447 * 2 ^ 59
def prefixEnd_816447 : Nat := 4983230072969 + 3 ^ 40 * 816447 * 2
def baseEnd_816447 : Nat := 279486493280981587371823

theorem tailTrace_816447 : CollatzResearch.WordTrace tailWord_816447 prefixEnd_816447 279486493280981587371823 := by
  unfold tailWord_816447
  simp only [CollatzResearch.WordTrace]
  refine ⟨29778268473159431891479595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19852178982106287927653063 29778268473159431891479595)
  ·
    refine ⟨44667402709739147837219393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29778268473159431891479595 44667402709739147837219393)
    ·
      refine ⟨33500552032304360877914545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44667402709739147837219393 33500552032304360877914545)
      ·
        refine ⟨25125414024228270658435909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33500552032304360877914545 25125414024228270658435909)
        ·
          refine ⟨4711015129542800748456733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25125414024228270658435909 4711015129542800748456733)
          ·
            refine ⟨1766630673578550280671275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4711015129542800748456733 1766630673578550280671275)
            ·
              refine ⟨2649946010367825421006913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1766630673578550280671275 2649946010367825421006913)
              ·
                refine ⟨1987459507775869065755185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2649946010367825421006913 1987459507775869065755185)
                ·
                  refine ⟨1490594630831901799316389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1987459507775869065755185 1490594630831901799316389)
                  ·
                    refine ⟨279486493280981587371823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1490594630831901799316389 279486493280981587371823)
                    ·
                      rfl

theorem cell22_816447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 4].length) (baseStart_816447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816447 prefixEnd_816447 := by exact prefixLift 816447
  have htrace : WordTrace (prefixWord ++ tailWord_816447) baseStart_816447 baseEnd_816447 := by
    simpa [prefixWord, tailWord_816447, baseEnd_816447] using wordTrace_append hprefix tailTrace_816447
  have hstable : (prefixWord ++ tailWord_816447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816447).length < 2 ^ (prefixWord ++ tailWord_816447).sum := by decide
  have hdescent : baseEnd_816447 < baseStart_816447 := by decide
  rcases family_descends (prefixWord ++ tailWord_816447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816449 : List Nat := [1, 2, 5, 2, 1, 1, 2, 1, 4, 3]
def baseStart_816449 : Nat := 118140960795 + 816449 * 2 ^ 59
def prefixEnd_816449 : Nat := 4983230072969 + 3 ^ 40 * 816449 * 2
def baseEnd_816449 : Nat := 279487177921854248821817

theorem tailTrace_816449 : CollatzResearch.WordTrace tailWord_816449 prefixEnd_816449 279487177921854248821817 := by
  unfold tailWord_816449
  simp only [CollatzResearch.WordTrace]
  refine ⟨29778341419152186233052401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19852227612768124155368267 29778341419152186233052401)
  ·
    refine ⟨22333756064364139674789301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29778341419152186233052401 22333756064364139674789301)
    ·
      refine ⟨2093789631034138094511497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22333756064364139674789301 2093789631034138094511497)
      ·
        refine ⟨1570342223275603570883623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2093789631034138094511497 1570342223275603570883623)
        ·
          refine ⟨2355513334913405356325435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1570342223275603570883623 2355513334913405356325435)
          ·
            refine ⟨3533270002370108034488153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2355513334913405356325435 3533270002370108034488153)
            ·
              refine ⟨2649952501777581025866115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3533270002370108034488153 2649952501777581025866115)
              ·
                refine ⟨3974928752666371538799173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2649952501777581025866115 3974928752666371538799173)
                ·
                  refine ⟨745299141124944663524845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3974928752666371538799173 745299141124944663524845)
                  ·
                    refine ⟨279487177921854248821817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 745299141124944663524845 279487177921854248821817)
                    ·
                      rfl

theorem cell22_816449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_816449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816449 prefixEnd_816449 := by exact prefixLift 816449
  have htrace : WordTrace (prefixWord ++ tailWord_816449) baseStart_816449 baseEnd_816449 := by
    simpa [prefixWord, tailWord_816449, baseEnd_816449] using wordTrace_append hprefix tailTrace_816449
  have hstable : (prefixWord ++ tailWord_816449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816449).length < 2 ^ (prefixWord ++ tailWord_816449).sum := by decide
  have hdescent : baseEnd_816449 < baseStart_816449 := by decide
  rcases family_descends (prefixWord ++ tailWord_816449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816507 : List Nat := [1, 1, 1, 1, 1, 6, 4, 2, 5]
def baseStart_816507 : Nat := 118140960795 + 816507 * 2 ^ 59
def prefixEnd_816507 : Nat := 4983230072969 + 3 ^ 40 * 816507 * 2
def baseEnd_816507 : Nat := 93169010835720476957213

theorem tailTrace_816507 : CollatzResearch.WordTrace tailWord_816507 prefixEnd_816507 93169010835720476957213 := by
  unfold tailWord_816507
  simp only [CollatzResearch.WordTrace]
  refine ⟨29780456852942062138663775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19853637901961374759109183 29780456852942062138663775)
  ·
    refine ⟨44670685279413093207995663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29780456852942062138663775 44670685279413093207995663)
    ·
      refine ⟨67006027919119639811993495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44670685279413093207995663 67006027919119639811993495)
      ·
        refine ⟨100509041878679459717990243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67006027919119639811993495 100509041878679459717990243)
        ·
          refine ⟨150763562818019189576985365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100509041878679459717990243 150763562818019189576985365)
          ·
            refine ⟨7067042007094649511421189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 150763562818019189576985365 7067042007094649511421189)
            ·
              refine ⟨1325070376330246783391473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7067042007094649511421189 1325070376330246783391473)
              ·
                refine ⟨993802782247685087543605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1325070376330246783391473 993802782247685087543605)
                ·
                  refine ⟨93169010835720476957213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 993802782247685087543605 93169010835720476957213)
                  ·
                    rfl

theorem cell22_816507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 5].length) (baseStart_816507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816507 prefixEnd_816507 := by exact prefixLift 816507
  have htrace : WordTrace (prefixWord ++ tailWord_816507) baseStart_816507 baseEnd_816507 := by
    simpa [prefixWord, tailWord_816507, baseEnd_816507] using wordTrace_append hprefix tailTrace_816507
  have hstable : (prefixWord ++ tailWord_816507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816507).length < 2 ^ (prefixWord ++ tailWord_816507).sum := by decide
  have hdescent : baseEnd_816507 < baseStart_816507 := by decide
  rcases family_descends (prefixWord ++ tailWord_816507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816537 : List Nat := [1, 2, 1, 2, 1, 5, 2, 1, 3, 4]
def baseStart_816537 : Nat := 118140960795 + 816537 * 2 ^ 59
def prefixEnd_816537 : Nat := 4983230072969 + 3 ^ 40 * 816537 * 2
def baseEnd_816537 : Nat := 279517302120251352621547

theorem tailTrace_816537 : CollatzResearch.WordTrace tailWord_816537 prefixEnd_816537 279517302120251352621547 := by
  unfold tailWord_816537
  simp only [CollatzResearch.WordTrace]
  refine ⟨29781551042833377262255865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19854367361888918174837243 29781551042833377262255865)
  ·
    refine ⟨22336163282125032946691899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29781551042833377262255865 22336163282125032946691899)
    ·
      refine ⟨33504244923187549420037849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22336163282125032946691899 33504244923187549420037849)
      ·
        refine ⟨25128183692390662065028387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33504244923187549420037849 25128183692390662065028387)
        ·
          refine ⟨37692275538585993097542581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25128183692390662065028387 37692275538585993097542581)
          ·
            refine ⟨3533650831742436852894617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37692275538585993097542581 3533650831742436852894617)
            ·
              refine ⟨2650238123806827639670963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3533650831742436852894617 2650238123806827639670963)
              ·
                refine ⟨3975357185710241459506445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2650238123806827639670963 3975357185710241459506445)
                ·
                  refine ⟨1490758944641340547314917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3975357185710241459506445 1490758944641340547314917)
                  ·
                    refine ⟨279517302120251352621547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1490758944641340547314917 279517302120251352621547)
                    ·
                      rfl

theorem cell22_816537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 4].length) (baseStart_816537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816537 prefixEnd_816537 := by exact prefixLift 816537
  have htrace : WordTrace (prefixWord ++ tailWord_816537) baseStart_816537 baseEnd_816537 := by
    simpa [prefixWord, tailWord_816537, baseEnd_816537] using wordTrace_append hprefix tailTrace_816537
  have hstable : (prefixWord ++ tailWord_816537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816537).length < 2 ^ (prefixWord ++ tailWord_816537).sum := by decide
  have hdescent : baseEnd_816537 < baseStart_816537 := by decide
  rcases family_descends (prefixWord ++ tailWord_816537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816569 : List Nat := [1, 2, 1, 4, 4, 1, 2, 1, 6]
def baseStart_816569 : Nat := 118140960795 + 816569 * 2 ^ 59
def prefixEnd_816569 : Nat := 4983230072969 + 3 ^ 40 * 816569 * 2
def baseEnd_816569 : Nat := 93176085458071311940483

theorem tailTrace_816569 : CollatzResearch.WordTrace tailWord_816569 prefixEnd_816569 93176085458071311940483 := by
  unfold tailWord_816569
  simp only [CollatzResearch.WordTrace]
  refine ⟨29782718178717446727420761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19855145452478297818280507 29782718178717446727420761)
  ·
    refine ⟨22337038634038085045565571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29782718178717446727420761 22337038634038085045565571)
    ·
      refine ⟨33505557951057127568348357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22337038634038085045565571 33505557951057127568348357)
      ·
        refine ⟨6282292115823211419065317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33505557951057127568348357 6282292115823211419065317)
        ·
          refine ⟨1177929771716852141074747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6282292115823211419065317 1177929771716852141074747)
          ·
            refine ⟨1766894657575278211612121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1177929771716852141074747 1766894657575278211612121)
            ·
              refine ⟨1325170993181458658709091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1766894657575278211612121 1325170993181458658709091)
              ·
                refine ⟨1987756489772187988063637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1325170993181458658709091 1987756489772187988063637)
                ·
                  refine ⟨93176085458071311940483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1987756489772187988063637 93176085458071311940483)
                  ·
                    rfl

theorem cell22_816569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 6].length) (baseStart_816569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816569 prefixEnd_816569 := by exact prefixLift 816569
  have htrace : WordTrace (prefixWord ++ tailWord_816569) baseStart_816569 baseEnd_816569 := by
    simpa [prefixWord, tailWord_816569, baseEnd_816569] using wordTrace_append hprefix tailTrace_816569
  have hstable : (prefixWord ++ tailWord_816569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816569).length < 2 ^ (prefixWord ++ tailWord_816569).sum := by decide
  have hdescent : baseEnd_816569 < baseStart_816569 := by decide
  rcases family_descends (prefixWord ++ tailWord_816569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816597 : List Nat := [1, 3, 2, 3, 1, 1, 3, 8]
def baseStart_816597 : Nat := 118140960795 + 816597 * 2 ^ 59
def prefixEnd_816597 : Nat := 4983230072969 + 3 ^ 40 * 816597 * 2
def baseEnd_816597 : Nat := 31059760149603466235707

theorem tailTrace_816597 : CollatzResearch.WordTrace tailWord_816597 prefixEnd_816597 31059760149603466235707 := by
  unfold tailWord_816597
  simp only [CollatzResearch.WordTrace]
  refine ⟨29783739422616007509440045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19855826281744005006293363 29783739422616007509440045)
  ·
    refine ⟨11168902283481002816040017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29783739422616007509440045 11168902283481002816040017)
    ·
      refine ⟨8376676712610752112030013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11168902283481002816040017 8376676712610752112030013)
      ·
        refine ⟨3141253767229032042011255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8376676712610752112030013 3141253767229032042011255)
        ·
          refine ⟨4711880650843548063016883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3141253767229032042011255 4711880650843548063016883)
          ·
            refine ⟨7067820976265322094525325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4711880650843548063016883 7067820976265322094525325)
            ·
              refine ⟨2650432866099495785446997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7067820976265322094525325 2650432866099495785446997)
              ·
                refine ⟨31059760149603466235707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2650432866099495785446997 31059760149603466235707)
                ·
                  rfl

theorem cell22_816597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 8].length) (baseStart_816597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816597 prefixEnd_816597 := by exact prefixLift 816597
  have htrace : WordTrace (prefixWord ++ tailWord_816597) baseStart_816597 baseEnd_816597 := by
    simpa [prefixWord, tailWord_816597, baseEnd_816597] using wordTrace_append hprefix tailTrace_816597
  have hstable : (prefixWord ++ tailWord_816597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816597).length < 2 ^ (prefixWord ++ tailWord_816597).sum := by decide
  have hdescent : baseEnd_816597 < baseStart_816597 := by decide
  rcases family_descends (prefixWord ++ tailWord_816597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816680 : List Nat := [2, 1, 5, 2, 2, 1, 1, 4, 1, 3]
def baseStart_816680 : Nat := 118140960795 + 816680 * 2 ^ 59
def prefixEnd_816680 : Nat := 4983230072969 + 3 ^ 40 * 816680 * 2
def baseEnd_816680 : Nat := 279566253942646646296109

theorem tailTrace_816680 : CollatzResearch.WordTrace tailWord_816680 prefixEnd_816680 279566253942646646296109 := by
  unfold tailWord_816680
  simp only [CollatzResearch.WordTrace]
  refine ⟨14893383340657656342355747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19857844454210208456474329 14893383340657656342355747)
  ·
    refine ⟨22340075010986484513533621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14893383340657656342355747 22340075010986484513533621)
    ·
      refine ⟨2094382032279982923143777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22340075010986484513533621 2094382032279982923143777)
      ·
        refine ⟨1570786524209987192357833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2094382032279982923143777 1570786524209987192357833)
        ·
          refine ⟨1178089893157490394268375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1570786524209987192357833 1178089893157490394268375)
          ·
            refine ⟨1767134839736235591402563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1178089893157490394268375 1767134839736235591402563)
            ·
              refine ⟨2650702259604353387103845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1767134839736235591402563 2650702259604353387103845)
              ·
                refine ⟨497006673675816260081971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2650702259604353387103845 497006673675816260081971)
                ·
                  refine ⟨745510010513724390122957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 497006673675816260081971 745510010513724390122957)
                  ·
                    refine ⟨279566253942646646296109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 745510010513724390122957 279566253942646646296109)
                    ·
                      rfl

theorem cell22_816680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_816680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816680 prefixEnd_816680 := by exact prefixLift 816680
  have htrace : WordTrace (prefixWord ++ tailWord_816680) baseStart_816680 baseEnd_816680 := by
    simpa [prefixWord, tailWord_816680, baseEnd_816680] using wordTrace_append hprefix tailTrace_816680
  have hstable : (prefixWord ++ tailWord_816680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816680).length < 2 ^ (prefixWord ++ tailWord_816680).sum := by decide
  have hdescent : baseEnd_816680 < baseStart_816680 := by decide
  rcases family_descends (prefixWord ++ tailWord_816680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816719 : List Nat := [1, 1, 2, 1, 1, 2, 3, 4, 4, 3]
def baseStart_816719 : Nat := 118140960795 + 816719 * 2 ^ 59
def prefixEnd_816719 : Nat := 4983230072969 + 3 ^ 40 * 816719 * 2
def baseEnd_816719 : Nat := 279579604439663544570989

theorem tailTrace_816719 : CollatzResearch.WordTrace tailWord_816719 prefixEnd_816719 279579604439663544570989 := by
  unfold tailWord_816719
  simp only [CollatzResearch.WordTrace]
  refine ⟨29788189128174022345381211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19858792752116014896920807 29788189128174022345381211)
  ·
    refine ⟨44682283692261033518071817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29788189128174022345381211 44682283692261033518071817)
    ·
      refine ⟨33511712769195775138553863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44682283692261033518071817 33511712769195775138553863)
      ·
        refine ⟨50267569153793662707830795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33511712769195775138553863 50267569153793662707830795)
        ·
          refine ⟨75401353730690494061746193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50267569153793662707830795 75401353730690494061746193)
          ·
            refine ⟨56551015298017870546309645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75401353730690494061746193 56551015298017870546309645)
            ·
              refine ⟨21206630736756701454866117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56551015298017870546309645 21206630736756701454866117)
              ·
                refine ⟨3976243263141881522787397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21206630736756701454866117 3976243263141881522787397)
                ·
                  refine ⟨745545611839102785522637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3976243263141881522787397 745545611839102785522637)
                  ·
                    refine ⟨279579604439663544570989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 745545611839102785522637 279579604439663544570989)
                    ·
                      rfl

theorem cell22_816719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4, 3].length) (baseStart_816719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816719 prefixEnd_816719 := by exact prefixLift 816719
  have htrace : WordTrace (prefixWord ++ tailWord_816719) baseStart_816719 baseEnd_816719 := by
    simpa [prefixWord, tailWord_816719, baseEnd_816719] using wordTrace_append hprefix tailTrace_816719
  have hstable : (prefixWord ++ tailWord_816719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816719).length < 2 ^ (prefixWord ++ tailWord_816719).sum := by decide
  have hdescent : baseEnd_816719 < baseStart_816719 := by decide
  rcases family_descends (prefixWord ++ tailWord_816719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816721 : List Nat := [1, 2, 2, 1, 3, 2, 4, 3, 4]
def baseStart_816721 : Nat := 118140960795 + 816721 * 2 ^ 59
def prefixEnd_816721 : Nat := 4983230072969 + 3 ^ 40 * 816721 * 2
def baseEnd_816721 : Nat := 93193429693512068673661

theorem tailTrace_816721 : CollatzResearch.WordTrace tailWord_816721 prefixEnd_816721 93193429693512068673661 := by
  unfold tailWord_816721
  simp only [CollatzResearch.WordTrace]
  refine ⟨29788262074166776686954017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19858841382777851124636011 29788262074166776686954017)
  ·
    refine ⟨22341196555625082515215513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29788262074166776686954017 22341196555625082515215513)
    ·
      refine ⟨16755897416718811886411635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22341196555625082515215513 16755897416718811886411635)
      ·
        refine ⟨25133846125078217829617453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16755897416718811886411635 25133846125078217829617453)
        ·
          refine ⟨9425192296904331686106545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25133846125078217829617453 9425192296904331686106545)
          ·
            refine ⟨7068894222678248764579909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9425192296904331686106545 7068894222678248764579909)
            ·
              refine ⟨1325417666752171643358733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7068894222678248764579909 1325417666752171643358733)
              ·
                refine ⟨497031625032064366259525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1325417666752171643358733 497031625032064366259525)
                ·
                  refine ⟨93193429693512068673661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 497031625032064366259525 93193429693512068673661)
                  ·
                    rfl

theorem cell22_816721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3, 4].length) (baseStart_816721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_816721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_816721 prefixEnd_816721 := by exact prefixLift 816721
  have htrace : WordTrace (prefixWord ++ tailWord_816721) baseStart_816721 baseEnd_816721 := by
    simpa [prefixWord, tailWord_816721, baseEnd_816721] using wordTrace_append hprefix tailTrace_816721
  have hstable : (prefixWord ++ tailWord_816721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816721).length < 2 ^ (prefixWord ++ tailWord_816721).sum := by decide
  have hdescent : baseEnd_816721 < baseStart_816721 := by decide
  rcases family_descends (prefixWord ++ tailWord_816721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
